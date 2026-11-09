import RamLang.Compiler.Proofs.Entry
import RamLang.EvaluationSoundness

namespace RamLang.Compiler
open WordRam ABI

/-- Public success is separate from the function's ordinary word-valued result. -/
def successCode : Code := [.mov status (.imm 1),.halt]

variable {w : Nat} {p : WordRam.Program registers} {rho : RandomMemory w}
  {s : State w registers} {stack : Region}

theorem success_terminates (hc : CodeAt p s.pc successCode) :
    WordRam.TerminatesIn p rho s 2 (s.put status (word w 1)) [] := by
  have hs : WordRam.Step p rho s (s.put status (word w 1)) none := by
    unfold WordRam.Step WordRam.step
    rw [hc.head]
    rfl
  refine ⟨1,rfl,.cons hs (.refl _),?_⟩
  unfold WordRam.step
  rw [show (s.put status (word w 1)).pc = s.pc+1 from rfl,hc.tail.head]

theorem success_stackBound {top : Nat} (hc : CodeAt p s.pc successCode)
    (ha : (s.regs sp).toNat ≤ top) : StackBound p rho s 2 top := by
  intro fuel hf
  rcases (show fuel = 0 ∨ fuel = 1 ∨ fuel = 2 by omega) with rfl | rfl | rfl
  all_goals simp only [WordRam.run,WordRam.step,hc.head,State.put,Operand.eval,
    hc.tail.head,WordRam.RunResult.prepend]
  all_goals simp_all [update,Fin.ext_iff,status,sp]

/-- The compiler emits the declared entry wrapper at PC zero. -/
theorem compile_wrapper {source : Program} {c : CompiledProgram} {f : Function}
    (hc : compile source = .ok c) (hf : source.functions[source.entry]? = some f) :
    CodeAt c.code 0 (wrapper f.frameSize
      ((c.functions[source.entry]?.map FunctionLayout.entry).getD 0) f.parameters.length) := by
  have hcheck := compile_checked hc
  unfold WellFormed at hcheck
  simp only [compile,hcheck,Except.ok.injEq] at hc
  subst c
  simp only [hf,Option.map_some,Option.getD_some]
  exact (CodeAt.toArray _).prefix

/-- The entry setup and successful continuation are parts of the same wrapper. -/
theorem wrapper_parts {frame target arity : Nat}
    (hc : CodeAt p 0 (wrapper frame target arity)) :
    CodeAt p 0 (parameterCode frame arity ++ installCode frame target) ∧
    CodeAt p (8+2*arity) successCode := by
  have heq : wrapper frame target arity =
      (parameterCode frame arity ++ installCode frame target) ++ successCode ++ errorCode := by
    simp [wrapper,parameterCode,initialCode,guardCode,installCode,successCode,errorCode,List.append_assoc]
  rw [heq] at hc
  have hlen : (parameterCode frame arity ++ installCode frame target).length = 8+2*arity := by
    simp only [parameterCode,initialCode,guardCode,installCode,List.length_append,List.length_cons,List.length_nil,
      entryArguments_length]
    omega
  exact ⟨hc.prefix.prefix,by simpa only [hlen,Nat.zero_add] using hc.prefix.suffix⟩

/-- A successful source derivation yields a terminating compiled invocation with
actual instruction count, application trace, and physical stack-pointer peak. -/
theorem compiled_returns {source : Program} {c : CompiledProgram} {f : Function}
    {value : Word w} {mem' : DataMemory w} {log : List (Access w)}
    (hcompile : compile source = .ok c) (hfit : c.Fits w)
    (hentry : source.functions[source.entry]? = some f)
    (hpc : s.pc = 0) (hsp : s.regs sp = word w stack.base)
    (hlimit : s.regs limit = word w (stack.base+stack.size)) (hstack : stack.Fits w)
    (hspace : f.frameSize ≤ stack.size)
    (d : Evaluation source rho (stack.size-f.frameSize) f.body
      ((entryValues s f.parameters.length).map some ++ List.replicate f.locals.length none)
      s.mem (.returned value) mem' log)
    (hsep : Separated stack log) :
    ∃ t trace, WordRam.TerminatesIn c.code rho s (12+2*f.parameters.length+instructions d) t trace ∧
      t.regs status = word w 1 ∧ t.regs result = value ∧ t.regs sp = word w stack.base ∧
      ApplicationMemory stack mem' t.mem ∧ projectTrace stack trace = log ∧
      StackBound c.code rho s (12+2*f.parameters.length+instructions d)
        (stack.base+f.frameSize+extraStack d) := by
  let entries := fun (id : FunctionId) => (c.functions[id]?.map FunctionLayout.entry).getD 0
  let frames := fun (id : FunctionId) => (source.functions[id]?.map Function.frameSize).getD 0
  have hlinked := compile_linked hcompile source.entry f hentry
  obtain ⟨hsetup,hsuccess⟩ := wrapper_parts (compile_wrapper hcompile hentry)
  have hsetup' : CodeAt c.code s.pc
      (parameterCode f.frameSize f.parameters.length ++ installCode f.frameSize (entries source.entry)) := by
    rw [hpc]; exact hsetup
  obtain ⟨t,trace₁,hs,htpc,hframe,hproj,hbound⟩ := entry_setup hsetup' hlinked.2.prefix hpc hsp hlimit hstack hspace
  have hslots : ((entryValues s f.parameters.length).map some ++
      List.replicate f.locals.length (none : Option (Word w))).length = f.slots := by
    simp [entryValues,Function.slots]
  have hretfit : 8+2*f.parameters.length < modulus w := hsuccess.address_fits hfit.1
  have himpl := compile_evaluation hcompile hfit d hsep
  obtain ⟨u,trace₂,hu⟩ := himpl stack.base (word w 0) (8+2*f.parameters.length) t hframe
    (by rw [hslots]; unfold Function.frameSize; omega) hretfit (by
      rw [htpc]; exact hlinked.2.suffix)
  obtain ⟨hupc,hufp,husp,huv,hulimit,huapp⟩ := hu.post
  have hsuccess' : CodeAt c.code u.pc successCode := by rw [hupc]; exact hsuccess
  have hh := (hs.trans hu.execution).then_terminates (success_terminates hsuccess')
  have hn : (10+2*f.parameters.length+instructions d)+2 = 12+2*f.parameters.length+instructions d := by omega
  refine ⟨u.put status (word w 1),trace₁++trace₂,?_,?_,?_,?_,huapp,?_,?_⟩
  · simpa only [hn,List.append_nil] using hh
  · simp [State.put]
  · simpa [State.put,update,Fin.ext_iff,result,status] using huv
  · simpa [State.put,update,Fin.ext_iff,sp,status] using husp
  · rw [project_append,hproj,hu.projection,List.nil_append]
  · have hb₂ : StackBound c.code rho t (instructions d) (stack.base+f.frameSize+extraStack d) := by
      have he : stack.base+2+((entryValues s f.parameters.length).map some ++
          List.replicate f.locals.length (none : Option (Word w))).length+extraStack d =
          stack.base+f.frameSize+extraStack d := by rw [hslots]; unfold Function.frameSize; omega
      simpa only [he] using hu.stackBound
    have hub := hb₂.end hu.execution
    have hb := StackBound.trans (hs.trans hu.execution)
      (StackBound.trans hs (hbound.mono (by omega)) hb₂) (success_stackBound hsuccess' hub)
    simpa only [hn] using hb

/-- Exhaustion inside the entry body preserves partial application effects and
terminates without executing the success continuation or unwinding the stack. -/
theorem compiled_body_exhausts {source : Program} {c : CompiledProgram} {f : Function}
    {mem' : DataMemory w} {log : List (Access w)}
    (hcompile : compile source = .ok c) (hfit : c.Fits w)
    (hentry : source.functions[source.entry]? = some f)
    (hpc : s.pc = 0) (hsp : s.regs sp = word w stack.base)
    (hlimit : s.regs limit = word w (stack.base+stack.size)) (hstack : stack.Fits w)
    (hspace : f.frameSize ≤ stack.size)
    (d : Evaluation source rho (stack.size-f.frameSize) f.body
      ((entryValues s f.parameters.length).map some ++ List.replicate f.locals.length none)
      s.mem .exhausted mem' log)
    (hsep : Separated stack log) :
    ∃ t trace, WordRam.TerminatesIn c.code rho s (10+2*f.parameters.length+instructions d) t trace ∧
      t.regs status = word w 2 ∧ ApplicationMemory stack mem' t.mem ∧
      projectTrace stack trace = log ∧
      StackBound c.code rho s (10+2*f.parameters.length+instructions d)
        (stack.base+f.frameSize+extraStack d) := by
  let entries := fun (id : FunctionId) => (c.functions[id]?.map FunctionLayout.entry).getD 0
  have hlinked := compile_linked hcompile source.entry f hentry
  obtain ⟨hsetup,hsuccess⟩ := wrapper_parts (compile_wrapper hcompile hentry)
  have hsetup' : CodeAt c.code s.pc
      (parameterCode f.frameSize f.parameters.length ++ installCode f.frameSize (entries source.entry)) := by
    rw [hpc]; exact hsetup
  obtain ⟨t,trace₁,hs,htpc,hframe,hproj,hbound⟩ := entry_setup hsetup' hlinked.2.prefix hpc hsp hlimit hstack hspace
  have hslots : ((entryValues s f.parameters.length).map some ++
      List.replicate f.locals.length (none : Option (Word w))).length = f.slots := by
    simp [entryValues,Function.slots]
  have hretfit : 8+2*f.parameters.length < modulus w := hsuccess.address_fits hfit.1
  obtain ⟨u,trace₂,hu⟩ := compile_evaluation hcompile hfit d hsep stack.base (word w 0)
    (8+2*f.parameters.length) t hframe (by rw [hslots]; unfold Function.frameSize; omega) hretfit (by
      rw [htpc]; exact hlinked.2.suffix)
  refine ⟨u,trace₁++trace₂,hs.then_terminates hu.execution,hu.post.1,hu.post.2,?_,?_⟩
  · rw [project_append,hproj,hu.projection,List.nil_append]
  · apply StackBound.trans hs (hbound.mono (by omega))
    have he : stack.base+2+((entryValues s f.parameters.length).map some ++
        List.replicate f.locals.length (none : Option (Word w))).length+extraStack d =
        stack.base+f.frameSize+extraStack d := by rw [hslots]; unfold Function.frameSize; omega
    simpa only [he] using hu.stackBound

theorem compile_exhaustion {source : Program} {c : CompiledProgram} {f : Function}
    (hc : compile source = .ok c) (hf : source.functions[source.entry]? = some f) :
    c.exhaustion = exhaustionPC f.parameters.length := by
  have hcheck := compile_checked hc
  unfold WellFormed at hcheck
  simp only [compile,hcheck,Except.ok.injEq] at hc
  subst c
  simp [hf]

/-- Too little capacity for even the entry frame halts in six instructions,
without reading or writing ordinary memory. -/
theorem compiled_entry_exhausts {source : Program} {c : CompiledProgram} {f : Function}
    (hcompile : compile source = .ok c) (hfit : c.Fits w)
    (hentry : source.functions[source.entry]? = some f)
    (hpc : s.pc = 0) (hsp : s.regs sp = word w stack.base)
    (hlimit : s.regs limit = word w (stack.base+stack.size)) (hstack : stack.Fits w)
    (hshort : stack.size < f.frameSize) :
    ∃ t, WordRam.TerminatesIn c.code rho s 6 t [] ∧ t.regs status = word w 2 ∧ t.mem = s.mem ∧
      StackBound c.code rho s 6 stack.base := by
  obtain ⟨hsetup,_⟩ := wrapper_parts (compile_wrapper hcompile hentry)
  have hinit : CodeAt c.code s.pc initialCode := by rw [hpc]; exact hsetup.prefix.prefix.prefix.prefix
  let t := afterInitial s
  have hs := initial_steps (rho := rho) hinit
  have htpc : t.pc = 2 := by simp [t,afterInitial,State.put,hpc]
  have htsp : t.regs sp = word w stack.base := by
    simpa [t,afterInitial,State.put,update,Fin.ext_iff,status,fp,sp] using hsp
  have htlimit : t.regs limit = word w (stack.base+stack.size) := by
    simpa [t,afterInitial,State.put,update,Fin.ext_iff,status,fp,limit] using hlimit
  have hguard : CodeAt c.code t.pc (guardCode f.frameSize (exhaustionPC f.parameters.length)) := by
    rw [htpc]
    exact hsetup.prefix.prefix.prefix.suffix
  have herror : CodeAt c.code (exhaustionPC f.parameters.length) errorCode := by
    rw [←compile_exhaustion hcompile hentry]
    exact compile_error hcompile
  have hframefit := compile_frame_fit hcompile hfit hentry
  have ht := guard_exhausted (rho := rho) hguard herror htsp htlimit (by omega) hstack hframefit
    (by simpa using hshort)
  refine ⟨_,hs.then_terminates ht,?_,rfl,?_⟩
  · simp [State.put]
  · have hb : stack.base < modulus w := by have := hstack; unfold Region.Fits at this; omega
    have hsbound : (s.regs sp).toNat ≤ stack.base := by rw [hsp,word_toNat_of_lt hb]; exact Nat.le_refl _
    have htbound : (t.regs sp).toNat ≤ stack.base := by rw [htsp,word_toNat_of_lt hb]; exact Nat.le_refl _
    exact StackBound.trans hs (quiet_stackBound hinit
      (by simp [Quiet,initialCode,straightInstruction,Instr.destination,Fin.ext_iff,status,fp,sp]) hsbound)
      (exhausted_stackBound hguard herror htsp htlimit (by omega) hstack hframefit (by simpa using hshort) htbound)

end RamLang.Compiler
