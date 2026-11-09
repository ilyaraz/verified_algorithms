import RamLang.Compiler.Proofs.Simulation

namespace RamLang.Compiler
open WordRam ABI

variable {w free n extra dst callee : Nat} {code : WordRam.Program registers} {rho : RandomMemory w}
  {frames entries : FunctionId → Nat} {exhausted : Nat} {stack : Region}
  {locals locals' : Locals w} {mem mem' : DataMemory w} {log : List (Access w)}
  {args : List Atom} {values : List (Word w)} {f : Function} {value : Word w}

/-- Each call contains one checked setup followed by its saved continuation. -/
theorem call_parts {pc : Nat}
    (hc : CodeAt code pc (lower frames entries exhausted pc (.call dst callee args))) :
    CodeAt code pc (callSetup (frames callee) (entries callee) exhausted args) ∧
    CodeAt code (pc+(arguments 0 args).length+6) (spill dst result) := by
  have heq : lower frames entries exhausted pc (.call dst callee args) =
      callSetup (frames callee) (entries callee) exhausted args ++ spill dst result := by
    simp [lower,callSetup,guardCode,installCode,List.append_assoc]
  rw [heq] at hc
  refine ⟨hc.prefix,?_⟩
  have hlen : (callSetup (frames callee) (entries callee) exhausted args).length =
      (arguments 0 args).length+6 := by simp [callSetup,guardCode,installCode]
  simpa only [hlen,Nat.add_assoc] using hc.suffix

/-- Insufficient capacity reaches the shared error halt before any argument or
callee header write, retaining the caller and all earlier application effects. -/
theorem implements_callExhausts
    (hframe : frames callee = f.frameSize) (hframefit : f.frameSize < modulus w)
    (herror : CodeAt code exhausted errorCode) (hshort : free < f.frameSize) :
    Implements code rho frames entries exhausted stack free (.call dst callee args) locals mem
      .exhausted mem [] 4 0 := by
  intro base savedFP returnPC s hf hfree hret hc
  obtain ⟨hsetup,_⟩ := call_parts hc
  have hguard : CodeAt code s.pc (guardCode f.frameSize exhausted) := by
    rw [hframe] at hsetup
    exact hsetup.prefix.prefix.prefix
  have hs := guard_exhausted (rho := rho) hguard herror hf.stackPointer hf.stackLimit
    hf.frameUpper hf.stackFits hframefit (by omega)
  refine ⟨(afterGuard f.frameSize exhausted s).put status (word w 2),[],⟨hs,?_,rfl,?_,?_⟩⟩
  · constructor
    · simp [State.put]
    · exact hf.applicationMemory
  · simp [AccessPolicy.AllowsTrace]
  · exact exhausted_stackBound hguard herror hf.stackPointer hf.stackLimit
      hf.frameUpper hf.stackFits hframefit (by omega) (hf.sp_le (by omega))

/-- A body returning from an ordinary call reconstructs its suspended caller,
then spills the result into the checked destination slot. -/
theorem implements_call
    (hframe : frames callee = f.frameSize)
    (hentry : CodeAt code (entries callee)
      (prologue ++ lower frames entries exhausted (entries callee+2) f.body))
    (hcodefit : code.size < modulus w)
    (he : args.mapM (Atom.eval locals) = .ok values) (harity : values.length = f.parameters.length)
    (hspace : f.frameSize ≤ free) (hw : writeLocal locals dst value = .ok locals')
    (hbody : Implements code rho frames entries exhausted stack (free-f.frameSize) f.body
      (values.map some ++ List.replicate f.locals.length none) mem (.returned value) mem' log n extra) :
    Implements code rho frames entries exhausted stack free (.call dst callee args) locals mem
      (.next locals') mem' log ((arguments 0 args).length+10+n) (f.frameSize+extra) := by
  intro base savedFP returnPC s hf hfree hret hc
  obtain ⟨hsetup,hspill⟩ := call_parts hc
  rw [hframe] at hsetup
  have hslots : 2+(values.map some ++ List.replicate f.locals.length (none : Option (Word w))).length = f.frameSize := by
    simp [Function.frameSize,Function.slots,harity]
  have hcapacity : base+2+locals.length+f.frameSize ≤ stack.base+stack.size := by
    have := hf.frameUpper
    omega
  obtain ⟨t,trace₁,hsetupSteps,htpc,hcallee,hprojSetup,hpolSetup,hbelowSetup⟩ :=
    call_setup (rho := rho) he harity hf hcapacity hsetup hentry.prefix
  have hreturn : s.pc+(arguments 0 args).length+6 < modulus w := hspill.address_fits hcodefit
  obtain ⟨u,trace₂,h₂⟩ := hbody (base+2+locals.length) (word w base)
    (s.pc+(arguments 0 args).length+6) t hcallee (by omega) hreturn (by
      rw [htpc]; exact hentry.suffix)
  obtain ⟨hupc,hufp,husp,huv,hulimit,huapp⟩ := h₂.post
  have hcaller : FrameState stack base locals savedFP returnPC mem' u := by
    apply restore_caller hf hufp husp hulimit huapp
    intro a ha hbelow
    exact (below_frame_preserved h₂.execution h₂.policy ha hbelow).trans (hbelowSetup a hbelow)
  obtain ⟨hd,rfl⟩ := writeLocal_ok hw
  have hresult : FrameState stack base (locals.set dst (some value)) savedFP returnPC mem'
      (afterSave (2+dst) result u) := hcaller.spill hd huv (by decide)
  have hspillCode : CodeAt code u.pc (spill dst result) := by rw [hupc]; exact hspill
  have hsteps := (hsetupSteps.trans h₂.execution).trans (spill_steps hspillCode)
  refine ⟨afterSave (2+dst) result u,(trace₁++trace₂)++saveTrace (2+dst) result u,⟨?_,⟨?_,hresult⟩,?_,?_,?_⟩⟩
  · have hn : ((arguments 0 args).length+8+n)+2 = (arguments 0 args).length+10+n := by omega
    simpa only [hn] using hsteps
  · rw [afterSave_pc,hupc]
    simp only [size]
    omega
  · rw [project_append,project_append,hprojSetup,h₂.projection,spill_project hcaller hd]
    simp
  · apply (AccessPolicy.allowsTrace_append _).mpr
    refine ⟨(AccessPolicy.allowsTrace_append _).mpr ⟨?_,?_⟩,?_⟩
    · exact framePolicy_mono (Nat.le_refl _) (by omega) hpolSetup
    · exact framePolicy_mono (by omega) (by omega) h₂.policy
    · exact framePolicy_mono (Nat.le_refl _) (by omega) (spill_policy hcaller hd)
  · have hsb := (call_setup_stackBound (rho := rho) hsetup hentry.prefix
      hf.stackPointer hf.stackLimit hcapacity hf.stackFits).mono
        (show base+2+locals.length+f.frameSize ≤ base+2+locals.length+(f.frameSize+extra) by omega)
    have hbb := h₂.stackBound.mono
      (show base+2+locals.length+2+(values.map some ++ List.replicate f.locals.length (none : Option (Word w))).length+extra ≤
        base+2+locals.length+(f.frameSize+extra) by omega)
    have hh := StackBound.trans (hsetupSteps.trans h₂.execution) (StackBound.trans hsetupSteps hsb hbb)
      (quiet_stackBound hspillCode (quiet_spill dst result) (hcaller.sp_le (by omega)))
    have hn : ((arguments 0 args).length+8+n)+2 = (arguments 0 args).length+10+n := by omega
    simpa only [spill,List.length_cons,List.length_nil,hn] using hh

/-- Exhaustion in a callee keeps all partial effects and halts without unwinding. -/
theorem implements_callBodyExhausts
    (hframe : frames callee = f.frameSize)
    (hentry : CodeAt code (entries callee)
      (prologue ++ lower frames entries exhausted (entries callee+2) f.body))
    (hcodefit : code.size < modulus w)
    (he : args.mapM (Atom.eval locals) = .ok values) (harity : values.length = f.parameters.length)
    (hspace : f.frameSize ≤ free)
    (hbody : Implements code rho frames entries exhausted stack (free-f.frameSize) f.body
      (values.map some ++ List.replicate f.locals.length none) mem .exhausted mem' log n extra) :
    Implements code rho frames entries exhausted stack free (.call dst callee args) locals mem
      .exhausted mem' log ((arguments 0 args).length+8+n) (f.frameSize+extra) := by
  intro base savedFP returnPC s hf hfree hret hc
  obtain ⟨hsetup,hspill⟩ := call_parts hc
  rw [hframe] at hsetup
  have hslots : 2+(values.map some ++ List.replicate f.locals.length (none : Option (Word w))).length = f.frameSize := by
    simp [Function.frameSize,Function.slots,harity]
  have hcapacity : base+2+locals.length+f.frameSize ≤ stack.base+stack.size := by
    have := hf.frameUpper
    omega
  obtain ⟨t,trace₁,hsetupSteps,htpc,hcallee,hprojSetup,hpolSetup,_⟩ :=
    call_setup (rho := rho) he harity hf hcapacity hsetup hentry.prefix
  have hreturn : s.pc+(arguments 0 args).length+6 < modulus w := hspill.address_fits hcodefit
  obtain ⟨u,trace₂,h₂⟩ := hbody (base+2+locals.length) (word w base)
    (s.pc+(arguments 0 args).length+6) t hcallee (by omega) hreturn (by
      rw [htpc]; exact hentry.suffix)
  refine ⟨u,trace₁++trace₂,⟨h₂.execution.prepend hsetupSteps,h₂.post,?_,?_,?_⟩⟩
  · rw [project_append,hprojSetup,h₂.projection,List.nil_append]
  · exact (AccessPolicy.allowsTrace_append _).mpr
      ⟨framePolicy_mono (Nat.le_refl _) (by omega) hpolSetup,
        framePolicy_mono (by omega) (by omega) h₂.policy⟩
  · exact StackBound.trans hsetupSteps
      ((call_setup_stackBound hsetup hentry.prefix hf.stackPointer hf.stackLimit hcapacity hf.stackFits).mono (by omega))
      (h₂.stackBound.mono (by omega))

/-- Complete finite-derivation simulation for arbitrary recursive and mutually
recursive bodies. It uses the actual ISA, charges every template instruction,
and preserves application/random traces while bounding every stack access. -/
theorem evaluation_simulation {source : Program} {stmt : Stmt} {flow : Flow w}
    (linked : LinkedFunctions source code frames entries exhausted)
    (fitCode : code.size < modulus w)
    (fitFrames : ∀ (id : FunctionId) (f : Function), source.functions[id]? = some f → f.frameSize < modulus w)
    (error : CodeAt code exhausted errorCode)
    (d : Evaluation source rho free stmt locals mem flow mem' log)
    (separated : Separated stack log) :
    Implements code rho frames entries exhausted stack free stmt locals mem flow mem' log
      (instructions d) (extraStack d) := by
  induction d with
  | skip => exact implements_skip
  | primitive he => exact implements_primitive he separated
  | sequence a b ia ib =>
    have hsep := (separated_append _ _).mp separated
    exact implements_sequence (ia hsep.1) (ib hsep.2) a.preserves_length
  | sequenceStop a stop ih => exact implements_sequenceStop stop (ih separated)
  | ifTrue test branch ih => exact implements_ifTrue test (ih separated)
  | ifFalse test branch ih => exact implements_ifFalse test (ih separated)
  | whileFalse test => exact implements_whileFalse test
  | whileContinue test body tail ia ib =>
    have hsep := (separated_append _ _).mp separated
    exact implements_whileContinue test (ia hsep.1) (ib hsep.2) body.preserves_length
  | whileStop test body stop ih => exact implements_whileStop test stop (ih separated)
  | call lookup args arity space body assign ih =>
    have hl := linked _ _ lookup
    exact implements_call hl.1 hl.2 fitCode args arity space assign (ih separated)
  | callExhausts lookup args arity destination space =>
    exact implements_callExhausts (linked _ _ lookup).1 (fitFrames _ _ lookup) error space
  | callBodyExhausts lookup args arity destination space body ih =>
    have hl := linked _ _ lookup
    exact implements_callBodyExhausts hl.1 hl.2 fitCode args arity space (ih separated)
  | ret hx => exact implements_return hx

end RamLang.Compiler
