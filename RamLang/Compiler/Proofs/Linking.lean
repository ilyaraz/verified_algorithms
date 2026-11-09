import RamLang.Compiler.Proofs.CallSimulation

namespace RamLang.Compiler
open WordRam ABI

variable {w id free : Nat} {f : Function} {rho : RandomMemory w} {stmt : Stmt}
  {locals : Locals w} {mem mem' : DataMemory w} {flow : Flow w} {log : List (Access w)}
  {stack : Region}

/-- The layout pass and emission pass identify the same single body at every index. -/
theorem layouts_body {code : WordRam.Program registers} (fs : List Function)
    (frames entries : FunctionId → Nat) (exhausted pc : Nat)
    (hc : CodeAt code pc (bodies frames entries exhausted pc fs))
    (hi : fs[id]? = some f) :
    ∃ layout, (layouts pc fs)[id]? = some layout ∧ layout.frameWords = f.frameSize ∧
      CodeAt code layout.entry (prologue ++ lower frames entries exhausted (layout.entry+2) f.body) := by
  induction fs generalizing pc id with
  | nil => simp at hi
  | cons first rest ih =>
    cases id with
    | zero =>
      simp only [List.getElem?_cons_zero,Option.some.injEq] at hi
      subst f
      exact ⟨⟨pc,prologue.length+size first.body,first.frameSize⟩,rfl,rfl,hc.prefix⟩
    | succ id =>
      simp only [List.getElem?_cons_succ] at hi
      have htail : CodeAt code (pc+prologue.length+size first.body)
          (bodies frames entries exhausted (pc+prologue.length+size first.body) rest) := by
        simpa only [List.length_append,lower_length,Nat.add_assoc] using hc.suffix
      obtain ⟨layout,hl,hf,hbody⟩ := ih _ htail hi
      refine ⟨layout,?_,hf,hbody⟩
      simpa only [layouts,List.getElem?_cons_succ,Nat.add_assoc] using hl

/-- Successful compilation provides the final-address function-body certificate
used by the recursive simulation; no saved code address is relocated afterward. -/
theorem compile_linked {source : Program} {c : CompiledProgram}
    (h : compile source = .ok c) :
    LinkedFunctions source c.code
      (fun id => (source.functions[id]?.map Function.frameSize).getD 0)
      (fun id => (c.functions[id]?.map FunctionLayout.entry).getD 0) c.exhaustion := by
  have hcheck := compile_checked h
  unfold WellFormed at hcheck
  simp only [compile,hcheck,Except.ok.injEq] at h
  subst c
  intro id f hi
  constructor
  · simp only [hi,Option.map_some,Option.getD_some]
  · let arity := ((source.functions[source.entry]?).map (fun f => f.parameters.length)).getD 0
    let fs := source.functions.toList
    let table := layouts (wrapperSize arity) fs
    let entries := fun (id : FunctionId) => (table[id]?.map FunctionLayout.entry).getD 0
    let frames := fun (id : FunctionId) => (source.functions[id]?.map Function.frameSize).getD 0
    let pre := wrapper (frames source.entry) (entries source.entry) arity
    have hbody : CodeAt (pre ++ bodies frames entries (exhaustionPC arity) (wrapperSize arity) fs).toArray
        (wrapperSize arity) (bodies frames entries (exhaustionPC arity) (wrapperSize arity) fs) := by
      have hh := (CodeAt.toArray (pre ++ bodies frames entries (exhaustionPC arity) (wrapperSize arity) fs)).suffix
      simpa only [pre,wrapper_length,Nat.zero_add] using hh
    obtain ⟨layout,hl,_,hc⟩ := layouts_body fs frames entries (exhaustionPC arity) (wrapperSize arity)
      hbody (by simpa [fs] using hi)
    have hent : entries id = layout.entry := by simp only [entries,table,hl,Option.map_some,Option.getD_some]
    change CodeAt _ (entries id) (prologue ++ lower frames entries (exhaustionPC arity) (entries id+2) f.body)
    rw [hent]
    exact hc

/-- The compiler's checked frame metadata supplies every width-dependent frame premise. -/
theorem compile_frame_fit {source : Program} {c : CompiledProgram}
    (h : compile source = .ok c) (hfit : c.Fits w) (hi : source.functions[id]? = some f) :
    f.frameSize < modulus w := by
  have hcheck := compile_checked h
  unfold WellFormed at hcheck
  simp only [compile,hcheck,Except.ok.injEq] at h
  subst c
  let arity := ((source.functions[source.entry]?).map (fun f => f.parameters.length)).getD 0
  let fs := source.functions.toList
  let table := layouts (wrapperSize arity) fs
  let entries := fun (id : FunctionId) => (table[id]?.map FunctionLayout.entry).getD 0
  let frames := fun (id : FunctionId) => (source.functions[id]?.map Function.frameSize).getD 0
  let pre := wrapper (frames source.entry) (entries source.entry) arity
  have hbody : CodeAt (pre ++ bodies frames entries (exhaustionPC arity) (wrapperSize arity) fs).toArray
      (wrapperSize arity) (bodies frames entries (exhaustionPC arity) (wrapperSize arity) fs) := by
    simpa only [pre,wrapper_length,Nat.zero_add] using
      (CodeAt.toArray (pre ++ bodies frames entries (exhaustionPC arity) (wrapperSize arity) fs)).suffix
  obtain ⟨layout,hl,hframe,_⟩ := layouts_body fs frames entries (exhaustionPC arity) (wrapperSize arity)
    hbody (by simpa [fs] using hi)
  rw [←hframe]
  exact hfit.2 layout (List.mem_of_getElem? hl)

/-- The shared exhaustion code is present at the advertised final address. -/
theorem compile_error {source : Program} {c : CompiledProgram}
    (h : compile source = .ok c) : CodeAt c.code c.exhaustion errorCode := by
  have hcheck := compile_checked h
  unfold WellFormed at hcheck
  simp only [compile,hcheck,Except.ok.injEq] at h
  subst c
  let arity := ((source.functions[source.entry]?).map (fun f => f.parameters.length)).getD 0
  let fs := source.functions.toList
  let table := layouts (wrapperSize arity) fs
  let entries := fun (id : FunctionId) => (table[id]?.map FunctionLayout.entry).getD 0
  let frames := fun (id : FunctionId) => (source.functions[id]?.map Function.frameSize).getD 0
  have hw := (CodeAt.toArray (wrapper (frames source.entry) (entries source.entry) arity ++
    bodies frames entries (exhaustionPC arity) (wrapperSize arity) fs)).prefix
  have heq : wrapper (frames source.entry) (entries source.entry) arity =
      ([.mov status (.imm 0),.mov fp (.imm 0),.sub left (.reg limit) (.reg sp),
        .branch .lt (.reg left) (.imm (frames source.entry)) (exhaustionPC arity),.store (.reg sp) (.reg fp)] ++
        entryArguments arity ++ [Instr.mov fp (.reg sp),.add sp (.reg sp) (.imm (frames source.entry)),
          .call link (entries source.entry),.mov status (.imm 1),.halt]) ++ errorCode := by
    simp [wrapper,errorCode,List.append_assoc]
  rw [heq] at hw
  have hl := wrapper_length (frames source.entry) (entries source.entry) arity
  rw [heq] at hl
  have hlen : ([Instr.mov status (.imm 0),.mov fp (.imm 0),.sub left (.reg limit) (.reg sp),
        .branch .lt (.reg left) (.imm (frames source.entry)) (exhaustionPC arity),.store (.reg sp) (.reg fp)] ++
        entryArguments arity ++ [Instr.mov fp (.reg sp),.add sp (.reg sp) (.imm (frames source.entry)),
          .call link (entries source.entry),.mov status (.imm 1),.halt]).length = exhaustionPC arity := by
    simp only [List.length_append,errorCode,List.length_cons,List.length_nil,wrapperSize] at hl
    unfold exhaustionPC
    simp only [List.length_append,List.length_cons,List.length_nil]
    omega
  have hh := hw.suffix
  simpa only [hlen,Nat.zero_add,←heq] using hh

/-- Finite capacity-aware body executions transfer to the output of compile,
with no hand-written body embedding or function-address assumptions. -/
theorem compile_evaluation {source : Program} {c : CompiledProgram}
    (hcompile : compile source = .ok c) (hfit : c.Fits w)
    (d : Evaluation source rho free stmt locals mem flow mem' log)
    (hsep : Separated stack log) :
    Implements c.code rho
      (fun id => (source.functions[id]?.map Function.frameSize).getD 0)
      (fun id => (c.functions[id]?.map FunctionLayout.entry).getD 0) c.exhaustion stack
      free stmt locals mem flow mem' log (instructions d) (extraStack d) :=
  evaluation_simulation (compile_linked hcompile) hfit.1
    (fun _ _ hi => compile_frame_fit hcompile hfit hi) (compile_error hcompile) d hsep

end RamLang.Compiler
