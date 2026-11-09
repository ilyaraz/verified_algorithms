import RamLang.Compiler.Proofs.Divergence

namespace RamLang.Compiler.ProofExamples
open WordRam ABI

/-- A minimal source proof exercises the entire compiler theorem from PC zero. -/
def literalProgram : RamLang.Program :=
  ⟨#[⟨"seven",[],[],.ret (.literal 7)⟩],0⟩

def literalCompiled : CompiledProgram :=
  match compile literalProgram with
  | .ok result => result
  | .error _ => ⟨#[],[],0⟩

def dirtyInitial : State 8 registers :=
  ⟨0,fun r => if r.val = 0 then word 8 100 else if r.val = 2 then word 8 102 else word 8 213,
    fun _ => word 8 213⟩

theorem literal_compiles : compile literalProgram = .ok literalCompiled := by rfl

theorem literal_fits : literalCompiled.Fits 8 := by
  change 21 < modulus 8 ∧ ∀ layout ∈ [FunctionLayout.mk 12 9 2], layout.frameWords < modulus 8
  constructor
  · decide
  · intro layout h
    simp only [List.mem_singleton] at h
    subst layout
    decide

/-- The target takes exactly nineteen instructions, even with initially dirty
stack words and registers. This proof uses a source derivation and the general
compiler theorem rather than executing or expanding the generated instructions. -/
theorem literal_verified (rho : RandomMemory 8) :
    ∃ t trace, WordRam.TerminatesIn literalCompiled.code rho dirtyInitial 19 t trace ∧
      t.regs status = word 8 1 ∧ t.regs result = word 8 7 ∧ t.regs sp = word 8 100 ∧
      ApplicationMemory ⟨100,2⟩ dirtyInitial.mem t.mem ∧ projectTrace ⟨100,2⟩ trace = [] ∧
      StackBound literalCompiled.code rho dirtyInitial 19 102 := by
  let d : Evaluation literalProgram rho 0 (.ret (.literal 7)) [] dirtyInitial.mem
      (.returned (word 8 7)) dirtyInitial.mem [] := .ret rfl
  have h := compiled_returns literal_compiles literal_fits
    (f := ⟨"seven",[],[],.ret (.literal 7)⟩) (by rfl)
    (stack := ⟨100,2⟩) (s := dirtyInitial) rfl rfl rfl (by change 100+2 < modulus 8; decide) (by decide) d
    (by simp [Separated])
  exact h

/-- The same source proof is an independent small-step source execution. -/
theorem literal_source_returns (rho : RandomMemory 8) :
    ∃ c, Returns literalProgram rho (some 2) (Config.initial literalProgram [] dirtyInitial.mem)
      (word 8 7) c [] ∧ c.mem = dirtyInitial.mem := by
  exact Evaluation.invocationReturns (f := ⟨"seven",[],[],.ret (.literal 7)⟩) rfl rfl (by decide)
    (Evaluation.ret rfl)

def spinProgram : RamLang.Program :=
  ⟨#[⟨"spin",[],[],.seq (.while ⟨.eq,.literal 1,.literal 1⟩ .skip) (.ret (.literal 0))⟩],0⟩

def spinCompiled : CompiledProgram :=
  match compile spinProgram with
  | .ok result => result
  | .error _ => ⟨#[],[],0⟩

theorem spin_compiles : compile spinProgram = .ok spinCompiled := by rfl

theorem spin_fits : spinCompiled.Fits 8 := by
  change 26 < modulus 8 ∧ ∀ layout ∈ [FunctionLayout.mk 12 14 2], layout.frameWords < modulus 8
  constructor
  · decide
  · intro layout h
    simp only [List.mem_singleton] at h
    subst layout
    decide

theorem spin_progress (rho : RandomMemory 8) :
    LoopProgress spinProgram rho ⟨100,2⟩ 0 ⟨.eq,.literal 1,.literal 1⟩ .skip
      (fun locals _ => locals = []) := by
  intro locals mem h
  subst locals
  refine ⟨rfl,[],mem,[],Evaluation.skip,rfl,?_⟩
  simp [Separated]

/-- A proved infinite source loop compiles to a genuinely infinite target run
with a fixed two-word stack, including entry from initially dirty RAM. -/
theorem spin_verified (rho : RandomMemory 8) :
    WordRam.Diverges spinCompiled.code rho dirtyInitial ∧
      ∀ fuel, ((WordRam.run spinCompiled.code rho fuel dirtyInitial).state.regs sp).toNat ≤ 102 := by
  let f : Function := ⟨"spin",[],[],.seq (.while ⟨.eq,.literal 1,.literal 1⟩ .skip) (.ret (.literal 0))⟩
  have hentry : spinProgram.functions[spinProgram.entry]? = some f := rfl
  have hlinked := compile_linked spin_compiles spinProgram.entry f hentry
  obtain ⟨hsetup,_⟩ := wrapper_parts (compile_wrapper spin_compiles hentry)
  obtain ⟨t,trace,hs,htpc,hf,hproj,hbound⟩ := entry_setup (rho := rho) (s := dirtyInitial)
    (stack := ⟨100,2⟩) hsetup hlinked.2.prefix rfl rfl rfl (by change 102 < modulus 8; decide) (by decide)
  have hloop : CodeAt spinCompiled.code t.pc
      (lower (fun id => (spinProgram.functions[id]?.map Function.frameSize).getD 0)
        (fun id => (spinCompiled.functions[id]?.map FunctionLayout.entry).getD 0)
        spinCompiled.exhaustion t.pc (.while ⟨.eq,.literal 1,.literal 1⟩ .skip)) := by
    rw [htpc]
    exact hlinked.2.suffix.prefix
  have hd := compiled_loop_diverges spin_compiles spin_fits (spin_progress rho) rfl hf rfl rfl
    (by decide) hloop
  have hb := compiled_loop_stackBound spin_compiles spin_fits (spin_progress rho) rfl hf rfl rfl
    (by decide) hloop
  change WordRam.Steps spinCompiled.code rho 10 dirtyInitial t trace at hs
  refine ⟨target_diverges_prepend hs hd,?_⟩
  intro fuel
  by_cases hshort : fuel ≤ 10
  · exact hbound fuel hshort
  · have he : fuel = 10+(fuel-10) := by omega
    rw [he,hs.run_eq]
    exact hb (fuel-10)

end RamLang.Compiler.ProofExamples
