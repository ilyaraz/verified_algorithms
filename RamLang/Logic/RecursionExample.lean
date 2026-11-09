import RamLang.Logic.Loop
import RamLang.Logic.Frame
import RamLang.Examples

namespace RamLang.Logic.Sum
open WordRam Compiler

/-- Mathematical triangular sum; the source result is this value reduced to a
word, so the proof permits ordinary wrapping of the computed result. -/
def model : Nat → Nat
  | 0 => 0
  | n+1 => model n+(n+1)

/-- Non-tail recursion with a live saved local has exact body cost 43n+11 and
extra stack peak 5n. Input representability makes the decreasing counter exact. -/
theorem evaluation (n : Nat) {w : Nat} (hn : n < modulus w) (rho : RandomMemory w)
    (mem : DataMemory w) (free : Nat) (space : 5*n ≤ free) :
    ∃ d : Evaluation Examples.sum rho free Examples.sumFunction.body
      [some (word w n),none,none] mem (.returned (word w (model n))) mem [],
      instructions d = 43*n+11 ∧ extraStack d = 5*n := by
  induction n generalizing free with
  | zero =>
    let d : Evaluation Examples.sum rho free Examples.sumFunction.body
        [some (word w 0),none,none] mem (.returned (word w 0)) mem [] :=
      .ifTrue (by simp [Condition.eval,Atom.eval,requireSome,Comparison.test,bind,pure,Except.bind,Except.pure]) (.ret rfl)
    exact ⟨d,rfl,rfl⟩
  | succ n ih =>
    obtain ⟨child,ht,hs⟩ := ih (by omega) (free-5) (by omega)
    have hne : word w (n+1) ≠ word w 0 := by
      intro he
      have he' := (word_eq_iff_of_lt hn (by omega : 0 < modulus w)).mp he
      omega
    have hsub : word w (n+1)-word w 1 = word w n := by
      rw [WordRam.word_sub (n+1) 1 (by omega) (by omega)]
      rfl
    have hadd : word w (model n)+word w (n+1) = word w (model (n+1)) := WordRam.word_add _ _
    let first : Evaluation Examples.sum rho free (.primitive (.move 1 (.local 0)))
        [some (word w (n+1)),none,none] mem
        (.next [some (word w (n+1)),some (word w (n+1)),none]) mem [] := .primitive (event := none) rfl
    let dec : Evaluation Examples.sum rho free (.primitive (.binary 0 .sub (.local 0) (.literal 1)))
        [some (word w (n+1)),some (word w (n+1)),none] mem
        (.next [some (word w n),some (word w (n+1)),none]) mem [] :=
      .primitive (event := none) (by simp [Primitive.eval,Atom.eval,requireSome,writeLocal,Binary.eval,hsub,bind,pure,Except.bind,Except.pure])
    let call : Evaluation Examples.sum rho free (.call 2 0 [.local 0])
        [some (word w n),some (word w (n+1)),none] mem
        (.next [some (word w n),some (word w (n+1)),some (word w (model n))]) mem [] :=
      .call (f := Examples.sumFunction) rfl rfl rfl (by change 5 ≤ free; omega) child rfl
    let add : Evaluation Examples.sum rho free (.primitive (.binary 2 .add (.local 2) (.local 1)))
        [some (word w n),some (word w (n+1)),some (word w (model n))] mem
        (.next [some (word w n),some (word w (n+1)),some (word w (model (n+1)))]) mem [] :=
      .primitive (event := none) (by simp [Primitive.eval,Atom.eval,requireSome,writeLocal,Binary.eval,hadd,bind,pure,Except.bind,Except.pure])
    let d : Evaluation Examples.sum rho free Examples.sumFunction.body
        [some (word w (n+1)),none,none] mem (.returned (word w (model (n+1)))) mem [] :=
      .ifFalse (by simp [Condition.eval,Atom.eval,requireSome,Comparison.test,hne,bind,pure,Except.bind,Except.pure])
        (.sequence first (.sequence dec (.sequence call (.sequence add (.ret rfl)))))
    refine ⟨d,?_,?_⟩
    · simp [d,first,dec,call,add,instructions,conditionCost,atom,primitive,spill,binary,
        arguments,epilogue,Flow.continues,ht]
      omega
    · simp [d,first,dec,call,add,extraStack,Examples.sumFunction,Function.frameSize,Function.slots,hs]
      omega

/-- Source-level correctness and resources, with no target-PC or frame-store
premises. The recursive computation preserves all application memory. -/
theorem contract (n : Nat) {w : Nat} (hn : n < modulus w) (rho : RandomMemory w)
    (mem : DataMemory w) (free : Nat) (space : 5*n ≤ free) :
    Contract Examples.sum rho free Examples.sumFunction.body [some (word w n),none,none] mem
      (fun flow mem' trace => flow = .returned (word w (model n)) ∧ mem' = mem ∧ trace = [])
      (43*n+11) (5*n) := by
  obtain ⟨d,ht,hs⟩ := evaluation n hn rho mem free space
  exact .ofEvaluation d ⟨rfl,rfl,rfl⟩ (by omega) (by omega)

/-- One finite compiled body is shared by every recursive invocation. -/
def compiled : CompiledProgram :=
  match compile Examples.sum with
  | .ok c => c
  | .error _ => ⟨#[],[],0⟩

theorem compiles : compile Examples.sum = .ok compiled := by rfl

/-- The fixed code and frame metadata fit whenever sixty-five code words fit. -/
theorem fits {w : Nat} (hw : 65 < modulus w) : compiled.Fits w := by
  change 65 < modulus w ∧ ∀ layout ∈ [FunctionLayout.mk 14 51 5], layout.frameWords < modulus w
  refine ⟨hw,?_⟩
  intro layout h
  simp only [List.mem_singleton] at h
  subst layout
  change 5 < modulus w
  omega

/-- General target theorem obtained solely from the source proof: 43n+25 actual
instructions, a five-word frame per live invocation, and no application effects. -/
theorem compiled_correct {w : Nat} (n : Nat) (hn : n < modulus w) (hw : 65 < modulus w)
    (rho : RandomMemory w) (s : State w ABI.registers) (stack : Region)
    (hpc : s.pc = 0) (hsp : s.regs ABI.sp = word w stack.base)
    (hlimit : s.regs ABI.limit = word w (stack.base+stack.size)) (hstack : stack.Fits w)
    (harg : s.regs (ABI.argument 0) = word w n) (hspace : 5*(n+1) ≤ stack.size) :
    ∃ t trace, WordRam.TerminatesIn compiled.code rho s (43*n+25) t trace ∧
      t.regs ABI.status = word w 1 ∧ t.regs ABI.result = word w (model n) ∧
      t.regs ABI.sp = word w stack.base ∧ ApplicationMemory stack s.mem t.mem ∧
      ABI.projectTrace stack trace = [] ∧ StackBound compiled.code rho s (43*n+25) (stack.base+5*(n+1)) := by
  obtain ⟨d,ht,hs⟩ := evaluation n hn rho s.mem (stack.size-5) (by omega)
  have he : (entryValues s Examples.sumFunction.parameters.length).map some ++
      List.replicate Examples.sumFunction.locals.length none = [some (word w n),none,none] := by
    change [some (s.regs (ABI.argument 0)),none,none] = _
    rw [harg]
  have transfer := compiled_returns (rho := rho) (value := word w (model n)) (mem' := s.mem) (log := []) compiles (fits hw) (f := Examples.sumFunction) rfl hpc hsp hlimit hstack
    (by change 5 ≤ stack.size; omega)
  rw [he] at transfer
  have h := transfer d (by simp [Separated])
  have hnwork : 12+2*Examples.sumFunction.parameters.length+instructions d = 43*n+25 := by
    change 12+2*1+instructions d = _
    omega
  have hnstack : stack.base+Examples.sumFunction.frameSize+extraStack d = stack.base+5*(n+1) := by
    change stack.base+5+extraStack d = _
    omega
  simpa only [hnwork,hnstack] using h

end RamLang.Logic.Sum
