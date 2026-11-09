import RamLang.Evaluation
import RamLang.Compiler.Lower

/-! Ghost resource functions on finite source derivations. Instruction charges
come from emitted templates; their transfer to target execution requires the
compiler simulation. None of these derivations is a runtime compiler input. -/
namespace RamLang.Compiler
open WordRam ABI

def conditionCost (c : Condition) : Nat := (atom left c.left).length + (atom right c.right).length

/-- Exact target work, including calls, local spills, and exhaustion, transferred
by `compile_evaluation`. Whole-program theorems charge the entry wrapper too. -/
def instructions (d : Evaluation p rho free stmt locals mem flow mem' trace) : Nat :=
  match d with
  | .skip => 0
  | .primitive (op := op) _ => (primitive op).length
  | .sequence a b => instructions a + instructions b
  | .sequenceStop a _ => instructions a
  | .ifTrue (condition := c) _ a => conditionCost c + 1 + instructions a
  | .ifFalse (condition := c) (flow := flow) _ a =>
      conditionCost c + 1 + instructions a + (if flow.continues then 1 else 0)
  | .whileFalse (condition := c) _ => conditionCost c + 2
  | .whileContinue (condition := c) _ a b => conditionCost c + 2 + instructions a + instructions b
  | .whileStop (condition := c) _ a _ => conditionCost c + 1 + instructions a
  | .call (args := args) _ _ _ _ body _ => (arguments 0 args).length + 10 + instructions body
  | .callExhausts _ _ _ _ _ => 4
  | .callBodyExhausts (args := args) _ _ _ _ _ body => (arguments 0 args).length + 8 + instructions body
  | .ret (atom := value) _ => (atom result value).length + epilogue.length

/-- Peak additional stack use; historical sequential calls combine by maximum. -/
def extraStack (d : Evaluation p rho free stmt locals mem flow mem' trace) : Nat :=
  match d with
  | .skip | .primitive _ | .whileFalse _ | .callExhausts _ _ _ _ _ | .ret _ => 0
  | .sequence a b | .whileContinue _ a b => max (extraStack a) (extraStack b)
  | .sequenceStop a _ | .ifTrue _ a | .ifFalse _ a | .whileStop _ a _ => extraStack a
  | .call (f := f) _ _ _ _ body _ | .callBodyExhausts (f := f) _ _ _ _ _ body =>
      f.frameSize + extraStack body

/-- Capacity-aware derivations cannot reserve more extra stack than available. -/
theorem extraStack_le (d : Evaluation p rho free stmt locals mem flow mem' trace) :
    extraStack d ≤ free := by
  induction d with
  | skip => simp [extraStack]
  | primitive => simp [extraStack]
  | sequence a b ia ib => exact Nat.max_le.mpr ⟨ia, ib⟩
  | sequenceStop a _ ih => exact ih
  | ifTrue _ a ih => exact ih
  | ifFalse _ a ih => exact ih
  | whileFalse => simp [extraStack]
  | whileContinue _ a b ia ib => exact Nat.max_le.mpr ⟨ia, ib⟩
  | whileStop _ a _ ih => exact ih
  | call _ _ _ space body _ ih => simp only [extraStack]; omega
  | callExhausts => simp [extraStack]
  | callBodyExhausts _ _ _ _ space body ih => simp only [extraStack]; omega
  | ret => simp [extraStack]

end RamLang.Compiler
