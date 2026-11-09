import RamLang.Logic.Contract

namespace RamLang
open WordRam Compiler Logic

/-- A call-free body is independent of its surrounding function table. -/
def Stmt.CallFree : Stmt → Prop
  | .skip | .primitive _ | .ret _ => True
  | .seq a b => a.CallFree ∧ b.CallFree
  | .ite _ a b => a.CallFree ∧ b.CallFree
  | .while _ body => body.CallFree
  | .call _ _ _ => False

/-- Reuse a proved call-free routine in any larger source program, without
changing its local state, effects, control decisions, or capacity parameter. -/
def Evaluation.reprogram (q : Program)
    (d : Evaluation p rho free stmt locals mem flow mem' trace) (hc : stmt.CallFree) :
    Evaluation q rho free stmt locals mem flow mem' trace :=
  match d with
  | .skip => .skip
  | .primitive h => .primitive h
  | .sequence a b => .sequence (a.reprogram q hc.1) (b.reprogram q hc.2)
  | .sequenceStop a stop => .sequenceStop (a.reprogram q hc.1) stop
  | .ifTrue test branch => .ifTrue test (branch.reprogram q hc.1)
  | .ifFalse test branch => .ifFalse test (branch.reprogram q hc.2)
  | .whileFalse test => .whileFalse test
  | .whileContinue test body tail => .whileContinue test (body.reprogram q hc) (tail.reprogram q hc)
  | .whileStop test body stop => .whileStop test (body.reprogram q hc) stop
  | .call _ _ _ _ _ _ => False.elim hc
  | .callExhausts _ _ _ _ _ => False.elim hc
  | .callBodyExhausts _ _ _ _ _ _ => False.elim hc
  | .ret value => .ret value

/-- Embedding a call-free derivation preserves its exact instruction charge. -/
theorem Evaluation.reprogram_instructions (q : Program)
    (d : Evaluation p rho free stmt locals mem flow mem' trace) (hc : stmt.CallFree) :
    instructions (d.reprogram q hc) = instructions d := by
  induction d with
  | skip | primitive | whileFalse | ret => rfl
  | sequence a b ia ib => simp only [reprogram,instructions,ia hc.1,ib hc.2]
  | sequenceStop a stop ih => exact ih hc.1
  | ifTrue test branch ih => simp only [reprogram,instructions,ih hc.1]
  | ifFalse test branch ih => simp only [reprogram,instructions,ih hc.2]
  | whileContinue test body tail ib it => simp only [reprogram,instructions,ib hc,it hc]
  | whileStop test body stop ih => simp only [reprogram,instructions,ih hc]
  | call | callExhausts | callBodyExhausts => exact False.elim hc

/-- Embedding a call-free derivation also preserves its stack charge. -/
theorem Evaluation.reprogram_stack (q : Program)
    (d : Evaluation p rho free stmt locals mem flow mem' trace) (hc : stmt.CallFree) :
    extraStack (d.reprogram q hc) = extraStack d := by
  induction d with
  | skip | primitive | whileFalse | ret => rfl
  | sequence a b ia ib => simp only [reprogram,extraStack,ia hc.1,ib hc.2]
  | sequenceStop a stop ih => exact ih hc.1
  | ifTrue test branch ih => exact ih hc.1
  | ifFalse test branch ih => exact ih hc.2
  | whileContinue test body tail ib it => simp only [reprogram,extraStack,ib hc,it hc]
  | whileStop test body stop ih => exact ih hc
  | call | callExhausts | callBodyExhausts => exact False.elim hc

/-- Source library contracts embed in a client's program with identical effects,
postconditions, work bounds and stack bounds. No target code is assumed. -/
theorem Logic.Contract.reprogram (q : Program) (hc : stmt.CallFree)
    (h : Contract p rho free stmt locals mem post work peak) :
    Contract q rho free stmt locals mem post work peak := by
  obtain ⟨flow,mem',trace,d,hpost,ht,hs⟩ := h
  exact Contract.ofEvaluation (d.reprogram q hc) hpost
    (by rw [d.reprogram_instructions]; exact ht) (by rw [d.reprogram_stack]; exact hs)

end RamLang
