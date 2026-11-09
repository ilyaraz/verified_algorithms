import RamLang.DSL.Automation

namespace RamLang.DSL
open Lean Meta Elab Tactic

/-- Normalize a local list's spine without unfolding symbolic word values. -/
partial def localSpine (e : Expr) : MetaM Expr := do
  let e ← whnf e
  if e.isAppOfArity ``List.cons 3 then
    let args := e.getAppArgs
    return mkAppN e.getAppFn #[args[0]!,args[1]!,← localSpine args[2]!]
  else return e

/-- Assemble a finite source derivation for straight-line code, calls and
branches. The supplied tactic proves branch tests; all generated terms use
checked Evaluation rules. Loops require an invariant and the loop rule.
The first half of a sequence is inferred before choosing continuation or early
return, avoiding speculative execution of unreachable statements. -/
syntax "ram_derive" "(" tacticSeq ")" : tactic

elab_rules : tactic
  | `(tactic| ram_derive ($test:tacticSeq)) => withMainContext do
    try
      evalTactic (← `(tactic| assumption))
      return
    catch _ => pure ()
    let goal ← getMainGoal
    let target ← whnf (← goal.getType)
    let args := target.getAppArgs
    unless target.isAppOfArity ``Evaluation 10 do
      throwError "ram_derive expects an Evaluation goal"
    let locals ← localSpine args[5]!
    let goal ← goal.change (mkAppN target.getAppFn (args.set! 5 locals))
    replaceMainGoal [goal]
    let target ← goal.getType
    let args := target.getAppArgs
    let stmt ← whnf args[4]!
    match stmt.getAppFn.constName? with
    | some ``Stmt.seq =>
      let flow ← mkFreshExprMVar (mkApp (mkConst ``Flow) args[0]!)
      let memory ← mkFreshExprMVar (← inferType args[6]!)
      let trace ← mkFreshExprMVar (← inferType args[9]!)
      let firstType := mkAppN (mkConst ``Evaluation)
        #[args[0]!,args[1]!,args[2]!,args[3]!,stmt.getAppArgs[0]!,args[5]!,args[6]!,flow,memory,trace]
      let first ← mkFreshExprMVar firstType
      let rest ← getGoals
      setGoals [first.mvarId!]
      evalTactic (← `(tactic| ram_derive ($test)))
      unless (← getGoals).isEmpty do throwError "unfinished first source statement"
      let first ← instantiateMVars first
      let flow ← whnf (← instantiateMVars flow)
      let continues := flow.isAppOf ``Flow.next
      let ctor := mkConst (if continues then ``Evaluation.sequence else ``Evaluation.sequenceStop)
      let (parameters,_,conclusion) ← forallMetaTelescopeReducing (← inferType ctor)
      let firstHole := parameters[parameters.size-2]!
      unless ← isDefEq (← inferType firstHole) (← inferType first) do
        throwError "source sequence intermediate state does not match"
      firstHole.mvarId!.assign first
      unless ← isDefEq conclusion target do throwError "source sequence result does not match"
      goal.assign (mkAppN ctor parameters)
      let secondHole := parameters[parameters.size-1]!
      setGoals (secondHole.mvarId! :: rest.tail!)
      if continues then evalTactic (← `(tactic| ram_derive ($test)))
      else evalTactic (← `(tactic| trivial))
    | some ``Stmt.skip => evalTactic (← `(tactic| exact RamLang.Evaluation.skip))
    | some ``Stmt.primitive => evalTactic (← `(tactic|
        first
        | exact RamLang.Evaluation.primitive (event := none) rfl
        | exact RamLang.Evaluation.primitive (event := some _) rfl
        | ram_primitive))
    | some ``Stmt.ret => evalTactic (← `(tactic| exact RamLang.Evaluation.ret rfl))
    | some ``Stmt.ite => evalTactic (← `(tactic|
        first
        | apply RamLang.Evaluation.ifTrue
          · solve | $test
          · ram_derive ($test)
        | apply RamLang.Evaluation.ifFalse
          · solve | $test
          · ram_derive ($test)))
    | some ``Stmt.call => evalTactic (← `(tactic|
        first
        | apply RamLang.Evaluation.call
          · first | assumption | rfl
          · rfl
          · first | assumption | (symm; assumption) | rfl
          · first | assumption | (conv => lhs; reduce); omega
          · ram_derive ($test)
          · rfl))
    | _ => throwError "ram_derive supports primitives, calls, conditionals and returns; use a loop contract for while"

end RamLang.DSL
