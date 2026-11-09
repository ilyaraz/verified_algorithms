import RamLang.DSL.Elaborate
import RamLang.Logic.Contract

/-! Small proof-producing tactics. They unfold independent source primitives
and resource templates, without introducing a verification axiom or oracle. -/
namespace RamLang.DSL

/-- Reduce source operand lookup, checked assignment, and pure word primitives;
remaining arithmetic and separation obligations stay visible to the user. -/
macro "ram_simp" : tactic => `(tactic|
  simp [RamLang.Primitive.eval,RamLang.Atom.eval,RamLang.Condition.eval,
    RamLang.requireSome,RamLang.writeLocal,RamLang.Binary.eval,WordRam.Comparison.test,
    bind,pure,Except.bind,Except.pure])

/-- Prove a concrete primitive source step, inferring whether it emits an event.
The resulting proof term is checked by Lean like every other source derivation. -/
macro "ram_primitive" : tactic => `(tactic|
  first
  | exact RamLang.Evaluation.primitive (event := none) (by ram_simp <;> rfl)
  | exact RamLang.Evaluation.primitive (event := some _) (by ram_simp <;> rfl))

/-- Normalize ghost instruction and stack charges from finite source proofs. -/
macro "ram_cost" : tactic => `(tactic|
  simp [RamLang.Compiler.instructions,RamLang.Compiler.extraStack,
    RamLang.Compiler.conditionCost,RamLang.Compiler.atom,RamLang.Compiler.primitive,
    RamLang.Compiler.spill,RamLang.Compiler.binary,RamLang.Compiler.arguments,
    RamLang.Compiler.epilogue,RamLang.Flow.continues,RamLang.Function.frameSize,RamLang.Function.slots])

end RamLang.DSL
