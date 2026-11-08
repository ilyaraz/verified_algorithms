import WordRam
import WordRam.Examples
import Lean

open WordRam

example : word 4 15 + word 4 1 = word 4 0 := by decide
example : word 4 0 - word 4 1 = word 4 15 := by decide
example : word 4 7 * word 4 3 = word 4 5 := by decide
example : word 4 7 % word 4 3 = word 4 1 := by decide
example : word 4 7 % word 4 1 = word 4 0 := by decide
example : word 4 7 % word 4 0 = word 4 7 := by decide

example : probability (fun rho : RandomMemory 1 => rho (word 1 0) = word 1 1) = 1/2 := by
  rw [probability_cell]
  norm_num [modulus]

example : probability (fun rho : RandomMemory 1 =>
    rho (word 1 0) = word 1 1 ∧ rho (word 1 1) = word 1 0) = 1/4 := by
  rw [probability_two_cells _ _ (by decide)]
  norm_num [modulus]

example : probability (fun rho : RandomMemory 1 =>
    rho (word 1 0) = word 1 1 ∧ rho (word 1 0) = word 1 0) = 0 := by
  rw [probability_repeated_cell]
  norm_num [word]

example : conditionalProbability (fun rho : RandomMemory 1 => rho (word 1 1) = word 1 0)
    (Matches {word 1 0} (fun _ => word 1 1)) = 1/2 := by
  rw [conditional_fresh_cell _ _ _ (by decide)]
  norm_num [modulus]

namespace WordRam.Examples

theorem randomRoundTrip_probability (regs : Registers w 2) (mem : DataMemory w)
    (x : Word w) :
    runProbability randomRoundTrip 4 (.initial regs mem) (fun r => r.state.regs 0 = x) =
      (modulus w : ℝ)⁻¹ := by
  unfold runProbability
  calc
    _ = probability (fun rho => rho (word w 3) = x) := probability_congr (by
      intro rho
      dsimp only
      rw [(randomRoundTrip_spec rho regs mem).2.2.1])
    _ = _ := probability_cell _ _

theorem spin_expectedSteps (w fuel : Nat) :
    expectedSteps spin fuel (State.zero w 0) = fuel := by
  have h : ∀ rho : RandomMemory w, (run spin rho fuel (State.zero w 0)).steps = fuel := by
    intro rho
    exact run_exhausted_steps (spin_diverges rho _ rfl fuel)
  simp [expectedSteps, h]

end WordRam.Examples

-- Audit every declaration belonging to this library, including all examples.
-- These commands inspect proofs; they do not provide proof terms to the library.
run_cmd do
  let env ← Lean.getEnv
  let allowed := [``propext, ``Classical.choice, ``Quot.sound]
  let mut checked := 0
  for (name, _) in env.constants.toList do
    if name.getRoot == `WordRam then
      for ax in ← Lean.collectAxioms name do
        unless allowed.contains ax do
          throwError "Unexpected axiom in {name}: {ax}"
      checked := checked + 1
  Lean.logInfo m!"Axiom audit passed for {checked} WordRam declarations."
  for name in [``word, ``unsignedMod, ``update, ``Operand.eval, ``Comparison.test, ``State.initial,
      ``State.zero, ``State.put, ``step, ``run, ``RunResult.prepend,
      ``RunResult.dataFootprint, ``RunResult.writeFootprint, ``RunResult.randomReads,
      ``RunResult.randomFootprint, ``RunResult.randomBitsExposed,
      ``Examples.arithmetic, ``Examples.mulMod, ``Examples.randomRoundTrip,
      ``Examples.countdown, ``Examples.spin, ``Examples.branchExample] do
    let axioms ← Lean.collectAxioms name
    unless axioms.isEmpty do
      throwError "Executable definition {name} uses axioms: {axioms}"
  Lean.logInfo "Executable definitions contain no axioms."
