import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-! Collision-bounded finite families. The counting contract is an exact integer
form of a uniform-PMF probability bound; it makes no independence claim about
hash outputs. The family and its proof are separate from RAM realization. -/
namespace Hashing

structure Family (Key Seed : Type) (slots : Nat) where
  eval : Seed → Key → Fin slots

/-- An exact finite counting inequality, avoiding rounded real probabilities. -/
def CollisionBound [Fintype Seed] (family : Family Key Seed slots) (constant : Nat) : Prop :=
  ∀ x y, x ≠ y →
    Nat.card {seed : Seed // family.eval seed x = family.eval seed y} * slots ≤
      constant * Fintype.card Seed

noncomputable def uniformLaw (Seed : Type) [Fintype Seed] [Nonempty Seed] : PMF Seed :=
  PMF.uniformOfFintype Seed

/-- The integer contract implies the same bound under the actual uniform PMF. -/
theorem CollisionBound.probability [Fintype Seed] [Nonempty Seed]
    {family : Family Key Seed slots} (h : CollisionBound family constant)
    (hm : 0 < slots) (hne : x ≠ y) :
    ((uniformLaw Seed).toOuterMeasure {a | family.eval a x = family.eval a y}).toReal ≤
      (constant : ℝ) / slots := by
  classical
  have hc := h x y hne
  rw [Nat.card_eq_fintype_card] at hc
  rw [uniformLaw, PMF.toOuterMeasure_uniformOfFintype_apply]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast]
  have hp : (0 : ℝ) < Fintype.card Seed := by exact_mod_cast Fintype.card_pos
  have hmp : (0 : ℝ) < slots := by exact_mod_cast hm
  apply (div_le_div_iff₀ hp hmp).mpr
  exact_mod_cast hc

end Hashing
