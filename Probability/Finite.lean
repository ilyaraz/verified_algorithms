import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Finite uniform averages, with an explicit bridge to the uniform PMF. No
stream, resampling, or infinite stopping-time model is introduced. -/
namespace FiniteProbability
noncomputable section
open scoped BigOperators Classical

variable {α β : Type*} [Fintype α] [Fintype β]

def mean (f : α → ℝ) : ℝ := (∑ a, f a) / Fintype.card α

def probability (event : α → Prop) : ℝ := mean (fun a => if event a then 1 else 0)

theorem mean_congr {f g : α → ℝ} (h : ∀ a, f a = g a) : mean f = mean g := by
  simp only [mean, h]

theorem mean_add (f g : α → ℝ) : mean (fun a => f a + g a) = mean f + mean g := by
  simp [mean, Finset.sum_add_distrib, add_div]

theorem mean_sum (indices : Finset ι) (f : ι → α → ℝ) :
    mean (fun a => ∑ i ∈ indices, f i a) = ∑ i ∈ indices, mean (f i) := by
  unfold mean
  rw [Finset.sum_comm]
  simp only [Finset.sum_div]

theorem mean_mul (c : ℝ) (f : α → ℝ) : mean (fun a => c * f a) = c * mean f := by
  simp [mean, ← Finset.mul_sum, mul_div_assoc]

@[simp] theorem mean_const [Nonempty α] (c : ℝ) : mean (fun _ : α => c) = c := by
  have hp : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp [mean, hp]

theorem mean_nonneg {f : α → ℝ} (h : ∀ a, 0 ≤ f a) : 0 ≤ mean f :=
  div_nonneg (Finset.sum_nonneg (fun a _ => h a)) (Nat.cast_nonneg _)

theorem mean_mono {f g : α → ℝ} (h : ∀ a, f a ≤ g a) : mean f ≤ mean g :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum (fun a _ => h a)) (Nat.cast_nonneg _)

theorem mean_le [Nonempty α] {f : α → ℝ} (h : ∀ a, f a ≤ c) : mean f ≤ c := by
  simpa using mean_mono h

theorem mean_equiv (e : α ≃ β) (f : β → ℝ) : mean (fun a => f (e a)) = mean f := by
  rw [mean, mean, Fintype.card_congr e, Equiv.sum_comp e]

theorem mean_prod (f : α × β → ℝ) :
    mean f = mean (fun a => mean (fun b => f (a,b))) := by
  simp only [mean, Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul,
    ← Finset.sum_div, div_div]
  rw [mul_comm (Fintype.card α : ℝ)]

/-- Pointwise conditional cost bounds compose under independent finite factors. -/
theorem mean_prod_le [Nonempty β] (f : α × β → ℝ) (budget : α → ℝ)
    (h : ∀ a, mean (fun b => f (a,b)) ≤ budget a) : mean f ≤ mean budget := by
  rw [mean_prod]
  exact mean_mono h

theorem probability_nonneg (event : α → Prop) : 0 ≤ probability event := by
  apply mean_nonneg
  intro a
  split <;> norm_num

theorem probability_le_one [Nonempty α] (event : α → Prop) : probability event ≤ 1 := by
  apply mean_le
  intro a
  split <;> norm_num

theorem probability_congr {E F : α → Prop} (h : ∀ a, E a ↔ F a) :
    probability E = probability F := by
  apply mean_congr
  intro a
  simp [h a]

@[simp] theorem probability_true [Nonempty α] : probability (fun _ : α => True) = 1 := by
  simp [probability]

@[simp] theorem probability_false : probability (fun _ : α => False) = 0 := by
  simp [probability, mean]

theorem mean_indicator (p : α → Prop) [DecidablePred p] :
    mean (fun x => if p x then (1 : ℝ) else 0) = probability p := by
  apply mean_congr
  intro x
  by_cases h : p x <;> simp [h]

theorem mean_ite [Nonempty α] (p : α → Prop) [DecidablePred p] (a b : ℝ) :
    mean (fun x => if p x then a else b) = probability p * a + (1-probability p)*b := by
  have he : ∀ x, (if p x then a else b) =
      (a-b)*(if p x then 1 else 0) + b := by intro x; split <;> ring
  rw [mean_congr he, mean_add, mean_mul, mean_const, mean_indicator]
  ring

theorem probability_compl [Nonempty α] (event : α → Prop) :
    probability (fun a => ¬event a) = 1-probability event := by
  classical
  calc
    _ = mean (fun a => if event a then (0 : ℝ) else 1) := by
      apply mean_congr
      intro a
      by_cases h : event a <;> simp [h]
    _ = 1-probability event := by simpa using mean_ite event 0 1

theorem probability_union (E F : α → Prop) :
    probability (fun a => E a ∨ F a) ≤ probability E + probability F := by
  classical
  rw [probability, probability, probability, ← mean_add]
  apply mean_mono
  intro a
  by_cases he : E a <;> by_cases hf : F a <;> simp [he, hf]

theorem probability_union_finset (indices : Finset ι) (events : ι → α → Prop) :
    probability (fun a => ∃ i ∈ indices, events i a) ≤ ∑ i ∈ indices, probability (events i) := by
  classical
  induction indices using Finset.induction_on with
  | empty => simp [probability, mean]
  | @insert i indices hi ih =>
    have he : ∀ a, (∃ j ∈ insert i indices, events j a) ↔
        events i a ∨ ∃ j ∈ indices, events j a := by intro a; simp
    rw [probability_congr he, Finset.sum_insert hi]
    exact (probability_union _ _).trans (add_le_add_left ih _)

/-- Markov's inequality, in a form that also allows a zero threshold. -/
theorem markov (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) :
    threshold * probability (fun a => threshold ≤ f a) ≤ mean f := by
  rw [probability, ← mean_mul]
  apply mean_mono
  intro a
  split <;> rename_i h
  · simpa using h
  · simpa using hf a

theorem probability_ge_le (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) (ht : 0 < threshold) :
    probability (fun a => threshold ≤ f a) ≤ mean f / threshold := by
  apply (le_div_iff₀ ht).mpr
  simpa [mul_comm] using markov f hf

/-- Cardinality and PMF bridges keep this average on the same finite uniform law. -/
theorem probability_card (event : α → Prop) :
    probability event = (Nat.card {a // event a} : ℝ) / Fintype.card α := by
  classical
  simp [probability, mean, Nat.card_eq_fintype_card, Fintype.card_subtype]

theorem probability_pmf [Nonempty α] (event : α → Prop) :
    probability event = ((PMF.uniformOfFintype α).toOuterMeasure {a | event a}).toReal := by
  classical
  rw [probability_card, PMF.toOuterMeasure_uniformOfFintype_apply]
  simp [ENNReal.toReal_div, Nat.card_eq_fintype_card]

end
end FiniteProbability
