import Algorithms.Dedup.Model

namespace Dedup
noncomputable section
open FiniteProbability
open scoped Classical

variable {Key Seed : Type} [DecidableEq Key] [Fintype Seed] [Nonempty Seed]

/-- The hash contract gives an exact finite-average collision probability. -/
theorem hash_collision_probability (family : Hashing.Family Key Seed slots)
    (h : Hashing.CollisionBound family constant) (hm : 0 < slots) (hne : x ≠ y) :
    probability (fun a => family.eval a x = family.eval a y) ≤ (constant : ℝ)/slots := by
  rw [probability_pmf]
  exact h.probability hm hne

theorem expected_collisions (family : Hashing.Family Key Seed slots)
    (h : Hashing.CollisionBound family constant) (hm : 0 < slots)
    (seen : List Key) (key : Key) :
    mean (fun a => (collisions (family.eval a) key seen : ℝ)) ≤
      ((constant : ℝ)/slots) * seen.length := by
  induction seen with
  | nil => simp [collisions]
  | cons x xs ih =>
    have he : ∀ a : Seed, (collisions (family.eval a) key (x::xs) : ℝ) =
        (if key ≠ x ∧ family.eval a x = family.eval a key then (1 : ℝ) else 0) +
          (collisions (family.eval a) key xs : ℝ) := by
      intro a
      simp only [collisions, Nat.cast_add]
      split <;> simp
    rw [mean_congr he, mean_add, mean_indicator]
    have hp : probability (fun a => key ≠ x ∧ family.eval a x = family.eval a key) ≤
        (constant : ℝ)/slots := by
      by_cases hk : key = x
      · subst x
        simp only [ne_eq, not_true_eq_false, false_and, probability_false]
        positivity
      · have he' : ∀ a, (key ≠ x ∧ family.eval a x = family.eval a key) ↔
            family.eval a x = family.eval a key := by intro a; simp [hk]
        rw [probability_congr he']
        exact hash_collision_probability family h hm (Ne.symm hk)
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    nlinarith

/-- This bound charges every occurrence, even a duplicate whose chain search
traverses other keys. The distinct-state evolution is independent of the seed. -/
theorem expected_comparisons (family : Hashing.Family Key Seed slots)
    (h : Hashing.CollisionBound family constant) (hm : 0 < slots)
    (xs seen : List Key) :
    mean (fun a => (comparisons (family.eval a) xs seen : ℝ)) ≤
      xs.length * (1 + ((constant : ℝ)/slots)*(seen.length+xs.length)) := by
  induction xs generalizing seen with
  | nil => simp [comparisons]
  | cons x xs ih =>
    have hscan : mean (fun a => (scanComparisons x (bucket (family.eval a) seen x) : ℝ)) ≤
        1 + ((constant : ℝ)/slots)*seen.length := by
      calc
        _ ≤ mean (fun a => (1 : ℝ) + (collisions (family.eval a) x seen : ℝ)) := by
          apply mean_mono
          intro a
          exact_mod_cast scan_le_collisions (family.eval a) seen x
        _ = 1 + mean (fun a => (collisions (family.eval a) x seen : ℝ)) := by rw [mean_add, mean_const]
        _ ≤ _ := add_le_add_left (expected_collisions family h hm seen x) 1
    have htail := ih (insert x seen)
    have hlen := insert_length (key := x) (seen := seen)
    have hlen' : ((insert x seen).length : ℝ) ≤ seen.length+1 := by exact_mod_cast hlen
    have hc : 0 ≤ (constant : ℝ)/slots := by positivity
    have hxs : (0 : ℝ) ≤ xs.length := Nat.cast_nonneg _
    have hh := mul_le_mul_of_nonneg_left hlen' hc
    have hh' := mul_le_mul_of_nonneg_left hh hxs
    have he : ∀ a : Seed, (comparisons (family.eval a) (x::xs) seen : ℝ) =
        (scanComparisons x (bucket (family.eval a) seen x) : ℝ) +
          (comparisons (family.eval a) xs (insert x seen) : ℝ) := by simp [comparisons]
    rw [mean_congr he, mean_add]
    simp only [List.length_cons, Nat.cast_add, Nat.cast_one]
    nlinarith

/-- With at least N buckets and collision constant two, the total expected
number of equality comparisons is at most 3N, for arbitrary multiplicities. -/
theorem expected_comparisons_linear (family : Hashing.Family Key Seed slots)
    (h : Hashing.CollisionBound family 2) (hm : 0 < slots)
    (xs : List Key) (hn : xs.length ≤ slots) :
    mean (fun a => (comparisons (family.eval a) xs [] : ℝ)) ≤ 3*xs.length := by
  have he := expected_comparisons family h hm xs []
  simp only [List.length_nil, Nat.cast_zero, zero_add, Nat.cast_ofNat] at he
  have hm' : (0 : ℝ) < slots := by exact_mod_cast hm
  have hn' : (xs.length : ℝ) ≤ slots := by exact_mod_cast hn
  have hh : (2 : ℝ)/slots*xs.length ≤ 2 := by
    have := mul_le_mul_of_nonneg_left hn' (show (0 : ℝ) ≤ 2/slots by positivity)
    simpa [hm'.ne'] using this
  have hmul := mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg xs.length : (0 : ℝ) ≤ xs.length)
  nlinarith

end
end Dedup
