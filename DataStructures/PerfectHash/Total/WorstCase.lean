import DataStructures.PerfectHash.Total.Correctness
import DataStructures.PerfectHash.Specification

namespace PerfectHash.Total
open WordRam Bounded

variable {w : Nat} {xs : List (Word w)} {l : Layout} {a : Word w}

/-- Uniform constants derived from the fixed instruction arrays and stage bounds. -/
def bounds : ResourceBounds := ⟨10000,33,10000,by decide,by decide,by decide⟩

theorem seed_count_le (w : Nat) : seedCount w ≤ modulus w := by
  unfold seedCount modulus
  exact Nat.pow_le_pow_right (by decide) (Nat.sub_le w 1)

theorem trial_work_le (accept : Word w → Bool) (B : Nat) (samples : Fin w → Word w) :
    trialWork accept B samples ≤ B*(w+seedCount w) := FiniteProbability.FiniteSearch.work_le _ _ _ _ _

theorem child_trial_work_le (xs : List (Word w)) (l : Layout) (a : Word w)
    (b : Fin (rootSlots xs)) (rho : RandomMemory w) :
    childTrialWork xs l a b rho ≤ childBudget xs a b*(w+seedCount w) := by
  unfold childTrialWork
  split
  · have hh := seed_count_pos w
    nlinarith
  · exact trial_work_le _ _ _

theorem child_work_le (xs : List (Word w)) (l : Layout) (a : Word w)
    (b : Fin (rootSlots xs)) (rho : RandomMemory w) :
    childWork xs l a b rho ≤ 42*(w+seedCount w+1)*(childCapacity xs a b+bucketCount xs a b+1) := by
  have hb := Construction.allocation_bits (bucketCount xs a b)
  have ht := child_trial_work_le xs l a b rho
  change Hashing.PowerOfTwo.bits (2*bucketCount xs a b*bucketCount xs a b) ≤ childCapacity xs a b at hb
  unfold childWork childBudget at *
  nlinarith

theorem remaining_work_le (hy : rootAccepted xs a = true) (rho : RandomMemory w) (j : Nat) :
    remainingWork xs l a rho j ≤ 6+42*(w+seedCount w+1)*(27*(values xs).length+2) := by
  have hs := Sizes.child_work_linear (rootHash xs a) (rootKeys xs) (accepted_energy hy)
    (by simpa [rootKeys] using root_slots_bound xs)
  change (∑ b : Fin (rootSlots xs), (childCapacity xs a b+bucketCount xs a b+1)) ≤ _ at hs
  simp only [rootKeys,List.length_reverse] at hs
  have hh : (∑ b : Fin (rootSlots xs), if j ≤ b.val then childWork xs l a b rho else 0) ≤
      ∑ b : Fin (rootSlots xs), 42*(w+seedCount w+1)*(childCapacity xs a b+bucketCount xs a b+1) := by
    apply Finset.sum_le_sum
    intro b _
    split
    · exact child_work_le xs l a b rho
    · exact Nat.zero_le _
  rw [← Finset.mul_sum] at hh
  have hm := Nat.mul_le_mul_left (42*(w+seedCount w+1)) hs
  unfold remainingWork
  omega

/-- The frozen worst-case shape needs no quadratic machine-arithmetic fit:
its square and universe factor are mathematical instruction bounds only. -/
theorem work_le_worst (ha : Admissible w xs.length l) (rho : RandomMemory w) :
    constructionWork xs l ha rho ≤ worstInstructions bounds w xs.length (StaticSet.distinctCount xs) := by
  have hd := values_length_le xs
  have hm := root_slots_bound xs
  have hb : Hashing.PowerOfTwo.bits (values xs).length ≤ (values xs).length :=
    Hashing.PowerOfTwo.least (Nat.le_of_lt Nat.lt_two_pow_self)
  have hc : Dedup.comparisons
      (Dedup.parameters (dedup_admissible ha) (rho (word w l.randomBase))).hash xs [] ≤ xs.length^2 := by
    simpa [pow_two] using Dedup.comparisons_worst
      (Dedup.parameters (dedup_admissible ha) (rho (word w l.randomBase))).hash xs []
  have hH := seed_count_le w
  have hw := ha.arithmetic.widthValue
  have hroot := trial_work_le (rootAccepted xs) (rootBudget xs) (rootRawSamples l rho)
  change rootWork xs l rho ≤ rootBudget xs*(w+seedCount w) at hroot
  have hr : rootWork xs l rho ≤ 140*modulus w*((values xs).length+1) := by
    unfold rootBudget at hroot
    nlinarith
  have htail := remaining_work_le (l := l) (root_seed_accepted ha rho) rho 0
  have ht : remainingWork xs l (rootSeed xs l rho) rho 0 ≤ 6+3402*modulus w*((values xs).length+1) := by
    nlinarith
  unfold constructionWork worstInstructions bounds
  rw [← values_length]
  simp only [Nat.pow_eq]
  nlinarith

theorem worst_le_fuel (xs : List (Word w)) :
    worstInstructions bounds w xs.length (StaticSet.distinctCount xs) ≤ constructionFuel bounds w xs.length := by
  have hd := StaticSet.distinctCount_le_length xs
  unfold constructionFuel worstInstructions
  exact Nat.mul_le_mul_left _ (Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _)

end PerfectHash.Total
