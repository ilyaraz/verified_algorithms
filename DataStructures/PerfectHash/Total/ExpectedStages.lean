import DataStructures.PerfectHash.Total.RandomLaw

namespace PerfectHash.Total
open WordRam Bounded FiniteProbability

/-- A child's cost as a function of its own raw block, with the accepted root
fixed. The function also includes charged allocation and loop continuation. -/
def childCostSamples (xs : List (Word w)) (a : Word w) (b : Fin (rootSlots xs))
    (samples : Fin w → Word w) : Nat :=
  4*Hashing.PowerOfTwo.bits (2*bucketCount xs a b*bucketCount xs a b)+38+
    if bucketCount xs a b ≤ 1 then childBudget xs a b
    else trialWork (childAccepted xs a b) (childBudget xs a b) samples

noncomputable section
open scoped Classical
set_option maxRecDepth 50000
set_option maxHeartbeats 20000000

variable {w : Nat} {xs : List (Word w)} {l : Layout} {a : Word w}

theorem expected_root_work (ha : Admissible w xs.length l) :
    mean (fun rho : RandomMemory w => (rootWork xs l rho : ℝ)) ≤ 3*rootBudget xs := by
  rw [show (fun rho : RandomMemory w => (rootWork xs l rho : ℝ)) =
    (fun rho => (trialWork (rootAccepted xs) (rootBudget xs) (rootRawSamples l rho) : ℝ)) from rfl,
    mean_root_samples ha (fun samples => (trialWork (rootAccepted xs) (rootBudget xs) samples : ℝ))]
  exact expected_trial_work _ (root_rejection_all ha) _

theorem expected_child_cost (ha : Admissible w xs.length l) (hr : rootAccepted xs a = true)
    (b : Fin (rootSlots xs)) :
    mean (fun samples : Fin w → Word w => (childCostSamples xs a b samples : ℝ)) ≤
      132*(childCapacity xs a b+bucketCount xs a b+1) := by
  have hb := Construction.allocation_bits (bucketCount xs a b)
  change Hashing.PowerOfTwo.bits (2*bucketCount xs a b*bucketCount xs a b) ≤ childCapacity xs a b at hb
  by_cases hd : bucketCount xs a b ≤ 1
  · simp only [childCostSamples,hd,↓reduceIte,mean_const]
    unfold childBudget
    exact_mod_cast (show 4*Hashing.PowerOfTwo.bits (2*bucketCount xs a b*bucketCount xs a b)+38+
      (10*childCapacity xs a b+17*bucketCount xs a b+30) ≤
        132*(childCapacity xs a b+bucketCount xs a b+1) by omega)
  · simp only [childCostSamples,hd,↓reduceIte,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
    rw [mean_add,mean_const]
    have hh := expected_trial_work (childAccepted xs a b) (child_rejection_all ha hr b) (childBudget xs a b)
    have hb' : (Hashing.PowerOfTwo.bits (2*bucketCount xs a b*bucketCount xs a b) : ℝ) ≤ childCapacity xs a b := by exact_mod_cast hb
    unfold childBudget at hh ⊢
    push_cast at hh
    nlinarith

/-- Averaging a child after conditioning on the root keeps its own size, even
when the root required exhaustive fallback. -/
theorem expected_child_work (ha : Admissible w xs.length l) (b : Fin (rootSlots xs)) :
    mean (fun rho : RandomMemory w => (childWork xs l (rootSeed xs l rho) b rho : ℝ)) ≤
      mean (fun rho : RandomMemory w =>
        132*((childCapacity xs (rootSeed xs l rho) b : ℝ)+bucketCount xs (rootSeed xs l rho) b+1)) := by
  change mean (fun rho : RandomMemory w =>
    (childCostSamples xs (selected (rootAccepted xs) (rootRawSamples l rho)) b (childRawSamples l w b.val rho) : ℝ)) ≤ _
  rw [mean_root_child ha b (fun past next => (childCostSamples xs (selected (rootAccepted xs) past) b next : ℝ))]
  have he := mean_root_samples ha (fun past =>
    132*((childCapacity xs (selected (rootAccepted xs) past) b : ℝ)+bucketCount xs (selected (rootAccepted xs) past) b+1))
  change _ = mean (fun past => 132*((childCapacity xs (selected (rootAccepted xs) past) b : ℝ)+
    bucketCount xs (selected (rootAccepted xs) past) b+1)) at he
  unfold rootSeed
  rw [he]
  apply mean_mono
  intro past
  exact expected_child_cost ha (search_total _ _ (root_fallback_total ha)).2 b

theorem child_sizes_sum (hr : rootAccepted xs a = true) :
    (∑ b : Fin (rootSlots xs), (childCapacity xs a b+bucketCount xs a b+1)) ≤ 27*(values xs).length+2 := by
  simpa only [rootKeys,List.length_reverse] using Sizes.child_work_linear (rootHash xs a) (rootKeys xs)
    (accepted_energy hr) (by simpa only [rootKeys,List.length_reverse] using root_slots_bound xs)

/-- The sum of conditional child budgets is linear for every accepted root;
there is no multiplication by a largest-bucket cost. -/
theorem expected_remaining_work (ha : Admissible w xs.length l) :
    mean (fun rho : RandomMemory w => (remainingWork xs l (rootSeed xs l rho) rho 0 : ℝ)) ≤
      6+132*(27*(values xs).length+2) := by
  simp only [remainingWork,Nat.zero_le,↓reduceIte,Nat.cast_add,Nat.cast_sum,Nat.cast_ofNat]
  rw [mean_add,mean_const,mean_sum]
  have hh := Finset.sum_le_sum (fun b (_ : b ∈ Finset.univ) => expected_child_work ha b)
  have hs : mean (fun rho : RandomMemory w => ∑ b : Fin (rootSlots xs),
      132*((childCapacity xs (rootSeed xs l rho) b : ℝ)+bucketCount xs (rootSeed xs l rho) b+1)) ≤
      132*(27*(values xs).length+2) := by
    apply mean_le
    intro rho
    have hsum := child_sizes_sum (root_seed_accepted ha rho)
    have hsum' : (∑ b : Fin (rootSlots xs),
      ((childCapacity xs (rootSeed xs l rho) b : ℝ)+bucketCount xs (rootSeed xs l rho) b+1)) ≤
        27*(values xs).length+2 := by exact_mod_cast hsum
    rw [← Finset.mul_sum]
    linarith
  rw [mean_sum] at hs
  exact add_le_add_left (hh.trans hs) 6

end
end PerfectHash.Total
