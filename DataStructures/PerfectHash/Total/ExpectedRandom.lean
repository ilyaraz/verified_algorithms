import DataStructures.PerfectHash.Total.Expected

namespace PerfectHash.Total
open WordRam Bounded FiniteProbability

def childReadSamples (xs : List (Word w)) (a : Word w) (b : Fin (rootSlots xs))
    (samples : Fin w → Word w) : Nat :=
  if bucketCount xs a b ≤ 1 then 0
  else Retry.attempts (childAccepted xs a b) w (fun i => Hashing.MultiplyShift.sample (samples i))

noncomputable section
open scoped Classical
set_option maxRecDepth 50000
set_option maxHeartbeats 20000000

variable {w : Nat} {xs : List (Word w)} {l : Layout} {a : Word w} {s : State w 64}

theorem expected_root_reads (ha : Admissible w xs.length l) :
    mean (fun rho : RandomMemory w => (rootAttempts xs l rho : ℝ)) ≤ 2 := by
  change mean (fun rho : RandomMemory w => (Retry.attempts (rootAccepted xs) w
    (fun i => Hashing.MultiplyShift.sample (rootRawSamples l rho i)) : ℝ)) ≤ _
  rw [mean_root_samples ha (fun samples => (Retry.attempts (rootAccepted xs) w
    (fun i => Hashing.MultiplyShift.sample (samples i)) : ℝ))]
  exact expected_raw_attempts _ (root_rejection_all ha)

theorem expected_child_reads (ha : Admissible w xs.length l) (hr : rootAccepted xs a = true)
    (b : Fin (rootSlots xs)) :
    mean (fun samples : Fin w → Word w => (childReadSamples xs a b samples : ℝ)) ≤ 2*bucketCount xs a b := by
  by_cases hd : bucketCount xs a b ≤ 1
  · simp only [childReadSamples,hd,↓reduceIte,Nat.cast_zero,mean_const]
    positivity
  · simp only [childReadSamples,hd,↓reduceIte]
    have he := expected_raw_attempts (childAccepted xs a b) (child_rejection_all ha hr b)
    have hb : (1 : ℝ) ≤ bucketCount xs a b := by exact_mod_cast (show 1 ≤ bucketCount xs a b by omega)
    linarith

theorem expected_child_reads_actual (ha : Admissible w xs.length l) (b : Fin (rootSlots xs)) :
    mean (fun rho : RandomMemory w => (childReads xs l (rootSeed xs l rho) b rho : ℝ)) ≤
      mean (fun rho : RandomMemory w => 2*(bucketCount xs (rootSeed xs l rho) b : ℝ)) := by
  change mean (fun rho : RandomMemory w =>
    (childReadSamples xs (selected (rootAccepted xs) (rootRawSamples l rho)) b (childRawSamples l w b.val rho) : ℝ)) ≤ _
  rw [mean_root_child ha b (fun past next => (childReadSamples xs (selected (rootAccepted xs) past) b next : ℝ))]
  unfold rootSeed
  rw [mean_root_samples ha (fun past => 2*(bucketCount xs (selected (rootAccepted xs) past) b : ℝ))]
  apply mean_mono
  intro past
  exact expected_child_reads ha (search_total _ _ (root_fallback_total ha)).2 b

theorem bucket_counts_sum (xs : List (Word w)) (a : Word w) :
    (∑ b : Fin (rootSlots xs), bucketCount xs a b) = (values xs).length := by
  simpa only [bucketCount,rootKeys,List.length_reverse] using Buckets.sum_count (rootHash xs a) (rootKeys xs)

theorem expected_remaining_reads (ha : Admissible w xs.length l) :
    mean (fun rho : RandomMemory w => (remainingReads xs l (rootSeed xs l rho) rho 0 : ℝ)) ≤
      2*(values xs).length := by
  simp only [remainingReads,Nat.zero_le,↓reduceIte,Nat.cast_sum]
  rw [mean_sum]
  have hh := Finset.sum_le_sum (fun b (_ : b ∈ Finset.univ) => expected_child_reads_actual ha b)
  have hs : mean (fun rho : RandomMemory w => ∑ b : Fin (rootSlots xs),
      2*(bucketCount xs (rootSeed xs l rho) b : ℝ)) = 2*(values xs).length := by
    have he (rho : RandomMemory w) : (∑ b : Fin (rootSlots xs),
        2*(bucketCount xs (rootSeed xs l rho) b : ℝ)) = 2*(values xs).length := by
      rw [← Finset.mul_sum,← Nat.cast_sum,bucket_counts_sum]
    rw [mean_congr he,mean_const]
  rw [mean_sum] at hs
  exact hh.trans_eq hs

theorem expected_construction_reads (ha : Admissible w xs.length l) :
    mean (fun rho : RandomMemory w => (constructionReads xs l rho : ℝ)) ≤
      (1+2*(StaticSet.distinctCount xs+1) : Nat) := by
  have hr := expected_root_reads ha
  have hc := expected_remaining_reads ha
  simp only [constructionReads,Nat.cast_add,Nat.cast_one,mean_add,mean_const]
  rw [← values_length]
  push_cast
  linarith

theorem expected_random_reads (ha : Admissible w xs.length l) (hp : s.pc = 0)
    (hin : BuildInput w xs.length l s.regs) (harr : ArrayAt s.mem l.inputBase xs) :
    StaticSet.expectedNat (fun rho => (run Total.program rho (constructionFuel bounds w xs.length) s).randomReads) ≤
      (1+2*(StaticSet.distinctCount xs+1) : Nat) := by
  change mean (fun rho : RandomMemory w => ((run Total.program rho (constructionFuel bounds w xs.length) s).randomReads : ℝ)) ≤ _
  apply le_trans _ (expected_construction_reads ha)
  apply mean_mono
  intro rho
  obtain ⟨k,t,log,hr,hk,hbuilt,hpol,hrandom,hreads⟩ := run_total ha rho hp hin harr
  rw [hr]
  exact_mod_cast Nat.le_of_eq hreads

theorem expected_exposed_bits (ha : Admissible w xs.length l) (hp : s.pc = 0)
    (hin : BuildInput w xs.length l s.regs) (harr : ArrayAt s.mem l.inputBase xs) :
    StaticSet.expectedNat (fun rho => (run Total.program rho (constructionFuel bounds w xs.length) s).randomBitsExposed) ≤
      (w*(1+2*(StaticSet.distinctCount xs+1)) : Nat) := by
  change mean (fun rho : RandomMemory w => ((run Total.program rho (constructionFuel bounds w xs.length) s).randomBitsExposed : ℝ)) ≤ _
  have he : mean (fun rho : RandomMemory w => ((run Total.program rho (constructionFuel bounds w xs.length) s).randomBitsExposed : ℝ)) ≤
      (w : ℝ)*mean (fun rho : RandomMemory w => ((run Total.program rho (constructionFuel bounds w xs.length) s).randomReads : ℝ)) := by
    rw [← mean_mul]
    apply mean_mono
    intro rho
    exact_mod_cast RunResult.exposed_le_reads (run Total.program rho (constructionFuel bounds w xs.length) s)
  have hr := expected_random_reads ha hp hin harr
  change mean (fun rho : RandomMemory w => ((run Total.program rho (constructionFuel bounds w xs.length) s).randomReads : ℝ)) ≤ _ at hr
  have hh := mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg w : (0 : ℝ) ≤ w)
  push_cast at hh ⊢
  exact he.trans hh

end
end PerfectHash.Total
