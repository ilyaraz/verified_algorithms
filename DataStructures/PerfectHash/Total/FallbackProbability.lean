import DataStructures.PerfectHash.Total.ExpectedRandom

namespace PerfectHash.Total
open WordRam Bounded FiniteProbability

def rootFallback (xs : List (Word w)) (l : Layout) (rho : RandomMemory w) : Bool :=
  Retry.failed (rootAccepted xs) w (rootSamples xs l rho)

def childFallbackSamples (xs : List (Word w)) (a : Word w) (b : Fin (rootSlots xs))
    (samples : Fin w → Word w) : Bool :=
  if bucketCount xs a b ≤ 1 then false
  else Retry.failed (childAccepted xs a b) w (fun i => Hashing.MultiplyShift.sample (samples i))

def childFallback (xs : List (Word w)) (l : Layout) (a : Word w) (b : Fin (rootSlots xs))
    (rho : RandomMemory w) : Bool := childFallbackSamples xs a b (childRawSamples l w b.val rho)

/-- The root or a hashed child exhausts its random budget. The stage-refinement
proofs identify these exact stopping rules with entry to the RAM fallback. -/
def FallbackEvent (xs : List (Word w)) (l : Layout) (rho : RandomMemory w) : Prop :=
  rootFallback xs l rho = true ∨ ∃ b : Fin (rootSlots xs), childFallback xs l (rootSeed xs l rho) b rho = true

noncomputable section
open scoped Classical
set_option maxRecDepth 50000
set_option maxHeartbeats 20000000

variable {w : Nat} {xs : List (Word w)} {l : Layout} {a : Word w}

def boolIndicator (b : Bool) : ℝ := if b then 1 else 0

theorem probability_bool {α : Type*} [Fintype α] (f : α → Bool) :
    FiniteProbability.probability (fun x => f x = true) = mean (fun x => boolIndicator (f x)) := by
  unfold FiniteProbability.probability
  apply mean_congr
  intro x
  cases hf : f x <;> simp [boolIndicator,hf]

theorem root_fallback_probability (ha : Admissible w xs.length l) :
    FiniteProbability.probability (fun rho : RandomMemory w => rootFallback xs l rho = true) ≤ (1/2 : ℝ)^w := by
  rw [probability_bool]
  unfold rootFallback
  change mean (fun rho : RandomMemory w => boolIndicator (Retry.failed (rootAccepted xs) w
    (fun i => Hashing.MultiplyShift.sample (rootRawSamples l rho i)))) ≤ _
  rw [mean_root_samples ha (fun samples => boolIndicator (Retry.failed (rootAccepted xs) w
    (fun i => Hashing.MultiplyShift.sample (samples i))))]
  simp only [Retry.failed_map]
  rw [← probability_bool]
  exact Retry.fallback_bound _ (root_rejection_all ha) w

theorem child_fallback_probability (ha : Admissible w xs.length l) (hr : rootAccepted xs a = true)
    (b : Fin (rootSlots xs)) :
    FiniteProbability.probability (fun samples : Fin w → Word w => childFallbackSamples xs a b samples = true) ≤
      (1/2 : ℝ)^w := by
  rw [probability_bool]
  by_cases hd : bucketCount xs a b ≤ 1
  · simp only [childFallbackSamples,hd,↓reduceIte,boolIndicator,Bool.false_eq_true,mean_const]
    positivity
  · simp only [childFallbackSamples,hd,↓reduceIte,Retry.failed_map]
    rw [← probability_bool]
    exact Retry.fallback_bound _ (child_rejection_all ha hr b) w

theorem child_fallback_probability_actual (ha : Admissible w xs.length l) (b : Fin (rootSlots xs)) :
    FiniteProbability.probability (fun rho : RandomMemory w => childFallback xs l (rootSeed xs l rho) b rho = true) ≤
      (1/2 : ℝ)^w := by
  rw [probability_bool]
  unfold childFallback rootSeed
  rw [mean_root_child ha b (fun past next => boolIndicator (childFallbackSamples xs (selected (rootAccepted xs) past) b next))]
  apply mean_le
  intro past
  rw [← probability_bool]
  exact child_fallback_probability ha (search_total _ _ (root_fallback_total ha)).2 b

/-- A union bound under the one immutable random-memory law. Root-dependent
children are handled conditionally; repeated seed values need not be unequal. -/
theorem fallback_probability (ha : Admissible w xs.length l) :
    WordRam.probability (FallbackEvent xs l) ≤ ((rootSlots xs : ℝ)+1)*(1/2 : ℝ)^w := by
  rw [RandomBlocks.probability_eq_finite]
  have hu := FiniteProbability.probability_union
    (fun rho : RandomMemory w => rootFallback xs l rho = true)
    (fun rho : RandomMemory w => ∃ b : Fin (rootSlots xs), childFallback xs l (rootSeed xs l rho) b rho = true)
  have hc := FiniteProbability.probability_union_finset (Finset.univ : Finset (Fin (rootSlots xs)))
    (fun b rho => childFallback xs l (rootSeed xs l rho) b rho = true)
  simp only [Finset.mem_univ,true_and] at hc
  have hb := Finset.sum_le_sum (fun b (_ : b ∈ (Finset.univ : Finset (Fin (rootSlots xs)))) =>
    child_fallback_probability_actual ha b)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hb
  have hr := root_fallback_probability ha
  change FiniteProbability.probability (FallbackEvent xs l) ≤ _ at hu
  nlinarith

end
end PerfectHash.Total
