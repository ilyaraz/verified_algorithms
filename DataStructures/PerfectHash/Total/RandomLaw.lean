import DataStructures.PerfectHash.Total.WorstCase
import WordRam.RandomBlocks

namespace PerfectHash.Total
open WordRam Bounded FiniteProbability
noncomputable section
open scoped Classical
set_option maxRecDepth 50000
set_option maxHeartbeats 20000000

variable {w : Nat} {xs : List (Word w)} {l : Layout} {a : Word w}

/-- Uniform averages are independent of equivalent finite-type enumerations. -/
theorem mean_instances {α : Type*} {i j : Fintype α} {f g : α → ℝ}
    (h : ∀ a, f a = g a) : @mean α i f = @mean α j g := by
  cases Subsingleton.elim i j
  exact @mean_congr α i f g h

theorem root_block_fit (ha : Admissible w xs.length l) :
    (Region.mk (l.randomBase+1) w).Fits w := by
  have hf : l.randomBase+1+w*(rootSlots xs+1) < modulus w := by
    simpa only [randomSpan,Nat.add_assoc] using random_span_fit ha
  have hh := RandomBlocks.stage_fits hf (show 0 < rootSlots xs+1 by omega)
  simpa [RandomBlocks.stageBase] using hh

theorem child_block_fit (ha : Admissible w xs.length l) (b : Fin (rootSlots xs)) :
    (Region.mk (childRandomBase l w b.val) w).Fits w := by
  have hf : l.randomBase+1+w*(rootSlots xs+1) < modulus w := by
    simpa only [randomSpan,Nat.add_assoc] using random_span_fit ha
  have hh := RandomBlocks.stage_fits hf (show b.val+1 < rootSlots xs+1 by omega)
  exact hh

theorem root_child_separated (b : Fin (rootSlots xs)) :
    (Region.mk (l.randomBase+1) w).Separated ⟨childRandomBase l w b.val,w⟩ := by
  have hh := RandomBlocks.stages_separated (base := l.randomBase) (w := w) (show 0 < b.val+1 by omega)
  simpa [RandomBlocks.stageBase,childRandomBase] using hh

/-- The addressed root block has exactly the uniform finite-tuple law. -/
theorem mean_root_samples (ha : Admissible w xs.length l) (f : (Fin w → Word w) → ℝ) :
    mean (fun rho : RandomMemory w => f (rootRawSamples l rho)) = mean f := by
  have h := RandomBlocks.mean_coordinates (RandomBlocks.address w (l.randomBase+1))
      (RandomBlocks.address_injective (root_block_fit ha)) f
  exact h.trans (mean_instances (fun _ => rfl))

/-- A child's samples are independent of the entire root block. The cost may
still depend arbitrarily on the root outcome, bucket contents, and allocation. -/
theorem mean_root_child (ha : Admissible w xs.length l) (b : Fin (rootSlots xs))
    (f : (Fin w → Word w) → (Fin w → Word w) → ℝ) :
    mean (fun rho : RandomMemory w => f (rootRawSamples l rho) (childRawSamples l w b.val rho)) =
      mean (fun past => mean (fun next => f past next)) := by
  have h := RandomBlocks.mean_disjoint (RandomBlocks.address w (l.randomBase+1))
      (RandomBlocks.address w (childRandomBase l w b.val))
      (RandomBlocks.address_injective (root_block_fit ha))
      (RandomBlocks.address_injective (child_block_fit ha b))
      (RandomBlocks.address_disjoint (root_block_fit ha) (child_block_fit ha b) (root_child_separated b)) f
  exact h.trans (mean_instances (fun _ => mean_instances (fun _ => rfl)))

/-- Exhaustive work on rejected random images is included in this expectation. -/
theorem expected_trial_work (accept : Word w → Bool)
    (hq : Retry.rejection (fun raw => accept (Hashing.MultiplyShift.sample raw)) ≤ 1/2) (B : Nat) :
    mean (fun samples : Fin w → Word w => (trialWork accept B samples : ℝ)) ≤ 3*B := by
  unfold trialWork seedCount
  simpa only [Nat.pow_eq] using FiniteSearch.expected_work_word _ hq B w

theorem expected_raw_attempts (accept : Word w → Bool)
    (hq : Retry.rejection (fun raw => accept (Hashing.MultiplyShift.sample raw)) ≤ 1/2) :
    mean (fun samples : Fin w → Word w =>
      (Retry.attempts accept w (fun i => Hashing.MultiplyShift.sample (samples i)) : ℝ)) ≤ 2 := by
  simp only [Retry.attempts_map]
  have hh := Retry.expected_attempts _ hq w
  have hp := pow_nonneg (FiniteProbability.probability_nonneg
    (fun raw => accept (Hashing.MultiplyShift.sample raw) = false)) w
  change 0 ≤ Retry.rejection (fun raw => accept (Hashing.MultiplyShift.sample raw))^w at hp
  linarith

end
end PerfectHash.Total
