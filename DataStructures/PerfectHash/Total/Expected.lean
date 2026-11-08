import DataStructures.PerfectHash.Total.ExpectedStages
import DataStructures.PerfectHash.Total.Interface
import Algorithms.Dedup.Expected

namespace PerfectHash.Total
open WordRam Bounded FiniteProbability
noncomputable section
open scoped Classical
set_option maxRecDepth 50000
set_option maxHeartbeats 20000000

variable {w : Nat} {xs : List (Word w)} {l : Layout} {s : State w 64}

/-- Every occurrence is charged in deduplication; its seed-independent output
permits the subsequent root/child analysis on the computed distinct array. -/
theorem expected_construction_work (ha : Admissible w xs.length l) :
    mean (fun rho : RandomMemory w => (constructionWork xs l ha rho : ℝ)) ≤
      (bounds.preprocess*(xs.length+1) : Nat) := by
  have hc : mean (fun rho : RandomMemory w => (Dedup.comparisons
      (Dedup.parameters (dedup_admissible ha) (rho (word w l.randomBase))).hash xs [] : ℝ)) ≤ 3*xs.length := by
    rw [Dedup.mean_cell (word w l.randomBase)
      (fun raw => (Dedup.comparisons (Dedup.parameters (dedup_admissible ha) raw).hash xs [] : ℝ))]
    exact Dedup.expected_raw_comparisons xs (dedupLayout l) (dedup_admissible ha)
  have hr := expected_root_work ha
  have ht := expected_remaining_work ha
  have hm := root_slots_bound xs
  have hd := values_length_le xs
  have hb : Hashing.PowerOfTwo.bits (values xs).length ≤ (values xs).length :=
    Hashing.PowerOfTwo.least (Nat.le_of_lt Nat.lt_two_pow_self)
  have hm' : (rootSlots xs : ℝ) ≤ 2*((values xs).length+1) := by exact_mod_cast hm
  have hd' : ((values xs).length : ℝ) ≤ xs.length := by exact_mod_cast hd
  have hb' : (Hashing.PowerOfTwo.bits (values xs).length : ℝ) ≤ (values xs).length := by exact_mod_cast hb
  unfold rootBudget at hr
  push_cast at hr
  simp only [constructionWork,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,
    mean_add,mean_mul,mean_const,bounds]
  nlinarith

/-- Expected actual instructions through successful halt, including rare
fallback executions. The evaluator guard does not replace the charged cost. -/
theorem expected_instructions (ha : Admissible w xs.length l) (hp : s.pc = 0)
    (hin : BuildInput w xs.length l s.regs) (harr : ArrayAt s.mem l.inputBase xs) :
    expectedSteps Total.program (constructionFuel bounds w xs.length) s ≤
      (bounds.preprocess*(xs.length+1) : Nat) := by
  change mean (fun rho : RandomMemory w => ((run Total.program rho (constructionFuel bounds w xs.length) s).steps : ℝ)) ≤ _
  apply le_trans _ (expected_construction_work ha)
  apply mean_mono
  intro rho
  obtain ⟨k,t,log,hr,hk,hbuilt,hpol,hrandom,hreads⟩ := run_total ha rho hp hin harr
  rw [hr]
  exact_mod_cast hk

end
end PerfectHash.Total
