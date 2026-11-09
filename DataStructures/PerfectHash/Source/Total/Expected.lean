import DataStructures.PerfectHash.Source.Total.Fuel
import DataStructures.PerfectHash.Total.Expected

namespace PerfectHash.Source.Total
open WordRam FiniteProbability
noncomputable section
open scoped Classical

/-- Uniform expectation includes rejected trials, rare exhaustive fallback,
initialization, calls and halt. Only the pure probability model is reused. -/
theorem expected_work (ha : PerfectHash.Admissible w xs.length l) :
    mean (fun rho : RandomMemory w => (constructionWork xs l ha rho : ℝ)) ≤
      (10000000*(xs.length+1) : Nat) := by
  have hm : mean (fun rho : RandomMemory w => (constructionWork xs l ha rho : ℝ)) ≤
      mean (fun rho : RandomMemory w => (1000*PerfectHash.Total.constructionWork xs l ha rho : ℝ)) := by
    apply mean_mono
    intro rho
    exact_mod_cast work_le_model ha rho
  rw [mean_mul] at hm
  have hh := PerfectHash.Total.expected_construction_work ha
  simp only [PerfectHash.Total.bounds,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat] at hh ⊢
  linarith

/-- Expected actual target instructions through successful halt are linear in
occurrences, with a uniform constant independent of width and random image. -/
theorem expected_instructions {w : Nat} {xs : List (Word w)} {l : Layout} {s : State w StaticSet.registerCount}
    (ha : Admissible w xs.length l) (hpc : s.pc = 0)
    (hin : BuildInput w xs.length l s.regs) (hinput : ArrayAt s.mem l.inputBase xs) :
    expectedSteps program (fuel w xs.length) s ≤ (10000000*(xs.length+1) : Nat) := by
  change mean (fun rho : RandomMemory w => ((run program rho (fuel w xs.length) s).steps : ℝ)) ≤ _
  apply le_trans _ (expected_work ha.toAdmissible)
  apply mean_mono
  intro rho
  obtain ⟨k,t,trace,hr,hk,_,_,_,_⟩ := run_total ha rho hpc hin hinput
  rw [hr]
  exact_mod_cast hk

end
end PerfectHash.Source.Total
