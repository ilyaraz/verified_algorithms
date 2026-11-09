import DataStructures.PerfectHash.Source.Total.Correctness
import DataStructures.PerfectHash.Total.WorstCase

namespace PerfectHash.Source.Total
open WordRam RamLang RamLang.Compiler RamLang.Logic PerfectHash.Bounded

/-- Source allocation, call setup and child trials are bounded by a fixed
multiple of the pure stopping-time cost, for each individual child. -/
theorem child_work_le (xs : List (Word w)) (l : Layout) (a : Word w)
    (rho : RandomMemory w) (b : Fin (rootSlots xs)) :
    Children.work xs a (searchWork xs l a rho) b ≤ 1000*PerfectHash.Total.childWork xs l a b rho := by
  unfold Children.work Allocation.work searchWork PerfectHash.Total.childWork
  omega

/-- Summation preserves the pointwise comparison, including the final loop exit. -/
theorem remaining_work_le (xs : List (Word w)) (l : Layout) (a : Word w)
    (rho : RandomMemory w) (j : Nat) :
    Children.remainingWork xs a (searchWork xs l a rho) j ≤ 1000*PerfectHash.Total.remainingWork xs l a rho j := by
  have hh : (∑ b : Fin (rootSlots xs), if j ≤ b.val then Children.work xs a (searchWork xs l a rho) b else 0) ≤
      ∑ b : Fin (rootSlots xs), 1000*(if j ≤ b.val then PerfectHash.Total.childWork xs l a b rho else 0) := by
    apply Finset.sum_le_sum
    intro b _
    split
    · exact child_work_le xs l a rho b
    · simp
  rw [← Finset.mul_sum] at hh
  unfold Children.remainingWork PerfectHash.Total.remainingWork
  omega

/-- The compiled source majorant includes preparation, all rejected and
fallback trials, all call traffic, public output and halt. It is bounded by a
constant multiple of the already analyzed pure mathematical work model. -/
theorem work_le_model (ha : PerfectHash.Admissible w xs.length l) (rho : RandomMemory w) :
    constructionWork xs l ha rho ≤ 1000*PerfectHash.Total.constructionWork xs l ha rho := by
  have hn := Hashing.PowerOfTwo.conservative xs.length
  have hbn : Hashing.PowerOfTwo.bits xs.length ≤ xs.length :=
    Hashing.PowerOfTwo.least (Nat.le_of_lt Nat.lt_two_pow_self)
  have htail := remaining_work_le xs l (PerfectHash.Total.rootSeed xs l rho) rho 0
  unfold constructionWork Constructor.work
  split
  · unfold PerfectHash.Total.constructionWork
    omega
  · simp only [Constructor.childWork]
    unfold Prepare.work rootWork PerfectHash.Total.constructionWork
    omega

/-- A fixed, image-independent evaluator guard covers the complete source run.
It is not supplied to the program and is never used as runtime advice. -/
def fuel (w N : Nat) : Nat := 1000*constructionFuel PerfectHash.Total.bounds w N

/-- Every source execution fits the fixed evaluator guard, including fallback. -/
theorem work_le_fuel (ha : PerfectHash.Admissible w xs.length l) (rho : RandomMemory w) :
    constructionWork xs l ha rho ≤ fuel w xs.length := by
  exact (work_le_model ha rho).trans (Nat.mul_le_mul_left 1000
    ((PerfectHash.Total.work_le_worst ha rho).trans (PerfectHash.Total.worst_le_fuel xs)))

end PerfectHash.Source.Total
