import DataStructures.PerfectHash.Total.WorstCase

namespace PerfectHash.Total
open WordRam Bounded

variable {w : Nat} {xs : List (Word w)} {l : Layout} {s : State w 64}

/-- The frozen occurrence-count fuel observes the program's own successful halt,
while preserving its sharper pointwise cost and exact random-read count. -/
theorem run_total (ha : Admissible w xs.length l) (rho : RandomMemory w) (hp : s.pc = 0)
    (hin : BuildInput w xs.length l s.regs) (harr : ArrayAt s.mem l.inputBase xs) :
    ∃ k t log, run Total.program rho (constructionFuel bounds w xs.length) s = ⟨t,k,log,.halted⟩ ∧
      k ≤ constructionWork xs l ha rho ∧ Built xs l (rootSeed xs l rho) t ∧
      (policy w xs.length l).AllowsTrace log ∧
      (log.filterMap Access.randomAddress).Sublist (consecutiveAddresses w l.randomBase (randomSpan w xs)) ∧
      (log.filterMap Access.randomAddress).length = constructionReads xs l rho := by
  obtain ⟨k,t,log,ht,hk,hpost,hpol,hr,hreads⟩ := total ha rho hp hin harr
  have hf := hk.trans ((work_le_worst ha rho).trans (worst_le_fuel xs))
  have hs := run_stable (p := Total.program) (rho := rho) (fuel := k) (s := s)
    (by simp [ht.run_eq]) (constructionFuel bounds w xs.length-k)
  rw [Nat.add_sub_of_le hf,ht.run_eq] at hs
  exact ⟨k,t,log,hs,hk,hpost,hpol,hr,hreads⟩

theorem prefixes (ha : Admissible w xs.length l) (rho : RandomMemory w) (hp : s.pc = 0)
    (hin : BuildInput w xs.length l s.regs) (harr : ArrayAt s.mem l.inputBase xs) (n : Nat) :
    (policy w xs.length l).AllowsTrace (run Total.program rho n s).trace ∧
      (∀ f, (run Total.program rho n s).reason ≠ .fault f) ∧
      (∀ addr, ¬ (l.output xs.length).Contains addr → ¬ (l.scratch xs.length).Contains addr →
        (run Total.program rho n s).state.mem addr = s.mem addr) := by
  obtain ⟨k,t,log,ht,hk,hpost,hpol,hr,hreads⟩ := total ha rho hp hin harr
  have hpre := ht.prefix_policy hpol n
  refine ⟨hpre,ht.noFault n,?_⟩
  intro addr ho hs
  apply run_frame
  intro hm
  obtain ⟨e,he,ha'⟩ := List.mem_filterMap.mp hm
  have hh := hpre e he
  cases e <;> simp_all [Access.writeAddress,AccessPolicy.Allows,policy]

end PerfectHash.Total
