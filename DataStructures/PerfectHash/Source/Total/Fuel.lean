import DataStructures.PerfectHash.Source.Total.Work

namespace PerfectHash.Source.Total
open WordRam RamLang RamLang.Compiler RamLang.Logic PerfectHash.Bounded

/-- Fixed fuel observes the constructor's own halt and retains the sharper
pointwise work bound, public outcomes, full access policy and random schedule. -/
theorem run_total {w : Nat} {xs : List (Word w)} {l : Layout} {s : State w StaticSet.registerCount}
    (ha : Admissible w xs.length l) (rho : RandomMemory w) (hpc : s.pc = 0)
    (hin : BuildInput w xs.length l s.regs) (hinput : ArrayAt s.mem l.inputBase xs) :
    ∃ k t trace, WordRam.run program rho (fuel w xs.length) s = ⟨t,k,trace,.halted⟩ ∧
      k ≤ constructionWork xs l ha.toAdmissible rho ∧ t.regs ⟨5,by decide⟩ = word w 1 ∧
      Public.Built xs l t ∧
      (PerfectHash.Bounded.policy w xs.length l).AllowsTrace trace ∧
      (trace.filterMap Access.randomAddress).Sublist (consecutiveAddresses w l.randomBase (randomSpan w xs)) := by
  obtain ⟨k,t,trace,ht,hk,hstatus,hpost,hp,hr⟩ := execution ha rho hpc hin hinput
  have hf := hk.trans (work_le_fuel ha.toAdmissible rho)
  have hs := run_stable (p := program) (rho := rho) (s := s) (fuel := k)
    (by rw [ht.run_eq]; simp) (fuel w xs.length-k)
  exact ⟨k,t,trace,by simpa only [Nat.add_sub_of_le hf,ht.run_eq] using hs,hk,hstatus,hpost,hp,hr⟩

/-- Every interrupted or completed run preserves all memory outside output and
scratch, in particular the disjoint occurrence array. -/
theorem frame {w : Nat} {xs : List (Word w)} {l : Layout} {s : State w StaticSet.registerCount}
    (ha : Admissible w xs.length l) (rho : RandomMemory w) (hpc : s.pc = 0)
    (hin : BuildInput w xs.length l s.regs) (hinput : ArrayAt s.mem l.inputBase xs)
    (budget : Nat) (a : Addr w) (ho : ¬ (l.output xs.length).Contains a) (hs : ¬ (l.scratch xs.length).Contains a) :
    (WordRam.run program rho budget s).state.mem a = s.mem a := by
  apply run_frame
  intro hm
  obtain ⟨e,he,hea⟩ := List.mem_filterMap.mp hm
  have hh := (prefix_safety ha rho hpc hin hinput budget).1 e he
  cases e <;> simp_all [Access.writeAddress,AccessPolicy.Allows,PerfectHash.Bounded.policy]

end PerfectHash.Source.Total
