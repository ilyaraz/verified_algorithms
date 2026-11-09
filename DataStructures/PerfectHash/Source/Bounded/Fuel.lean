import DataStructures.PerfectHash.Source.Bounded.Correctness
import DataStructures.PerfectHash.Bounded.Fuel

namespace PerfectHash.Source.Bounded
open WordRam RamLang RamLang.Compiler RamLang.Logic PerfectHash.Bounded

/-- A fixed evaluator guard covers worst-case comparisons and every capped
trial. It is derived from actual instruction work, not used as runtime advice. -/
def fuel (w N : Nat) : Nat := 100000*(Nat.pow (N+1) 2+(w+1)*(N+1))

/-- Each allocated child charges its capacity, chain length and all reached
trials, with no uncharged initialization or rejected work. -/
theorem child_work_le (hw : 1 ≤ w) (xs : List (Word w)) (l : Layout) (a : Word w)
    (rho : RandomMemory w) (b : Fin (rootSlots xs)) :
    Children.work xs a (searchWork xs l a rho) b ≤
      1000*(w+1)*(childCapacity xs a b+bucketCount xs a b+1) := by
  have hb := Construction.allocation_bits (bucketCount xs a b)
  change Hashing.PowerOfTwo.bits (2*bucketCount xs a b*bucketCount xs a b) ≤ childCapacity xs a b at hb
  have hr := child_attempts_le hw xs l a b rho
  have hh := Nat.mul_le_mul_left (500*(childCapacity xs a b+bucketCount xs a b+1)) hr
  unfold Children.work Allocation.work searchWork
  nlinarith

/-- Accepted root energy makes the complete packed-child work linear in the
number of distinct keys for each fixed retry cap. -/
theorem remaining_work_le (ha : PerfectHash.Admissible w xs.length l) (hy : rootAccepted xs a = true)
    (rho : RandomMemory w) (j : Nat) :
    Children.remainingWork xs a (searchWork xs l a rho) j ≤ 12+1000*(w+1)*(27*(values xs).length+2) := by
  have hs := Sizes.child_work_linear (rootHash xs a) (rootKeys xs) (accepted_energy hy)
    (by simpa [rootKeys] using root_slots_bound xs)
  change (∑ b : Fin (rootSlots xs), (childCapacity xs a b+bucketCount xs a b+1)) ≤ _ at hs
  simp only [rootKeys,List.length_reverse] at hs
  have hh : (∑ b : Fin (rootSlots xs), if j ≤ b.val then Children.work xs a (searchWork xs l a rho) b else 0) ≤
      ∑ b : Fin (rootSlots xs), 1000*(w+1)*(childCapacity xs a b+bucketCount xs a b+1) := by
    apply Finset.sum_le_sum
    intro b _
    split
    · exact child_work_le ha.arithmetic.positiveWidth xs l a rho b
    · exact Nat.zero_le _
  rw [←Finset.mul_sum] at hh
  have hm := Nat.mul_le_mul_left (1000*(w+1)) hs
  unfold Children.remainingWork
  omega

/-- Every pointwise instruction bound is below the explicit, image-independent
fuel guard, including empty input and both budget-failure paths. -/
theorem work_le_fuel (ha : PerfectHash.Admissible w xs.length l) (rho : RandomMemory w) :
    constructionWork xs l ha rho ≤ fuel w xs.length := by
  have hd := values_length_le xs
  have hm := root_slots_bound xs
  have hn := Hashing.PowerOfTwo.conservative xs.length
  have hb : Hashing.PowerOfTwo.bits (values xs).length ≤ (values xs).length :=
    Hashing.PowerOfTwo.least (Nat.le_of_lt Nat.lt_two_pow_self)
  have hbn : Hashing.PowerOfTwo.bits xs.length ≤ xs.length :=
    Hashing.PowerOfTwo.least (Nat.le_of_lt Nat.lt_two_pow_self)
  have hc : Dedup.comparisons
      (Dedup.parameters (dedup_admissible ha) (rho (word w l.randomBase))).hash xs [] ≤ xs.length^2 := by
    simpa [pow_two] using Dedup.comparisons_worst
      (Dedup.parameters (dedup_admissible ha) (rho (word w l.randomBase))).hash xs []
  have hr : rootAttempts xs l rho ≤ w := FiniteProbability.Retry.attempts_le _ _ _
  have hrb := Nat.mul_le_mul_left (300*((values xs).length+rootSlots xs+1)+155) hr
  have hroot : rootWork xs l rho ≤ 1100*w*(xs.length+1)+12 := by
    unfold rootWork
    nlinarith
  have htail : Constructor.childWork xs (rootChoice xs l rho) (fun a => searchWork xs l a rho) ≤
      42+1000*(w+1)*(27*(values xs).length+2) := by
    cases he : rootChoice xs l rho with
    | none => simp only [Constructor.childWork,he]; omega
    | some a =>
      have hh := remaining_work_le ha (root_choice_accepted he) rho 0
      simp only [Constructor.childWork,he]
      omega
  unfold constructionWork Constructor.work
  split
  · unfold fuel
    simp only [Nat.pow_eq]
    nlinarith
  · unfold Prepare.work fuel
    simp only [Nat.pow_eq]
    nlinarith

/-- Fixed fuel observes the constructor's own halt and retains the sharper
pointwise work bound, public outcomes, full access policy and random schedule. -/
theorem run_total {w : Nat} {xs : List (Word w)} {l : Layout} {s : State w StaticSet.registerCount}
    (ha : Admissible w xs.length l) (rho : RandomMemory w) (hpc : s.pc = 0)
    (hin : BuildInput w xs.length l s.regs) (hinput : ArrayAt s.mem l.inputBase xs) :
    ∃ k t trace, WordRam.run program rho (fuel w xs.length) s = ⟨t,k,trace,.halted⟩ ∧
      k ≤ constructionWork xs l ha.toAdmissible rho ∧ t.regs ⟨5,by decide⟩ = word w 1 ∧
      ((t.regs ⟨18,by decide⟩ = word w 0 ∧
        Constructor.Failed (rootChoice xs l rho) (fun a b => childChoice xs l a b rho)) ∨ Public.Built xs l t) ∧
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

end PerfectHash.Source.Bounded
