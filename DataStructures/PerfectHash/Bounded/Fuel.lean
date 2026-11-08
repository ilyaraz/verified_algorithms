import DataStructures.PerfectHash.Bounded.Correctness

namespace PerfectHash.Bounded
open WordRam Construction.Registers Registers

/-- Interpreter guard derived from the concrete bounded code. This is not the
actual instruction cost and supplies no distinct-count advice to the machine. -/
def fuel (w N : Nat) : Nat := 10000*(Nat.pow (N+1) 2+(w+1)*(N+1))

variable {w : Nat} {xs : List (Word w)} {l : Layout} {s : State w 64}

theorem root_choice_accepted (h : rootChoice xs l rho = some a) : rootAccepted xs a = true :=
  FiniteProbability.Retry.find_sound _ _ _ h

theorem work_le_fuel (ha : Admissible w xs.length l) (rho : RandomMemory w) :
    constructionWork xs l ha rho ≤ fuel w xs.length := by
  have hd := values_length_le xs
  have hm := root_slots_bound xs
  have hb : Hashing.PowerOfTwo.bits (values xs).length ≤ (values xs).length :=
    Hashing.PowerOfTwo.least (Nat.le_of_lt Nat.lt_two_pow_self)
  have hc : Dedup.comparisons
      (Dedup.parameters (dedup_admissible ha) (rho (word w l.randomBase))).hash xs [] ≤ xs.length^2 := by
    simpa [pow_two] using Dedup.comparisons_worst
      (Dedup.parameters (dedup_admissible ha) (rho (word w l.randomBase))).hash xs []
  have hr : rootAttempts xs l rho ≤ w := FiniteProbability.Retry.attempts_le _ _ _
  have hrb := Nat.mul_le_mul_left (20*rootSlots xs+25*(values xs).length+20) hr
  have hroot : (20*rootSlots xs+25*(values xs).length+20)*rootAttempts xs l rho ≤ 65*w*(xs.length+1) := by
    nlinarith
  have htail : tailWork xs l rho ≤ 17+42*(w+1)*(27*(values xs).length+2) := by
    cases he : rootChoice xs l rho with
    | none => simp only [tailWork,he]; omega
    | some a =>
      have hh := remaining_work_le ha (root_choice_accepted he) rho 0
      simp only [tailWork,he]
      omega
  unfold constructionWork fuel
  simp only [Nat.pow_eq]
  nlinarith

theorem random_span_le (xs : List (Word w)) : randomSpan w xs ≤ randomCapacity w (StaticSet.distinctCount xs) := by
  have hm := root_slots_bound xs
  rw [values_length] at hm
  have hh := Nat.mul_le_mul_left w (Nat.add_le_add_right hm 1)
  unfold randomSpan randomCapacity bucketCapacity
  omega

theorem random_span_fit (ha : Admissible w xs.length l) : l.randomBase+randomSpan w xs < modulus w := by
  have hm := root_slots_bound xs
  have hd := values_length_le xs
  have hh := Nat.mul_le_mul_left w (show rootSlots xs+1 ≤ bucketCapacity xs.length+1 by unfold bucketCapacity; omega)
  have hf := ha.random
  change l.randomBase+randomCapacity w xs.length < modulus w at hf
  unfold randomSpan randomCapacity at *
  omega

/-- Sufficient fuel observes the program's own halt, retaining the pointwise
cost and the explicit success/failure result rather than treating fuel as cost. -/
theorem run_total (ha : Admissible w xs.length l) (rho : RandomMemory w) (hp : s.pc = 0)
    (hin : BuildInput w xs.length l s.regs) (harr : ArrayAt s.mem l.inputBase xs) :
    ∃ k t log, run program rho (fuel w xs.length) s = ⟨t,k,log,.halted⟩ ∧
      k ≤ constructionWork xs l ha rho ∧
      (t.regs status = word w 0 ∨ ∃ a, Built xs l a t) ∧ (policy w xs.length l).AllowsTrace log ∧
      (log.filterMap Access.randomAddress).Sublist (consecutiveAddresses w l.randomBase (randomSpan w xs)) := by
  obtain ⟨k,t,log,ht,hk,hpost,hpol,hr⟩ := total ha rho hp hin harr
  have hf := hk.trans (work_le_fuel ha rho)
  have hs := run_stable (p := program) (rho := rho) (fuel := k) (s := s)
    (by simp [ht.run_eq]) (fuel w xs.length-k)
  rw [Nat.add_sub_of_le hf,ht.run_eq] at hs
  exact ⟨k,t,log,hs,hk,hpost,hpol,hr⟩

/-- Every finite prefix stays within the declared access regions and cannot
fault, including prefixes interrupted in unsuccessful trials. -/
theorem prefixes (ha : Admissible w xs.length l) (rho : RandomMemory w) (hp : s.pc = 0)
    (hin : BuildInput w xs.length l s.regs) (harr : ArrayAt s.mem l.inputBase xs) (n : Nat) :
    (policy w xs.length l).AllowsTrace (run program rho n s).trace ∧
      (∀ f, (run program rho n s).reason ≠ .fault f) ∧
      (∀ addr, ¬ (l.output xs.length).Contains addr → ¬ (l.scratch xs.length).Contains addr →
        (run program rho n s).state.mem addr = s.mem addr) := by
  obtain ⟨k,t,log,ht,hk,hpost,hpol,hr⟩ := total ha rho hp hin harr
  have hpre := ht.prefix_policy hpol n
  refine ⟨hpre,ht.noFault n,?_⟩
  intro addr ho hs
  apply run_frame
  intro hm
  obtain ⟨e,he,ha'⟩ := List.mem_filterMap.mp hm
  have hh := hpre e he
  cases e <;> simp_all [Access.writeAddress,AccessPolicy.Allows,policy]

end PerfectHash.Bounded
