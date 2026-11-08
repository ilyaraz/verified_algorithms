import DataStructures.PerfectHash.Total.OuterLoop

namespace PerfectHash.Total
open WordRam Bounded Construction.Registers Bounded.Registers

set_option maxRecDepth 50000
set_option maxHeartbeats 20000000

/-- Pointwise cost of the complete constructor, including all failed random
trials and all deterministic fallback candidates actually covered by the bound. -/
def constructionWork (xs : List (Word w)) (l : Layout) (ha : Admissible w xs.length l) (rho : RandomMemory w) : Nat :=
  9+40*(xs.length+1)+9*Dedup.comparisons
    (Dedup.parameters (dedup_admissible ha) (rho (word w l.randomBase))).hash xs []+
    (4*Hashing.PowerOfTwo.bits (values xs).length+17)+rootWork xs l rho+11+
      remainingWork xs l (rootSeed xs l rho) rho 0

/-- Exact random reads to successful completion. Fallback never adds reads. -/
def constructionReads (xs : List (Word w)) (l : Layout) (rho : RandomMemory w) : Nat :=
  1+rootAttempts xs l rho+remainingReads xs l (rootSeed xs l rho) rho 0

variable {w : Nat} {xs : List (Word w)} {l : Layout} {s : State w 64}

/-- Every admissible repeated-input execution halts successfully, for every
random-memory image. The result has the same retained-local M6 query view. -/
theorem total (ha : Admissible w xs.length l) (rho : RandomMemory w) (hp : s.pc = 0)
    (hin : BuildInput w xs.length l s.regs) (harr : ArrayAt s.mem l.inputBase xs) :
    ∃ k t log, TerminatesIn Total.program rho s k t log ∧ k ≤ constructionWork xs l ha rho ∧
      Built xs l (rootSeed xs l rho) t ∧ (policy w xs.length l).AllowsTrace log ∧
      (log.filterMap Access.randomAddress).Sublist (consecutiveAddresses w l.randomBase (randomSpan w xs)) ∧
      (log.filterMap Access.randomAddress).length = constructionReads xs l rho := by
  obtain ⟨kd,u,ld,htd,hkd,hd,hpold,hrd⟩ := deduplicate xs l ha rho hp hin harr
  obtain ⟨v,hti,hready,hmem⟩ := initialize_root ha hd rho
  obtain ⟨kr,t,lr,htr,hkr,hs,hpolr,hrr⟩ := root_stage ha rho hready
  have hpref := ((lift_steps htd).trans (lift_steps hti)).trans htr
  have hpolpref : (policy w xs.length l).AllowsTrace (ld++lr) :=
    (AccessPolicy.allowsTrace_append _).mpr ⟨hpold,hpolr⟩
  have hrsub : (lr.filterMap Access.randomAddress).Sublist (consecutiveAddresses w (l.randomBase+1) w) := by
    rw [hrr]
    exact consecutiveAddresses_sublist w _ (FiniteProbability.Retry.attempts_le _ _ _)
  have hprefsub : ((ld++lr).filterMap Access.randomAddress).Sublist
      ([word w l.randomBase]++consecutiveAddresses w (l.randomBase+1) w) := by
    rw [List.filterMap_append,hrd]
    exact (List.Sublist.refl _).append hrsub
  have hhead := lift_steps (root_header t rho hs.pc)
  obtain ⟨ko,z,lo,hto,hko,hout,hpolo,hro,hrcount⟩ := outer_loop ha rho (hs.outer ha) (by omega : 0+rootSlots xs = rootSlots xs)
  refine ⟨kd+(4*Hashing.PowerOfTwo.bits (values xs).length+17)+kr+11+ko,z,
    (ld++lr)++headerTrace t++lo,by simpa using (hpref.trans hhead).then_terminates hto,?_,hout,?_,?_,?_⟩
  · unfold constructionWork
    omega
  · exact (AccessPolicy.allowsTrace_append _).mpr ⟨
      (AccessPolicy.allowsTrace_append _).mpr ⟨hpolpref,root_header_policy ha hs.core.globals⟩,hpolo⟩
  · simp only [List.filterMap_append,headerTrace,List.filterMap_cons,Access.randomAddress,
      List.filterMap_nil,List.append_nil]
    rw [random_schedule]
    simpa only [List.filterMap_append] using hprefsub.append hro
  · simp only [List.filterMap_append,headerTrace,List.filterMap_cons,Access.randomAddress,
      List.filterMap_nil,List.append_nil,List.length_append,hrd,hrr,hrcount,
      List.length_cons,List.length_nil,consecutiveAddresses_length,constructionReads]

end PerfectHash.Total
