import DataStructures.PerfectHash.Total.Fuel
import WordRam.Footprint

namespace PerfectHash.Total
open WordRam Bounded

variable {w : Nat} {xs : List (Word w)} {l : Layout} {s : State w 64}

theorem access_of_policy (result : RunResult w 64)
    (h : (policy w N l).AllowsTrace result.trace) : BuildAccess w N l result := by
  have hd : ∀ a ∈ result.dataFootprint,
      (l.input N).Contains a ∨ (l.output N).Contains a ∨ (l.scratch N).Contains a := by
    intro a ha
    have hh := eraseDups_subset _ ha
    obtain ⟨e,he,hea⟩ := List.mem_filterMap.mp hh
    have hp := h e he
    cases e <;> simp_all [Access.dataAddress,AccessPolicy.Allows,policy]
  refine ⟨hd,?_,?_,?_⟩
  · intro a ha
    have hh := eraseDups_subset _ ha
    obtain ⟨e,he,hea⟩ := List.mem_filterMap.mp hh
    have hp := h e he
    cases e <;> simp_all [Access.writeAddress,AccessPolicy.Allows,policy]
  · intro a ha
    obtain ⟨e,he,hea⟩ := List.mem_filterMap.mp ha
    have hp := h e he
    cases e <;> simp_all [Access.randomAddress,AccessPolicy.Allows,policy]
  · have hh := footprint_three result (l.input N) (l.output N) (l.scratch N) hd
    change result.dataFootprint.length+64 ≤ N+dictionaryCapacity N+workspaceCapacity N+64
    exact Nat.add_le_add_right hh _

/-- The complete frozen output contract, including all-image time, exact
computed distinct count, retained locality, and separate random resources. -/
theorem output (ha : Admissible w xs.length l) (rho : RandomMemory w) (hp : s.pc = 0)
    (hin : BuildInput w xs.length l s.regs) (harr : ArrayAt s.mem l.inputBase xs) :
    BuildOutput Table.representation bounds xs l s.mem
      (run Total.program rho (constructionFuel bounds w xs.length) s) := by
  obtain ⟨k,t,log,hr,hk,hbuilt,hpol,hrandom,hreads⟩ := run_total ha rho hp hin harr
  have hdesc := hbuilt.descriptor ha
  have hfresh : (log.filterMap Access.randomAddress).Nodup :=
    (consecutiveAddresses_nodup (random_span_fit ha)).sublist hrandom
  have hmax : (log.filterMap Access.randomAddress).length ≤ randomCapacity w (StaticSet.distinctCount xs) := by
    have hh := hrandom.length_le
    rw [consecutiveAddresses_length] at hh
    exact hh.trans (random_span_le xs)
  have hframe := (prefixes ha rho hp hin harr (constructionFuel bounds w xs.length)).2.2
  rw [hr] at hframe ⊢
  refine ⟨rfl,hk.trans (work_le_worst ha rho),?_,hbuilt.retained ha,hbuilt.computed_distinct ha,?_,?_,hframe,hmax,hfresh,?_⟩
  · rw [hdesc]; rfl
  · rw [hdesc]; exact hbuilt.representation
  · intro a hinput
    exact hframe a (Region.not_contains_of_separated ha.ordinary.input_output hinput)
      (Region.not_contains_of_separated ha.ordinary.input_scratch hinput)
  · have he := RunResult.exposed_le_reads (RunResult.mk t k log .halted)
    exact he.trans (Nat.mul_le_mul_left w hmax)

/-- The all-prefix access policy includes the actual distinct-address footprint
and therefore the frozen peak ordinary-memory bound, including registers. -/
theorem prefix_access (ha : Admissible w xs.length l) (rho : RandomMemory w) (hp : s.pc = 0)
    (hin : BuildInput w xs.length l s.regs) (harr : ArrayAt s.mem l.inputBase xs) (n : Nat) :
    BuildAccess w xs.length l (run Total.program rho n s) :=
  access_of_policy _ (prefixes ha rho hp hin harr n).1

/-- Every completed table answers all word queries after arbitrary overwrites
outside its actual retained descriptor. No successful-randomness premise remains. -/
theorem query_after_build (ha : Admissible w xs.length l) (rho : RandomMemory w) (hp : s.pc = 0)
    (hin : BuildInput w xs.length l s.regs) (harr : ArrayAt s.mem l.inputBase xs) :
    let result := run Total.program rho (constructionFuel bounds w xs.length) s
    let retained := StaticSet.readDescriptor result.state.regs
    ∀ mem', AgreeOn retained result.state.mem mem' → ∀ (q : Word w) queryRegs,
      StaticSet.QueryInput retained q queryRegs → ∀ queryRho : RandomMemory w,
        StaticSet.QueryOutput xs.toFinset retained q mem' Query.cost
          (run Query.program queryRho Query.cost (.initial queryRegs mem')) := by
  dsimp only
  intro mem' hagree q qrs hq qrho
  exact (Query.spec Total.program).after_overwrite ha.arithmetic.positiveWidth
    (output ha rho hp hin harr).represents hagree hq qrho

end PerfectHash.Total
