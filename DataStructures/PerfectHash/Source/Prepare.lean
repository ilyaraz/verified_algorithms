import DataStructures.PerfectHash.Source.Regions

namespace PerfectHash.Source.Prepare
open WordRam RamLang RamLang.Compiler RamLang.Logic
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000

/-- Sampling, rounding and deduplication execute inside an ordinary helper. -/
def function : RamLang.Function := Bounded.source.functions[13]'(by decide)

/-- Pointwise charged work retains the actual full-key comparison count. -/
def work (xs : List (Word w)) (l : Layout) (ha : Admissible w xs.length l) (rho : RandomMemory w) : Nat :=
  300*(xs.length+Hashing.PowerOfTwo.size xs.length+1)+55*Dedup.comparisons
    (Dedup.parameters (PerfectHash.Bounded.dedup_admissible ha) (rho (word w l.randomBase))).hash xs []+
    19*Hashing.PowerOfTwo.bits xs.length+200

/-- The executed preparation returns the seed-independent distinct array, with
one fresh random read and all ordinary effects outside the internal stack. -/
theorem contract {w free : Nat} (p : RamLang.Program) (rho : RandomMemory w) (mem : DataMemory w)
    (xs : List (Word w)) (l : Layout) (ha : Admissible w xs.length l)
    (hround : p.functions[1]? = some Hashing.Source.Rounding.function)
    (hfill : p.functions[2]? = some RamLang.Logic.Fill.function)
    (hsample : p.functions[3]? = some Hashing.Source.Sampling.function)
    (hsearch : p.functions[4]? = some Dedup.Source.Search.function)
    (hdedup : p.functions[5]? = some Dedup.Source.Pass.function)
    (hfree : 36 ≤ free) (hinput : ArrayAt mem l.inputBase xs) :
    Contract p rho free function.body
      ([word w l.inputBase,word w xs.length,word w l.outputBase,word w l.scratchBase,word w l.randomBase,word w w].map some ++
        List.replicate function.locals.length none) mem
      (fun flow mem' log => flow = .returned (word w (PerfectHash.Bounded.values xs).length) ∧
        ArrayAt mem' ((PerfectHash.Bounded.dedupLayout l).compact xs.length).base (PerfectHash.Bounded.values xs) ∧
        (Source.policy w xs.length l).AllowsTrace log ∧
        RamLang.Library.Retry.randomAddresses log = [word w l.randomBase]) (work xs l ha rho) 36 := by
  let haD := PerfectHash.Bounded.dedup_admissible ha
  let parameters := Dedup.parameters haD (rho (word w l.randomBase))
  let shiftCell := word w l.outputBase+word w 1
  let memory := update mem shiftCell (word w (w-Hashing.PowerOfTwo.bits xs.length))
  obtain ⟨flow,mem₁,log₁,round,⟨hflow,hmem,hlog⟩,ht₁,hp₁⟩ :=
    Hashing.Source.Rounding.contract (free := free-6) p rho mem xs.length shiftCell haD.bucket_fit
  subst flow
  subst mem₁
  subst log₁
  let sampled := Hashing.Source.Sampling.evaluation (free := free-7) p rho memory (word w l.randomBase)
  have hsWork : instructions sampled = 32 := rfl
  have hsPeak : extraStack sampled = 0 := rfl
  have hcell : (l.output xs.length).Contains shiftCell := by
    simpa [shiftCell,WordRam.word_add] using Source.header_inside ha (by decide : 1 < 4)
  have harray : ArrayAt memory l.inputBase xs := by
    apply hinput.update_outside ha.ordinary.input
    exact Region.not_contains_of_separated (Region.separated_symm ha.ordinary.input_output) hcell
  have hc := Dedup.Source.Pass.contract (free := free-26) p rho memory (PerfectHash.Bounded.dedupLayout l)
    parameters.hash parameters.seed parameters.shift xs hfill hsearch (by omega) haD
    parameters.capacity parameters.range parameters.realizes rfl harray
  have hc' : Contract p rho (free-26) Dedup.Source.Pass.function.body
      ([word w l.inputBase,word w xs.length,word w l.scratchBase,word w (Hashing.PowerOfTwo.size xs.length),
        Hashing.MultiplyShift.sample (rho (word w l.randomBase)),memory shiftCell].map some ++
        List.replicate Dedup.Source.Pass.function.locals.length none) memory
      (fun flow mem' log => flow = .returned (word w (Dedup.collect xs []).length) ∧
        Dedup.Representation w xs.length (PerfectHash.Bounded.dedupLayout l) (Hashing.PowerOfTwo.size xs.length)
          parameters.hash (Dedup.collect xs []) mem' ∧
        (Dedup.Source.Pass.policy (PerfectHash.Bounded.dedupLayout l) xs.length).AllowsTrace log)
      (300*(xs.length+Hashing.PowerOfTwo.size xs.length+1)+55*Dedup.comparisons parameters.hash xs []) 10 := by
    simpa only [parameters,Dedup.parameters,PerfectHash.Bounded.dedupLayout,memory,update_same] using hc
  obtain ⟨flow,mem',log,dedup,⟨hf,hrep,hpol⟩,ht,hpeak⟩ := hc'
  subst flow
  have hdedupPolicy := Source.dedup_policy hpol
  have hrandomNone : RamLang.Library.Retry.randomAddresses log = [] := by
    apply List.filterMap_eq_nil_iff.mpr
    intro e he
    have hh := hpol e he
    cases e <;> simp_all [Dedup.Source.Pass.policy,AccessPolicy.Allows,Access.randomAddress]
  have hsampleAddress : (l.random w xs.length).Contains (word w l.randomBase) :=
    Region.contains_index ha.random (i := 0) (by simp [Layout.random,randomCapacity])
  have hroundSpace : 6 ≤ free := by omega
  have hsampleSpace : 7 ≤ free := by omega
  have hdedupSpace : 26 ≤ free := by omega
  refine ⟨_,_,_,by ram_derive (search_test),?_,?_,?_⟩
  · refine ⟨?_,hrep.compact,?_,?_⟩
    · simp [PerfectHash.Bounded.values]
    · intro e he
      simp only [Option.toList_none,Option.toList_some,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,false_or] at he
      rcases he with rfl | rfl | rfl | he
      · exact Or.inl hcell
      · exact Or.inr (Or.inl hcell)
      · exact hsampleAddress
      · exact hdedupPolicy e he
    · simp only [RamLang.Library.Retry.randomAddresses_append,List.append_nil]
      change [] ++ ([word w l.randomBase] ++ RamLang.Library.Retry.randomAddresses log) = _
      rw [hrandomNone]
      rfl
  · ram_cost
    unfold work
    change _ ≤ 300*(xs.length+Hashing.PowerOfTwo.size xs.length+1)+55*Dedup.comparisons parameters.hash xs []+
      19*Hashing.PowerOfTwo.bits xs.length+200
    omega
  · ram_cost
    change 6+extraStack round ≤ 36 ∧ 7+extraStack sampled ≤ 36 ∧ 26+extraStack dedup ≤ 36
    omega

end PerfectHash.Source.Prepare
