import DataStructures.PerfectHash.Bounded.Fuel

namespace PerfectHash.Bounded
open WordRam Construction.Registers Registers

variable {w : Nat} {xs : List (Word w)} {l : Layout} {a : Word w} {s : State w 64}

theorem Built.descriptor (h : Built xs l a s) (ha : Admissible w xs.length l) :
    StaticSet.readDescriptor s.regs = Packed.region l.outputBase (childCapacity xs a) := by
  have hf := packed_fit ha h.accepted
  change l.outputBase+Packed.words (childCapacity xs a) < modulus w at hf
  unfold StaticSet.readDescriptor
  change Region.mk (s.regs Construction.Registers.input).toNat (s.regs count).toNat = _
  rw [h.base,h.extent,word_toNat_of_lt (by omega),word_toNat_of_lt (by omega)]
  rfl

theorem Built.computed_distinct (h : Built xs l a s) (ha : Admissible w xs.length l) :
    (s.regs directory).toNat = StaticSet.distinctCount xs := by
  rw [h.distinct]
  have hd := StaticSet.distinctCount_le_length xs
  have hf := ha.arithmetic.linearSizes
  exact word_toNat_of_lt (by omega)

theorem Built.retained (h : Built xs l a s) (ha : Admissible w xs.length l) :
    (StaticSet.readDescriptor s.regs).size ≤ dictionaryCapacity (StaticSet.distinctCount xs) := by
  rw [h.descriptor ha]
  simpa [Packed.region,dictionaryCapacity,values_length] using retained_bound h.accepted

/-- A successful bounded build supports all subsequent word queries after any
overwrite outside its returned descriptor. Query correctness is imported from
M6, including exact zero/one answers, local reads, and full memory preservation. -/
theorem query_after_build (ha : Admissible w xs.length l) (rho : RandomMemory w) (hp : s.pc = 0)
    (hin : BuildInput w xs.length l s.regs) (harr : ArrayAt s.mem l.inputBase xs)
    (hs : (run program rho (fuel w xs.length) s).state.regs status = word w 1) :
    let result := run program rho (fuel w xs.length) s
    let retained := StaticSet.readDescriptor result.state.regs
    ∀ mem', AgreeOn retained result.state.mem mem' → ∀ (q : Word w) queryRegs,
      StaticSet.QueryInput retained q queryRegs → ∀ queryRho : RandomMemory w,
        StaticSet.QueryOutput xs.toFinset retained q mem' Query.cost
          (run Query.program queryRho Query.cost (.initial queryRegs mem')) := by
  obtain ⟨k,t,log,hr,hk,hout,hpol,hrandom⟩ := run_total ha rho hp hin harr
  rw [hr] at hs ⊢
  dsimp only at hs ⊢
  rcases hout with hz | ⟨a,hbuilt⟩
  · have hone : 1 < modulus w := by have := ha.arithmetic.linearSizes; omega
    have he := hz.symm.trans hs
    have hh := (word_eq_iff_of_lt (by omega : 0 < modulus w) hone).mp he
    omega
  · intro mem' hagree q qrs hq qrho
    have hv : Table.representation.Holds xs.toFinset (StaticSet.readDescriptor t.regs) t.mem := by
      rw [hbuilt.descriptor ha]
      exact hbuilt.representation
    exact (Query.spec program).after_overwrite ha.arithmetic.positiveWidth hv hagree hq qrho

/-- Bounded executions use a prefix of each disjoint random block. Even a failure
run reads no address twice and respects the distinct-count reservation bound. -/
theorem random_reads (ha : Admissible w xs.length l) (rho : RandomMemory w) (hp : s.pc = 0)
    (hin : BuildInput w xs.length l s.regs) (harr : ArrayAt s.mem l.inputBase xs) :
    (run program rho (fuel w xs.length) s).randomAddresses.Nodup ∧
      (run program rho (fuel w xs.length) s).randomReads ≤ randomCapacity w (StaticSet.distinctCount xs) := by
  obtain ⟨k,t,log,hr,hk,hout,hpol,hrandom⟩ := run_total ha rho hp hin harr
  rw [hr]
  change (log.filterMap Access.randomAddress).Nodup ∧ (log.filterMap Access.randomAddress).length ≤ _
  refine ⟨(consecutiveAddresses_nodup (random_span_fit ha)).sublist hrandom,?_⟩
  have hh := hrandom.length_le
  rw [consecutiveAddresses_length] at hh
  exact hh.trans (random_span_le xs)

theorem input_unchanged (ha : Admissible w xs.length l) (rho : RandomMemory w) (hp : s.pc = 0)
    (hin : BuildInput w xs.length l s.regs) (harr : ArrayAt s.mem l.inputBase xs) (n : Nat)
    (had : (l.input xs.length).Contains addr) : (run program rho n s).state.mem addr = s.mem addr :=
  (prefixes ha rho hp hin harr n).2.2 addr
    (Region.not_contains_of_separated ha.ordinary.input_output had)
    (Region.not_contains_of_separated ha.ordinary.input_scratch had)

end PerfectHash.Bounded
