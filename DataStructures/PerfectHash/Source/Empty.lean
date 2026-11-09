import DataStructures.PerfectHash.Source.Regions
import DataStructures.PerfectHash.Representation

namespace PerfectHash.Source.Empty
open WordRam RamLang RamLang.Compiler RamLang.Logic
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000

/-- The empty constructor has a single ordinary clear call and six metadata stores. -/
def function : RamLang.Function := Bounded.source.functions[14]'(by decide)

/-- An empty dictionary retains a header and one empty directory entry. -/
def words (w base : Nat) : List (Word w) :=
  [word w 1,word w w,word w 1,word w 0,word w 0,word w 1,word w w,word w (base+8)]

/-- Exact empty-table memory, including initialization of dirty occupancy/count words. -/
def memory (mem : DataMemory w) (base : Nat) : DataMemory w :=
  update (update (update (update (update (update (Fill.filled mem base 8 (word w 0))
    (word w base) (word w 1)) (word w (base+1)) (word w w)) (word w (base+2)) (word w 1))
    (word w (base+5)) (word w 1)) (word w (base+6)) (word w w)) (word w (base+7)) (word w (base+8))

/-- All eight retained words have their specified values after initialization. -/
theorem memory_array (hf : base+8 < modulus w) (mem : DataMemory w) :
    ArrayAt (memory mem base) base (words w base) := by
  intro i
  have hi : i.val < 8 := i.isLt
  change memory mem base (word w (base+i.val)) = (words w base)[i.val]
  unfold memory
  rw [update_word _ _ _ (by omega),update_word _ _ _ (by omega),update_word _ _ _ (by omega),
    update_word _ _ _ (by omega),update_word _ _ _ (by omega),update_word _ _ _ (by omega)]
  simp only [Fill.filled,word_toNat_of_lt (by omega : base+i.val < modulus w)]
  have h : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 ∨ i.val = 4 ∨ i.val = 5 ∨ i.val = 6 ∨ i.val = 7 := by omega
  rcases h with h | h | h | h | h | h | h | h <;> simp [h,words] <;> omega

/-- Empty construction needs no random access and at most five additional stack
words. Its concrete instruction allowance includes clearing, calls and return. -/
theorem contract {w free : Nat} (p : RamLang.Program) (rho : RandomMemory w) (mem : DataMemory w)
    (l : Layout) (ha : Admissible w 0 l) (hfill : p.functions[2]? = some Fill.function) (hfree : 5 ≤ free) :
    Contract p rho free function.body
      ([word w l.outputBase,word w w].map some ++ List.replicate function.locals.length none) mem
      (fun flow mem' log => flow = .returned (word w (l.outputBase+8)) ∧
        ArrayAt mem' l.outputBase (words w l.outputBase) ∧ (Source.policy w 0 l).AllowsTrace log ∧
        RamLang.Library.Retry.randomAddresses log = []) 300 5 := by
  have hf : l.outputBase+8 < modulus w := by have h := ha.ordinary.output; change l.outputBase+64 < modulus w at h; omega
  have hc := (RamLang.Library.Fill.contract (free := free-5) rho mem l.outputBase 8 (word w 0) hf).reprogram
    p (by repeat constructor)
  obtain ⟨flow,mem',log,fill,⟨hv,hm,hp⟩,ht,hs⟩ := hc
  subst flow
  subst mem'
  have hinside (i : Nat) (hi : i < 8) : (l.output 0).Contains (word w (l.outputBase+i)) :=
    Region.contains_index ha.ordinary.output (by change i < 64; omega)
  have hp' : (Source.policy w 0 l).AllowsTrace log := by
    intro e he
    have h := hp e he
    cases e with
    | dataRead => exact False.elim h
    | randomRead => exact False.elim h
    | dataWrite a v =>
      apply Or.inl
      change l.outputBase ≤ a.toNat ∧ a.toNat < l.outputBase+64
      change l.outputBase ≤ a.toNat ∧ a.toNat < l.outputBase+8 at h
      omega
  have hr : RamLang.Library.Retry.randomAddresses log = [] := by
    apply List.filterMap_eq_nil_iff.mpr
    intro e he
    have h := hp e he
    cases e <;> simp_all [Fill.policy,AccessPolicy.Allows,Access.randomAddress]
  refine ⟨_,_,_,by ram_derive (search_test),?_,?_,?_⟩
  · refine ⟨by simp only [Binary.eval,WordRam.word_add],?_,?_,?_⟩
    · simpa only [Binary.eval,WordRam.word_add] using memory_array hf mem
    · intro e he
      simp only [Option.toList_none,Option.toList_some,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,false_or] at he
      rcases he with he | rfl | rfl | rfl | rfl | rfl | rfl
      · exact hp' e he
      all_goals apply Or.inl
      all_goals try simp only [Binary.eval,WordRam.word_add]
      all_goals first | exact hinside 0 (by decide) | exact hinside 1 (by decide) | exact hinside 2 (by decide) | exact hinside 5 (by decide) | exact hinside 6 (by decide) | exact hinside 7 (by decide)
    · simpa [RamLang.Library.Retry.randomAddresses_append,RamLang.Library.Retry.randomAddresses,
        Access.randomAddress] using hr
  · ram_cost
    omega
  · ram_cost
    change 5+extraStack fill ≤ 5
    omega

/-- Proof-only descriptor for the stored empty table. -/
def data (w : Nat) : Table.Data w :=
  ⟨1,word w 1,word w w,fun _ => 0,fun _ => word w 1,fun _ => word w w,fun _ => 0,fun _ _ => none⟩

/-- The eight initialized words establish the same retained-local representation
used by every query theorem. -/
theorem representation (hf : base+8 < modulus w) (hw : w < modulus w)
    (h : ArrayAt mem base (words w base)) : Table.View ∅ ⟨base,8⟩ mem (data w) := by
  have hc (i : Nat) (hi : i < 8) : mem (word w (base+i)) = (words w base)[i] := h ⟨i,hi⟩
  have hv : Table.Valid ∅ (data w) := by
    refine ⟨?_,?_,?_,?_,?_⟩
    · intro x
      change (unsignedShiftRight (word w 1*x) (word w w)).toNat < 1
      rw [unsignedShiftRight_large _ _ (by rw [word_toNat_of_lt hw])]
      exact (by decide : 0 < 1)
    · intro b; simp [data,Table.Data.bucket]
    · intro b; rfl
    · intro b hb; exact False.elim (Nat.not_lt_zero _ hb)
    · intro b i hi; exact False.elim (Nat.not_lt_zero _ hi)
  refine ⟨hv,by simp [data,Packed.words],hf,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa [words] using hc 0 (by decide)
  · simpa [words] using hc 1 (by decide)
  · simpa [words] using hc 2 (by decide)
  · simpa [words] using hc 3 (by decide)
  · intro b; have hb : b.val = 0 := Fin.eq_zero b |> congrArg Fin.val
    simpa [data,Packed.directory,hb,words] using hc 4 (by decide)
  · intro b; have hb : b.val = 0 := Fin.eq_zero b |> congrArg Fin.val
    simpa [data,Packed.directory,hb,words] using hc 5 (by decide)
  · intro b; have hb : b.val = 0 := Fin.eq_zero b |> congrArg Fin.val
    simpa [data,Packed.directory,hb,words] using hc 6 (by decide)
  · intro b; have hb : b.val = 0 := Fin.eq_zero b |> congrArg Fin.val
    simpa [data,Packed.directory,Packed.table,Packed.tablesBase,hb,words] using hc 7 (by decide)
  · intro b i hi; exact False.elim (Nat.not_lt_zero _ hi)
  · intro b i hi; exact False.elim (Nat.not_lt_zero _ hi)

end PerfectHash.Source.Empty
