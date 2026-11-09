import DataStructures.PerfectHash.Source.Query.Program
import DataStructures.PerfectHash.Representation

namespace PerfectHash.Source.Query
open WordRam RamLang RamLang.Compiler RamLang.Logic

set_option maxRecDepth 65536
set_option maxHeartbeats 20000000

/-- Source queries only read the retained descriptor. Stack traffic is added
and bounded separately by the generic compiler theorem. -/
def policy (r : Region) : AccessPolicy w := ⟨r.Contains,fun _ => False,fun _ => False⟩

macro "source_test" : tactic => `(tactic|
  simp [function,program,Binary.eval,Condition.eval,Atom.eval,requireSome,Comparison.test,bind,pure,Except.bind,Except.pure,
    WordRam.word_add,WordRam.word_mul,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,Nat.mul_comm, *])

macro "source_prove" : tactic => `(tactic|
  (simp only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,Nat.mul_comm] at *
   refine ⟨_,_,_,by ram_derive (source_test),?_,?_,?_⟩
   · simp [function,program,Binary.eval,AccessPolicy.AllowsTrace,AccessPolicy.Allows,policy,
       WordRam.word_add,WordRam.word_mul,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm,Nat.mul_comm, *]
   · ram_cost <;> simp [function,program]
   · ram_cost <;> simp [function,program]))

variable {w : Nat} {S : Finset (Word w)} {r : Region} {mem : DataMemory w} {d : Table.Data w}

/-- All paths of the C-like query implement the existing table model. Its proof
uses independent source rules; target PCs and frame stores do not occur here. -/
theorem contract (v : Table.View S r mem d) (q : Word w) (rho : RandomMemory w)
    {free : Nat} (hfree : 7 ≤ free) :
    Contract program rho free function.body
      ([word w r.base,q].map some ++ List.replicate function.locals.length none) mem
      (fun flow mem' trace => flow = .returned (word w (if q ∈ S then 1 else 0)) ∧
        mem' = mem ∧ (policy r).AllowsTrace trace) 221 7 := by
  let b : Fin d.buckets := ⟨d.rootIndex q,v.valid.rootRange q⟩
  have hroot : unsignedShiftRight (d.rootSeed*q) d.rootShift = word w b.val := by
    change _ = word w (unsignedShiftRight (d.rootSeed*q) d.rootShift).toNat
    simp only [word,BitVec.ofNat_toNat,BitVec.setWidth_eq]
  have hseed := v.headerSeed
  have hshift := v.headerShift
  have hcount := v.directoryCount b
  have htable := v.directoryTable b
  have hcseed := v.directorySeed b
  have hcshift := v.directoryShift b
  simp only [Packed.directory] at hcount htable hcseed hcshift
  have hcount0 : word w (d.count b) = word w 0 ↔ d.count b = 0 :=
    word_eq_iff_of_lt (v.count_fit b) (by have := v.four_lt; omega)
  have hcount1 : word w (d.count b) = word w 1 ↔ d.count b = 1 :=
    word_eq_iff_of_lt (v.count_fit b) (by have := v.four_lt; omega)
  have hone : word w 1 ≠ word w 0 := by
    intro he
    have hh := congrArg BitVec.toNat he
    rw [word_toNat_of_lt (by have := v.four_lt; omega : 1 < modulus w),
      word_toNat_of_lt (by have := v.four_lt; omega : 0 < modulus w)] at hh
    omega
  have local0 := v.contains_header (i := 0) (by decide)
  have local1 := v.contains_header (i := 1) (by decide)
  have localDir0 := v.contains_directory b (i := 0) (by decide)
  have localDir1 := v.contains_directory b (i := 1) (by decide)
  have localDir2 := v.contains_directory b (i := 2) (by decide)
  have localDir3 := v.contains_directory b (i := 3) (by decide)
  simp only [Nat.add_zero,Packed.directory] at local0 localDir0 localDir1 localDir2 localDir3
  by_cases hc : d.count b = 0
  · have hnot : q ∉ S := v.valid.empty_bucket b hc rfl
    source_prove
  · have hpos : 0 < d.count b := Nat.pos_of_ne_zero hc
    let i := d.slotIndex b q
    have hi : i < d.slots b := v.valid.slotRange b hpos q
    have hflag := v.occupancy b i hi
    have localFlag := v.contains_table b hi (j := 0) (by decide)
    have localKey := v.contains_table b hi (j := 1) (by decide)
    simp only [Nat.add_zero] at localFlag
    have hmember := v.valid.selected_slot b hpos (x := q) rfl
    change d.contents b i = some q ↔ q ∈ S at hmember
    cases hcontent : d.contents b i with
    | none =>
      have hnot : q ∉ S := by rw [← hmember,hcontent]; simp
      simp only [hcontent,Option.isSome_none,Bool.false_eq_true,↓reduceIte] at hflag
      by_cases hs : d.count b = 1
      · have hi0 : i = 0 := by simp [i,Table.Data.slotIndex,hs]
        simp only [hi0,Nat.mul_zero,Nat.add_zero] at hflag localFlag localKey
        source_prove
      · have hhash : unsignedShiftRight (d.seed b*q) (d.shift b) = word w i := by
          change _ = word w (d.slotIndex b q)
          simp only [Table.Data.slotIndex,hs,↓reduceIte,word,BitVec.ofNat_toNat,BitVec.setWidth_eq]
        source_prove
    | some k =>
      have hstored := v.keys b i hi k hcontent
      simp only [hcontent,Option.isSome_some,↓reduceIte] at hflag
      have hm : q ∈ S ↔ k = q := by simpa only [hcontent,Option.some.injEq] using hmember.symm
      by_cases hs : d.count b = 1
      · have hi0 : i = 0 := by simp [i,Table.Data.slotIndex,hs]
        simp only [hi0,Nat.mul_zero,Nat.add_zero] at hflag hstored localFlag localKey
        by_cases hk : k = q <;> source_prove
      · have hhash : unsignedShiftRight (d.seed b*q) (d.shift b) = word w i := by
          change _ = word w (d.slotIndex b q)
          simp only [Table.Data.slotIndex,hs,↓reduceIte,word,BitVec.ofNat_toNat,BitVec.setWidth_eq]
        by_cases hk : k = q <;> source_prove

/-- The source contract also yields an independent small-step source execution
without any stack-capacity limit or assumption about compiled machine states. -/
theorem source_returns (v : Table.View S r mem d) (q : Word w) (rho : RandomMemory w) :
    ∃ value c trace,
      Returns program rho none (Config.initial program [word w r.base,q] mem) value c trace ∧
      value = word w (if q ∈ S then 1 else 0) ∧ c.mem = mem ∧ (policy r).AllowsTrace trace := by
  have h := (contract v q rho (free := 7) (Nat.le_refl _)).consequence
    (post' := fun flow mem' trace => ∃ value, flow = .returned value ∧
      (value = word w (if q ∈ S then 1 else 0) ∧ mem' = mem ∧ (policy r).AllowsTrace trace))
    (by rintro flow mem' trace ⟨hf,hm,hp⟩; exact ⟨_,hf,rfl,hm,hp⟩)
    (Nat.le_refl _) (Nat.le_refl _)
  exact h.sourceReturns (f := function) (values := [word w r.base,q]) rfl rfl

end PerfectHash.Source.Query
