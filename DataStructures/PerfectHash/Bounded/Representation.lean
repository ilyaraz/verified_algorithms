import DataStructures.PerfectHash.Bounded.Partial
import DataStructures.PerfectHash.Query.Correctness

namespace PerfectHash.Bounded
open WordRam

/-- Proof-side description of exactly the parameters and full keys stored by
completed child trials; it is never an input to preprocessing or query. -/
def tableData (xs : List (Word w)) (a : Word w) (seeds : Fin (rootSlots xs) → Word w) : Table.Data w where
  buckets := rootSlots xs
  rootSeed := a
  rootShift := word w (w-Hashing.PowerOfTwo.bits (values xs).length)
  count := bucketCount xs a
  seed := seeds
  shift b := word w (Construction.Allocation.childShift w (bucketCount xs a b))
  slots := childCapacity xs a
  contents b := Construction.slotContents (childHash w (bucketCount xs a b) (seeds b)) (bucketKeys xs a b).reverse

variable {w : Nat} {xs : List (Word w)} {l : Layout} {a : Word w}
  {seeds : Fin (rootSlots xs) → Word w} {mem : DataMemory w}

theorem table_root_index (ha : Admissible w xs.length l) (x : Word w) :
    (tableData xs a seeds).rootIndex x = (rootHash xs a x).val := by
  change (unsignedShiftRight (a*x) (word w (w-Hashing.PowerOfTwo.bits (values xs).length))).toNat = _
  rw [root_evaluator ha]
  apply word_toNat_of_lt
  have hm := root_slots_bound xs
  have hd := values_length_le xs
  have hf := ha.arithmetic.linearSizes
  have hx := (rootHash xs a x).isLt
  omega

theorem table_slot_index (ha : Admissible w xs.length l) (b : Fin (rootSlots xs)) (x : Word w) :
    (tableData xs a seeds).slotIndex b x = childHash w (bucketCount xs a b) (seeds b) x := by
  change (if bucketCount xs a b = 1 then 0 else _) = _
  by_cases hb : bucketCount xs a b = 1
  · rw [if_pos hb,child_hash_direct ha.arithmetic.widthValue (by omega)]
  · rw [if_neg hb]
    rfl

theorem child_positions (h : childAccepted xs a b chosen = true) :
    ((bucketKeys xs a b).reverse.map (childHash w (bucketCount xs a b) chosen)).Nodup := by
  have hh := (Construction.childAccepted_iff (childHash w (bucketCount xs a b) chosen) []
    (bucketKeys xs a b) (by simp)).mp h
  simpa using hh

theorem table_valid (ha : Admissible w xs.length l) (hy : rootAccepted xs a = true)
    (hs : ∀ b, childAccepted xs a b (seeds b) = true) : Table.Valid xs.toFinset (tableData xs a seeds) := by
  refine ⟨?_,?_,fun _ => rfl,?_,?_⟩
  · intro x
    rw [table_root_index ha]
    exact (rootHash xs a x).isLt
  · intro b
    change bucketCount xs a b = _
    rw [← bucket_length,← List.toFinset_card_of_nodup (bucket_nodup xs a b)]
    congr 1
    ext x
    simp [Table.Data.bucket,bucket_membership,table_root_index ha]
  · intro b hb x
    rw [table_slot_index ha]
    exact child_hash_range ha.arithmetic.widthValue (bucket_fit ha hy b).2 hb _ _
  · intro b i hi x
    change Construction.slotContents (childHash w (bucketCount xs a b) (seeds b)) (bucketKeys xs a b).reverse i = some x ↔ _
    rw [Construction.slotContents_some _ _ (child_positions (hs b)),List.mem_reverse,bucket_membership,
      table_root_index ha,table_slot_index ha]
    simp only [List.mem_toFinset,and_assoc]

/-- Finishing every child establishes the existing, retained-local query
representation. The selected seeds below are proof witnesses for stored words. -/
theorem Partial.representation (h : Partial xs l a (rootSlots xs) mem) (ha : Admissible w xs.length l) :
    Table.representation.Holds xs.toFinset (Packed.region l.outputBase (childCapacity xs a)) mem := by
  classical
  let seeds : Fin (rootSlots xs) → Word w := fun b => (h.children b b.isLt).choose
  have hc (b : Fin (rootSlots xs)) : CompleteChild xs l a b (seeds b) mem := (h.children b b.isLt).choose_spec
  refine ⟨tableData xs a seeds,table_valid ha h.accepted (fun b => (hc b).accepted),rfl,packed_fit ha h.accepted,
    ?_,?_,?_,?_,h.counts,fun b => (hc b).seed,fun b => (hc b).shift,fun b => (hc b).table,?_,?_⟩
  · simpa [headerWords] using h.header ⟨0,by simp [headerWords]⟩
  · simpa [headerWords] using h.header ⟨1,by simp [headerWords]⟩
  · simpa [headerWords] using h.header ⟨2,by simp [headerWords]⟩
  · have hh := h.header ⟨3,by simp [headerWords]⟩
    simpa [headerWords,values_length,StaticSet.distinctCount] using hh
  · intro b i hi
    have hh := (hc b).slots.occupied i hi
    convert hh using 1
    change word w (if (Construction.slotContents (childHash w (bucketCount xs a b) (seeds b))
      (bucketKeys xs a b).reverse i).isSome then 1 else 0) = _
    cases (Construction.slotContents (childHash w (bucketCount xs a b) (seeds b)) (bucketKeys xs a b).reverse i).isSome <;> rfl
  · intro b i hi x hx
    exact (hc b).slots.stored i hi x hx

end PerfectHash.Bounded
