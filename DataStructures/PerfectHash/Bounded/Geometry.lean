import DataStructures.PerfectHash.Bounded.RootTrial
import DataStructures.PerfectHash.Representation

namespace PerfectHash.Bounded
open WordRam

/-- The linked lists retain reverse compact order; this is also the input order
used by the abstract child searches. -/
def rootKeys (xs : List (Word w)) : List (Word w) := (values xs).reverse

def bucketCount (xs : List (Word w)) (a : Word w) (b : Fin (rootSlots xs)) : Nat :=
  Buckets.count (rootHash xs a) (rootKeys xs) b

def bucketChain (xs : List (Word w)) (a : Word w) (b : Fin (rootSlots xs)) : List (Word w × Nat) :=
  Dedup.chain (fun x => (rootHash xs a x).val) (rootKeys xs) b.val

def bucketKeys (xs : List (Word w)) (a : Word w) (b : Fin (rootSlots xs)) : List (Word w) :=
  (bucketChain xs a b).map Prod.fst

def childCapacity (xs : List (Word w)) (a : Word w) (b : Fin (rootSlots xs)) : Nat :=
  Sizes.childSlots (bucketCount xs a b)

def tableCursorAt (xs : List (Word w)) (l : Layout) (a : Word w) (j : Nat) : Nat :=
  Packed.tablesBase l.outputBase (rootSlots xs)+2*Packed.slotPrefix (childCapacity xs a) j

variable {w : Nat} {xs : List (Word w)} {l : Layout} {a : Word w}

theorem bucket_keys (xs : List (Word w)) (a : Word w) (b : Fin (rootSlots xs)) :
    bucketKeys xs a b = Buckets.keys (rootHash xs a) (rootKeys xs) b := by
  unfold bucketKeys bucketChain
  rw [Dedup.chain_keys]
  unfold Buckets.keys
  congr 1
  funext x
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq,Fin.ext_iff]

@[simp] theorem bucket_length (xs : List (Word w)) (a : Word w) (b : Fin (rootSlots xs)) :
    (bucketKeys xs a b).length = bucketCount xs a b := by rw [bucket_keys]; rfl

theorem bucket_chain_length (xs : List (Word w)) (a : Word w) (b : Fin (rootSlots xs)) :
    (bucketChain xs a b).length = bucketCount xs a b := by
  rw [← bucket_length]
  exact (List.length_map _).symm

theorem bucket_indices (b : Fin (rootSlots xs)) (p : Word w × Nat) (hp : p ∈ bucketChain xs a b) :
    0 < p.2 ∧ p.2 ≤ (values xs).length := by
  have hh := Dedup.chain_index hp
  simpa [rootKeys] using hh

theorem bucket_nodup (xs : List (Word w)) (a : Word w) (b : Fin (rootSlots xs)) :
    (bucketKeys xs a b).Nodup := by
  rw [bucket_keys]
  exact Buckets.nodup _ _ _ (by simpa [rootKeys] using values_nodup xs)

theorem bucket_membership (b : Fin (rootSlots xs)) (x : Word w) :
    x ∈ bucketKeys xs a b ↔ x ∈ xs ∧ (rootHash xs a x).val = b.val := by
  rw [bucket_keys,Buckets.mem_keys]
  simp [rootKeys,Fin.ext_iff]

theorem accepted_energy (h : rootAccepted xs a = true) :
    Buckets.energy (rootHash xs a) (rootKeys xs) ≤ 6*(rootKeys xs).length := by
  unfold rootKeys
  rw [Construction.energy_perm _ (List.reverse_perm _),List.length_reverse]
  exact of_decide_eq_true h

theorem capacities_total (h : rootAccepted xs a = true) :
    (∑ b : Fin (rootSlots xs), childCapacity xs a b) ≤ 24*(values xs).length := by
  simpa [childCapacity,bucketCount,rootKeys] using Sizes.total_slots _ _ (accepted_energy h)

theorem retained_bound (h : rootAccepted xs a = true) :
    Packed.words (childCapacity xs a) ≤ 64*((values xs).length+1) := by
  have hm := root_slots_bound xs
  have hq := capacities_total h
  unfold Packed.words
  omega

theorem packed_fit (ha : Admissible w xs.length l) (h : rootAccepted xs a = true) :
    (Packed.region l.outputBase (childCapacity xs a)).Fits w := by
  have hl := retained_bound h
  have hd := values_length_le xs
  have ho := ha.ordinary.output
  change l.outputBase+64*(xs.length+1) < modulus w at ho
  change l.outputBase+Packed.words (childCapacity xs a) < modulus w
  omega

theorem cursor_start (xs : List (Word w)) (l : Layout) (a : Word w) :
    tableCursorAt xs l a 0 = l.outputBase+4+4*rootSlots xs := by
  simp [tableCursorAt,Packed.tablesBase]

theorem cursor_next (xs : List (Word w)) (l : Layout) (a : Word w) (b : Fin (rootSlots xs)) :
    tableCursorAt xs l a (b.val+1) = tableCursorAt xs l a b.val+2*childCapacity xs a b := by
  simp [tableCursorAt,Packed.prefix_next,Nat.mul_add,Nat.add_assoc]

theorem cursor_end (xs : List (Word w)) (l : Layout) (a : Word w) :
    tableCursorAt xs l a (rootSlots xs) = l.outputBase+Packed.words (childCapacity xs a) := by
  simp [tableCursorAt,Packed.prefix_end,Packed.tablesBase,Packed.words,Nat.add_assoc]

theorem cursor_le_end (xs : List (Word w)) (l : Layout) (a : Word w) (hj : j ≤ rootSlots xs) :
    tableCursorAt xs l a j ≤ l.outputBase+Packed.words (childCapacity xs a) := by
  have hh := Packed.prefix_mono (childCapacity xs a) hj
  rw [Packed.prefix_end] at hh
  unfold tableCursorAt Packed.tablesBase Packed.words
  omega

def childContext (ha : Admissible w xs.length l) (h : rootAccepted xs a = true)
    (b : Fin (rootSlots xs)) :
    Construction.Child.Context w (values xs).length (childCapacity xs a b) := by
  have hp := packed_fit ha h
  have hs := ha.ordinary.scratch
  have ho := ha.ordinary.output
  have sep := ha.ordinary.output_scratch
  have hd := values_length_le xs
  have hq := retained_bound h
  have hb := Packed.prefix_bound (childCapacity xs a) b
  simp only [Region.Fits,Packed.region,Packed.words,Layout.scratch,workspaceCapacity,
    Layout.output,dictionaryCapacity] at hp hs ho
  simp only [Region.Separated,Layout.output,Layout.scratch,dictionaryCapacity,workspaceCapacity] at sep
  refine ⟨l.scratchBase,Packed.table l.outputBase (childCapacity xs a) b,?_,?_,?_,?_⟩
  · change l.scratchBase+2*(values xs).length < modulus w
    omega
  · change Packed.table l.outputBase (childCapacity xs a) b+2*childCapacity xs a b < modulus w
    unfold Packed.table Packed.tablesBase
    omega
  · simp only [Region.Separated,Packed.table,Packed.tablesBase]
    unfold Packed.words at hq
    omega
  · omega

/-- Stored child shifts use zero hash bits for direct buckets. -/
def childHash (w count : Nat) (a x : Word w) : Nat :=
  (unsignedShiftRight (a*x) (word w (Construction.Allocation.childShift w count))).toNat

theorem child_hash_direct (hw : w < modulus w) (hb : b ≤ 1) (a x : Word w) :
    childHash w b a x = 0 := by
  unfold childHash Construction.Allocation.childShift
  rw [if_pos hb,unsignedShiftRight_large _ _ (by rw [word_toNat_of_lt hw])]
  rfl

theorem child_hash_range (hw : w < modulus w) (hq : Sizes.childSlots b < modulus w)
    (hb : 0 < b) (a x : Word w) : childHash w b a x < Sizes.childSlots b := by
  by_cases hd : b ≤ 1
  · rw [child_hash_direct hw hd,Sizes.childSlots,if_pos hd]
    exact hb
  · have he : unsignedShiftRight (a*x) (word w (Construction.Allocation.childShift w b)) =
        Hashing.MultiplyShift.eval a x (Hashing.PowerOfTwo.computeBits (2*b*b)) := by
      simp only [Construction.Allocation.childShift,hd,↓reduceIte,unsignedShiftRight,Hashing.MultiplyShift.eval,
        word_toNat_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hw)]
    unfold childHash
    rw [he]
    simpa [Sizes.childSlots,hd] using Hashing.MultiplyShift.eval_range_all a x
      (Hashing.PowerOfTwo.computeBits (2*b*b))

theorem bucket_fit (ha : Admissible w xs.length l) (h : rootAccepted xs a = true)
    (b : Fin (rootSlots xs)) :
    bucketCount xs a b < modulus w ∧ childCapacity xs a b < modulus w := by
  have hd := values_length_le xs
  have hf := ha.arithmetic.linearSizes
  have he := accepted_energy h
  have hh := Construction.Allocation.accepted_fit (rootHash xs a) (rootKeys xs) b he
    (by simp only [rootKeys,List.length_reverse]; omega : 64*((rootKeys xs).length+1) < modulus w)
  exact ⟨hh.1,hh.2.2⟩

theorem bucket_hash_range (ha : Admissible w xs.length l) (h : rootAccepted xs a = true)
    (b : Fin (rootSlots xs)) (seed : Word w) (p : Word w × Nat) (hp : p ∈ bucketChain xs a b) :
    childHash w (bucketCount xs a b) seed p.1 < childCapacity xs a b := by
  apply child_hash_range ha.arithmetic.widthValue (bucket_fit ha h b).2
  rw [← bucket_chain_length]
  exact List.length_pos_of_mem hp

end PerfectHash.Bounded
