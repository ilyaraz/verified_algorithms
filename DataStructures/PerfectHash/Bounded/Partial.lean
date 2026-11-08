import DataStructures.PerfectHash.Bounded.ChildSearch

namespace PerfectHash.Bounded
open WordRam

def headerWords (xs : List (Word w)) (a : Word w) : List (Word w) :=
  [a,word w (w-Hashing.PowerOfTwo.bits (values xs).length),word w (rootSlots xs),word w (values xs).length]

structure CompleteChild (xs : List (Word w)) (l : Layout) (a : Word w) (b : Fin (rootSlots xs))
    (chosen : Word w) (mem : DataMemory w) : Prop where
  accepted : childAccepted xs a b chosen = true
  seed : mem (word w (Packed.directory l.outputBase b+1)) = chosen
  shift : mem (word w (Packed.directory l.outputBase b+2)) =
    word w (Construction.Allocation.childShift w (bucketCount xs a b))
  table : mem (word w (Packed.directory l.outputBase b+3)) =
    word w (Packed.table l.outputBase (childCapacity xs a) b)
  slots : Construction.SlotsAt (childHash w (bucketCount xs a b) chosen) (childCapacity xs a b)
    (Packed.table l.outputBase (childCapacity xs a) b) (bucketKeys xs a b).reverse mem

/-- Memory simulation at the outer loop: counts and nodes are stable, pending
heads still point to root chains, and completed children already satisfy query
placement. No assertion relies on uninitialized metadata of pending children. -/
structure Partial (xs : List (Word w)) (l : Layout) (a : Word w) (j : Nat) (mem : DataMemory w) : Prop where
  accepted : rootAccepted xs a = true
  header : ArrayAt mem l.outputBase (headerWords xs a)
  counts : ∀ b, mem (word w (Packed.directory l.outputBase b)) = word w (bucketCount xs a b)
  heads : ∀ b : Fin (rootSlots xs), j ≤ b.val →
    mem (word w (Packed.directory l.outputBase b+1)) = word w (Dedup.firstIndex (bucketChain xs a b))
  chains : ∀ b, Dedup.ChainAt mem l.scratchBase (bucketChain xs a b)
  children : ∀ b : Fin (rootSlots xs), b.val < j → ∃ chosen, CompleteChild xs l a b chosen mem

variable {w : Nat} {xs : List (Word w)} {l : Layout} {a : Word w} {b : Fin (rootSlots xs)}
  {mem mem' : DataMemory w}

theorem CompleteChild.frame (h : CompleteChild xs l a b chosen mem)
    (ha : Admissible w xs.length l) (hy : rootAccepted xs a = true)
    (hd : AgreeOn ⟨Packed.directory l.outputBase b,4⟩ mem mem')
    (ht : AgreeOn ⟨Packed.table l.outputBase (childCapacity xs a) b,2*childCapacity xs a b⟩ mem mem') :
    CompleteChild xs l a b chosen mem' := by
  have hdf : (Region.mk (Packed.directory l.outputBase b) 4).Fits w := by
    have hf := packed_fit ha hy
    have hb := Packed.directory_bound l.outputBase (childCapacity xs a) b (by decide : 3 < 4)
    change l.outputBase+Packed.words (childCapacity xs a) < modulus w at hf
    change Packed.directory l.outputBase b+4 < modulus w
    omega
  have htf := (childContext ha hy b).table_fit
  refine ⟨h.accepted,?_,?_,?_,?_,?_⟩
  · rw [← hd _ (Region.contains_index hdf (by decide : 1 < 4))]; exact h.seed
  · rw [← hd _ (Region.contains_index hdf (by decide : 2 < 4))]; exact h.shift
  · rw [← hd _ (Region.contains_index hdf (by decide : 3 < 4))]; exact h.table
  · intro i hi
    rw [← ht _ (Region.contains_index htf (by omega : 2*i < 2*childCapacity xs a b))]
    exact h.slots.occupied i hi
  · intro i hi x hx
    rw [Nat.add_assoc,← ht _ (Region.contains_index htf (by omega : 2*i+1 < 2*childCapacity xs a b))]
    simpa [Nat.add_assoc] using h.slots.stored i hi x hx

/-- The root header and all earlier children lie outside a current child's
table interval. Repeated clearing therefore preserves the outer-loop invariant. -/
theorem Partial.child_frame (h : Partial xs l a j mem) (ha : Admissible w xs.length l)
    (hb : j ≤ b.val) (hf : ChildFrame xs l a b mem mem') : Partial xs l a j mem' := by
  let ctx := childContext ha h.accepted b
  have hheaderfit : (Region.mk l.outputBase 4).Fits w := by
    have hh := ha.ordinary.output
    change l.outputBase+64*(xs.length+1) < modulus w at hh
    change l.outputBase+4 < modulus w
    omega
  have hheadsep : (Region.mk l.outputBase 4).Separated ⟨ctx.tableBase,2*childCapacity xs a b⟩ := by
    left
    change l.outputBase+4 ≤ Packed.table l.outputBase (childCapacity xs a) b
    unfold Packed.table Packed.tablesBase
    omega
  have hdir (c : Fin (rootSlots xs)) (i : Nat) (hi : i < 4) :
      mem' (word w (Packed.directory l.outputBase c+i)) = mem (word w (Packed.directory l.outputBase c+i)) := by
    apply hf
    have hc : (Region.mk (Packed.directory l.outputBase c) 4).Fits w := by
      have hp := packed_fit ha h.accepted
      have hh := Packed.directory_bound l.outputBase (childCapacity xs a) c (by decide : 3 < 4)
      change l.outputBase+Packed.words (childCapacity xs a) < modulus w at hp
      change Packed.directory l.outputBase c+4 < modulus w
      omega
    exact Region.not_contains_of_separated (Packed.directory_table_separated _ _ c b)
      (Region.contains_index hc hi)
  refine ⟨h.accepted,?_,?_,?_,?_,?_⟩
  · apply h.header.congr (by simpa [headerWords] using hheaderfit)
    intro addr hh
    symm
    exact hf addr (Region.not_contains_of_separated hheadsep (by simpa [headerWords] using hh))
  · intro c
    rw [show mem' (word w (Packed.directory l.outputBase c)) = mem (word w (Packed.directory l.outputBase c))
      from by simpa using hdir c 0 (by decide)]
    exact h.counts c
  · intro c hc
    rw [hdir c 1 (by decide)]
    exact h.heads c hc
  · intro c
    apply (h.chains c).frame (bucket_indices c) ctx.node_fit
    intro addr hh
    symm
    exact hf addr (Region.not_contains_of_separated ctx.separated hh)
  · intro c hc
    obtain ⟨chosen,hc'⟩ := h.children c hc
    refine ⟨chosen,hc'.frame ha h.accepted ?_ ?_⟩
    · intro addr hh
      symm
      exact hf addr (Region.not_contains_of_separated (Packed.directory_table_separated _ _ c b) hh)
    · intro addr hh
      symm
      exact hf addr (Region.not_contains_of_separated (Packed.tables_separated _ _ c b (by omega)) hh)

end PerfectHash.Bounded
