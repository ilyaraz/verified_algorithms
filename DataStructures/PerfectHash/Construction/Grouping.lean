import DataStructures.PerfectHash.Construction.Energy
import Algorithms.Dedup.Representation

namespace PerfectHash.Construction
open WordRam Buckets

/-- The trial's directory and linked nodes are linear, disjoint regions. -/
structure GroupSpace (w m N dir nodes : Nat) : Prop where
  directory : (Region.mk dir (4*m)).Fits w
  nodes_fit : (Region.mk nodes (2*N)).Fits w
  separated : (Region.mk dir (4*m)).Separated ⟨nodes,2*N⟩

/-- Bucket counts and linked heads describe the processed prefix. Node indices
are one based, so every key value remains available as ordinary data. -/
structure Grouped (hash : Word w → Fin m) (dir nodes : Nat) (seen : List (Word w))
    (mem : DataMemory w) : Prop where
  counts : ∀ b : Fin m, mem (word w (dir+4*b.val)) = word w (count hash seen b)
  heads : ∀ b : Fin m, mem (word w (dir+4*b.val+1)) =
    word w (Dedup.firstIndex (Dedup.chain (fun x => (hash x).val) seen b.val))
  chains : ∀ b : Fin m, Dedup.ChainAt mem nodes (Dedup.chain (fun x => (hash x).val) seen b.val)

variable {w m N dir nodes : Nat} {hash : Word w → Fin m} {seen : List (Word w)}
  {mem : DataMemory w} {key : Word w}

theorem Grouped.empty (h : ArrayAt mem dir (List.replicate (4*m) (word w 0))) :
    Grouped hash dir nodes [] mem := by
  refine ⟨?_,?_,?_⟩
  · intro b
    simpa using h ⟨4*b.val,by have := b.isLt; simp only [List.length_replicate]; omega⟩
  · intro b
    have hh := h ⟨4*b.val+1,by have := b.isLt; simp only [List.length_replicate]; omega⟩
    simpa [Dedup.firstIndex,Nat.add_assoc] using hh
  · intros; trivial

/-- Exact four-store effect of a successful grouping iteration. -/
def groupMemory (dir nodes d b c : Nat) (key next : Word w) (mem : DataMemory w) : DataMemory w :=
  update (update (update (update mem (word w (nodes+2*d)) key)
    (word w (nodes+2*d+1)) next) (word w (dir+4*b+1)) (word w (d+1)))
    (word w (dir+4*b)) (word w (c+1))

theorem groupMemory_apply (h : GroupSpace w m N dir nodes) (hd : d < N) (hb : b < m)
    (key next : Word w) (mem : DataMemory w) (a : Addr w) :
    groupMemory dir nodes d b c key next mem a =
      if a.toNat = dir+4*b then word w (c+1)
      else if a.toNat = dir+4*b+1 then word w (d+1)
      else if a.toNat = nodes+2*d+1 then next
      else if a.toNat = nodes+2*d then key else mem a := by
  have hf := h.directory
  have hg := h.nodes_fit
  simp only [Region.Fits] at hf hg
  unfold groupMemory
  rw [update_word _ _ _ (by omega),update_word _ _ _ (by omega),
    update_word _ _ _ (by omega),update_word _ _ _ (by omega)]

theorem groupMemory_frame (h : GroupSpace w m N dir nodes) (hd : d < N) (hb : b < m)
    (key next : Word w) (mem : DataMemory w) (a : Addr w)
    (ha : ¬ (Region.mk dir (4*m)).Contains a) (hn : ¬ (Region.mk nodes (2*N)).Contains a) :
    groupMemory dir nodes d b c key next mem a = mem a := by
  rw [groupMemory_apply h hd hb]
  simp only [Region.Contains] at ha hn
  split <;> (try split) <;> (try split) <;> (try split) <;> first | rfl | assumption | omega

/-- The concrete stores preserve every existing chain and update only the selected
bucket. Neither rejected energy nor a zero key can create a spurious node. -/
theorem Grouped.insert (rep : Grouped hash dir nodes seen mem)
    (h : GroupSpace w m N dir nodes) (hd : seen.length < N) :
    Grouped hash dir nodes (key::seen)
      (groupMemory dir nodes seen.length (hash key).val (count hash seen (hash key)) key
        (word w (Dedup.firstIndex (Dedup.chain (fun x => (hash x).val) seen (hash key).val))) mem) := by
  have hf := h.directory
  have hg := h.nodes_fit
  have sep := h.separated
  simp only [Region.Fits] at hf hg
  simp only [Region.Separated] at sep
  have old : AgreeOn ⟨nodes,2*seen.length⟩ mem
      (groupMemory dir nodes seen.length (hash key).val (count hash seen (hash key)) key
        (word w (Dedup.firstIndex (Dedup.chain (fun x => (hash x).val) seen (hash key).val))) mem) := by
    intro a ha
    symm
    rw [groupMemory_apply h hd (hash key).isLt]
    have hb := (hash key).isLt
    simp only [Region.Contains] at ha
    split <;> (try split) <;> (try split) <;> (try split) <;> first | rfl | assumption | omega
  refine ⟨?_,?_,?_⟩
  · intro b
    have hb := b.isLt
    have hk := (hash key).isLt
    rw [groupMemory_apply h hd hk,word_toNat_of_lt (by omega : dir+4*b.val < modulus w),count_cons]
    by_cases he : hash key = b
    · subst b
      simp
    · have hv : (hash key).val ≠ b.val := fun hv => he (Fin.ext hv)
      have ho := rep.counts b
      split <;> (try split) <;> (try split) <;> (try split) <;>
        first | simpa [he] using ho | omega
  · intro b
    have hb := b.isLt
    have hk := (hash key).isLt
    rw [groupMemory_apply h hd hk,word_toNat_of_lt (by omega : dir+4*b.val+1 < modulus w),Dedup.chain_cons]
    by_cases he : (hash key).val = b.val
    · simp only [he,↓reduceIte,Dedup.firstIndex]
      split <;> first | rfl | omega
    · simp only [he,↓reduceIte]
      have ho := rep.heads b
      split <;> (try split) <;> (try split) <;> (try split) <;> first | exact ho | omega
  · intro b
    have ho := (rep.chains b).frame (fun _ hp => Dedup.chain_index hp)
      (by simp only [Region.Fits]; omega : (Region.mk nodes (2*seen.length)).Fits w) old
    rw [Dedup.chain_cons]
    split
    · rename_i he
      refine ⟨?_,?_,ho⟩
      · rw [groupMemory_apply h hd (hash key).isLt]
        simp only [Dedup.nodeAddress,Nat.add_sub_cancel]
        rw [word_toNat_of_lt (by omega : nodes+2*seen.length < modulus w)]
        have hk := (hash key).isLt
        split <;> (try split) <;> (try split) <;> (try split) <;> first | rfl | omega
      · rw [groupMemory_apply h hd (hash key).isLt]
        simp only [Dedup.nodeAddress,Nat.add_sub_cancel]
        rw [word_toNat_of_lt (by omega : nodes+2*seen.length+1 < modulus w)]
        have hk := (hash key).isLt
        split <;> (try split) <;> (try split) <;> first | simpa [he] | omega
    · exact ho

end PerfectHash.Construction
