import Algorithms.Dedup.Representation

namespace Dedup
open WordRam

/-- The four stores executed when a key is absent from its chain. -/
def insertMemory (l : Layout) (N d bucket : Nat) (key next : Word w)
    (mem : DataMemory w) : DataMemory w :=
  update (update (update (update mem
    (word w ((l.nodes N).base+2*d)) key)
    (word w ((l.nodes N).base+2*d+1)) next)
    (word w ((l.compact N).base+d)) key)
    (word w (l.scratch+bucket)) (word w (d+1))

variable {w N d b : Nat} {l : Layout} {key next : Word w} {mem : DataMemory w}

theorem insertMemory_apply (h : Admissible w N l) (hd : d < N) (hb : b < 2*(N+1))
    (a : Addr w) :
    insertMemory l N d b key next mem a =
      if a.toNat = l.scratch+b then word w (d+1)
      else if a.toNat = (l.compact N).base+d then key
      else if a.toNat = (l.nodes N).base+2*d+1 then next
      else if a.toNat = (l.nodes N).base+2*d then key else mem a := by
  have hf := h.workspace
  simp only [Layout.workspace, workspaceCapacity, Region.Fits] at hf
  unfold insertMemory
  rw [update_word _ _ _ (by omega)]
  rw [update_word _ _ _ (by simp only [Layout.compact]; omega)]
  rw [update_word _ _ _ (by simp only [Layout.nodes]; omega)]
  rw [update_word _ _ _ (by simp only [Layout.nodes]; omega)]

theorem insertMemory_frame (h : Admissible w N l) (hd : d < N) (hb : b < 2*(N+1))
    (ha : ¬ (l.workspace N).Contains a) :
    insertMemory l N d b key next mem a = mem a := by
  rw [insertMemory_apply h hd hb]
  simp only [Layout.workspace, workspaceCapacity, Region.Contains] at ha
  simp only [Layout.compact, Layout.nodes]
  split <;> (try split) <;> (try split) <;> (try split) <;> first | rfl | assumption | omega

/-- Concrete stores establish all logical insertion obligations, including the
compact prefix and the old-node frame. All addresses are derived below 2^w. -/
theorem Representation.insertMemory {m : Nat} {hash : Word w → Nat}
    {seen : List (Word w)} (rep : Representation w N l m hash seen mem)
    (h : Admissible w N l) (hm : m ≤ 2*(N+1)) (hk : hash key < m)
    (fresh : key ∉ seen) (space : seen.length < N) :
    Representation w N l m hash (key::seen)
      (insertMemory l N seen.length (hash key) key
        (word w (firstIndex (chain hash seen (hash key)))) mem) := by
  have hf := h.workspace
  simp only [Layout.workspace, workspaceCapacity, Region.Fits] at hf
  have hb : hash key < 2*(N+1) := by omega
  apply rep.insert (by simp only [Region.Fits, Layout.nodes]; omega) fresh space
  · intro b hb'
    rw [insertMemory_apply h space hb]
    rw [word_toNat_of_lt (by omega : l.scratch+b < modulus w)]
    simp only [Layout.nodes, Layout.compact]
    by_cases he : hash key = b
    · simp [he]
    · have hne : l.scratch+b ≠ l.scratch+hash key := by omega
      simp only [hne, ↓reduceIte, he]
      split <;> (try split) <;> (try split) <;> first | rfl | assumption | omega
  · rw [insertMemory_apply h space hb]
    simp only [nodeAddress, Nat.add_sub_cancel]
    rw [word_toNat_of_lt (by simp only [Layout.nodes]; omega :
      (l.nodes N).base+2*seen.length < modulus w)]
    simp only [Layout.nodes, Layout.compact]
    split <;> (try split) <;> (try split) <;> first | rfl | assumption | omega
  · rw [insertMemory_apply h space hb]
    simp only [nodeAddress, Nat.add_sub_cancel]
    rw [word_toNat_of_lt (by simp only [Layout.nodes]; omega :
      (l.nodes N).base+2*seen.length+1 < modulus w)]
    simp only [Layout.nodes, Layout.compact]
    split <;> (try split) <;> first | rfl | assumption | omega
  · intro a ha
    rw [insertMemory_apply h space hb]
    simp only [Region.Contains, Layout.nodes] at ha
    simp only [Layout.nodes, Layout.compact]
    split <;> (try split) <;> (try split) <;> (try split) <;> first | rfl | assumption | omega
  · rw [arrayAt_append]
    constructor
    · intro i
      rw [insertMemory_apply h space hb]
      rw [word_toNat_of_lt (by
        have hi := i.isLt
        simp only [List.length_reverse] at hi
        simp only [Layout.compact]; omega : (l.compact N).base+i.val < modulus w)]
      have hi := i.isLt
      simp only [List.length_reverse] at hi
      have old := rep.compact i
      simp only [Layout.compact, Layout.nodes] at *
      split <;> (try split) <;> (try split) <;> (try split) <;> first | rfl | assumption | omega
    · rw [arrayAt_cons]
      refine ⟨?_, by simp⟩
      simp only [List.length_reverse]
      rw [insertMemory_apply h space hb]
      rw [word_toNat_of_lt (by simp only [Layout.compact]; omega :
        (l.compact N).base+seen.length < modulus w)]
      simp only [Layout.compact, Layout.nodes]
      split <;> first | rfl | assumption | omega

end Dedup
