import DataStructures.PerfectHash.Bounded.Partial

namespace PerfectHash.Bounded
open WordRam

variable {w : Nat} {xs : List (Word w)} {l : Layout} {a : Word w}
  {b c : Fin (rootSlots xs)} {i j : Nat} {mem : DataMemory w} {v : Word w}

theorem directory_fit (ha : Admissible w xs.length l) (b : Fin (rootSlots xs)) :
    (Region.mk (Packed.directory l.outputBase b) 4).Fits w := by
  have hm := root_slots_bound xs
  have hd := values_length_le xs
  have ho := ha.ordinary.output
  have hb := b.isLt
  change l.outputBase+64*(xs.length+1) < modulus w at ho
  simp only [Region.Fits,Packed.directory]
  omega

theorem directory_address_eq (ha : Admissible w xs.length l) (hi : i < 4) (hj : j < 4) :
    word w (Packed.directory l.outputBase b+i) = word w (Packed.directory l.outputBase c+j) ↔ b = c ∧ i = j := by
  rw [word_eq_iff_of_lt (Region.index_lt (i := i) (directory_fit ha b) (show i ≤ 4 by omega))
    (Region.index_lt (i := j) (directory_fit ha c) (show j ≤ 4 by omega))]
  simp only [Packed.directory,Fin.ext_iff]
  omega

theorem header_directory_write (ha : Admissible w xs.length l)
    (hh : ArrayAt mem l.outputBase (headerWords xs a)) (b : Fin (rootSlots xs)) (hi : i < 4) :
    ArrayAt (update mem (word w (Packed.directory l.outputBase b+i)) v) l.outputBase (headerWords xs a) := by
  have hf := ha.ordinary.output
  change l.outputBase+64*(xs.length+1) < modulus w at hf
  apply hh.update_outside (by simp [Region.Fits,headerWords]; omega)
  simp only [Region.Contains,headerWords,List.length_cons,List.length_nil,
    word_toNat_of_lt (Region.index_lt (i := i) (directory_fit ha b) (show i ≤ 4 by omega))]
  simp only [Packed.directory]
  omega

theorem nodes_directory_write (ha : Admissible w xs.length l) (b : Fin (rootSlots xs)) (hi : i < 4) :
    AgreeOn ⟨l.scratchBase,2*(values xs).length⟩ mem (update mem (word w (Packed.directory l.outputBase b+i)) v) := by
  have hs := ha.ordinary.output_scratch
  have hd := values_length_le xs
  have hm := root_slots_bound xs
  have hb := b.isLt
  simp only [Region.Separated,Layout.output,Layout.scratch,dictionaryCapacity,workspaceCapacity] at hs
  apply AgreeOn.update_outside (AgreeOn.refl _ _)
  simp only [Region.Contains]
  rw [word_toNat_of_lt (Region.index_lt (i := i) (directory_fit ha b) (show i ≤ 4 by omega))]
  simp only [Packed.directory]
  omega

theorem CompleteChild.directory_write (h : CompleteChild xs l a c chosen mem)
    (ha : Admissible w xs.length l) (hy : rootAccepted xs a = true)
    (hb : c.val < b.val) (hi : i < 4) :
    CompleteChild xs l a c chosen (update mem (word w (Packed.directory l.outputBase b+i)) v) := by
  apply h.frame ha hy
  · apply AgreeOn.update_outside (AgreeOn.refl _ _)
    exact Region.not_contains_of_separated (Region.separated_symm (Packed.directory_separated _ c b hb))
      (Region.contains_index (directory_fit ha b) hi)
  · apply AgreeOn.update_outside (AgreeOn.refl _ _)
    exact Region.not_contains_of_separated (Packed.directory_table_separated _ _ b c)
      (Region.contains_index (directory_fit ha b) hi)

/-- Allocation may fill the current entry's shift/table fields while retaining
all pending heads and completed siblings. -/
theorem Partial.metadata_write (h : Partial xs l a j mem) (ha : Admissible w xs.length l)
    (hb : j ≤ b.val) (hi : 2 ≤ i) (hi' : i < 4) :
    Partial xs l a j (update mem (word w (Packed.directory l.outputBase b+i)) v) := by
  refine ⟨h.accepted,header_directory_write ha h.header b hi',?_,?_,?_,?_⟩
  · intro c
    rw [update_other]
    · exact h.counts c
    · intro he
      have hh := (directory_address_eq (b := c) (c := b) ha (by decide : 0 < 4) hi').mp (by simpa using he)
      omega
  · intro c hc
    rw [update_other]
    · exact h.heads c hc
    · intro he
      have hh := (directory_address_eq ha (by decide : 1 < 4) hi').mp he
      omega
  · intro c
    exact (h.chains c).frame (bucket_indices c) (childContext ha h.accepted b).node_fit (nodes_directory_write ha b hi')
  · intro c hc
    obtain ⟨chosen,hc'⟩ := h.children c hc
    exact ⟨chosen,hc'.directory_write ha h.accepted (by omega) hi'⟩

/-- Replacing a consumed head by its accepted seed advances the completed prefix
by one. The other fields and the initialized table must already be established. -/
theorem Partial.complete (h : Partial xs l a b.val mem) (ha : Admissible w xs.length l)
    (hc : CompleteChild xs l a b chosen (update mem (word w (Packed.directory l.outputBase b+1)) chosen)) :
    Partial xs l a (b.val+1) (update mem (word w (Packed.directory l.outputBase b+1)) chosen) := by
  refine ⟨h.accepted,header_directory_write ha h.header b (by decide),?_,?_,?_,?_⟩
  · intro c
    rw [update_other]
    · exact h.counts c
    · intro he
      have hh := (directory_address_eq (b := c) (c := b) ha (by decide : 0 < 4) (by decide : 1 < 4)).mp
        (by simpa using he)
      omega
  · intro c hj
    rw [update_other]
    · exact h.heads c (by omega)
    · intro he
      have hh := (directory_address_eq ha (by decide : 1 < 4) (by decide : 1 < 4)).mp he
      have heq := hh.1
      subst c
      omega
  · intro c
    exact (h.chains c).frame (bucket_indices c) (childContext ha h.accepted b).node_fit
      (nodes_directory_write ha b (by decide : 1 < 4))
  · intro c hj
    by_cases he : c = b
    · subst c; exact ⟨chosen,hc⟩
    · have hj' : c.val < b.val := by have hn : c.val ≠ b.val := fun hh => he (Fin.ext hh); omega
      obtain ⟨chosen',hc'⟩ := h.children c hj'
      exact ⟨chosen',hc'.directory_write ha h.accepted hj' (by decide : 1 < 4)⟩

end PerfectHash.Bounded
