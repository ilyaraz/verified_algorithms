import DataStructures.PerfectHash.Source.Children.Spec

namespace PerfectHash.Source.Children
open WordRam RamLang RamLang.Compiler RamLang.Logic PerfectHash.Bounded

variable {w : Nat} {xs : List (Word w)} {l : Layout} {a seed : Word w}
  {b : Fin (rootSlots xs)} {mem mem' : DataMemory w}

/-- Each field of an allocated directory entry belongs to reserved output. -/
theorem directory_inside (ha : Admissible w xs.length l) (b : Fin (rootSlots xs)) (hi : i < 4) :
    (l.output xs.length).Contains (word w (Packed.directory l.outputBase b+i)) := by
  have hm := root_slots_bound xs
  have hd := values_length_le xs
  have hb := b.isLt
  have he : Packed.directory l.outputBase b+i = l.outputBase+(4+4*b.val+i) := by
    simp [Packed.directory,Nat.add_assoc]
  rw [he]
  apply Region.contains_index ha.ordinary.output
  change 4+4*b.val+i < 64*(xs.length+1)
  omega

/-- Source allocation fills only shift and table pointer, preserving the full
partial-table invariant before the current child is searched. -/
theorem allocated_partial (ha : Admissible w xs.length l) (h : Partial xs l a b.val mem) :
    Partial xs l a b.val (Source.Allocation.memory mem (Packed.directory l.outputBase b)
      (Packed.table l.outputBase (childCapacity xs a) b) (bucketCount xs a b)) :=
  (h.metadata_write ha (Nat.le_refl _) (by decide : 2 ≤ 2) (by decide : 2 < 4)).metadata_write
    ha (Nat.le_refl _) (by decide : 2 ≤ 3) (by decide : 3 < 4)

/-- Only the current directory is accessed by source allocation. -/
theorem allocation_policy (ha : Admissible w xs.length l) (b : Fin (rootSlots xs)) :
    (Source.policy w xs.length l).AllowsTrace
      (Source.Allocation.trace w (Packed.directory l.outputBase b)
        (Packed.table l.outputBase (childCapacity xs a) b) (bucketCount xs a b)) := by
  intro e he
  simp only [Source.Allocation.trace,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl | rfl | rfl
  · exact Or.inr (Or.inl (directory_inside ha b (by decide : 0 < 4)))
  · exact Or.inl (directory_inside ha b (by decide : 2 < 4))
  · exact Or.inl (directory_inside ha b (by decide : 3 < 4))

/-- Repeated child trials preserve all completed tables, pending heads and the
header because their only ordinary writes lie in the current private table. -/
theorem searched_partial (ha : Admissible w xs.length l) (h : Partial xs l a b.val mem)
    {p : RamLang.Program} {rho : RandomMemory w} {free : Nat} {stmt : Stmt} {locals : Locals w}
    {flow : Flow w} {log : List (Access w)}
    (d : Evaluation p rho free stmt locals mem flow mem' log)
    (hp : (Source.Search.Child.policy l.scratchBase (values xs).length
      (Packed.table l.outputBase (childCapacity xs a) b) (childCapacity xs a b)
      (childRandomBase l w b.val) w).AllowsTrace log) : Partial xs l a b.val mem' :=
  h.child_frame ha (Nat.le_refl _) (fun addr hout => d.frame_of_policy hp hout)

/-- Completing a consumed child replaces only its linked head with the chosen
seed, retaining its initialized table and advancing the partial invariant. -/
theorem completed_partial (ha : Admissible w xs.length l) (h : Partial xs l a b.val mem)
    (hc : childAccepted xs a b seed = true)
    (hs : mem (word w (Packed.directory l.outputBase b+2)) = word w (Source.Allocation.shift w (bucketCount xs a b)))
    (ht : mem (word w (Packed.directory l.outputBase b+3)) = word w (Packed.table l.outputBase (childCapacity xs a) b))
    (hslots : Construction.SlotsAt (childHash w (bucketCount xs a b) seed) (childCapacity xs a b)
      (Packed.table l.outputBase (childCapacity xs a) b) (bucketKeys xs a b).reverse mem) :
    Partial xs l a (b.val+1) (update mem (word w (Packed.directory l.outputBase b+1)) seed) := by
  apply h.complete ha
  refine ⟨hc,update_same _ _ _,?_,?_,?_⟩
  · rw [update_other]
    · simpa only [shift_eq] using hs
    · intro he
      have hh := (directory_address_eq ha (by decide : 2 < 4) (by decide : 1 < 4)).mp he
      omega
  · rw [update_other]
    · exact ht
    · intro he
      have hh := (directory_address_eq ha (by decide : 3 < 4) (by decide : 1 < 4)).mp he
      omega
  · apply slots_frame hslots (childContext ha h.accepted b).table_fit
    apply AgreeOn.update_outside (AgreeOn.refl _ _)
    exact Region.not_contains_of_separated (Packed.directory_table_separated _ _ b b)
      (Region.contains_index (directory_fit ha b) (by decide : 1 < 4))

/-- A stage's random block lies inside the original public random reservation. -/
theorem random_inside (ha : Admissible w xs.length l) (b : Fin (rootSlots xs))
    (h : (Region.mk (childRandomBase l w b.val) w).Contains addr) : (l.random w xs.length).Contains addr := by
  have hb := child_random_block (l := l) (w := w) (xs := xs) b
  change l.randomBase ≤ addr.toNat ∧ addr.toNat < l.randomBase+randomCapacity w xs.length
  simp only [Region.Contains] at h
  have hl : l.randomBase ≤ childRandomBase l w b.val := by unfold childRandomBase; omega
  omega

/-- A child search has the same ordinary footprint as one trial; its additional
random events are confined to that child's fresh block. -/
theorem search_policy (ha : Admissible w xs.length l) (hy : rootAccepted xs a = true)
    (b : Fin (rootSlots xs))
    (h : (Source.Search.Child.policy l.scratchBase (values xs).length
      (Packed.table l.outputBase (childCapacity xs a) b) (childCapacity xs a b)
      (childRandomBase l w b.val) w).AllowsTrace log) : (Source.policy w xs.length l).AllowsTrace log := by
  intro e he
  have hh := h e he
  cases e with
  | randomRead => exact random_inside ha b hh
  | dataRead addr value =>
    apply Source.child_policy ha hy b (log := [.dataRead addr value])
    · intro e he
      simp only [List.mem_singleton] at he
      subst e
      exact hh
    · simp
  | dataWrite addr value =>
    apply Source.child_policy ha hy b (log := [.dataWrite addr value])
    · intro e he
      simp only [List.mem_singleton] at he
      subst e
      exact hh
    · simp

end PerfectHash.Source.Children
