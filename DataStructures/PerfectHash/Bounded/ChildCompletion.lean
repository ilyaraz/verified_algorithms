import DataStructures.PerfectHash.Bounded.Allocation

namespace PerfectHash.Bounded
open WordRam Construction.Registers Registers

set_option maxRecDepth 50000
set_option maxHeartbeats 20000000

variable {w : Nat} {xs : List (Word w)} {l : Layout} {a : Word w} {b : Fin (rootSlots xs)} {s : State w 64}

theorem ChildSetup.allocated (h : ChildSetup xs l a b s) (pc : Nat) :
    ChildSetup xs l a b (allocatedState s pc) := by
  have hr (r : Reg 64) (h1 : r ≠ trialsLeft) (h2 : r ≠ temp) (h3 : r ≠ randomCursor)
      (h4 : r ≠ stage) (h5 : r ≠ fallbackMode) : (allocatedState s pc).regs r = s.regs r := by
    simp [allocatedState,update,h1,h2,h3,h4,h5]
  have hg : Globals xs l (allocatedState s pc).regs := by
    apply h.core.globals.frame
    intro r hh
    have hc : ∀ r : Reg 64, globalRegister r = true →
        r ≠ trialsLeft ∧ r ≠ temp ∧ r ≠ randomCursor ∧ r ≠ stage ∧ r ≠ fallbackMode := by decide
    obtain ⟨h1,h2,h3,h4,h5⟩ := hc r hh
    exact hr r h1 h2 h3 h4 h5
  refine ⟨⟨hg,?_,?_,?_,?_,h.core.chain⟩,h.partial,?_,?_,?_,?_,h.storedShift,h.storedTable⟩
  all_goals rw [hr _ (by decide) (by decide) (by decide) (by decide) (by decide)]
  · exact h.core.table
  · exact h.core.slots
  · exact h.core.shift
  · exact h.core.head
  · exact h.index
  · exact h.directory
  · exact h.endPointer
  · exact h.count

theorem ChildSetup.direct (h : ChildSetup xs l a b s) : ChildSetup xs l a b (directState s) := by
  have hr (r : Reg 64) (hn : r ≠ seed) : (directState s).regs r = s.regs r := by simp [directState,update,hn]
  have hg : Globals xs l (directState s).regs := by
    apply h.core.globals.frame
    intro r hh
    apply hr
    intro he
    subst r
    simp [globalRegister,seed] at hh
  refine ⟨⟨hg,?_,?_,?_,?_,h.core.chain⟩,h.partial,?_,?_,?_,?_,h.storedShift,h.storedTable⟩
  all_goals rw [hr _ (by decide)]
  · exact h.core.table
  · exact h.core.slots
  · exact h.core.shift
  · exact h.core.head
  · exact h.index
  · exact h.directory
  · exact h.endPointer
  · exact h.count

theorem ChildFound.setup (h : ChildFound xs l a b s.regs s.mem chosen t)
    (ha : Admissible w xs.length l) (hs : ChildSetup xs l a b s) : ChildSetup xs l a b t := by
  refine ⟨h.core,hs.partial.child_frame ha (by omega) h.frame,?_,?_,?_,?_,?_,?_⟩
  · rw [h.registers bucketIndex (by decide)]; exact hs.index
  · rw [h.registers directoryCursor (by decide)]; exact hs.directory
  · rw [h.registers tableEnd (by decide)]; exact hs.endPointer
  · rw [h.registers childCount (by decide)]; exact hs.count
  · rw [h.frame _ (Region.not_contains_of_separated (Packed.directory_table_separated _ _ b b)
      (Region.contains_index (directory_fit ha b) (by decide : 2 < 4)))]
    exact hs.storedShift
  · rw [h.frame _ (Region.not_contains_of_separated (Packed.directory_table_separated _ _ b b)
      (Region.contains_index (directory_fit ha b) (by decide : 3 < 4)))]
    exact hs.storedTable

theorem slots_frame {f : Word w → Nat} {q base : Nat} {seen : List (Word w)} {mem mem' : DataMemory w}
    (h : Construction.SlotsAt f q base seen mem) (hf : (Region.mk base (2*q)).Fits w)
    (hh : AgreeOn ⟨base,2*q⟩ mem mem') : Construction.SlotsAt f q base seen mem' := by
  constructor
  · intro i hi
    rw [← hh _ (Region.contains_index hf (by omega : 2*i < 2*q))]
    exact h.occupied i hi
  · intro i hi x hx
    rw [Nat.add_assoc,← hh _ (Region.contains_index hf (by omega : 2*i+1 < 2*q))]
    simpa [Nat.add_assoc] using h.stored i hi x hx

theorem ChildSetup.completed (h : ChildSetup xs l a b s) (ha : Admissible w xs.length l)
    (hc : childAccepted xs a b (s.regs seed) = true)
    (hs : Construction.SlotsAt (childHash w (bucketCount xs a b) (s.regs seed)) (childCapacity xs a b)
      (Packed.table l.outputBase (childCapacity xs a) b) (bucketKeys xs a b).reverse s.mem) :
    CompleteChild xs l a b (s.regs seed) (childSuccess s).mem := by
  have hm : (childSuccess s).mem = update s.mem (word w (Packed.directory l.outputBase b+1)) (s.regs seed) := by
    change update s.mem (s.regs directoryCursor+word w 1) (s.regs seed) = _
    rw [h.directory,word_add]
  rw [hm]
  refine ⟨hc,update_same _ _ _,?_,?_,?_⟩
  · rw [update_other]
    · exact h.storedShift
    · intro he
      have hh := (directory_address_eq ha (by decide : 2 < 4) (by decide : 1 < 4)).mp he
      omega
  · rw [update_other]
    · exact h.storedTable
    · intro he
      have hh := (directory_address_eq ha (by decide : 3 < 4) (by decide : 1 < 4)).mp he
      omega
  · apply slots_frame hs (childContext ha h.partial.accepted b).table_fit
    apply AgreeOn.update_outside (AgreeOn.refl _ _)
    exact Region.not_contains_of_separated (Packed.directory_table_separated _ _ b b)
      (Region.contains_index (directory_fit ha b) (by decide : 1 < 4))

theorem ChildSetup.outer (h : ChildSetup xs l a b s) (ha : Admissible w xs.length l)
    (hc : CompleteChild xs l a b (s.regs seed) (childSuccess s).mem) :
    OuterState xs l a (b.val+1) (childSuccess s) := by
  have hg : Globals xs l (childSuccess s).regs := by
    apply h.core.globals.frame
    intro r hr
    have hh : ∀ r : Reg 64, globalRegister r = true →
        r ≠ temp ∧ r ≠ bucketIndex ∧ r ≠ directoryCursor ∧ r ≠ tableCursor := by decide
    obtain ⟨ht,hi,hd,htb⟩ := hh r hr
    simp [childSuccess,update,ht,hi,hd,htb]
  have hm : (childSuccess s).mem = update s.mem (word w (Packed.directory l.outputBase b+1)) (s.regs seed) := by
    change update s.mem (s.regs directoryCursor+word w 1) (s.regs seed) = _
    rw [h.directory,word_add]
  refine ⟨rfl,hg,?_,?_,?_,by have := b.isLt; omega,?_⟩
  · change s.regs bucketIndex+word w 1 = _
    rw [h.index,word_add]
  · have hd : s.regs (41 : Reg 64) = word w (Packed.directory l.outputBase b) := h.directory
    simp only [childSuccess,update,directoryCursor,bucketIndex,tableCursor,temp,
      Fin.isValue,Fin.reduceFinMk,↓reduceIte,hd,word_add]
    congr 1
  · change update (update (update (update s.regs temp (s.regs directoryCursor+word w 1)) tableCursor (s.regs tableEnd))
      directoryCursor (s.regs directoryCursor+word w 4)) bucketIndex (s.regs bucketIndex+word w 1) tableCursor = _
    simp only [update,tableCursor,directoryCursor,bucketIndex,temp,Fin.isValue,Fin.reduceFinMk,↓reduceIte]
    exact h.endPointer
  · rw [hm] at hc ⊢
    exact h.partial.complete ha hc

end PerfectHash.Bounded
