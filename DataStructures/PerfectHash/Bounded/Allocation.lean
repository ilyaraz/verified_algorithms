import DataStructures.PerfectHash.Bounded.OuterInitialization

namespace PerfectHash.Bounded
open WordRam Construction.Registers Registers

set_option maxRecDepth 50000
set_option maxHeartbeats 20000000

/-- An allocated child's stable control state and already-written metadata.
Retrying its private table preserves this state and the completed prefix. -/
structure ChildSetup (xs : List (Word w)) (l : Layout) (a : Word w) (b : Fin (rootSlots xs))
    (s : State w 64) : Prop where
  core : ChildState xs l a b s
  «partial» : Partial xs l a b.val s.mem
  index : s.regs bucketIndex = word w b.val
  directory : s.regs directoryCursor = word w (Packed.directory l.outputBase b)
  endPointer : s.regs tableEnd = word w (tableCursorAt xs l a (b.val+1))
  count : s.regs childCount = word w (bucketCount xs a b)
  storedShift : s.mem (word w (Packed.directory l.outputBase b+2)) =
    word w (Construction.Allocation.childShift w (bucketCount xs a b))
  storedTable : s.mem (word w (Packed.directory l.outputBase b+3)) =
    word w (Packed.table l.outputBase (childCapacity xs a) b)

variable {w : Nat} {xs : List (Word w)} {l : Layout} {a : Word w} {b : Fin (rootSlots xs)} {s : State w 64}

theorem allocation_register_preserved (r : Reg 64) (hr : 32 ≤ r.val) :
    ∀ (pc : Nat) (i : Instr 64), Construction.Allocation.program[pc]? = some i → i.destination ≠ some r := by
  apply register_preserved_of_check
  have hc : ∀ r : Reg 64, 32 ≤ r.val → ∀ pc : Fin Construction.Allocation.program.size,
      Construction.Allocation.program[pc.val].destination ≠ some r := by decide
  exact hc r hr

theorem allocation_policy (ha : Admissible w xs.length l) (b : Fin (rootSlots xs))
    (h : (Construction.Allocation.policy (Packed.directory l.outputBase b)).AllowsTrace log) :
    (policy w xs.length l).AllowsTrace log := by
  have hd := values_length_le xs
  have hm := root_slots_bound xs
  have hb := b.isLt
  intro e he
  have hh := h e he
  cases e with
  | dataRead addr v =>
    change (Region.mk _ 4).Contains addr at hh
    simp only [Region.Contains,Packed.directory] at hh
    change _ ∨ _ ∨ _
    simp only [Layout.input,Layout.output,Layout.scratch,dictionaryCapacity,workspaceCapacity,Region.Contains]
    omega
  | dataWrite addr v =>
    change (Region.mk _ 4).Contains addr at hh
    simp only [Region.Contains,Packed.directory] at hh
    change _ ∨ _
    simp only [Layout.output,Layout.scratch,dictionaryCapacity,workspaceCapacity,Region.Contains]
    omega
  | randomRead addr v => exact False.elim hh

/-- Allocation executes the count load, rounded square, shift computation, and
two metadata stores. Its natural endpoint is the next packed prefix. -/
theorem allocate_child (ha : Admissible w xs.length l) (h : OuterState xs l a b.val s)
    (rho : RandomMemory w) :
    ∃ k t log, Steps program rho k s t log ∧
      k ≤ 4*Hashing.PowerOfTwo.bits (2*bucketCount xs a b*bucketCount xs a b)+22 ∧
      t.pc = location .allocated ∧ ChildSetup xs l a b t ∧
      (policy w xs.length l).AllowsTrace log ∧ log.filterMap Access.randomAddress = [] := by
  let u : State w 64 := {childCall s with pc := 0}
  have hui : u.regs address = word w (Packed.directory l.outputBase b) := by
    simpa [u,childCall,update,address,table,width] using h.directory
  have hut : u.regs table = word w (Packed.table l.outputBase (childCapacity xs a) b) := by
    simpa [u,childCall,update,table,width,tableCursorAt,Packed.table] using h.table
  have huw : u.regs width = word w w := by
    simpa [u,childCall,update] using h.globals.saved.width
  have huc : u.mem (u.regs address) = word w (bucketCount xs a b) := by rw [hui]; exact h.partial.counts b
  have hfit := bucket_fit ha h.partial.accepted b
  have hone : 1 < modulus w := by have := ha.arithmetic.linearSizes; omega
  obtain ⟨k,t,log,ht,hk,hpost,hpol⟩ := Construction.Allocation.total rho (s := u) rfl huc huw hfit.1 hfit.2
    ha.arithmetic.widthValue hone (directory_fit ha b) hui
  have hcall := ht.call allocation_embedded allocation_returns
  have hu : u.relocate (location (.block .allocation 0)) = childCall s := rfl
  rw [hu] at hcall
  have hne : s.regs bucketIndex ≠ s.regs buckets := by
    rw [h.index,h.globals.buckets]
    have hm := root_slots_bound xs
    have hd := values_length_le xs
    have hf := ha.arithmetic.linearSizes
    intro he
    have hb := b.isLt
    have hh := (word_eq_iff_of_lt (by omega : b.val < modulus w) (by omega : rootSlots xs < modulus w)).mp he
    omega
  have hsteps := (child_next s rho h.pc hne).trans hcall
  have hug : Globals xs l u.regs := by
    apply h.globals.frame
    intro r hr
    have hn : r ≠ address ∧ r ≠ table := by
      have hc : ∀ r : Reg 64, globalRegister r = true → r ≠ address ∧ r ≠ table := by decide
      exact hc r hr
    by_cases he : r = width
    · subst r; exact huw.trans h.globals.width.symm
    · simp [u,childCall,update,hn.1,hn.2,he]
  have hregs (r : Reg 64) (hr : 32 ≤ r.val) : t.regs r = s.regs r := by
    rw [ht.register_frame (allocation_register_preserved r hr)]
    have hc : r ≠ width ∧ r ≠ table ∧ r ≠ address := by
      have hh : ∀ r : Reg 64, 32 ≤ r.val → r ≠ width ∧ r ≠ table ∧ r ≠ address := by decide
      exact hh r hr
    simp [u,childCall,update,hc.1,hc.2.1,hc.2.2]
  have hmemory : t.mem =
      update (update s.mem (word w (Packed.directory l.outputBase b+3))
        (word w (Packed.table l.outputBase (childCapacity xs a) b)))
        (word w (Packed.directory l.outputBase b+2))
        (word w (Construction.Allocation.childShift w (bucketCount xs a b))) := by
    rw [hpost.memory,hui,hut,word_add,word_add]
    rfl
  have hpartial : Partial xs l a b.val t.mem := by
    rw [hmemory]
    exact (h.partial.metadata_write ha (by omega) (by decide : 2 ≤ 3) (by decide)).metadata_write ha
      (by omega) (by decide : 2 ≤ 2) (by decide)
  refine ⟨4+k,{t with pc := location .allocated},log,by simpa using hsteps,by omega,rfl,
    ⟨⟨allocation_preserves_globals (t := t) hug ht,hpost.table.trans hut,hpost.slots,hpost.shift,?_,hpartial.chains b⟩,
      hpartial,(hregs bucketIndex (by decide)).trans h.index,(hregs directoryCursor (by decide)).trans h.directory,
      ?_,hpost.count,?_,?_⟩,allocation_policy ha b hpol,?_⟩
  · rw [hpost.head,hui,word_add]
    exact h.partial.heads b (by omega)
  · rw [hpost.endPointer,hut,word_add,cursor_next]
    rfl
  · rw [hmemory,update_same]
  · rw [hmemory,update_other,update_same]
    intro he
    have hh := (directory_address_eq ha (by decide : 3 < 4) (by decide : 2 < 4)).mp he
    omega
  · apply List.filterMap_eq_nil_iff.mpr
    intro e he
    have hh := hpol e he
    cases e <;> simp_all [Access.randomAddress,AccessPolicy.Allows,Construction.Allocation.policy]

end PerfectHash.Bounded
