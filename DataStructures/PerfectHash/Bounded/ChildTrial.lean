import DataStructures.PerfectHash.Bounded.Geometry

namespace PerfectHash.Bounded
open WordRam Construction.Registers Registers

set_option maxRecDepth 50000
set_option maxHeartbeats 20000000

/-- Invariant shared by every candidate for one child. Its linked root chain
and computed allocation remain fixed while the private table is retried. -/
structure ChildState (xs : List (Word w)) (l : Layout) (a : Word w) (b : Fin (rootSlots xs))
    (s : State w 64) : Prop where
  globals : Globals xs l s.regs
  table : s.regs Construction.Registers.table = word w (Packed.table l.outputBase (childCapacity xs a) b)
  slots : s.regs Construction.Registers.slots = word w (childCapacity xs a b)
  shift : s.regs Construction.Registers.shift = word w (Construction.Allocation.childShift w (bucketCount xs a b))
  head : s.regs rootHead = word w (Dedup.firstIndex (bucketChain xs a b))
  chain : Dedup.ChainAt s.mem l.scratchBase (bucketChain xs a b)

def childAccepted (xs : List (Word w)) (a : Word w) (b : Fin (rootSlots xs)) (seed : Word w) : Bool :=
  Construction.childAccepted (childHash w (bucketCount xs a b) seed) [] (bucketKeys xs a b)

variable {w : Nat} {xs : List (Word w)} {l : Layout} {a : Word w} {b : Fin (rootSlots xs)} {s : State w 64}

theorem child_register_preserved (r : Reg 64)
    (hr : r = seed ∨ r = shift ∨ r = table ∨ r = slots ∨ 27 ≤ r.val) :
    ∀ (pc : Nat) (i : Instr 64), Construction.Child.program[pc]? = some i → i.destination ≠ some r := by
  apply register_preserved_of_check
  have hc : ∀ r : Reg 64, (r = seed ∨ r = shift ∨ r = table ∨ r = slots ∨ 27 ≤ r.val) →
      ∀ pc : Fin Construction.Child.program.size, Construction.Child.program[pc.val].destination ≠ some r := by decide
  exact hc r hr

theorem ChildState.input (h : ChildState xs l a b s) (ha : Admissible w xs.length l)
    (hy : rootAccepted xs a = true) :
    Construction.Child.Input (childContext ha hy b) (childHash w (bucketCount xs a b) (s.regs seed))
      (bucketChain xs a b) {s with pc := 0} := by
  refine ⟨rfl,h.globals.nodes,h.table,h.slots,h.head,?_,bucket_hash_range ha hy b (s.regs seed),
    bucket_indices b,h.chain⟩
  intro x
  change unsignedShiftRight (s.regs seed*x) (s.regs Construction.Registers.shift) = _
  rw [h.shift]
  unfold childHash
  apply BitVec.eq_of_toNat_eq
  rw [word_toNat_of_lt (word_bound _)]

theorem child_policy (ha : Admissible w xs.length l) (hy : rootAccepted xs a = true)
    (h : (Construction.Child.policy (childContext ha hy b)).AllowsTrace log) :
    (policy w xs.length l).AllowsTrace log := by
  have hd := values_length_le xs
  have hq := retained_bound hy
  have hb := Packed.prefix_bound (childCapacity xs a) b
  intro e he
  have hh := h e he
  cases e with
  | dataRead addr v =>
    change _ ∨ _ at hh
    simp only [childContext,Region.Contains,Packed.table,Packed.tablesBase] at hh
    change _ ∨ _ ∨ _
    simp only [Layout.input,Layout.output,Layout.scratch,dictionaryCapacity,workspaceCapacity,Region.Contains]
    unfold Packed.words at hq
    rcases hh with hh | hh <;> omega
  | dataWrite addr v =>
    change (Region.mk _ _).Contains addr at hh
    simp only [childContext,Region.Contains,Packed.table,Packed.tablesBase] at hh
    change _ ∨ _
    simp only [Layout.output,Layout.scratch,dictionaryCapacity,workspaceCapacity,Region.Contains]
    unfold Packed.words at hq
    omega
  | randomRead addr v => exact False.elim hh

/-- Every inlined child trial is local to its allocated slot interval, including
rejection. The successful slot view records full keys and initialized flags. -/
theorem child_trial (ha : Admissible w xs.length l) (hy : rootAccepted xs a = true)
    (h : ChildState xs l a b s) (hp : s.pc = location .childTrial) (rho : RandomMemory w) :
    ∃ k t log, Steps program rho k s t log ∧
      k ≤ 10*childCapacity xs a b+17*bucketCount xs a b+7 ∧
      t.pc = location .childResult ∧ ChildState xs l a b t ∧
      t.regs status = word w (childAccepted xs a b (s.regs seed)).toNat ∧
      (childAccepted xs a b (s.regs seed) = true →
        Construction.SlotsAt (childHash w (bucketCount xs a b) (s.regs seed)) (childCapacity xs a b)
          (Packed.table l.outputBase (childCapacity xs a) b) (bucketKeys xs a b).reverse t.mem) ∧
      (∀ r, r = seed ∨ r = shift ∨ r = table ∨ r = slots ∨ 27 ≤ r.val → t.regs r = s.regs r) ∧
      (∀ addr, ¬ (Region.mk (Packed.table l.outputBase (childCapacity xs a) b) (2*childCapacity xs a b)).Contains addr →
        t.mem addr = s.mem addr) ∧
      (policy w xs.length l).AllowsTrace log ∧ log.filterMap Access.randomAddress = [] := by
  let u : State w 64 := {s with pc := 0}
  obtain ⟨k,t,log,ht,hk,hpost,hpol⟩ := Construction.Child.total (s := u) (h.input ha hy) rho
  have hcall := ht.call child_embedded child_returns
  have hu : u.relocate (location (.block .child 0)) = s := by
    have he : location (.block .child 0) = location .childTrial := by decide
    cases s
    simp_all [u,State.relocate]
  rw [hu] at hcall
  have hr (r : Reg 64) (hh : r = seed ∨ r = shift ∨ r = table ∨ r = slots ∨ 27 ≤ r.val) :
      t.regs r = s.regs r := ht.register_frame (child_register_preserved r hh)
  have hframe (addr : Addr w)
      (hh : ¬ (Region.mk (Packed.table l.outputBase (childCapacity xs a) b) (2*childCapacity xs a b)).Contains addr) :
      t.mem addr = s.mem addr := ht.choose_spec.2.1.frame_of_policy hpol hh
  have hchain : Dedup.ChainAt t.mem l.scratchBase (bucketChain xs a b) := by
    apply h.chain.frame (bucket_indices b) (childContext ha hy b).node_fit
    intro addr hh
    symm
    exact hframe addr (Region.not_contains_of_separated (childContext ha hy b).separated hh)
  refine ⟨k,{t with pc := location .childResult},log,hcall,by simpa [bucket_chain_length] using hk,rfl,
    ⟨child_preserves_globals (s := u) (t := t) h.globals ht,?_,?_,?_,?_,hchain⟩,
    hpost.status,?_,hr,hframe,child_policy ha hy hpol,?_⟩
  · exact (hr table (Or.inr (Or.inr (Or.inl rfl)))).trans h.table
  · exact (hr slots (Or.inr (Or.inr (Or.inr (Or.inl rfl))))).trans h.slots
  · exact (hr shift (Or.inr (Or.inl rfl))).trans h.shift
  · exact (hr rootHead (Or.inr (Or.inr (Or.inr (Or.inr (by decide)))))).trans h.head
  · intro hh
    simpa using hpost.slots hh
  · apply List.filterMap_eq_nil_iff.mpr
    intro e he
    have hh := hpol e he
    cases e <;> simp_all [Access.randomAddress,AccessPolicy.Allows,Construction.Child.policy]

end PerfectHash.Bounded
