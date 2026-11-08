import DataStructures.PerfectHash.Bounded.RootInitialization
import Hashing.MultiplyShiftRounding

namespace PerfectHash.Bounded
open WordRam Construction.Registers Registers

set_option maxRecDepth 50000
set_option maxHeartbeats 20000000

/-- A total, full-word evaluator, also usable before any seed is accepted. -/
def rootHash (xs : List (Word w)) (a : Word w) (x : Word w) : Fin (rootSlots xs) :=
  ⟨(Hashing.MultiplyShift.eval a x (Hashing.PowerOfTwo.computeBits (values xs).length)).toNat,
    Hashing.MultiplyShift.eval_range_all _ _ _⟩

theorem root_evaluator (ha : Admissible w xs.length l) (a x : Word w) :
    unsignedShiftRight (a*x) (word w (w-Hashing.PowerOfTwo.bits (values xs).length)) =
      word w (rootHash xs a x).val := by
  change unsignedShiftRight (a*x) (word w (w-Hashing.PowerOfTwo.bits (values xs).length)) =
    word w (Hashing.MultiplyShift.eval a x (Hashing.PowerOfTwo.computeBits (values xs).length)).toNat
  unfold unsignedShiftRight Hashing.MultiplyShift.eval
  rw [Hashing.PowerOfTwo.computeBits_eq,word_toNat_of_lt
    (Nat.lt_of_le_of_lt (Nat.sub_le _ _) ha.arithmetic.widthValue)]
  apply BitVec.eq_of_toNat_eq
  simp only [word_toNat,Nat.mod_mod]

def rootAccepted (xs : List (Word w)) (a : Word w) : Bool :=
  decide (Buckets.energy (rootHash xs a) (values xs) ≤ 6*(values xs).length)

/-- Parameters and compact keys survive every root attempt, successful or not. -/
structure RootState (xs : List (Word w)) (l : Layout) (s : State w 64) : Prop where
  globals : Globals xs l s.regs
  shift : s.regs Construction.Registers.shift = word w (w-Hashing.PowerOfTwo.bits (values xs).length)
  array : ArrayAt s.mem ((dedupLayout l).compact xs.length).base (values xs)

variable {w : Nat} {xs : List (Word w)} {l : Layout} {s : State w 64}

theorem root_policy (ha : Admissible w xs.length l)
    (h : (Construction.Root.policy (rootContext xs l ha)).AllowsTrace log) :
    (policy w xs.length l).AllowsTrace log := by
  have hd := values_length_le xs
  have hm := root_slots_bound xs
  intro e he
  have hh := h e he
  cases e with
  | dataRead a v =>
    change _ ∨ _ ∨ _ at hh
    simp only [rootContext,dedupLayout,Dedup.Layout.compact,Region.Contains] at hh
    change _ ∨ _ ∨ _
    simp only [Layout.input,Layout.output,Layout.scratch,dictionaryCapacity,workspaceCapacity,Region.Contains]
    rcases hh with hi | hi | hi <;> omega
  | dataWrite a v =>
    change _ ∨ _ at hh
    simp only [rootContext,Region.Contains] at hh
    change _ ∨ _
    simp only [Layout.output,Layout.scratch,dictionaryCapacity,workspaceCapacity,Region.Contains]
    rcases hh with hi | hi <;> omega
  | randomRead a v => exact False.elim hh

theorem RootState.entry (h : RootState xs l s) (ha : Admissible w xs.length l) :
    Construction.Root.Input (rootContext xs l ha) (rootHash xs (s.regs seed)) (values xs)
      {rootEntry s with pc := 0} := by
  rcases h with ⟨hg,hsh,ha'⟩
  refine ⟨rfl,?_,?_,?_,?_,?_,?_,rfl,ha'⟩
  · simpa [rootEntry,update] using hg.compact
  · simpa [rootEntry,update,Construction.Registers.input,count] using hg.count
  · simpa [rootEntry,update,Construction.Registers.input,directory] using hg.directory
  · simpa [rootEntry,update,Construction.Registers.input,nodes] using hg.nodes
  · simpa [rootEntry,update,Construction.Registers.input,buckets] using hg.buckets
  · intro x
    simpa [rootEntry,update,Construction.Registers.input,seed,shift,hsh] using root_evaluator ha (s.regs seed) x

theorem root_register_preserved (r : Reg 64) (hr : r = seed ∨ r = shift ∨ 26 ≤ r.val) :
    ∀ (pc : Nat) (i : Instr 64), Construction.Root.program[pc]? = some i → i.destination ≠ some r := by
  apply register_preserved_of_check
  have hc : ∀ r : Reg 64, r = seed ∨ r = shift ∨ 26 ≤ r.val →
      ∀ pc : Fin Construction.Root.program.size, Construction.Root.program[pc.val].destination ≠ some r := by decide
  exact hc r hr

/-- One inlined root trial, including input reset and its return jump. The
charged trace includes clearing and all stores made by rejected attempts. -/
theorem root_trial (ha : Admissible w xs.length l) (h : RootState xs l s)
    (hp : s.pc = location .rootTrial) (rho : RandomMemory w) :
    ∃ k t log, Steps program rho k s t log ∧ k ≤ 20*rootSlots xs+25*(values xs).length+10 ∧
      t.pc = location .rootResult ∧ RootState xs l t ∧
      t.regs status = word w (rootAccepted xs (s.regs seed)).toNat ∧
      (rootAccepted xs (s.regs seed) = true →
        Construction.Grouped (rootHash xs (s.regs seed)) (l.outputBase+4) l.scratchBase (values xs).reverse t.mem) ∧
      (∀ r, r = seed ∨ r = shift ∨ 26 ≤ r.val → t.regs r = s.regs r) ∧
      (policy w xs.length l).AllowsTrace log ∧ log.filterMap Access.randomAddress = [] := by
  let u : State w 64 := {rootEntry s with pc := 0}
  obtain ⟨k,t,log,ht,hk,hpost,hpol⟩ := Construction.Root.total (s := u) (h.entry ha) rho
  have hcall := ht.call root_embedded root_returns
  have hu : u.relocate (location (.block .root 0)) = rootEntry s := rfl
  rw [hu] at hcall
  have hsteps := (root_entry s rho hp).trans hcall
  have hreg (r : Reg 64) (hr : r = seed ∨ r = shift ∨ 26 ≤ r.val) : t.regs r = s.regs r := by
    rw [ht.register_frame (root_register_preserved r hr)]
    have hn : r ≠ Construction.Registers.input := by
      rcases hr with hr | hr | hr
      · subst r; decide
      · subst r; decide
      · intro he; subst r; simp [Construction.Registers.input] at hr
    simp [u,rootEntry,update,hn]
  have hg0 : Globals xs l u.regs := by
    apply h.globals.frame
    intro r hr
    have hn : r ≠ Construction.Registers.input := by
      intro he; subst r; simp [globalRegister,Construction.Registers.input] at hr
    simp [u,rootEntry,update,hn]
  have harr : ArrayAt t.mem ((dedupLayout l).compact xs.length).base (values xs) := by
    apply h.array.congr (rootContext xs l ha).input_fit
    intro a hi
    symm
    apply ht.choose_spec.2.1.frame_of_policy hpol
    change ¬ (_ ∨ _)
    exact not_or.mpr ⟨Region.not_contains_of_separated (rootContext xs l ha).input_directory hi,
      Region.not_contains_of_separated (rootContext xs l ha).input_nodes hi⟩
  refine ⟨1+k,{t with pc := location .rootResult},log,by simpa using hsteps,by omega,rfl,
    ⟨root_preserves_globals (t := t) hg0 ht,(hreg shift (Or.inr (Or.inl rfl))).trans h.shift,harr⟩,
    Construction.Root.status_correct (t := t) hpost,?_,hreg,root_policy ha hpol,?_⟩
  · intro hy
    have he : Construction.groupAccepted (rootHash xs (s.regs seed))
      (6*(values xs).length-Buckets.energy (rootHash xs (s.regs seed)) []) [] (values xs) = true := by
      rw [Construction.groupAccepted_iff]
      simp only [Buckets.energy_nil,Nat.sub_zero,Nat.zero_add,List.append_nil]
      rw [Construction.energy_perm _ (List.reverse_perm _)]
      exact of_decide_eq_true hy
    simpa using hpost.grouped he
  · apply List.filterMap_eq_nil_iff.mpr
    intro e he
    have hh := hpol e he
    cases e <;> simp_all [Access.randomAddress,AccessPolicy.Allows,Construction.Root.policy]

end PerfectHash.Bounded
