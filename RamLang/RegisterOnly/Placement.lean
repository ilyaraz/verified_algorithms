import RamLang.Compiler.Proofs.Code
import RamLang.Primitive

namespace RamLang.RegisterOnly
open WordRam

/-- The alternate ABI reserves two result/status registers; the remaining
capacity is a checked finite budget for caller and inlined-helper locals. -/
def result (capacity : Nat) : Reg (capacity+2) := ⟨0,Nat.zero_lt_succ (capacity+1)⟩

def status (capacity : Nat) : Reg (capacity+2) := ⟨1,Nat.succ_lt_succ (Nat.zero_lt_succ capacity)⟩

/-- Total register addressing. Successful placement proves the modulus inactive
for every used slot; excess demand is rejected before executable code is returned. -/
def slot (capacity base index : Nat) : Reg (capacity+2) :=
  ⟨(base+index+2) % (capacity+2),Nat.mod_lt _ (Nat.zero_lt_succ (capacity+1))⟩

/-- A caller or helper occupies a contiguous, representable register interval. -/
def Fits (capacity base count : Nat) : Prop := base+count ≤ capacity

/-- Moving an interval base is equivalent to adding that offset to the local index. -/
theorem slot_shift (capacity base offset i : Nat) :
    slot capacity (base+offset) i = slot capacity base (offset+i) := by
  simp [slot,Nat.add_assoc]

/-- Initialized source locals have their values in the assigned registers.
Uninitialized slots remain unconstrained, allowing dirty initial registers. -/
def LocalsAt (regs : Registers w (capacity+2)) (base : Nat) (locals : Locals w) : Prop :=
  ∀ i value, locals[i]? = some (some value) → regs (slot capacity base i) = value

/-- Placement bounds remove modular wrapping from a used register index. -/
theorem slot_val {capacity base count i : Nat} (hf : Fits capacity base count) (hi : i < count) :
    (slot capacity base i).val = base+i+2 := Nat.mod_eq_of_lt (by unfold Fits at hf; omega)

/-- Distinct locals have distinct physical registers under the placement bound. -/
theorem slot_injective {capacity base count i j : Nat} (hf : Fits capacity base count)
    (hi : i < count) (hj : j < count) : slot capacity base i = slot capacity base j ↔ i = j := by
  constructor
  · intro he
    have h := congrArg Fin.val he
    rw [slot_val hf hi,slot_val hf hj] at h
    omega
  · rintro rfl; rfl

/-- Two disjoint allocated intervals cannot alias physical registers. -/
theorem slot_disjoint {capacity first second n m i j : Nat}
    (hfirst : Fits capacity first n) (hsecond : Fits capacity second m)
    (hsep : first+n ≤ second) (hi : i < n) (hj : j < m) :
    slot capacity first i ≠ slot capacity second j := by
  intro he
  have h := congrArg Fin.val he
  rw [slot_val hfirst hi,slot_val hsecond hj] at h
  omega

/-- Allocated local registers never alias the public result register. -/
theorem slot_ne_result {capacity base count i : Nat} (hf : Fits capacity base count) (hi : i < count) :
    slot capacity base i ≠ result capacity := by
  intro he
  have h := congrArg Fin.val he
  rw [slot_val hf hi] at h
  change base+i+2 = 0 at h
  omega

/-- Allocated local registers never alias the public status register. -/
theorem slot_ne_status {capacity base count i : Nat} (hf : Fits capacity base count) (hi : i < count) :
    slot capacity base i ≠ status capacity := by
  intro he
  have h := congrArg Fin.val he
  rw [slot_val hf hi] at h
  change base+i+2 = 1 at h
  omega

/-- A checked local assignment is a register update with no ordinary-memory effect. -/
theorem LocalsAt.write {capacity base dst : Nat} {regs : Registers w (capacity+2)}
    {locals out : Locals w} {value : Word w} (hf : Fits capacity base locals.length)
    (hl : LocalsAt regs base locals) (hw : writeLocal locals dst value = .ok out) :
    LocalsAt (update regs (slot capacity base dst) value) base out := by
  obtain ⟨hd,rfl⟩ := writeLocal_ok hw
  intro i v hi
  have hib : i < locals.length := by
    have := List.getElem?_eq_some_iff.mp hi
    simpa using this.1
  by_cases he : i = dst
  · subst i
    rw [List.getElem?_set_self hd] at hi
    cases hi
    exact update_same _ _ _
  · rw [update_other _ _ _ _ (fun h => he ((slot_injective hf hib hd).mp h))]
    exact hl i v (by simpa [List.getElem?_set,he,Ne.symm he] using hi)

/-- Register changes outside an invocation's slots preserve its local relation. -/
theorem LocalsAt.frame {capacity base : Nat} {regs regs' : Registers w (capacity+2)}
    {locals : Locals w} (hl : LocalsAt regs base locals)
    (agree : ∀ i, i < locals.length → regs' (slot capacity base i) = regs (slot capacity base i)) :
    LocalsAt regs' base locals := by
  intro i v hi
  rw [agree i (List.getElem?_eq_some_iff.mp hi).1]
  exact hl i v hi

/-- Reconstruct caller locals after an inline return overwrites its designated
destination while preserving every other live caller slot. -/
theorem LocalsAt.restore {capacity base dst : Nat} {before after : Registers w (capacity+2)}
    {locals out : Locals w} {value : Word w} (hf : Fits capacity base locals.length)
    (hl : LocalsAt before base locals) (hw : writeLocal locals dst value = .ok out)
    (hvalue : after (slot capacity base dst) = value)
    (hframe : ∀ i, i < locals.length → i ≠ dst → after (slot capacity base i) = before (slot capacity base i)) :
    LocalsAt after base out := by
  apply (hl.write hf hw).frame
  intro i hi
  have hlen := writeLocal_preserves_length hw
  have hib : i < locals.length := by omega
  by_cases he : i = dst
  · subst i
    rw [update_same,hvalue]
  · rw [update_other _ _ _ _ (fun h => he ((slot_injective hf hib (writeLocal_ok hw).1).mp h))]
    exact hframe i hib he

/-- Register operands preserve source atom values directly, with no compiler
loads or stores for accessing invocation-local variables. -/
def atom (capacity base : Nat) : Atom → Operand (capacity+2)
  | .literal n => .imm n
  | .local i => .reg (slot capacity base i)

/-- Reading a placed atom agrees with the independent source evaluator. -/
theorem atom_value {capacity base : Nat} {regs : Registers w (capacity+2)}
    {locals : Locals w} {a : Atom} {v : Word w} (hl : LocalsAt regs base locals)
    (hv : a.eval locals = .ok v) : (atom capacity base a).eval regs = v := by
  cases a with
  | literal n => cases hv; rfl
  | «local» i =>
    cases hh : locals[i]? with
    | none => simp [Atom.eval,hh,requireSome] at hv
    | some value =>
      cases value with
      | none => simp [Atom.eval,hh,requireSome] at hv
      | some value =>
        simp [Atom.eval,hh,requireSome] at hv
        subst v
        exact hl i value hh

end RamLang.RegisterOnly
