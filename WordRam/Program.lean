import WordRam.Word

namespace WordRam

abbrev Reg (R : Nat) := Fin R
abbrev Registers (w R : Nat) := Reg R → Word w

inductive Operand (R : Nat) where
  | reg (r : Reg R)
  | imm (n : Nat)
  deriving DecidableEq, Repr

def Operand.eval (rs : Registers w R) : Operand R → Word w
  | .reg r => rs r
  | .imm n => word w n

inductive Comparison where
  | eq | ne | lt | le
  deriving DecidableEq, Repr

def Comparison.test (c : Comparison) (x y : Word w) : Bool :=
  match c with
  | .eq => x == y
  | .ne => x != y
  | .lt => x.toNat < y.toNat
  | .le => x.toNat ≤ y.toNat

inductive Instr (R : Nat) where
  | mov (dst : Reg R) (src : Operand R)
  | add (dst : Reg R) (x y : Operand R)
  | sub (dst : Reg R) (x y : Operand R)
  | mul (dst : Reg R) (x y : Operand R)
  | mod (dst : Reg R) (x y : Operand R)
  | shr (dst : Reg R) (x count : Operand R)
  | load (dst : Reg R) (addr : Operand R)
  | store (addr src : Operand R)
  | rload (dst : Reg R) (addr : Operand R)
  | branch (cmp : Comparison) (x y : Operand R) (target : Nat)
  | jump (target : Nat)
  | call (link : Reg R) (target : Nat)
  | jumpReg (target : Operand R)
  | halt
  deriving DecidableEq, Repr

abbrev Program (R : Nat) := Array (Instr R)

/-- Instructions whose relocation needs only a change of PC. -/
def Instr.pcRelocatable : Instr R → Bool
  | .call _ _ | .jumpReg _ => false
  | _ => true

/-- A decidable certificate for the original instruction subset. -/
def Program.PCRelocatable (p : Program R) : Prop := p.all Instr.pcRelocatable = true

instance programPCRelocatableDecidable (p : Program R) : Decidable p.PCRelocatable := inferInstanceAs (Decidable (_ = _))

theorem Program.PCRelocatable.fetch {p : Program R} {i : Instr R} {pc : Nat} (h : p.PCRelocatable) (hi : p[pc]? = some i) :
    i.pcRelocatable = true := by
  obtain ⟨hb, he⟩ := Array.getElem?_eq_some_iff.mp hi
  rw [← he]
  exact Array.all_eq_true.mp h pc hb

end WordRam
