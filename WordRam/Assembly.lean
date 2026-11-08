import WordRam.Blocks

/-! Symbolic control-flow operands and relocation into larger programs. Labels
are explicit finite data; no proof or noncomputable choice supplies code. -/
namespace WordRam

/-- Relocate just the absolute control-flow operands. -/
def Instr.relocate (base : Nat) : Instr R → Instr R
  | .branch c x y target => .branch c x y (base + target)
  | .jump target => .jump (base + target)
  | .call link target => .call link (base + target)
  | i => i

@[simp] theorem Instr.relocate_zero (i : Instr R) : i.relocate 0 = i := by
  cases i <;> simp [relocate]

theorem Instr.relocate_add (i : Instr R) :
    (i.relocate a).relocate b = i.relocate (b+a) := by
  cases i <;> simp [relocate, Nat.add_assoc]

namespace Assembly

inductive Instruction (R : Nat) (Label : Type) where
  | emit (i : Instr R)
  | branch (c : Comparison) (x y : Operand R) (target : Label)
  | jump (target : Label)
  | call (link : Reg R) (target : Label)
  deriving Repr

def Instruction.resolve (labels : Label → Nat) : Instruction R Label → Instr R
  | .emit i => i
  | .branch c x y l => .branch c x y (labels l)
  | .jump l => .jump (labels l)
  | .call link l => .call link (labels l)

/-- Labels refer to instruction offsets, and emitted instructions are ordinary
RAM instructions. Relocation also handles numeric targets in emitted code. -/
def assemble (base : Nat) (labels : Label → Nat) (code : Array (Instruction R Label)) :
    Program R := ⟨code.toList.map (fun i => (i.resolve labels).relocate base)⟩

@[simp] theorem assemble_size (base : Nat) (labels : Label → Nat)
    (code : Array (Instruction R Label)) : (assemble base labels code).size = code.size := by
  simp [assemble]

theorem assemble_fetch (base : Nat) (labels : Label → Nat)
    (code : Array (Instruction R Label)) (h : j < code.size) :
    (assemble base labels code)[j]? = some ((code[j].resolve labels).relocate base) := by
  simp [assemble, h]

/-- Zero-cost label markers. The first pass computes offsets; the second emits
instructions. Duplicate labels resolve to their first occurrence. Validity below
requires unique definitions and rejects missing targets before code is used. -/
inductive Item (R : Nat) (Label : Type) where
  | label (name : Label)
  | instruction (i : Instruction R Label)
  deriving Repr

def instructions : List (Item R Label) → List (Instruction R Label)
  | [] => []
  | .label _ :: xs => instructions xs
  | .instruction i :: xs => i :: instructions xs

def labelOffset [DecidableEq Label] (l : Label) : List (Item R Label) → Option Nat
  | [] => none
  | .label k :: xs => if k = l then some 0 else labelOffset l xs
  | .instruction _ :: xs => (labelOffset l xs).map Nat.succ

def labelsDefined : List (Item R Label) → List Label
  | [] => []
  | .label l :: xs => l :: labelsDefined xs
  | .instruction _ :: xs => labelsDefined xs

def Instruction.target : Instruction R Label → Option Label
  | .emit _ => none
  | .branch _ _ _ l | .jump l | .call _ l => some l

def Valid [DecidableEq Label] (source : List (Item R Label)) : Prop :=
  (labelsDefined source).Nodup ∧
    ∀ i ∈ instructions source, ∀ l, i.target = some l → (labelOffset l source).isSome

/-- Unresolved references return none. Duplicate labels are also rejected. -/
def compile [DecidableEq Label] (base : Nat) (source : List (Item R Label)) : Option (Program R) :=
  if (labelsDefined source).eraseDups.length = (labelsDefined source).length ∧
      (instructions source).all (fun i => i.target.all (fun l => (labelOffset l source).isSome)) then
    some (assemble base (fun l => (labelOffset l source).getD 0) (instructions source).toArray)
  else none

end Assembly

def State.relocate (s : State w R) (base : Nat) : State w R :=
  { s with pc := base + s.pc }

/-- A block's fetched instructions occur at the new offset. Surrounding code may
be arbitrary; continuation addresses can lie outside this block. -/
def Embedded (p q : Program R) (base : Nat) : Prop :=
  ∀ pc i, p[pc]? = some i → q[base + pc]? = some (i.relocate base)

/-- Appending a relocated block between arbitrary neighboring arrays satisfies
exactly the fetch relation used by the execution relocation theorem. -/
theorem Embedded.append (leading p trailing : Program R) :
    Embedded p (leading ++ p.map (Instr.relocate leading.size) ++ trailing) leading.size := by
  intro pc i hi
  obtain ⟨hp, he⟩ := Array.getElem?_eq_some_iff.mp hi
  rw [Array.getElem?_append_left (by simp; omega)]
  rw [Array.getElem?_append_right (by omega)]
  simp [hp, he]

variable {w R : Nat} {p q : Program R} {rho : RandomMemory w}
  {s t : State w R} {base : Nat}

theorem Step.relocate (h : Step p rho s t event) (he : Embedded p q base)
    (hc : p.PCRelocatable := by decide) :
    Step q rho (s.relocate base) (t.relocate base) event := by
  unfold Step step at h ⊢
  cases hi : p[s.pc]? with
  | none => simp [hi] at h
  | some i =>
    rw [show (s.relocate base).pc = base + s.pc from rfl, he _ _ hi]
    have hsafe := hc.fetch hi
    cases i <;> simp only [Instr.pcRelocatable, Bool.false_eq_true] at hsafe
    all_goals try contradiction
    all_goals simp only [hi, StepResult.next.injEq] at h
    all_goals try { cases h }
    all_goals rcases h with ⟨rfl, rfl⟩
    all_goals simp [Instr.relocate, State.relocate, State.put, Nat.add_assoc]
    split <;> rfl

theorem Steps.relocate (h : Steps p rho k s t log) (he : Embedded p q base)
    (hc : p.PCRelocatable := by decide) :
    Steps q rho k (s.relocate base) (t.relocate base) log := by
  induction h with
  | refl => exact .refl _
  | cons hs ht ih => exact .cons (hs.relocate he hc) ih

theorem halt_relocate (h : step p rho s = .halt) (he : Embedded p q base) :
    step q rho (s.relocate base) = .halt := by
  unfold step at h ⊢
  cases hi : p[s.pc]? with
  | none => simp [hi] at h
  | some i =>
    rw [show (s.relocate base).pc = base + s.pc from rfl, he _ _ hi]
    cases i <;> simp_all [Instr.relocate]

theorem TerminatesIn.relocate (h : TerminatesIn p rho s k t log) (he : Embedded p q base)
    (hc : p.PCRelocatable := by decide) :
    TerminatesIn q rho (s.relocate base) k (t.relocate base) log := by
  obtain ⟨n, hk, hs, ht⟩ := h
  exact ⟨n, hk, hs.relocate he hc, halt_relocate ht he⟩

end WordRam
