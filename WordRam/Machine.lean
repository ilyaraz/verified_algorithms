import WordRam.Memory
import WordRam.Program

namespace WordRam

structure State (w R : Nat) where
  pc : Nat
  regs : Registers w R
  mem : DataMemory w

def State.initial (regs : Registers w R) (mem : DataMemory w) : State w R :=
  ⟨0, regs, mem⟩

def State.zero (w R : Nat) : State w R := .initial (fun _ => 0) (zeroMemory w)

def State.put (s : State w R) (dst : Reg R) (v : Word w) : State w R :=
  { s with pc := s.pc + 1, regs := update s.regs dst v }

inductive Access (w : Nat) where
  | dataRead (address : Addr w) (value : Word w)
  | dataWrite (address : Addr w) (value : Word w)
  | randomRead (address : Addr w) (value : Word w)
  deriving DecidableEq, Repr

def Access.writeAddress : Access w → Option (Addr w)
  | .dataWrite a _ => some a
  | _ => none

def Access.dataAddress : Access w → Option (Addr w)
  | .dataRead a _ | .dataWrite a _ => some a
  | _ => none

def Access.randomAddress : Access w → Option (Addr w)
  | .randomRead a _ => some a
  | _ => none

inductive Fault where
  | invalidPC (pc : Nat)
  deriving DecidableEq, Repr

inductive StepResult (w R : Nat) where
  | next (state : State w R) (access : Option (Access w))
  | halt
  | fault (reason : Fault)

def StepResult.accesses : StepResult w R → List (Access w)
  | .next _ a => a.toList
  | _ => []

/-- The authoritative instruction semantics. All operands use the old registers.
The immutable random memory is an external parameter, never part of mutable state. -/
def step (p : Program R) (rho : RandomMemory w) (s : State w R) : StepResult w R :=
  let val := Operand.eval s.regs
  match p[s.pc]? with
  | none => .fault (.invalidPC s.pc)
  | some (.mov d x) => .next (s.put d (val x)) none
  | some (.add d x y) => .next (s.put d (val x + val y)) none
  | some (.sub d x y) => .next (s.put d (val x - val y)) none
  | some (.mul d x y) => .next (s.put d (val x * val y)) none
  | some (.mod d x y) => .next (s.put d (unsignedMod (val x) (val y))) none
  | some (.shr d x count) => .next (s.put d (unsignedShiftRight (val x) (val count))) none
  | some (.load d a) => .next (s.put d (s.mem (val a))) (some (.dataRead (val a) (s.mem (val a))))
  | some (.store a x) =>
      .next { s with pc := s.pc + 1, mem := update s.mem (val a) (val x) }
        (some (.dataWrite (val a) (val x)))
  | some (.rload d a) => .next (s.put d (rho (val a))) (some (.randomRead (val a) (rho (val a))))
  | some (.branch cmp x y target) =>
      .next { s with pc := if cmp.test (val x) (val y) then target else s.pc + 1 } none
  | some (.jump target) => .next { s with pc := target } none
  | some (.call link target) =>
      .next { s with pc := target, regs := update s.regs link (word w (s.pc + 1)) } none
  | some (.jumpReg target) => .next { s with pc := (val target).toNat } none
  | some .halt => .halt

/-- A relation derived from the executable transition, not a second interpreter. -/
def Step (p : Program R) (rho : RandomMemory w) (s t : State w R)
    (access : Option (Access w)) : Prop := step p rho s = .next t access

theorem step_deterministic (h : Step p rho s t a) (h' : Step p rho s u b) :
    t = u ∧ a = b := by
  exact StepResult.next.inj (h.symm.trans h')

end WordRam
