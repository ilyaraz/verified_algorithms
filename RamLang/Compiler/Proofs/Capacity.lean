import RamLang.Compiler.Proofs.Return
import WordRam.Refinement

namespace RamLang.Compiler
open WordRam ABI

/-- Subtract remaining capacity before adding a frame; this subtraction cannot wrap. -/
theorem remaining_toNat (horder : current ≤ bound) (hfit : bound < modulus w) :
    (word w bound - word w current).toNat = bound-current := by
  rw [sub_toNat, word_toNat_of_lt hfit, word_toNat_of_lt (by omega)]
  rw [show bound + modulus w - current = (bound-current) + modulus w by omega,
    Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

def guardCode (frame exhausted : Nat) : Code :=
  [.sub left (.reg limit) (.reg sp), .branch .lt (.reg left) (.imm frame) exhausted]

def afterGuard (frame exhausted : Nat) (s : State w registers) : State w registers :=
  let remaining := s.regs limit - s.regs sp
  let t := s.put left remaining
  { t with pc := if Comparison.test .lt remaining (word w frame) then exhausted else t.pc+1 }

variable {w frame exhausted : Nat} {p : WordRam.Program registers} {rho : RandomMemory w}
  {s : State w registers}

theorem guard_steps (h : CodeAt p s.pc (guardCode frame exhausted)) :
    WordRam.Steps p rho 2 s (afterGuard frame exhausted s) [] := by
  let t := s.put left (s.regs limit - s.regs sp)
  have hs : WordRam.Step p rho s t none := by
    unfold WordRam.Step WordRam.step
    rw [h.head]
    rfl
  have ht : WordRam.Step p rho t (afterGuard frame exhausted s) none := by
    unfold WordRam.Step WordRam.step
    rw [show t.pc = s.pc+1 from rfl, h.tail.head]
    simp [afterGuard, t, Operand.eval, State.put]
  exact .cons hs (.cons ht (.refl _))

/-- The target branch tests the mathematical free capacity, without first adding
an overflowing frame size to the stack pointer. -/
theorem guard_decision {current bound : Nat}
    (hsp : s.regs sp = word w current) (hl : s.regs limit = word w bound)
    (horder : current ≤ bound) (hbound : bound < modulus w) (hframe : frame < modulus w) :
    (afterGuard frame exhausted s).pc =
      if bound-current < frame then exhausted else s.pc+2 := by
  simp only [afterGuard, hsp, hl, Comparison.test, remaining_toNat horder hbound,
    word_toNat_of_lt hframe, State.put, decide_eq_true_eq]

def errorCode : Code := [.mov status (.imm 2), .halt]

/-- Runtime exhaustion is a charged status write followed by an ordinary halt. -/
theorem error_terminates (h : CodeAt p s.pc errorCode) :
    WordRam.TerminatesIn p rho s 2 (s.put status (word w 2)) [] := by
  have hs : WordRam.Step p rho s (s.put status (word w 2)) none := by
    unfold WordRam.Step WordRam.step
    rw [h.head]
    rfl
  have hh : WordRam.step p rho (s.put status (word w 2)) = .halt := by
    unfold WordRam.step
    rw [show (s.put status (word w 2)).pc = s.pc+1 from rfl, h.tail.head]
  exact ⟨1, rfl, .cons hs (.refl _), hh⟩

/-- An unsuccessful allocation executes exactly four instructions and makes no
memory access at all, before any callee-header or argument store can execute. -/
theorem guard_exhausted {current bound : Nat}
    (hcode : CodeAt p s.pc (guardCode frame exhausted)) (herr : CodeAt p exhausted errorCode)
    (hsp : s.regs sp = word w current) (hl : s.regs limit = word w bound)
    (horder : current ≤ bound) (hbound : bound < modulus w) (hframe : frame < modulus w)
    (hshort : bound-current < frame) :
    WordRam.TerminatesIn p rho s 4
      ((afterGuard frame exhausted s).put status (word w 2)) [] := by
  have hpc := guard_decision hsp hl horder hbound hframe (exhausted := exhausted)
  simp only [if_pos hshort] at hpc
  have ht : WordRam.TerminatesIn p rho (afterGuard frame exhausted s) 2
      ((afterGuard frame exhausted s).put status (word w 2)) [] :=
    error_terminates (by rw [hpc]; exact herr)
  exact (guard_steps hcode).then_terminates ht

/-- Every word in an admitted frame lies in the reserved stack region. -/
theorem allocated_slot_inside (stack : Region) (hfit : stack.Fits w)
    (hbase : stack.base ≤ current) (hcurrent : current ≤ stack.base+stack.size)
    (hspace : frame ≤ stack.base+stack.size-current) (hi : i < frame) :
    stack.Contains (word w (current+i)) := by
  have he : current+i < stack.base+stack.size := by omega
  have hw : current+i < modulus w := by unfold Region.Fits at hfit; omega
  unfold Region.Contains
  rw [word_toNat_of_lt hw]
  omega

end RamLang.Compiler
