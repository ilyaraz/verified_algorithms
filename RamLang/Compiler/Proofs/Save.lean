import RamLang.Compiler.Proofs.Atoms

namespace RamLang.Compiler
open WordRam ABI

/-- Generic two-instruction frame store, used for locals and saved links. -/
def saveCode (offset : Nat) (src : Reg registers) : Code :=
  [.add address (.reg fp) (.imm offset), .store (.reg address) (.reg src)]

def afterSave (offset : Nat) (src : Reg registers) (s : State w registers) : State w registers :=
  let a := s.regs fp + word w offset
  let t := s.put address a
  { t with pc := t.pc+1, mem := update s.mem a (t.regs src) }

def saveTrace (offset : Nat) (src : Reg registers) (s : State w registers) : List (Access w) :=
  let a := s.regs fp + word w offset
  [.dataWrite a ((s.put address a).regs src)]

variable {w offset : Nat} {p : WordRam.Program registers} {rho : RandomMemory w}
  {s : State w registers} {src r : Reg registers}

theorem save_steps (h : CodeAt p s.pc (saveCode offset src)) :
    WordRam.Steps p rho 2 s (afterSave offset src s) (saveTrace offset src s) := by
  let a := s.regs fp + word w offset
  let t := s.put address a
  have hs : WordRam.Step p rho s t none := by
    unfold WordRam.Step WordRam.step
    rw [h.head]
    rfl
  have ht : WordRam.Step p rho t (afterSave offset src s)
      (some (.dataWrite a (t.regs src))) := by
    unfold WordRam.Step WordRam.step
    rw [show t.pc = s.pc+1 from rfl, h.tail.head]
    simp [afterSave, t, a, Operand.eval, State.put]
  exact .cons hs (.cons ht (.refl _))

theorem afterSave_pc : (afterSave offset src s).pc = s.pc+2 := by
  rfl

theorem afterSave_register (h : r ≠ address) :
    (afterSave offset src s).regs r = s.regs r := by
  simp [afterSave, State.put, h]

/-- The stored value is the pre-template source register when it is not the address temporary. -/
theorem afterSave_mem (h : src ≠ address) :
    (afterSave offset src s).mem = update s.mem (s.regs fp + word w offset) (s.regs src) := by
  simp [afterSave, State.put, h]

theorem spill_steps (h : CodeAt p s.pc (spill dst src)) :
    WordRam.Steps p rho 2 s (afterSave (2+dst) src s) (saveTrace (2+dst) src s) :=
  save_steps h

theorem prologue_steps (h : CodeAt p s.pc prologue) :
    WordRam.Steps p rho 2 s (afterSave 1 link s) (saveTrace 1 link s) :=
  save_steps h

/-- The spill installs the source local update without touching any other slot. -/
theorem spill_locals {locals : Locals w} {base dst : Nat} {v : Word w}
    (hm : FrameLocals s.mem base locals) (hf : FrameFits w base locals.length)
    (hd : dst < locals.length) (hfp : s.regs fp = word w base)
    (hs : s.regs src = v) (ha : src ≠ address) :
    FrameLocals (afterSave (2+dst) src s).mem base (locals.set dst (some v)) := by
  rw [afterSave_mem ha, hfp, hs, slotAddress_eq]
  exact hm.set hf hd v

end RamLang.Compiler
