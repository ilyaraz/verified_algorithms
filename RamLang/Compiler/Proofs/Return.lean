import RamLang.Compiler.Proofs.Save

namespace RamLang.Compiler
open WordRam ABI

def afterEpilogue (s : State w registers) : State w registers :=
  let a := s.regs fp + word w 1
  let savedLink := s.mem a
  let savedFP := s.mem (s.regs fp)
  { pc := savedLink.toNat
    regs := update (update (update (update (update s.regs address a) link savedLink)
      caller savedFP) sp (s.regs fp)) fp savedFP
    mem := s.mem }

def returnTrace (s : State w registers) : List (Access w) :=
  [.dataRead (s.regs fp + word w 1) (s.mem (s.regs fp + word w 1)),
    .dataRead (s.regs fp) (s.mem (s.regs fp))]

variable {w : Nat} {p : WordRam.Program registers} {rho : RandomMemory w}
  {s : State w registers}

/-- All six teardown instructions execute, charging both header reads and the
indirect return. This is valid even for malformed saved links; fit is separate. -/
theorem epilogue_steps (h : CodeAt p s.pc epilogue) :
    WordRam.Steps p rho 6 s (afterEpilogue s) (returnTrace s) := by
  let a := s.regs fp + word w 1
  let savedLink := s.mem a
  let savedFP := s.mem (s.regs fp)
  let t₁ := s.put address a
  let t₂ := t₁.put link savedLink
  let t₃ := t₂.put caller savedFP
  let t₄ := t₃.put sp (s.regs fp)
  let t₅ := t₄.put fp savedFP
  have h₁ : WordRam.Step p rho s t₁ none := by
    unfold WordRam.Step WordRam.step
    rw [h.head]
    rfl
  have h₂ : WordRam.Step p rho t₁ t₂ (some (.dataRead a savedLink)) := by
    unfold WordRam.Step WordRam.step
    rw [show t₁.pc = s.pc+1 from rfl, h.tail.head]
    simp [t₂, t₁, a, savedLink, Operand.eval, State.put]
  have h₃ : WordRam.Step p rho t₂ t₃ (some (.dataRead (s.regs fp) savedFP)) := by
    unfold WordRam.Step WordRam.step
    rw [show t₂.pc = s.pc+1+1 from rfl, h.tail.tail.head]
    simp [t₃, t₂, t₁, savedFP, Operand.eval, State.put, update, Fin.ext_iff, fp, address, link]
  have h₄ : WordRam.Step p rho t₃ t₄ none := by
    unfold WordRam.Step WordRam.step
    rw [show t₃.pc = s.pc+1+1+1 from rfl, h.tail.tail.tail.head]
    simp [t₄, t₃, t₂, t₁, Operand.eval, State.put, update, Fin.ext_iff, fp, address, link, caller]
  have h₅ : WordRam.Step p rho t₄ t₅ none := by
    unfold WordRam.Step WordRam.step
    rw [show t₄.pc = s.pc+1+1+1+1 from rfl, h.tail.tail.tail.tail.head]
    simp [t₅, t₄, t₃, Operand.eval, State.put, update, Fin.ext_iff, caller, sp]
  have h₆ : WordRam.Step p rho t₅ (afterEpilogue s) none := by
    unfold WordRam.Step WordRam.step
    rw [show t₅.pc = s.pc+1+1+1+1+1 from rfl, h.tail.tail.tail.tail.tail.head]
    simp [afterEpilogue, t₅, t₄, t₃, t₂, t₁, a, savedFP, savedLink,
      Operand.eval, State.put, update, Fin.ext_iff, fp, address, link, caller, sp]
  exact .cons h₁ (.cons h₂ (.cons h₃ (.cons h₄ (.cons h₅ (.cons h₆ (.refl _))))))

/-- Return restores the caller's registers while preserving the result and memory. -/
theorem epilogue_restores {base returnPC : Nat} {savedFP : Word w}
    (hfp : s.regs fp = word w base)
    (hl : s.mem (word w (base+1)) = word w returnPC)
    (hf : s.mem (word w base) = savedFP)
    (hfit : returnPC < modulus w) :
    (afterEpilogue s).pc = returnPC ∧
    (afterEpilogue s).regs fp = savedFP ∧
    (afterEpilogue s).regs sp = word w base ∧
    (afterEpilogue s).regs result = s.regs result ∧
    (afterEpilogue s).mem = s.mem := by
  simp only [afterEpilogue, hfp, word_add, hl, hf, word_toNat_of_lt hfit]
  simp [update, Fin.ext_iff, fp, sp, result, address, link, caller]

end RamLang.Compiler
