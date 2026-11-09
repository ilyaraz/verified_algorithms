import RamLang.Compiler.Proofs.Frames

namespace RamLang.Compiler
open WordRam ABI

/-- Exact target state after one lowered atom, including the address temporary. -/
def afterAtom (dst : Reg registers) (value : Atom) (s : State w registers) : State w registers :=
  match value with
  | .literal n => s.put dst (word w n)
  | .local id =>
    let a := s.regs fp + word w (2+id)
    (s.put address a).put dst (s.mem a)

def atomTrace (value : Atom) (s : State w registers) : List (Access w) :=
  match value with
  | .literal _ => []
  | .local id =>
    let a := s.regs fp + word w (2+id)
    [.dataRead a (s.mem a)]

variable {w : Nat} {p : WordRam.Program registers} {rho : RandomMemory w}
  {s : State w registers} {dst r : Reg registers} {value : Atom}
  {locals : Locals w} {base id : Nat} {v : Word w}

/-- The atom template executes its advertised number of actual target instructions. -/
theorem atom_steps (h : CodeAt p s.pc (atom dst value)) :
    WordRam.Steps p rho (atom dst value).length s (afterAtom dst value s) (atomTrace value s) := by
  cases value with
  | literal n =>
    have hs : WordRam.Step p rho s (s.put dst (word w n)) none := by
      unfold WordRam.Step WordRam.step
      rw [h.head]
      rfl
    exact .cons hs (.refl _)
  | «local» id =>
    let a := s.regs fp + word w (2+id)
    let t := s.put address a
    have hs : WordRam.Step p rho s t none := by
      unfold WordRam.Step WordRam.step
      rw [h.head]
      rfl
    have ht : WordRam.Step p rho t (t.put dst (s.mem a)) (some (.dataRead a (s.mem a))) := by
      unfold WordRam.Step WordRam.step
      rw [show t.pc = s.pc+1 from rfl, h.tail.head]
      simp [t, a, Operand.eval, State.put]
    exact .cons hs (.cons ht (.refl _))

theorem afterAtom_pc : (afterAtom dst value s).pc = s.pc + (atom dst value).length := by
  cases value <;> simp [afterAtom, atom, State.put, Nat.add_assoc]

theorem afterAtom_mem : (afterAtom dst value s).mem = s.mem := by
  cases value <;> rfl

/-- Only the destination and address temporary can change during atom loading. -/
theorem afterAtom_register (hd : r ≠ dst) (ha : r ≠ address) :
    (afterAtom dst value s).regs r = s.regs r := by
  cases value <;> simp [afterAtom, State.put, hd, ha]

/-- Successful source local reads identify an initialized, in-range slot. -/
theorem local_eval (h : Atom.eval locals (.local id) = .ok v) :
    locals[id]? = some (some v) ∧ id < locals.length := by
  cases hi : locals[id]? with
  | none => simp [Atom.eval, hi, requireSome] at h
  | some value =>
    cases value with
    | none => simp [Atom.eval, hi, requireSome] at h
    | some value =>
      simp only [Atom.eval, hi, Option.join_some, requireSome, Except.ok.injEq] at h
      subst v
      exact ⟨rfl, (List.getElem?_eq_some_iff.mp hi).1⟩

/-- Source atom values coincide with their concrete stack/register implementation. -/
theorem atom_value (hf : s.regs fp = word w base) (hm : FrameLocals s.mem base locals)
    (he : value.eval locals = .ok v) : (afterAtom dst value s).regs dst = v := by
  cases value with
  | literal n =>
    simp only [Atom.eval, Except.ok.injEq] at he
    subst v
    simp [afterAtom, State.put]
  | «local» id =>
    have hh := local_eval he
    simp only [afterAtom, State.put, update_same]
    rw [hf, slotAddress_eq]
    exact hm id v hh.1

/-- Atom loads introduce only ordinary reads of frame slots, so their trace
vanishes under application projection. Random events are never removed here. -/
theorem atom_project (stack : Region) (hf : s.regs fp = word w base)
    (hs : ∀ i, i < locals.length → stack.Contains (slotAddress base i : Addr w))
    (he : value.eval locals = .ok v) : projectTrace stack (atomTrace value s) = [] := by
  cases value with
  | literal n => rfl
  | «local» id =>
    have hb := hs id (local_eval he).2
    simp only [atomTrace]
    rw [hf, slotAddress_eq]
    simp [projectTrace, applicationEvent, hb.1, hb.2]

end RamLang.Compiler
