import RamLang.Compiler.Proofs.State
import WordRam.Blocks

namespace RamLang.Compiler
open WordRam ABI

/-- Stack reads stay within the live allocation; stack writes preserve the
current frame's two saved control words and all suspended caller frames. -/
def framePolicy (stack : Region) (base top : Nat) : AccessPolicy w where
  read a := ¬ stack.Contains a ∨ (base ≤ a.toNat ∧ a.toNat < top)
  write a := ¬ stack.Contains a ∨ (base+2 ≤ a.toNat ∧ a.toNat < top)
  random _ := True

/-- Source memory effects must exclude the reserved ordinary stack. -/
def Separated (stack : Region) (trace : List (Access w)) : Prop :=
  ∀ event ∈ trace, applicationEvent stack event = true

variable {w base top returnPC dst : Nat} {stack : Region} {locals : Locals w}
  {savedFP value : Word w} {application : DataMemory w} {s : State w registers}
  {src : Reg registers} {a : Atom}

@[simp] theorem project_append (a b : List (Access w)) :
    projectTrace stack (a++b) = projectTrace stack a ++ projectTrace stack b := by
  exact List.filter_append _ _

@[simp] theorem separated_append (a b : List (Access w)) :
    Separated stack (a++b) ↔ Separated stack a ∧ Separated stack b := by
  simp [Separated, List.mem_append, or_imp, forall_and]

theorem separated_read {a : Addr w} {v : Word w}
    (h : Separated stack [.dataRead a v]) : ¬ stack.Contains a := by
  have := h (.dataRead a v) (by simp)
  simp [applicationEvent] at this
  unfold Region.Contains
  omega

theorem separated_write {a : Addr w} {v : Word w}
    (h : Separated stack [.dataWrite a v]) : ¬ stack.Contains a := by
  have := h (.dataWrite a v) (by simp)
  simp [applicationEvent] at this
  unfold Region.Contains
  omega

theorem Separated.project (h : Separated stack trace) : projectTrace stack trace = trace :=
  List.filter_eq_self.mpr h

theorem Separated.policy (h : Separated stack trace) :
    (framePolicy stack base top).AllowsTrace trace := by
  intro e he
  have hh := h e he
  cases e with
  | dataRead a v => exact Or.inl (by simp [applicationEvent] at hh; unfold Region.Contains; omega)
  | dataWrite a v => exact Or.inl (by simp [applicationEvent] at hh; unfold Region.Contains; omega)
  | randomRead a v => trivial

theorem framePolicy_mono (hl : base' ≤ base) (hu : top ≤ top')
    (h : (framePolicy stack base top : AccessPolicy w).AllowsTrace trace) :
    (framePolicy stack base' top' : AccessPolicy w).AllowsTrace trace := by
  intro e he
  have hh := h e he
  cases e with
  | dataRead a v => rcases hh with h | ⟨h₁,h₂⟩; exact Or.inl h; exact Or.inr ⟨by omega, by omega⟩
  | dataWrite a v => rcases hh with h | ⟨h₁,h₂⟩; exact Or.inl h; exact Or.inr ⟨by omega, by omega⟩
  | randomRead a v => trivial

/-- Each atom's internal reads obey the allocated-frame policy. -/
theorem atom_policy (h : FrameState stack base locals savedFP returnPC application s)
    (he : a.eval locals = .ok value) :
    (framePolicy stack base (base+2+locals.length)).AllowsTrace (atomTrace a s) := by
  cases a with
  | literal n => simp [atomTrace, AccessPolicy.AllowsTrace]
  | «local» id =>
    have hb := (local_eval he).2
    simp only [atomTrace, h.framePointer, slotAddress_eq]
    intro e hevent
    simp only [List.mem_singleton] at hevent
    subst e
    apply Or.inr
    simp only [slotAddress, word_toNat_of_lt (h.frameFits.slot_lt hb)]
    omega

/-- A local spill is a stack-only event within the current allocation. -/
theorem spill_project (h : FrameState stack base locals savedFP returnPC application s)
    (hd : dst < locals.length) : projectTrace stack (saveTrace (2+dst) src s) = [] := by
  have hb := h.slotInside hd
  simp only [saveTrace, h.framePointer, slotAddress_eq]
  simp [projectTrace, applicationEvent, hb.1, hb.2]

theorem spill_policy (h : FrameState stack base locals savedFP returnPC application s)
    (hd : dst < locals.length) :
    (framePolicy stack base (base+2+locals.length)).AllowsTrace (saveTrace (2+dst) src s) := by
  simp only [saveTrace, h.framePointer, slotAddress_eq]
  intro e he
  simp only [List.mem_singleton] at he
  subst e
  apply Or.inr
  simp only [slotAddress, word_toNat_of_lt (h.frameFits.slot_lt hd)]
  omega

theorem project_stack_write {a : Addr w} {v : Word w} (h : stack.Contains a) :
    projectTrace stack [.dataWrite a v] = [] := by
  simp [projectTrace,applicationEvent,h.1,h.2]

theorem project_stack_read {a : Addr w} {v : Word w} (h : stack.Contains a) :
    projectTrace stack [.dataRead a v] = [] := by
  simp [projectTrace,applicationEvent,h.1,h.2]

end RamLang.Compiler
