import RamLang.Compiler.Proofs.Capacity

namespace RamLang.Compiler
open WordRam ABI

/-- Application memory and physical memory agree away from the reserved stack. -/
def ApplicationMemory (stack : Region) (application physical : DataMemory w) : Prop :=
  ∀ a, ¬ stack.Contains a → physical a = application a

/-- A stable function-body boundary. Dirty uninitialized local slots remain
unconstrained; saved control words are represented in charged ordinary RAM. -/
structure FrameState (stack : Region) (base : Nat) (locals : Locals w)
    (savedFP : Word w) (returnPC : Nat) (application : DataMemory w)
    (s : State w registers) : Prop where
  stackFits : stack.Fits w
  baseLower : stack.base ≤ base
  frameUpper : base+2+locals.length ≤ stack.base+stack.size
  framePointer : s.regs fp = word w base
  stackPointer : s.regs sp = word w (base+2+locals.length)
  stackLimit : s.regs limit = word w (stack.base+stack.size)
  localValues : FrameLocals s.mem base locals
  savedFrame : s.mem (word w base) = savedFP
  savedLink : s.mem (word w (base+1)) = word w returnPC
  applicationMemory : ApplicationMemory stack application s.mem

variable {w base returnPC dst : Nat} {stack : Region} {locals : Locals w}
  {savedFP value : Word w} {application : DataMemory w} {s : State w registers}
  {target src : Reg registers} {atomValue : Atom}

theorem FrameState.frameFits (h : FrameState stack base locals savedFP returnPC application s) :
    FrameFits w base locals.length := by
  have := h.stackFits
  unfold Region.Fits at this
  unfold FrameFits
  have := h.frameUpper
  omega

theorem FrameState.slotInside (h : FrameState stack base locals savedFP returnPC application s)
    (hi : i < locals.length) : stack.Contains (slotAddress base i : Addr w) := by
  unfold slotAddress Region.Contains
  rw [word_toNat_of_lt (h.frameFits.slot_lt hi)]
  have := h.baseLower
  have := h.frameUpper
  omega

theorem FrameState.headerInside (h : FrameState stack base locals savedFP returnPC application s)
    (hi : i < 2) : stack.Contains (word w (base+i)) := by
  have hb : base+i < modulus w := by
    have := h.frameFits
    unfold FrameFits at this
    omega
  unfold Region.Contains
  rw [word_toNat_of_lt hb]
  have := h.baseLower
  have := h.frameUpper
  omega

/-- Atom loading modifies only designated temporary registers. -/
theorem FrameState.afterAtom (h : FrameState stack base locals savedFP returnPC application s)
    (hfp : fp ≠ target) (hsp : sp ≠ target) (hl : limit ≠ target) :
    FrameState stack base locals savedFP returnPC application (afterAtom target atomValue s) := by
  refine ⟨h.stackFits, h.baseLower, h.frameUpper, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [afterAtom_register hfp (by decide)]
    exact h.framePointer
  · rw [afterAtom_register hsp (by decide)]
    exact h.stackPointer
  · rw [afterAtom_register hl (by decide)]
    exact h.stackLimit
  · simpa only [afterAtom_mem] using h.localValues
  · simpa only [afterAtom_mem] using h.savedFrame
  · simpa only [afterAtom_mem] using h.savedLink
  · simpa only [afterAtom_mem] using h.applicationMemory

/-- A local spill preserves saved control words and all application memory. -/
theorem FrameState.spill (h : FrameState stack base locals savedFP returnPC application s)
    (hd : dst < locals.length) (hv : s.regs src = value) (ha : src ≠ address) :
    FrameState stack base (locals.set dst (some value)) savedFP returnPC application
      (afterSave (2+dst) src s) := by
  have hm : (afterSave (2+dst) src s).mem = update s.mem (slotAddress base dst) value := by
    rw [afterSave_mem ha, h.framePointer, hv, slotAddress_eq]
  have hi := h.slotInside hd
  have hne (i : Nat) (hb : i < 2) : word w (base+i) ≠ (slotAddress base dst : Addr w) := by
    intro he
    have hf : base+i < modulus w := by
      have := h.frameFits
      unfold FrameFits at this
      omega
    have hh := (word_eq_iff_of_lt hf (h.frameFits.slot_lt hd)).mp he
    omega
  refine ⟨h.stackFits, h.baseLower, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using h.frameUpper
  · rw [afterSave_register (by decide)]
    exact h.framePointer
  · rw [afterSave_register (by decide)]
    simpa using h.stackPointer
  · rw [afterSave_register (by decide)]
    exact h.stackLimit
  · rw [hm]
    exact h.localValues.set h.frameFits hd value
  · rw [hm, update_other _ _ _ _ (by simpa using hne 0 (by decide))]
    exact h.savedFrame
  · rw [hm, update_other _ _ _ _ (hne 1 (by decide))]
    exact h.savedLink
  · intro a outside
    rw [hm, update_other]
    · exact h.applicationMemory a outside
    · intro he
      exact outside (he ▸ hi)

/-- Temporary register updates leave the abstract invocation unchanged. -/
theorem FrameState.put (h : FrameState stack base locals savedFP returnPC application s)
    (hfp : fp ≠ target) (hsp : sp ≠ target) (hl : limit ≠ target) (v : Word w) :
    FrameState stack base locals savedFP returnPC application (s.put target v) := by
  refine ⟨h.stackFits, h.baseLower, h.frameUpper, ?_, ?_, ?_, h.localValues,
    h.savedFrame, h.savedLink, h.applicationMemory⟩
  · simpa only [State.put, update_other _ _ _ _ hfp] using h.framePointer
  · simpa only [State.put, update_other _ _ _ _ hsp] using h.stackPointer
  · simpa only [State.put, update_other _ _ _ _ hl] using h.stackLimit

/-- Control-flow changes do not affect the frame representation. -/
theorem FrameState.pc (h : FrameState stack base locals savedFP returnPC application s) (pc : Nat) :
    FrameState stack base locals savedFP returnPC application { s with pc := pc } := by
  cases h
  constructor <;> assumption

/-- An application write updates the abstract memory and preserves the entire frame. -/
theorem FrameState.store (h : FrameState stack base locals savedFP returnPC application s)
    (a : Addr w) (v : Word w) (ha : ¬ stack.Contains a) :
    FrameState stack base locals savedFP returnPC (update application a v)
      { s with pc := s.pc+1, mem := update s.mem a v } := by
  refine ⟨h.stackFits, h.baseLower, h.frameUpper, h.framePointer, h.stackPointer,
    h.stackLimit, ?_, ?_, ?_, ?_⟩
  · apply h.localValues.update_outside
    intro i hi he
    exact ha (he ▸ h.slotInside hi)
  · change update s.mem a v (word w base) = savedFP
    rw [update_other]
    · exact h.savedFrame
    · intro he
      apply ha
      simpa only [Nat.add_zero] using he ▸ h.headerInside (i := 0) (by decide)
  · change update s.mem a v (word w (base+1)) = word w returnPC
    rw [update_other]
    · exact h.savedLink
    · intro he
      exact ha (he ▸ h.headerInside (i := 1) (by decide))
  · intro b outside
    by_cases he : b = a
    · subst b; simp
    · simp only [update_other _ _ _ _ he]
      exact h.applicationMemory b outside

/-- Writes into a prospective callee allocation preserve the suspended caller. -/
theorem FrameState.storeAbove (h : FrameState stack base locals savedFP returnPC application s)
    (a : Addr w) (v : Word w) (ha : stack.Contains a)
    (habove : base+2+locals.length ≤ a.toNat) :
    FrameState stack base locals savedFP returnPC application
      { s with pc := s.pc+1, mem := update s.mem a v } := by
  have hne (j : Nat) (hj : j < 2+locals.length) : word w (base+j) ≠ a := by
    intro he
    have hb : base+j < modulus w := by have := h.frameFits; unfold FrameFits at this; omega
    have he' := congrArg BitVec.toNat he
    rw [word_toNat_of_lt hb] at he'
    omega
  refine ⟨h.stackFits,h.baseLower,h.frameUpper,h.framePointer,h.stackPointer,h.stackLimit,?_,?_,?_,?_⟩
  · apply h.localValues.update_outside
    intro i hi
    simpa only [slotAddress,Nat.add_assoc] using Ne.symm (hne (2+i) (by omega))
  · change update s.mem a v (word w base) = savedFP
    rw [update_other _ _ _ _ (by simpa using hne 0 (by omega))]
    exact h.savedFrame
  · change update s.mem a v (word w (base+1)) = word w returnPC
    rw [update_other _ _ _ _ (hne 1 (by omega))]
    exact h.savedLink
  · intro b outside
    change update s.mem a v b = application b
    rw [update_other]
    · exact h.applicationMemory b outside
    · intro he; exact outside (he ▸ ha)

end RamLang.Compiler
