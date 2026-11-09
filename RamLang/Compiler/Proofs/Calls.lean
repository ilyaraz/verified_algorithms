import RamLang.Compiler.Proofs.Arguments

namespace RamLang.Compiler
open WordRam ABI

variable {w base returnPC current frame entry exhausted : Nat} {stack : Region}
  {locals : Locals w} {savedFP : Word w} {mem : DataMemory w}
  {s : State w registers} {p : WordRam.Program registers} {rho : RandomMemory w}

/-- The allocation guard leaves all frame invariants intact on either branch. -/
theorem FrameState.guard (hf : FrameState stack base locals savedFP returnPC mem s) :
    FrameState stack base locals savedFP returnPC mem (afterGuard frame exhausted s) :=
  (hf.put (target := left) (by decide) (by decide) (by decide) _).pc _

/-- Save the suspended fp at the prospective frame base before copying arguments. -/
def afterHeader (s : State w registers) : State w registers :=
  { s with pc := s.pc+1, mem := update s.mem (s.regs sp) (s.regs fp) }

theorem header_step (hc : CodeAt p s.pc [.store (.reg sp) (.reg fp)]) :
    WordRam.Step p rho s (afterHeader s) (some (.dataWrite (s.regs sp) (s.regs fp))) := by
  unfold WordRam.Step WordRam.step
  rw [hc.head]
  rfl

def installCode (frame entry : Nat) : Code :=
  [.mov fp (.reg sp),.add sp (.reg sp) (.imm frame),.call link entry]

def afterInstall (frame entry : Nat) (s : State w registers) : State w registers :=
  { s with
    pc := entry
    regs := update (update (update s.regs fp (s.regs sp)) sp (s.regs sp + word w frame))
      link (word w (s.pc+3)) }

/-- Install the frame and execute the actual ISA call, including its saved PC. -/
theorem install_steps (hc : CodeAt p s.pc (installCode frame entry)) :
    WordRam.Steps p rho 3 s (afterInstall frame entry s) [] := by
  let t₁ := s.put fp (s.regs sp)
  let t₂ := t₁.put sp (s.regs sp + word w frame)
  have h₁ : WordRam.Step p rho s t₁ none := by
    unfold WordRam.Step WordRam.step
    rw [hc.head]
    rfl
  have h₂ : WordRam.Step p rho t₁ t₂ none := by
    unfold WordRam.Step WordRam.step
    rw [show t₁.pc = s.pc+1 from rfl,hc.tail.head]
    simp [t₁,t₂,Operand.eval,State.put,update,Fin.ext_iff,fp,sp]
  have h₃ : WordRam.Step p rho t₂ (afterInstall frame entry s) none := by
    unfold WordRam.Step WordRam.step
    rw [show t₂.pc = s.pc+1+1 from rfl,hc.tail.tail.head]
    simp [afterInstall,t₁,t₂,Operand.eval,State.put,Nat.add_assoc]
  exact .cons h₁ (.cons h₂ (.cons h₃ (.refl _)))

/-- Saving the incoming link completes a new activation without clearing locals. -/
theorem prologue_frame (hfit : stack.Fits w) (hlower : stack.base ≤ base)
    (hupper : base+2+locals.length ≤ stack.base+stack.size)
    (hfp : s.regs fp = word w base) (hsp : s.regs sp = word w (base+2+locals.length))
    (hlimit : s.regs limit = word w (stack.base+stack.size))
    (hlocals : FrameLocals s.mem base locals) (hsaved : s.mem (word w base) = savedFP)
    (hlink : s.regs link = word w returnPC) (happ : ApplicationMemory stack mem s.mem) :
    FrameState stack base locals savedFP returnPC mem (afterSave 1 link s) := by
  have hb : FrameFits w base locals.length := by unfold FrameFits; unfold Region.Fits at hfit; omega
  have h₀ : base < modulus w := by unfold FrameFits at hb; omega
  have h₁ : base+1 < modulus w := by unfold FrameFits at hb; omega
  have hinside : stack.Contains (word w (base+1)) := by
    unfold Region.Contains; rw [word_toNat_of_lt h₁]; omega
  have hmem : (afterSave 1 link s).mem = update s.mem (word w (base+1)) (word w returnPC) := by
    rw [afterSave_mem (by decide),hfp,word_add,hlink]
  refine ⟨hfit,hlower,hupper,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [afterSave_register (by decide)]; exact hfp
  · rw [afterSave_register (by decide)]; exact hsp
  · rw [afterSave_register (by decide)]; exact hlimit
  · rw [hmem]
    apply hlocals.update_outside
    intro i hi he
    have he' := (word_eq_iff_of_lt h₁ (hb.slot_lt hi)).mp he
    omega
  · rw [hmem,update_other]
    · exact hsaved
    · intro he
      have := (word_eq_iff_of_lt h₀ h₁).mp he
      omega
  · rw [hmem,update_same]
  · intro a outside
    rw [hmem,update_other]
    · exact happ a outside
    · intro he; exact outside (he ▸ hinside)

/-- The prefix shared by every ordinary call. The body is reached only after
its full frame has passed the capacity check. -/
def callSetup (frame entry exhausted : Nat) (args : List Atom) : Code :=
  guardCode frame exhausted ++ [.store (.reg sp) (.reg fp)] ++ arguments 0 args ++ installCode frame entry

/-- Successful setup enters the one shared callee body with initialized arguments,
charged header stores, and all older stack words preserved. -/
theorem call_setup {args : List Atom} {values : List (Word w)} {f : Function}
    (he : args.mapM (Atom.eval locals) = .ok values) (harity : values.length = f.parameters.length)
    (hf : FrameState stack base locals savedFP returnPC mem s)
    (hspace : base+2+locals.length+f.frameSize ≤ stack.base+stack.size)
    (hc : CodeAt p s.pc (callSetup f.frameSize entry exhausted args))
    (hentry : CodeAt p entry prologue) :
    ∃ t trace, WordRam.Steps p rho ((arguments 0 args).length+8) s t trace ∧
      t.pc = entry+2 ∧
      FrameState stack (base+2+locals.length)
        (values.map some ++ List.replicate f.locals.length none) (word w base)
        (s.pc+(arguments 0 args).length+6) mem t ∧
      projectTrace stack trace = [] ∧
      (framePolicy stack base (base+2+locals.length+f.frameSize)).AllowsTrace trace ∧
      (∀ a : Addr w, a.toNat < base+2+locals.length → t.mem a = s.mem a) := by
  let current := base+2+locals.length
  let top := current+f.frameSize
  let t₁ := afterGuard f.frameSize exhausted s
  let t₂ := afterHeader t₁
  have hbound : stack.base+stack.size < modulus w := hf.stackFits
  have hframe : f.frameSize < modulus w := by dsimp [current,top] at *; omega
  have hcurrent : current < modulus w := by have := hf.frameFits; exact this
  have hpc₁ : t₁.pc = s.pc+2 := by
    rw [guard_decision hf.stackPointer hf.stackLimit hf.frameUpper hbound hframe]
    split <;> omega
  have h₁ : FrameState stack base locals savedFP returnPC mem t₁ := hf.guard
  have hinside : stack.Contains (word w current) := by
    unfold Region.Contains; rw [word_toNat_of_lt hcurrent]
    have := hf.baseLower
    have : 2 ≤ f.frameSize := by simp [Function.frameSize,Function.slots]
    dsimp [current] at *; omega
  have h₂ : FrameState stack base locals savedFP returnPC mem t₂ := by
    have hh := h₁.storeAbove (word w current) (word w base) hinside
      (by rw [word_toNat_of_lt hcurrent]; exact Nat.le_refl _)
    simpa only [t₂,afterHeader,h₁.stackPointer,h₁.framePointer] using hh
  have hpc₂ : t₂.pc = s.pc+3 := by change t₁.pc+1 = _; rw [hpc₁]
  change CodeAt p s.pc (((guardCode f.frameSize exhausted ++ [.store (.reg sp) (.reg fp)]) ++
    arguments 0 args) ++ installCode f.frameSize entry) at hc
  have hguard := guard_steps (rho := rho) hc.prefix.prefix.prefix
  have hheader : WordRam.Step p rho t₁ t₂ (some (.dataWrite (word w current) (word w base))) := by
    have hh := header_step (rho := rho) (s := t₁) (by
      rw [hpc₁]; exact hc.prefix.prefix.suffix)
    simpa only [h₁.stackPointer,h₁.framePointer] using hh
  have hargsCode : CodeAt p t₂.pc (arguments 0 args) := by
    rw [hpc₂]
    exact hc.prefix.suffix
  obtain ⟨t₃,logArgs,hargs,hpc₃,h₃,harray,hprojArgs,hpolArgs,hbelowArgs⟩ :=
    arguments_steps (rho := rho) he h₂ hargsCode
      (top := top) (by dsimp [top,current]; simp [Function.frameSize,Function.slots,harity]; omega) hspace
  let t₄ := afterInstall f.frameSize entry t₃
  let t₅ := afterSave 1 link t₄
  have hinstallCode : CodeAt p t₃.pc (installCode f.frameSize entry) := by
    rw [hpc₃,hpc₂]
    have hlen : (guardCode f.frameSize exhausted ++ [Instr.store (.reg sp) (.reg fp)] ++ arguments 0 args).length =
        3 + (arguments 0 args).length := by
      simp only [guardCode,List.length_append,List.length_cons,List.length_nil]
    simpa only [hlen,Nat.add_assoc] using hc.suffix
  have hinstall := install_steps (rho := rho) hinstallCode
  have hsave := prologue_steps (rho := rho) (s := t₄) hentry
  have hpc₃' : t₃.pc+3 = s.pc+(arguments 0 args).length+6 := by rw [hpc₃,hpc₂]; omega
  have hfp₄ : t₄.regs fp = word w current := by
    simp only [t₄,afterInstall]
    simp only [update_other _ _ _ _ (show fp ≠ link by decide),
      update_other _ _ _ _ (show fp ≠ sp by decide),update_same,h₃.stackPointer,current]
  have hsp₄ : t₄.regs sp = word w top := by
    simp only [t₄,afterInstall,update_other _ _ _ _ (show sp ≠ link by decide),update_same,
      h₃.stackPointer,word_add,current,top]
  have hlimit₄ : t₄.regs limit = word w (stack.base+stack.size) := by
    simp only [t₄,afterInstall,update_other _ _ _ _ (show limit ≠ link by decide),
      update_other _ _ _ _ (show limit ≠ sp by decide),update_other _ _ _ _ (show limit ≠ fp by decide),
      h₃.stackLimit]
  have hlink₄ : t₄.regs link = word w (s.pc+(arguments 0 args).length+6) := by
    simp only [t₄,afterInstall,update_same,hpc₃']
  have hsaved₄ : t₄.mem (word w current) = word w base := by
    change t₃.mem _ = _
    rw [hbelowArgs _ (by rw [word_toNat_of_lt hcurrent]; omega)]
    simp only [t₂,afterHeader,h₁.stackPointer,h₁.framePointer,current,update_same]
  have hslots : (values.map some ++ List.replicate f.locals.length (none : Option (Word w))).length = f.slots := by
    simp [Function.slots,harity]
  have hcallee : FrameState stack current
      (values.map some ++ List.replicate f.locals.length none) (word w base)
      (s.pc+(arguments 0 args).length+6) mem t₅ := by
    apply prologue_frame hf.stackFits (by have := hf.baseLower; dsimp [current]; omega)
      (by rw [hslots]; simpa [Function.frameSize,current,Nat.add_assoc] using hspace) hfp₄
      (by rw [hslots]; simpa [Function.frameSize,top,Nat.add_assoc] using hsp₄) hlimit₄ _ hsaved₄ hlink₄ h₃.applicationMemory
    exact FrameLocals.parameters (by simpa [current] using harray) _
  have hfinalMem : t₅.mem = update t₃.mem (word w (current+1))
      (word w (s.pc+(arguments 0 args).length+6)) := by
    rw [afterSave_mem (by decide),hfp₄,word_add,hlink₄]
    rfl
  have hcurrent₁ : current+1 < modulus w := by
    have : 2 ≤ f.frameSize := by simp [Function.frameSize,Function.slots]
    dsimp [current] at *; omega
  have hinside₁ : stack.Contains (word w (current+1)) := by
    unfold Region.Contains; rw [word_toNat_of_lt hcurrent₁]
    have := hf.baseLower
    have : 2 ≤ f.frameSize := by simp [Function.frameSize,Function.slots]
    dsimp [current] at *; omega
  have hsaveProj : projectTrace stack (saveTrace 1 link t₄) = [] := by
    simp only [saveTrace,hfp₄,word_add]
    exact project_stack_write hinside₁
  have hsavePol : (framePolicy stack base top).AllowsTrace (saveTrace 1 link t₄) := by
    simp only [saveTrace,hfp₄,word_add]
    intro e hevent
    simp only [List.mem_singleton] at hevent
    subst e
    apply Or.inr
    rw [word_toNat_of_lt hcurrent₁]
    have : 2 ≤ f.frameSize := by simp [Function.frameSize,Function.slots]
    dsimp [current,top]; omega
  have hheadPol : (framePolicy stack base top).AllowsTrace [.dataWrite (word w current) (word w base)] := by
    intro e hevent
    simp only [List.mem_singleton] at hevent
    subst e
    apply Or.inr
    rw [word_toNat_of_lt hcurrent]
    have : 2 ≤ f.frameSize := by simp [Function.frameSize,Function.slots]
    dsimp [current,top]; omega
  refine ⟨t₅,[.dataWrite (word w current) (word w base)] ++ logArgs ++ saveTrace 1 link t₄,
    ?_,rfl,hcallee,?_,?_,?_⟩
  · have hh := (((hguard.trans (.cons hheader (.refl _))).trans hargs).trans hinstall).trans hsave
    have hn : ((2+(0+1))+(arguments 0 args).length)+3+2 = (arguments 0 args).length+8 := by omega
    simpa only [hn,Option.toList_some,List.nil_append,List.append_nil,List.append_assoc] using hh
  · rw [project_append,project_append,project_stack_write hinside,hprojArgs,hsaveProj]; rfl
  · exact (AccessPolicy.allowsTrace_append _).mpr
      ⟨(AccessPolicy.allowsTrace_append _).mpr ⟨hheadPol,hpolArgs⟩,hsavePol⟩
  · intro a ha
    rw [hfinalMem,update_other]
    · rw [hbelowArgs a (by omega)]
      change update t₁.mem (t₁.regs sp) (t₁.regs fp) a = s.mem a
      rw [h₁.stackPointer,update_other]
      · rfl
      · intro heq
        have hh := congrArg BitVec.toNat heq
        rw [word_toNat_of_lt hcurrent] at hh
        omega
    · intro heq
      have hh := congrArg BitVec.toNat heq
      rw [word_toNat_of_lt hcurrent₁] at hh
      omega

end RamLang.Compiler
