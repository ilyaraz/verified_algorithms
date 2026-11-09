import RamLang.Compiler.Proofs.EntryArguments

namespace RamLang.Compiler
open WordRam ABI

/-- Public initialization writes status and the outermost saved-fp sentinel. -/
def initialCode : Code := [.mov status (.imm 0),.mov fp (.imm 0)]

def afterInitial (s : State w registers) : State w registers :=
  (s.put status (word w 0)).put fp (word w 0)

/-- Entry prefix through parameter initialization, before installing the new frame. -/
def parameterCode (frame arity : Nat) : Code :=
  initialCode ++ guardCode frame (exhaustionPC arity) ++ [.store (.reg sp) (.reg fp)] ++ entryArguments arity

variable {w frame arity : Nat} {p : WordRam.Program registers} {rho : RandomMemory w}
  {s : State w registers} {stack : Region}

theorem initial_steps (hc : CodeAt p s.pc initialCode) :
    WordRam.Steps p rho 2 s (afterInitial s) [] := by
  have h₁ : WordRam.Step p rho s (s.put status (word w 0)) none := by
    unfold WordRam.Step WordRam.step
    rw [hc.head]
    rfl
  have h₂ : WordRam.Step p rho (s.put status (word w 0)) (afterInitial s) none := by
    unfold WordRam.Step WordRam.step
    rw [show (s.put status (word w 0)).pc = s.pc+1 from rfl,hc.tail.head]
    rfl
  exact .cons h₁ (.cons h₂ (.refl _))

theorem entryValues_congr {s t : State w registers}
    (h : ∀ i, t.regs (entryArgument i) = s.regs (entryArgument i)) :
    entryValues t arity = entryValues s arity := by
  unfold entryValues
  apply List.map_congr_left
  intro i hi
  exact h i

/-- The entry prefix initializes parameters and both preserved control-register
roles without assuming anything about the initial contents of stack memory. -/
theorem entry_parameters (hc : CodeAt p s.pc (parameterCode frame arity))
    (hpc : s.pc = 0) (hsp : s.regs sp = word w stack.base)
    (hlimit : s.regs limit = word w (stack.base+stack.size))
    (hfit : stack.Fits w) (hparams : 2+arity ≤ frame) (hspace : frame ≤ stack.size) :
    ∃ t trace, WordRam.Steps p rho (5+2*arity) s t trace ∧ t.pc = 5+2*arity ∧
      t.regs fp = word w 0 ∧ t.regs sp = word w stack.base ∧
      t.regs limit = word w (stack.base+stack.size) ∧
      ArrayAt t.mem (stack.base+2) (entryValues s arity) ∧
      t.mem (word w stack.base) = word w 0 ∧
      ApplicationMemory stack s.mem t.mem ∧ projectTrace stack trace = [] ∧
      StackBound p rho s (5+2*arity) stack.base := by
  let t₁ := afterInitial s
  let t₂ := afterGuard frame (exhaustionPC arity) t₁
  let t₃ := afterHeader t₂
  have h₁ := initial_steps (rho := rho) hc.prefix.prefix.prefix
  have hpc₁ : t₁.pc = 2 := by simp [t₁,afterInitial,State.put,hpc]
  have hsp₁ : t₁.regs sp = word w stack.base := by
    simpa [t₁,afterInitial,State.put,update,Fin.ext_iff,status,fp,sp] using hsp
  have hlimit₁ : t₁.regs limit = word w (stack.base+stack.size) := by
    simpa [t₁,afterInitial,State.put,update,Fin.ext_iff,status,fp,limit] using hlimit
  have hguard : CodeAt p t₁.pc (guardCode frame (exhaustionPC arity)) := by
    rw [hpc₁]
    simpa only [hpc,initialCode,List.length_cons,List.length_nil] using hc.prefix.prefix.suffix
  have h₂ := guard_steps (rho := rho) hguard
  have hbound : stack.base+stack.size < modulus w := hfit
  have hframe : frame < modulus w := by omega
  have hpc₂ : t₂.pc = 4 := by
    rw [guard_decision hsp₁ hlimit₁ (by omega) hbound hframe,hpc₁]
    split <;> omega
  have hsp₂ : t₂.regs sp = word w stack.base := by
    simpa [t₂,afterGuard,State.put,update,Fin.ext_iff,left,sp] using hsp₁
  have hfp₂ : t₂.regs fp = word w 0 := by
    simp [t₂,t₁,afterGuard,afterInitial,State.put,update,Fin.ext_iff,left,fp,status]
  have hlimit₂ : t₂.regs limit = word w (stack.base+stack.size) := by
    simpa [t₂,afterGuard,State.put,update,Fin.ext_iff,left,limit] using hlimit₁
  have hheader : CodeAt p t₂.pc [.store (.reg sp) (.reg fp)] := by
    rw [hpc₂]
    simpa only [hpc,initialCode,guardCode,List.length_append,List.length_cons,List.length_nil] using hc.prefix.suffix
  have h₃ : WordRam.Step p rho t₂ t₃ (some (.dataWrite (word w stack.base) (word w 0))) := by
    simpa only [hsp₂,hfp₂] using header_step (rho := rho) hheader
  have hpc₃ : t₃.pc = 5 := by change t₂.pc+1 = _; rw [hpc₂]
  have hsp₃ : t₃.regs sp = word w stack.base := hsp₂
  have hargs : CodeAt p t₃.pc (entryArguments arity) := by
    rw [hpc₃]
    simpa only [hpc,initialCode,guardCode,List.length_append,List.length_cons,List.length_nil] using hc.suffix
  obtain ⟨t,trace,hs,htpc,hregs,harray,happ,hproj,hpol,hbelow⟩ :=
    entryArguments_steps (rho := rho) hargs hsp₃ hfit (Nat.le_refl _) (by omega)
  have hvalues : entryValues t₃ arity = entryValues s arity := by
    apply entryValues_congr
    intro i
    obtain ⟨hisp,hifp,hilimit,hileft,histatus⟩ := entryArgument_ne_control i
    simp only [t₃,afterHeader,t₂,afterGuard,t₁,afterInitial,State.put,
      update_other _ _ _ _ hileft,update_other _ _ _ _ hifp,update_other _ _ _ _ histatus]
  have hb : stack.base < modulus w := by omega
  have hinside : stack.Contains (word w stack.base) := by
    unfold Region.Contains; rw [word_toNat_of_lt hb]; omega
  have hmem : t₃.mem = update s.mem (word w stack.base) (word w 0) := by
    change update t₂.mem (t₂.regs sp) (t₂.regs fp) = _
    rw [hsp₂,hfp₂]
    rfl
  have htotal := ((h₁.trans h₂).trans (.cons h₃ (.refl _))).trans hs
  refine ⟨t,[.dataWrite (word w stack.base) (word w 0)]++trace,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · have hn : (2+2+(0+1))+2*arity = 5+2*arity := by omega
    simpa only [hn,List.nil_append,Option.toList_some,List.append_nil] using htotal
  · rw [htpc,hpc₃]
  · exact (hregs fp (by decide)).trans hfp₂
  · exact (hregs sp (by decide)).trans hsp₂
  · exact (hregs limit (by decide)).trans hlimit₂
  · rw [hvalues] at harray; exact harray
  · rw [hbelow _ (by rw [word_toNat_of_lt hb]; omega),hmem,update_same]
  · intro a hout
    rw [happ a hout,hmem,update_other]
    intro he; exact hout (he ▸ hinside)
  · rw [project_append,project_stack_write hinside,hproj]; rfl
  · have hs₀ : (s.regs sp).toNat ≤ stack.base := by rw [hsp,word_toNat_of_lt hb]; exact Nat.le_refl _
    have hs₁ : (t₁.regs sp).toNat ≤ stack.base := by rw [hsp₁,word_toNat_of_lt hb]; exact Nat.le_refl _
    have hs₂ : (t₂.regs sp).toNat ≤ stack.base := by rw [hsp₂,word_toNat_of_lt hb]; exact Nat.le_refl _
    have hs₃ : (t₃.regs sp).toNat ≤ stack.base := by rw [hsp₃,word_toNat_of_lt hb]; exact Nat.le_refl _
    have hinitBound := quiet_stackBound (rho := rho) hc.prefix.prefix.prefix
      (by simp [Quiet,initialCode,straightInstruction,Instr.destination,Fin.ext_iff,status,fp,sp]) hs₀
    have hargBound : StackBound p rho t₃ (2*arity) stack.base := by
      simpa only [entryArguments_length] using quiet_stackBound (rho := rho) hargs (quiet_entryArguments arity) hs₃
    have hh := StackBound.trans ((h₁.trans h₂).trans (.cons h₃ (.refl _)))
      (StackBound.trans (h₁.trans h₂)
        (StackBound.trans h₁ hinitBound (guard_stackBound hguard hs₁))
        (StackBound.single h₃ hs₂ hs₃)) hargBound
    simpa only [show 2+2+(0+1) = 5 from rfl] using hh

/-- Successful entry setup reaches the shared body with a complete frame and a
word-encoded continuation to the public success wrapper. -/
theorem entry_setup {f : Function} {entry : Nat}
    (hc : CodeAt p s.pc (parameterCode f.frameSize f.parameters.length ++ installCode f.frameSize entry))
    (hentry : CodeAt p entry prologue) (hpc : s.pc = 0)
    (hsp : s.regs sp = word w stack.base) (hlimit : s.regs limit = word w (stack.base+stack.size))
    (hfit : stack.Fits w) (hspace : f.frameSize ≤ stack.size) :
    ∃ t trace, WordRam.Steps p rho (10+2*f.parameters.length) s t trace ∧ t.pc = entry+2 ∧
      FrameState stack stack.base
        ((entryValues s f.parameters.length).map some ++ List.replicate f.locals.length none)
        (word w 0) (8+2*f.parameters.length) s.mem t ∧
      projectTrace stack trace = [] ∧
      StackBound p rho s (10+2*f.parameters.length) (stack.base+f.frameSize) := by
  have hp : 2+f.parameters.length ≤ f.frameSize := by simp [Function.frameSize,Function.slots]
  obtain ⟨t,trace,hs,htpc,htfp,htsp,htlimit,harray,hsaved,happ,hproj,hbound⟩ :=
    entry_parameters (rho := rho) hc.prefix hpc hsp hlimit hfit hp hspace
  have hlen : (parameterCode f.frameSize f.parameters.length).length = 5+2*f.parameters.length := by
    simp only [parameterCode,initialCode,guardCode,entryArguments_length,List.length_append,List.length_cons,List.length_nil]
  have hinstallCode : CodeAt p t.pc (installCode f.frameSize entry) := by
    rw [htpc]
    simpa only [hpc,hlen,Nat.zero_add] using hc.suffix
  let u := afterInstall f.frameSize entry t
  let v := afterSave 1 link u
  have hi := install_steps (rho := rho) hinstallCode
  have hsave := prologue_steps (rho := rho) (s := u) hentry
  have hufp : u.regs fp = word w stack.base := by
    simp only [u,afterInstall,update_other _ _ _ _ (show fp ≠ link by decide),
      update_other _ _ _ _ (show fp ≠ sp by decide),update_same,htsp]
  have husp : u.regs sp = word w (stack.base+f.frameSize) := by
    simp only [u,afterInstall,update_other _ _ _ _ (show sp ≠ link by decide),update_same,htsp,word_add]
  have hulimit : u.regs limit = word w (stack.base+stack.size) := by
    simp only [u,afterInstall,update_other _ _ _ _ (show limit ≠ link by decide),
      update_other _ _ _ _ (show limit ≠ sp by decide),update_other _ _ _ _ (show limit ≠ fp by decide),htlimit]
  have hulink : u.regs link = word w (8+2*f.parameters.length) := by
    simp only [u,afterInstall,update_same,htpc]
    congr 1
    omega
  have hslots : ((entryValues s f.parameters.length).map some ++
      List.replicate f.locals.length (none : Option (Word w))).length = f.slots := by
    simp [entryValues,Function.slots]
  have hframe : FrameState stack stack.base
      ((entryValues s f.parameters.length).map some ++ List.replicate f.locals.length none)
      (word w 0) (8+2*f.parameters.length) s.mem v := by
    apply prologue_frame hfit (Nat.le_refl _) _ hufp _ hulimit _ hsaved hulink happ
    · rw [hslots]; unfold Function.frameSize at hspace; omega
    · rw [hslots]
      simpa only [Function.frameSize,Nat.add_assoc] using husp
    · exact FrameLocals.parameters harray _
  have hb : stack.base+1 < modulus w := by
    have hh := hfit
    unfold Region.Fits at hh
    omega
  have hin : stack.Contains (word w (stack.base+1)) := by
    unfold Region.Contains; rw [word_toNat_of_lt hb]; omega
  have hsaveProj : projectTrace stack (saveTrace 1 link u) = [] := by
    simp only [saveTrace,hufp,word_add]
    exact project_stack_write hin
  have htotal := (hs.trans hi).trans hsave
  have hn : (5+2*f.parameters.length)+3+2 = 10+2*f.parameters.length := by omega
  refine ⟨v,trace++saveTrace 1 link u,?_,rfl,hframe,?_,?_⟩
  · simpa only [hn,List.append_nil] using htotal
  · rw [project_append,hproj,hsaveProj]; rfl
  · have hend : stack.base+f.frameSize < modulus w := by have := hfit; unfold Region.Fits at this; omega
    have htb : (t.regs sp).toNat ≤ stack.base+f.frameSize := by
      rw [htsp,word_toNat_of_lt (by omega)]; omega
    have hub : (u.regs sp).toNat ≤ stack.base+f.frameSize := by
      rw [husp,word_toNat_of_lt hend]
      exact Nat.le_refl _
    have hh := StackBound.trans (hs.trans hi)
      (StackBound.trans hs (hbound.mono (by omega)) (install_stackBound hinstallCode htb (by
        rw [htsp,word_add,word_toNat_of_lt hend]; exact Nat.le_refl _)))
      (quiet_stackBound (s := u) (code := prologue) hentry
        (by simp [Quiet,prologue,straightInstruction,Instr.destination,Fin.ext_iff,address,sp]) hub)
    simpa only [prologue,List.length_cons,List.length_nil,hn] using hh

end RamLang.Compiler
