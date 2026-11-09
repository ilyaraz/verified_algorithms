import RamLang.Compiler.Proofs.Control

namespace RamLang.Compiler
open WordRam ABI

/-- Straight-line instructions always advance the PC by one. This deliberately
excludes calls and all control-flow instructions. -/
def straightInstruction : Instr R → Prop
  | .mov _ _ | .add _ _ _ | .sub _ _ _ | .mul _ _ _ | .mod _ _ _
  | .shr _ _ _ | .load _ _ | .store _ _ | .rload _ _ => True
  | _ => False

variable {w R k : Nat} {p : WordRam.Program R} {rho : RandomMemory w}
  {s t : State w R} {event : Option (Access w)} {i : Instr R} {r : Reg R}

/-- Local fetch information suffices for the register-frame property. -/
theorem instruction_register (hs : WordRam.Step p rho s t event)
    (hi : p[s.pc]? = some i) (hn : i.destination ≠ some r) : t.regs r = s.regs r := by
  unfold WordRam.Step WordRam.step at hs
  rw [hi] at hs
  cases i <;> simp only [StepResult.next.injEq] at hs
  all_goals try { cases hs }
  all_goals obtain ⟨rfl,rfl⟩ := hs
  all_goals simp_all [Instr.destination,State.put,update,Ne.symm]

theorem straight_next (hi : p[s.pc]? = some i) (hl : straightInstruction i) :
    ∃ t event, WordRam.Step p rho s t event ∧ t.pc = s.pc+1 := by
  cases i <;> simp only [straightInstruction] at hl
  all_goals try contradiction
  all_goals unfold WordRam.Step WordRam.step; rw [hi]
  all_goals exact ⟨_,_,rfl,rfl⟩

/-- Every instruction-level observation of a straight-line register-preserving
block retains that register, including the observation just after the block. -/
theorem straight_prefix_register {code : List (Instr R)}
    (hc : CodeAt p s.pc code)
    (hl : ∀ i ∈ code, straightInstruction i)
    (hn : ∀ i ∈ code, i.destination ≠ some r) (hk : k ≤ code.length) :
    (WordRam.run p rho k s).state.regs r = s.regs r := by
  induction code generalizing k s with
  | nil =>
    have : k = 0 := by simpa using hk
    subst k
    rfl
  | cons i rest ih =>
    cases k with
    | zero => rfl
    | succ k =>
      obtain ⟨t,event,hs,hpc⟩ := straight_next (rho := rho) hc.head (hl i (by simp))
      have hreg := instruction_register hs hc.head (hn i (by simp))
      have hh := ih (s := t) (k := k) (by rw [hpc]; exact hc.tail)
        (fun j hj => hl j (by simp [hj])) (fun j hj => hn j (by simp [hj])) (by simp at hk; omega)
      change WordRam.step p rho s = .next t event at hs
      simpa only [WordRam.run,hs,WordRam.RunResult.prepend] using hh.trans hreg

/-- A natural upper bound on the physical stack pointer at every observed instruction. -/
def StackBound (p : WordRam.Program registers) (rho : RandomMemory w)
    (s : State w registers) (work top : Nat) : Prop :=
  ∀ fuel, fuel ≤ work → ((WordRam.run p rho fuel s).state.regs sp).toNat ≤ top

variable {p : WordRam.Program registers} {s t : State w registers}
  {rho : RandomMemory w} {n m top top' : Nat} {trace : List (Access w)}

theorem StackBound.mono (h : StackBound p rho s n top) (ht : top ≤ top') :
    StackBound p rho s n top' := fun fuel hf => Nat.le_trans (h fuel hf) ht

/-- Instruction prefixes compose, including the boundary between fragments. -/
theorem StackBound.trans (hs : WordRam.Steps p rho n s t trace)
    (ha : StackBound p rho s n top) (hb : StackBound p rho t m top) :
    StackBound p rho s (n+m) top := by
  intro fuel hf
  by_cases hshort : fuel ≤ n
  · exact ha fuel hshort
  · have he : fuel = n+(fuel-n) := by omega
    rw [he,hs.run_eq]
    exact hb (fuel-n) (by omega)

theorem StackBound.end (h : StackBound p rho s n top) (hs : WordRam.Steps p rho n s t trace) :
    (t.regs sp).toNat ≤ top := by
  have hh := h n (Nat.le_refl _)
  rw [hs.exhausted] at hh
  exact hh

theorem StackBound.zero (h : (s.regs sp).toNat ≤ top) : StackBound p rho s 0 top := by
  intro fuel hf
  have : fuel = 0 := by omega
  subst fuel
  exact h

theorem StackBound.single (hs : WordRam.Step p rho s t event)
    (ha : (s.regs sp).toNat ≤ top) (hb : (t.regs sp).toNat ≤ top) :
    StackBound p rho s 1 top := by
  intro fuel hf
  cases fuel with
  | zero => exact ha
  | succ fuel =>
    have : fuel = 0 := by omega
    subst fuel
    change WordRam.step p rho s = .next t event at hs
    simpa [WordRam.run,hs,WordRam.RunResult.prepend] using hb

/-- Quiet templates are straight-line and preserve the physical stack pointer. -/
def Quiet (code : Code) : Prop :=
  ∀ i ∈ code, straightInstruction i ∧ i.destination ≠ some sp

@[simp] theorem quiet_append (a b : Code) : Quiet (a++b) ↔ Quiet a ∧ Quiet b := by
  simp [Quiet,List.mem_append,or_imp,forall_and,and_assoc,and_left_comm,and_comm]

theorem quiet_atom {dst : Reg registers} (hd : dst ≠ sp) (x : Atom) : Quiet (atom dst x) := by
  intro instruction hi
  cases x with
  | literal value =>
    simp only [atom,List.mem_singleton] at hi
    subst instruction
    exact ⟨trivial,fun h => hd (Option.some.inj h)⟩
  | «local» id =>
    simp only [atom,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl
    · exact ⟨trivial,by change (some address : Option (Reg registers)) ≠ some sp; decide⟩
    · exact ⟨trivial,fun h => hd (Option.some.inj h)⟩

theorem quiet_spill (dst : Nat) (src : Reg registers) : Quiet (spill dst src) := by
  simp [Quiet,spill,straightInstruction,Instr.destination,Fin.ext_iff,address,sp]

theorem quiet_primitive (op : Primitive) : Quiet (primitive op) := by
  have leftAtom := quiet_atom (dst := left) (by decide)
  have rightAtom := quiet_atom (dst := right) (by decide)
  cases op with
  | move d x => exact (quiet_append _ _).mpr ⟨leftAtom x,quiet_spill d left⟩
  | binary d op x y =>
    apply (quiet_append _ _).mpr
    refine ⟨(quiet_append _ _).mpr ⟨(quiet_append _ _).mpr ⟨leftAtom x,rightAtom y⟩,?_⟩,quiet_spill d left⟩
    cases op <;> simp [Quiet,binary,straightInstruction,Instr.destination,Fin.ext_iff,left,sp]
  | load d x =>
    apply (quiet_append _ _).mpr
    refine ⟨(quiet_append _ _).mpr ⟨leftAtom x,?_⟩,quiet_spill d left⟩
    simp [Quiet,straightInstruction,Instr.destination,Fin.ext_iff,left,sp]
  | random d x =>
    apply (quiet_append _ _).mpr
    refine ⟨(quiet_append _ _).mpr ⟨leftAtom x,?_⟩,quiet_spill d left⟩
    simp [Quiet,straightInstruction,Instr.destination,Fin.ext_iff,left,sp]
  | store x y =>
    apply (quiet_append _ _).mpr
    refine ⟨(quiet_append _ _).mpr ⟨leftAtom x,rightAtom y⟩,?_⟩
    simp [Quiet,straightInstruction,Instr.destination]

theorem quiet_arguments (args : List Atom) (i : Nat) : Quiet (arguments i args) := by
  induction args generalizing i with
  | nil => simp [arguments,Quiet]
  | cons a rest ih =>
    apply (quiet_append _ _).mpr
    refine ⟨(quiet_append _ _).mpr ⟨quiet_atom (by decide) a,?_⟩,ih (i+1)⟩
    simp [Quiet,straightInstruction,Instr.destination,Fin.ext_iff,address,sp]

/-- Quiet templates preserve the stack pointer at every internal instruction. -/
theorem quiet_stackBound {code : Code} (hc : CodeAt p s.pc code) (hq : Quiet code)
    (ha : (s.regs sp).toNat ≤ top) : StackBound p rho s code.length top := by
  intro fuel hf
  rw [straight_prefix_register hc (fun i hi => (hq i hi).1) (fun i hi => (hq i hi).2) hf]
  exact ha

/-- A final jump/branch can follow a quiet prefix when the observed endpoint is bounded. -/
theorem quiet_final_stackBound {code : Code}
    (hc : CodeAt p s.pc code) (hq : Quiet code)
    (hs : WordRam.Steps p rho (code.length+1) s t trace)
    (ha : (s.regs sp).toNat ≤ top) (hb : (t.regs sp).toNat ≤ top) :
    StackBound p rho s (code.length+1) top := by
  intro fuel hf
  by_cases he : fuel = code.length+1
  · rw [he,hs.exhausted]
    exact hb
  · exact quiet_stackBound hc hq ha fuel (by omega)

theorem FrameState.sp_le {stack : Region} {base returnPC : Nat} {locals : Locals w}
    {savedFP : Word w} {mem : DataMemory w}
    (hf : FrameState stack base locals savedFP returnPC mem s)
    (ht : base+2+locals.length ≤ top) : (s.regs sp).toNat ≤ top := by
  rw [hf.stackPointer,word_toNat_of_lt hf.frameFits]
  exact ht

/-- The guard changes no stack pointer, on either the success or error branch. -/
theorem guard_stackBound {frame exhausted : Nat} (hc : CodeAt p s.pc (guardCode frame exhausted))
    (ha : (s.regs sp).toNat ≤ top) : StackBound p rho s 2 top := by
  apply quiet_final_stackBound (code := [.sub left (.reg limit) (.reg sp)]) hc.prefix
    (by simp [Quiet,straightInstruction,Instr.destination,Fin.ext_iff,left,sp]) (guard_steps hc) ha
  simpa [afterGuard,State.put,update,Fin.ext_iff,sp,left] using ha

/-- All return-template prefixes keep sp below the maximum of its old value and fp. -/
theorem epilogue_stackBound (hc : CodeAt p s.pc epilogue)
    (ha : (s.regs sp).toNat ≤ top) (hb : (s.regs fp).toNat ≤ top) :
    StackBound p rho s 6 top := by
  intro fuel hf
  rcases (show fuel = 0 ∨ fuel = 1 ∨ fuel = 2 ∨ fuel = 3 ∨ fuel = 4 ∨ fuel = 5 ∨ fuel = 6 by omega) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals simp only [WordRam.run,WordRam.step,hc.head,State.put,Operand.eval,
    hc.tail.head,hc.tail.tail.head,hc.tail.tail.tail.head,hc.tail.tail.tail.tail.head,
    hc.tail.tail.tail.tail.tail.head,WordRam.RunResult.prepend]
  all_goals simp_all [update,Fin.ext_iff,address,fp,sp,link,caller]

/-- Every instruction of frame installation keeps sp below the checked new end. -/
theorem install_stackBound {frame entry : Nat} (hc : CodeAt p s.pc (installCode frame entry))
    (ha : (s.regs sp).toNat ≤ top) (hb : (s.regs sp + word w frame).toNat ≤ top) :
    StackBound p rho s 3 top := by
  intro fuel hf
  rcases (show fuel = 0 ∨ fuel = 1 ∨ fuel = 2 ∨ fuel = 3 by omega) with rfl | rfl | rfl | rfl
  all_goals simp only [WordRam.run,WordRam.step,hc.head,State.put,Operand.eval,
    hc.tail.head,hc.tail.tail.head,WordRam.RunResult.prepend]
  all_goals simp_all [update,Fin.ext_iff,fp,sp,link]

/-- Straight-line templates execute completely at their checked linked addresses. -/
theorem straight_execution {code : Code} (hc : CodeAt p s.pc code)
    (hl : ∀ i ∈ code, straightInstruction i) :
    ∃ t trace, WordRam.Steps p rho code.length s t trace ∧ t.pc = s.pc+code.length := by
  induction code generalizing s with
  | nil => exact ⟨s,[],.refl _,by simp⟩
  | cons i rest ih =>
    obtain ⟨t,event,hs,hpc⟩ := straight_next (rho := rho) hc.head (hl i (by simp))
    obtain ⟨u,trace,ht,hend⟩ := ih (s := t) (by rw [hpc]; exact hc.tail) (fun j hj => hl j (by simp [hj]))
    refine ⟨u,event.toList++trace,.cons hs ht,?_⟩
    rw [hend,hpc]; simp; omega

/-- Primitive templates preserve the stack pointer at every instruction. -/
theorem primitive_stackBound {stack : Region} {base returnPC : Nat} {locals : Locals w}
    {savedFP : Word w} {mem : DataMemory w} {op : Primitive}
    (hf : FrameState stack base locals savedFP returnPC mem s)
    (hc : CodeAt p s.pc (primitive op)) (ht : base+2+locals.length ≤ top) :
    StackBound p rho s (primitive op).length top :=
  quiet_stackBound hc (quiet_primitive op) (hf.sp_le ht)

/-- Conditions keep sp fixed during both operand loads and the final branch. -/
theorem condition_stackBound {c : Condition} {target : Nat}
    (hc : CodeAt p s.pc ((atom left c.left ++ atom right c.right) ++
      [.branch c.comparison (.reg left) (.reg right) target]))
    (hs : WordRam.Steps p rho (conditionCost c+1) s t trace)
    (ha : (s.regs sp).toNat ≤ top) (hb : (t.regs sp).toNat ≤ top) :
    StackBound p rho s (conditionCost c+1) top := by
  have hq : Quiet (atom left c.left ++ atom right c.right) :=
    (quiet_append _ _).mpr ⟨quiet_atom (by decide) _,quiet_atom (by decide) _⟩
  have he : (atom left c.left ++ atom right c.right).length = conditionCost c := by simp [conditionCost]
  have hh := quiet_final_stackBound hc.prefix hq (by rw [he]; exact hs) ha hb
  simpa only [he] using hh

/-- Returning a value keeps every temporary and teardown state within its frame bound. -/
theorem return_stackBound {stack : Region} {base returnPC : Nat} {locals : Locals w}
    {savedFP : Word w} {mem : DataMemory w} {x : Atom}
    (hf : FrameState stack base locals savedFP returnPC mem s)
    (hc : CodeAt p s.pc (atom result x ++ epilogue)) (ht : base+2+locals.length ≤ top) :
    StackBound p rho s ((atom result x).length+6) top := by
  have h₁ := hf.afterAtom (target := result) (atomValue := x) (by decide) (by decide) (by decide)
  have hb : ((afterAtom result x s).regs fp).toNat ≤ top := by
    rw [h₁.framePointer,word_toNat_of_lt (show base < modulus w by
      have := hf.frameFits; unfold FrameFits at this; omega)]
    omega
  exact StackBound.trans (atom_steps hc.prefix)
    (quiet_stackBound hc.prefix (quiet_atom (by decide) _) (hf.sp_le ht))
    (epilogue_stackBound (by rw [afterAtom_pc]; exact hc.suffix) (h₁.sp_le ht) hb)

/-- The error halt preserves sp even at and after the status-write instruction. -/
theorem error_stackBound (hc : CodeAt p s.pc errorCode) (ha : (s.regs sp).toNat ≤ top) :
    StackBound p rho s 2 top := by
  intro fuel hf
  rcases (show fuel = 0 ∨ fuel = 1 ∨ fuel = 2 by omega) with rfl | rfl | rfl
  all_goals simp only [WordRam.run,WordRam.step,hc.head,State.put,Operand.eval,
    hc.tail.head,WordRam.RunResult.prepend]
  all_goals simp_all [update,Fin.ext_iff,status,sp]

/-- Guard failure never allocates a frame, at any instruction of its error path. -/
theorem exhausted_stackBound {frame exhausted current bound : Nat}
    (hcode : CodeAt p s.pc (guardCode frame exhausted)) (herr : CodeAt p exhausted errorCode)
    (hsp : s.regs sp = word w current) (hl : s.regs limit = word w bound)
    (horder : current ≤ bound) (hbound : bound < modulus w) (hframe : frame < modulus w)
    (hshort : bound-current < frame) (ha : (s.regs sp).toNat ≤ top) :
    StackBound p rho s 4 top := by
  have hpc := guard_decision hsp hl horder hbound hframe (exhausted := exhausted)
  rw [if_pos hshort] at hpc
  exact StackBound.trans (guard_steps hcode) (guard_stackBound hcode ha)
    (error_stackBound (by rw [hpc]; exact herr) (by
      simpa [afterGuard,State.put,update,Fin.ext_iff,sp,left] using ha))

/-- Successful call setup respects its checked stack high-water mark at every
instruction, including the interval before the incoming link has been saved. -/
theorem call_setup_stackBound {frame entry exhausted current bound : Nat} {args : List Atom}
    (hc : CodeAt p s.pc (callSetup frame entry exhausted args))
    (hentry : CodeAt p entry prologue)
    (hsp : s.regs sp = word w current) (hl : s.regs limit = word w bound)
    (hspace : current+frame ≤ bound) (hbound : bound < modulus w) :
    StackBound p rho s ((arguments 0 args).length+8) (current+frame) := by
  let t₁ := afterGuard frame exhausted s
  let middle : Code := [.store (.reg sp) (.reg fp)] ++ arguments 0 args
  change CodeAt p s.pc (((guardCode frame exhausted ++ [.store (.reg sp) (.reg fp)]) ++
    arguments 0 args) ++ installCode frame entry) at hc
  have hguard := guard_steps (rho := rho) hc.prefix.prefix.prefix
  have hframe : frame < modulus w := by omega
  have hpc₁ : t₁.pc = s.pc+2 := by
    rw [guard_decision hsp hl (by omega) hbound hframe]
    split <;> omega
  have hmidCode : CodeAt p t₁.pc middle := by
    have hh : CodeAt p s.pc (guardCode frame exhausted ++ middle) := by
      simpa only [middle,List.append_assoc] using hc.prefix
    rw [hpc₁]
    exact hh.suffix
  have hmidQuiet : Quiet middle :=
    (quiet_append _ _).mpr ⟨by simp [Quiet,straightInstruction,Instr.destination],quiet_arguments args 0⟩
  obtain ⟨t₂,log,hs,hpc₂⟩ := straight_execution (rho := rho) hmidCode (fun i hi => (hmidQuiet i hi).1)
  have hsp₁ : t₁.regs sp = word w current := by
    simpa [t₁,afterGuard,State.put,update,Fin.ext_iff,sp,left] using hsp
  have hsp₂ : t₂.regs sp = word w current := by
    have hh := straight_prefix_register hmidCode (fun i hi => (hmidQuiet i hi).1)
      (fun i hi => (hmidQuiet i hi).2) (Nat.le_refl middle.length) (rho := rho)
    rw [hs.exhausted] at hh
    exact hh.trans hsp₁
  have hinstallCode : CodeAt p t₂.pc (installCode frame entry) := by
    have heq : t₂.pc = s.pc + ((guardCode frame exhausted ++ [Instr.store (.reg sp) (.reg fp)]) ++ arguments 0 args).length := by
      rw [hpc₂,hpc₁]
      simp only [guardCode,middle,List.length_append,List.length_cons,List.length_nil]
      omega
    rw [heq]
    exact hc.suffix
  let t₃ := afterInstall frame entry t₂
  have hinstall := install_steps (rho := rho) hinstallCode
  have hsp₃ : t₃.regs sp = word w (current+frame) := by
    simp only [t₃,afterInstall,update_other _ _ _ _ (show sp ≠ link by decide),update_same,hsp₂,word_add]
  have ha : (s.regs sp).toNat ≤ current+frame := by rw [hsp,word_toNat_of_lt (by omega)]; omega
  have hb : (t₁.regs sp).toNat ≤ current+frame := by rw [hsp₁,word_toNat_of_lt (by omega)]; omega
  have hd : (t₂.regs sp).toNat ≤ current+frame := by rw [hsp₂,word_toNat_of_lt (by omega)]; omega
  have he : (t₃.regs sp).toNat ≤ current+frame := by rw [hsp₃,word_toNat_of_lt (by omega)]; exact Nat.le_refl _
  have hsum : StackBound p rho s (2+middle.length+3+2) (current+frame) :=
    StackBound.trans ((hguard.trans hs).trans hinstall)
      (StackBound.trans (hguard.trans hs)
        (StackBound.trans hguard (guard_stackBound hc.prefix.prefix.prefix ha)
          (quiet_stackBound hmidCode hmidQuiet hb))
        (install_stackBound hinstallCode hd (by rw [hsp₂,word_add,word_toNat_of_lt (by omega)]; exact Nat.le_refl _)))
      (quiet_stackBound (s := t₃) (code := prologue) hentry
        (by simp [Quiet,prologue,straightInstruction,Instr.destination,Fin.ext_iff,address,sp]) he)
  have hn : 2+middle.length+3+2 = (arguments 0 args).length+8 := by
    simp only [middle,List.length_append,List.length_cons,List.length_nil]
    omega
  simpa only [hn] using hsum

end RamLang.Compiler
