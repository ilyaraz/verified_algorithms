import RamLang.Compiler.Proofs.Primitives

namespace RamLang.Compiler
open WordRam ABI

/-- The prospective-frame argument store uses sp, leaving the caller fp installed. -/
def argumentCode (i : Nat) : Code :=
  [.add address (.reg sp) (.imm (2+i)), .store (.reg address) (.reg left)]

def afterArgument (i : Nat) (s : State w registers) : State w registers :=
  let a := s.regs sp + word w (2+i)
  { (s.put address a) with pc := s.pc+2, mem := update s.mem a (s.regs left) }

def argumentTrace (i : Nat) (s : State w registers) : List (Access w) :=
  [.dataWrite (s.regs sp + word w (2+i)) (s.regs left)]

variable {w base returnPC i top : Nat} {stack : Region} {locals : Locals w}
  {savedFP : Word w} {mem : DataMemory w} {s : State w registers}
  {p : WordRam.Program registers} {rho : RandomMemory w}

theorem argument_steps (hc : CodeAt p s.pc (argumentCode i)) :
    WordRam.Steps p rho 2 s (afterArgument i s) (argumentTrace i s) := by
  let a := s.regs sp + word w (2+i)
  let t := s.put address a
  have h₁ : WordRam.Step p rho s t none := by
    unfold WordRam.Step WordRam.step
    rw [hc.head]
    rfl
  have h₂ : WordRam.Step p rho t (afterArgument i s) (some (.dataWrite a (s.regs left))) := by
    unfold WordRam.Step WordRam.step
    rw [show t.pc = s.pc+1 from rfl,hc.tail.head]
    simp [afterArgument,t,a,Operand.eval,State.put,update,Fin.ext_iff,left,address,Nat.add_assoc]
  exact .cons h₁ (.cons h₂ (.refl _))

theorem FrameState.argument (hf : FrameState stack base locals savedFP returnPC mem s)
    (hspace : base+2+locals.length+2+i < stack.base+stack.size) :
    FrameState stack base locals savedFP returnPC mem (afterArgument i s) := by
  let a := s.regs sp + word w (2+i)
  have haeq : a = word w (base+2+locals.length+2+i) := by
    simp only [a,hf.stackPointer,word_add]; congr 1; omega
  have hword : base+2+locals.length+2+i < modulus w := by
    have := hf.stackFits; unfold Region.Fits at this; omega
  have hin : stack.Contains a := by
    rw [haeq]; unfold Region.Contains; rw [word_toNat_of_lt hword]
    have := hf.baseLower
    omega
  have habove : base+2+locals.length ≤ a.toNat := by rw [haeq,word_toNat_of_lt hword]; omega
  have ht := hf.put (target := address) (by decide) (by decide) (by decide) a
  have hw := ht.storeAbove a (s.regs left) hin habove
  simpa only [afterArgument,a,State.put,Nat.add_assoc] using hw

/-- Successful argument evaluation has exactly one value per source atom. -/
theorem arguments_length {args : List Atom} {values : List (Word w)}
    (he : args.mapM (Atom.eval locals) = .ok values) : values.length = args.length := by
  induction args generalizing values with
  | nil =>
    simp [List.mapM_nil,pure,Except.pure] at he
    subst values
    rfl
  | cons a rest ih =>
    cases ha : a.eval locals with
    | error e => simp [List.mapM_cons,ha,bind,Except.bind] at he
    | ok v =>
      cases hr : rest.mapM (Atom.eval locals) with
      | error e => simp [List.mapM_cons,ha,hr,bind,Except.bind] at he
      | ok vs =>
        simp [List.mapM_cons,ha,hr,bind,pure,Except.bind,Except.pure] at he
        subst values
        simpa using ih hr

/-- Argument copying charges all atom loads and stores, preserves the suspended
caller, initializes the new argument array, and leaves lower stack words intact. -/
theorem arguments_steps {args : List Atom} {values : List (Word w)}
    (he : args.mapM (Atom.eval locals) = .ok values)
    (hf : FrameState stack base locals savedFP returnPC mem s)
    (hc : CodeAt p s.pc (arguments i args))
    (hspace : base+2+locals.length+2+i+values.length ≤ top)
    (htop : top ≤ stack.base+stack.size) :
    ∃ t trace, WordRam.Steps p rho (arguments i args).length s t trace ∧
      t.pc = s.pc+(arguments i args).length ∧
      FrameState stack base locals savedFP returnPC mem t ∧
      ArrayAt t.mem (base+2+locals.length+2+i) values ∧
      projectTrace stack trace = [] ∧
      (framePolicy stack base top).AllowsTrace trace ∧
      (∀ a : Addr w, a.toNat < base+2+locals.length+2+i → t.mem a = s.mem a) := by
  induction args generalizing values i s with
  | nil =>
    simp [List.mapM_nil,pure,Except.pure] at he
    subst values
    exact ⟨s,[],.refl _,by simp [arguments],hf,by simp, rfl,by simp [AccessPolicy.AllowsTrace],by simp⟩
  | cons a rest ih =>
    cases ha : a.eval locals with
    | error e => simp [List.mapM_cons,ha,bind,Except.bind] at he
    | ok v =>
      cases hr : rest.mapM (Atom.eval locals) with
      | error e => simp [List.mapM_cons,ha,hr,bind,Except.bind] at he
      | ok vs =>
        simp [List.mapM_cons,ha,hr,bind,pure,Except.bind,Except.pure] at he
        subst values
        let current := base+2+locals.length
        let t₁ := afterAtom left a s
        let t₂ := afterArgument i t₁
        have h₁ : FrameState stack base locals savedFP returnPC mem t₁ :=
          hf.afterAtom (by decide) (by decide) (by decide)
        have hword : current+2+i < modulus w := by
          have := hf.stackFits
          unfold Region.Fits at this
          simp only [List.length_cons] at hspace
          omega
        have hin : stack.Contains (word w (current+2+i)) := by
          unfold Region.Contains
          rw [word_toNat_of_lt hword]
          have := hf.baseLower
          simp only [List.length_cons] at hspace
          dsimp [current] at *
          omega
        have h₂ : FrameState stack base locals savedFP returnPC mem t₂ :=
          h₁.argument (by simp only [List.length_cons] at hspace; omega)
        have hv : t₁.regs left = v := atom_value hf.framePointer hf.localValues ha
        have hm : t₂.mem = update s.mem (word w (current+2+i)) v := by
          simp only [t₂,afterArgument,h₁.stackPointer,word_add,hv,t₁,afterAtom_mem]
          congr 2
          omega
        have hpc : t₂.pc = s.pc+(atom left a).length+2 := by
          simp only [t₂,afterArgument,t₁,afterAtom_pc]
        change CodeAt p s.pc ((atom left a ++ argumentCode i) ++ arguments (i+1) rest) at hc
        have ht : WordRam.Steps p rho ((atom left a).length+2) s t₂
            (atomTrace a s ++ argumentTrace i t₁) :=
          (atom_steps hc.prefix.prefix).trans (argument_steps (by rw [afterAtom_pc]; exact hc.prefix.suffix))
        have hnext : CodeAt p t₂.pc (arguments (i+1) rest) := by
          rw [hpc]
          simpa [argumentCode,Nat.add_assoc] using hc.suffix
        obtain ⟨t,trace,hs,hend,hfend,harray,hproj,hpol,hbelow⟩ := ih hr h₂ hnext (by
          simp only [List.length_cons] at hspace
          omega)
        have hlen : (arguments i (a::rest)).length =
            ((atom left a).length+2)+(arguments (i+1) rest).length := by
          simp only [arguments,List.length_append,List.length_cons,List.length_nil]
        refine ⟨t,(atomTrace a s ++ argumentTrace i t₁) ++ trace,?_,?_,hfend,?_,?_,?_,?_⟩
        · rw [hlen]; exact ht.trans hs
        · rw [hend,hpc,hlen]; omega
        · rw [arrayAt_cons]
          constructor
          · rw [hbelow _ (by rw [word_toNat_of_lt hword]; omega),hm,update_same]
          · simpa only [Nat.add_assoc] using harray
        · rw [project_append,project_append,hproj,
            atom_project stack hf.framePointer (fun j hj => hf.slotInside hj) ha]
          have harg : projectTrace stack (argumentTrace i t₁) = [] := by
            simp only [argumentTrace,h₁.stackPointer,word_add]
            have heq : base+2+locals.length+(2+i) = current+2+i := by omega
            rw [heq]
            exact project_stack_write hin
          rw [harg]; rfl
        · apply (AccessPolicy.allowsTrace_append _).mpr
          refine ⟨(AccessPolicy.allowsTrace_append _).mpr ⟨?_,?_⟩,hpol⟩
          · exact framePolicy_mono (Nat.le_refl _) (by simp only [List.length_cons] at hspace; omega)
              (atom_policy hf ha)
          · simp only [argumentTrace,h₁.stackPointer,word_add]
            intro e hevent
            simp only [List.mem_singleton] at hevent
            subst e
            apply Or.inr
            have heq : base+2+locals.length+(2+i) = current+2+i := by omega
            rw [heq,word_toNat_of_lt hword]
            simp only [List.length_cons] at hspace
            dsimp [current] at *
            omega
        · intro b hb
          rw [hbelow b (by omega),hm,update_other]
          intro heq
          have hb' := congrArg BitVec.toNat heq
          rw [word_toNat_of_lt hword] at hb'
          omega

end RamLang.Compiler
