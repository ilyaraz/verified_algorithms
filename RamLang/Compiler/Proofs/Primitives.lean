import RamLang.Compiler.Proofs.Effects
import RamLang.Primitive

namespace RamLang.Compiler
open WordRam ABI

variable {w base returnPC dst n : Nat} {stack : Region} {locals locals' : Locals w}
  {savedFP value : Word w} {mem mem' : DataMemory w} {s t : State w registers}
  {p : WordRam.Program registers} {rho : RandomMemory w} {trace observed : List (Access w)}
  {x y : Atom} {op : Binary}

/-- A continuing source fragment is implemented with its exact charged work,
application trace, frame representation, and stack footprint. -/
def LocalExecution (p : WordRam.Program registers) (rho : RandomMemory w)
    (stack : Region) (base : Nat) (savedFP : Word w) (returnPC : Nat)
    (s : State w registers) (n : Nat) (locals' : Locals w) (mem' : DataMemory w)
    (observed : List (Access w)) : Prop :=
  ∃ t trace, WordRam.Steps p rho n s t trace ∧ t.pc = s.pc+n ∧
    FrameState stack base locals' savedFP returnPC mem' t ∧
    projectTrace stack trace = observed ∧
    (framePolicy stack base (base+2+locals'.length)).AllowsTrace trace

/-- Finish an evaluated assignment with the two explicitly charged slot-store instructions. -/
theorem assignment_finish (hs : WordRam.Steps p rho n s t trace)
    (hpc : t.pc = s.pc+n) (hf : FrameState stack base locals savedFP returnPC mem t)
    (hv : t.regs left = value) (hw : writeLocal locals dst value = .ok locals')
    (hc : CodeAt p t.pc (spill dst left)) (hp : projectTrace stack trace = observed)
    (hpol : (framePolicy stack base (base+2+locals.length)).AllowsTrace trace) :
    LocalExecution p rho stack base savedFP returnPC s (n+2) locals' mem observed := by
  obtain ⟨hd, rfl⟩ := writeLocal_ok hw
  refine ⟨afterSave (2+dst) left t, trace ++ saveTrace (2+dst) left t,
    hs.trans (spill_steps hc), ?_, hf.spill hd hv (by decide), ?_, ?_⟩
  · rw [afterSave_pc, hpc]; omega
  · rw [project_append, hp, spill_project hf hd, List.append_nil]
  · simpa using (AccessPolicy.allowsTrace_append _).mpr ⟨hpol, spill_policy hf hd⟩

/-- The binary instruction uses the two previously evaluated operand registers. -/
theorem binary_step (h : CodeAt p s.pc [binary op]) :
    WordRam.Step p rho s (s.put left (op.eval (s.regs left) (s.regs right))) none := by
  unfold WordRam.Step WordRam.step
  rw [h.head]
  cases op <;> rfl

/-- Evaluate two operands left-to-right without changing any source local or memory. -/
theorem pair_steps (hc : CodeAt p s.pc (atom left x ++ atom right y)) :
    WordRam.Steps p rho ((atom left x).length + (atom right y).length) s
      (afterAtom right y (afterAtom left x s))
      (atomTrace x s ++ atomTrace y (afterAtom left x s)) := by
  exact (atom_steps hc.prefix).trans (atom_steps (by rw [afterAtom_pc]; exact hc.suffix))

theorem pair_values (hf : FrameState stack base locals savedFP returnPC mem s)
    (hx : x.eval locals = .ok a) (hy : y.eval locals = .ok b) :
    (afterAtom right y (afterAtom left x s)).regs left = a ∧
    (afterAtom right y (afterAtom left x s)).regs right = b := by
  have h₁ := hf.afterAtom (target := left) (atomValue := x) (by decide) (by decide) (by decide)
  constructor
  · rw [afterAtom_register (by decide) (by decide)]
    exact atom_value hf.framePointer hf.localValues hx
  · exact atom_value h₁.framePointer h₁.localValues hy

/-- Each of the six primitive forms implements its independent source operation. -/
theorem primitive_steps {operation : Primitive} {event : Option (Access w)}
    (he : operation.eval rho locals mem = .ok (locals',mem',event))
    (hsep : Separated stack event.toList)
    (hf : FrameState stack base locals savedFP returnPC mem s)
    (hc : CodeAt p s.pc (primitive operation)) :
    LocalExecution p rho stack base savedFP returnPC s (primitive operation).length
      locals' mem' event.toList := by
  cases operation with
  | move d x =>
    obtain ⟨v,hx,hw,hm,hevent⟩ := Primitive.move_ok he
    subst mem' event
    simp only [Option.toList_some,Option.toList_none] at hsep ⊢
    have h₁ := hf.afterAtom (target := left) (atomValue := x) (by decide) (by decide) (by decide)
    have hh := assignment_finish (rho := rho) (atom_steps hc.prefix) afterAtom_pc h₁
      (atom_value hf.framePointer hf.localValues hx) hw
      (by rw [afterAtom_pc]; exact hc.suffix)
      (atom_project stack hf.framePointer (fun i hi => hf.slotInside hi) hx) (atom_policy hf hx)
    simpa [primitive, spill] using hh
  | binary d op x y =>
    obtain ⟨a,b,hx,hy,hw,hm,hevent⟩ := Primitive.binary_ok he
    subst mem' event
    simp only [Option.toList_some,Option.toList_none] at hsep ⊢
    let t₁ := afterAtom left x s
    let t₂ := afterAtom right y t₁
    let t₃ := t₂.put left (op.eval a b)
    have h₁ : FrameState stack base locals savedFP returnPC mem t₁ :=
      hf.afterAtom (by decide) (by decide) (by decide)
    have h₂ : FrameState stack base locals savedFP returnPC mem t₂ :=
      h₁.afterAtom (by decide) (by decide) (by decide)
    have hv := pair_values hf hx hy
    have hc' := hc
    change CodeAt p s.pc (((atom left x ++ atom right y) ++ [binary op]) ++ spill d left) at hc'
    have hpair := pair_steps (rho := rho) hc'.prefix.prefix
    have hb : WordRam.Step p rho t₂ t₃ none := by
      have hb := binary_step (op := op) (rho := rho) (s := t₂) (by
        simp only [t₂,t₁,afterAtom_pc,Nat.add_assoc]
        simpa only [List.length_append] using hc'.prefix.suffix)
      simpa only [t₃,t₂,t₁,hv.1,hv.2] using hb
    have hex := hpair.trans (WordRam.Steps.cons hb (.refl _))
    have hpc : t₃.pc = s.pc + ((atom left x).length + (atom right y).length + 1) := by
      simp only [t₃,State.put,t₂,t₁,afterAtom_pc]; omega
    have h₃ : FrameState stack base locals savedFP returnPC mem t₃ :=
      h₂.put (by decide) (by decide) (by decide) _
    have hcode : CodeAt p t₃.pc (spill d left) := by
      rw [hpc]
      simpa using hc'.suffix
    have hprojection : projectTrace stack
        ((atomTrace x s ++ atomTrace y t₁) ++ Option.toList (none : Option (Access w))) = [] := by
      simp only [project_append, atom_project stack hf.framePointer (fun i hi => hf.slotInside hi) hx,
        atom_project stack h₁.framePointer (fun i hi => h₁.slotInside hi) hy]
      rfl
    have hpolicy : (framePolicy stack base (base+2+locals.length)).AllowsTrace
        ((atomTrace x s ++ atomTrace y t₁) ++ Option.toList (none : Option (Access w))) := by
      simpa using (AccessPolicy.allowsTrace_append _).mpr ⟨atom_policy hf hx, atom_policy h₁ hy⟩
    have hh := assignment_finish (rho := rho) (by simpa using hex) hpc h₃
      (show t₃.regs left = op.eval a b by simp [t₃,State.put]) hw hcode hprojection hpolicy
    simpa [primitive,spill,Nat.add_assoc] using hh
  | load d x =>
    obtain ⟨a,hx,hw,hm,hevent⟩ := Primitive.load_ok he
    subst mem' event
    simp only [Option.toList_some,Option.toList_none] at hsep ⊢
    have hout := separated_read hsep
    let t₁ := afterAtom left x s
    let t₂ := t₁.put left (mem a)
    have h₁ : FrameState stack base locals savedFP returnPC mem t₁ :=
      hf.afterAtom (by decide) (by decide) (by decide)
    have hv : t₁.regs left = a := atom_value hf.framePointer hf.localValues hx
    have hc' := hc
    change CodeAt p s.pc ((atom left x ++ [.load left (.reg left)]) ++ spill d left) at hc'
    have hs : WordRam.Step p rho t₁ t₂ (some (.dataRead a (mem a))) := by
      unfold WordRam.Step WordRam.step
      rw [show t₁.pc = s.pc+(atom left x).length from afterAtom_pc, hc'.prefix.suffix.head]
      simp only [Operand.eval,hv,h₁.applicationMemory a hout]
      rfl
    have hex := (atom_steps hc'.prefix.prefix).trans (WordRam.Steps.cons hs (.refl _))
    have hpc : t₂.pc = s.pc + ((atom left x).length+1) := by
      simp only [t₂,State.put,t₁,afterAtom_pc]; omega
    have h₂ : FrameState stack base locals savedFP returnPC mem t₂ :=
      h₁.put (by decide) (by decide) (by decide) _
    have hh := assignment_finish (rho := rho) (by simpa using hex) hpc h₂
      (show t₂.regs left = mem a by simp [t₂,State.put]) hw
      (by rw [hpc]; simpa using hc'.suffix)
      (show projectTrace stack (atomTrace x s ++ [.dataRead a (mem a)]) = [.dataRead a (mem a)] by
        rw [project_append, atom_project stack hf.framePointer (fun i hi => hf.slotInside hi) hx,
          hsep.project, List.nil_append])
      ((AccessPolicy.allowsTrace_append _).mpr ⟨atom_policy hf hx,hsep.policy⟩)
    simpa [primitive,spill,Nat.add_assoc] using hh
  | random d x =>
    obtain ⟨a,hx,hw,hm,hevent⟩ := Primitive.random_ok he
    subst mem' event
    simp only [Option.toList_some,Option.toList_none] at hsep ⊢
    let t₁ := afterAtom left x s
    let t₂ := t₁.put left (rho a)
    have h₁ : FrameState stack base locals savedFP returnPC mem t₁ :=
      hf.afterAtom (by decide) (by decide) (by decide)
    have hv : t₁.regs left = a := atom_value hf.framePointer hf.localValues hx
    have hc' := hc
    change CodeAt p s.pc ((atom left x ++ [.rload left (.reg left)]) ++ spill d left) at hc'
    have hs : WordRam.Step p rho t₁ t₂ (some (.randomRead a (rho a))) := by
      unfold WordRam.Step WordRam.step
      rw [show t₁.pc = s.pc+(atom left x).length from afterAtom_pc, hc'.prefix.suffix.head]
      simp only [Operand.eval,hv]
      rfl
    have hex := (atom_steps hc'.prefix.prefix).trans (WordRam.Steps.cons hs (.refl _))
    have hpc : t₂.pc = s.pc + ((atom left x).length+1) := by
      simp only [t₂,State.put,t₁,afterAtom_pc]; omega
    have h₂ : FrameState stack base locals savedFP returnPC mem t₂ :=
      h₁.put (by decide) (by decide) (by decide) _
    have hh := assignment_finish (rho := rho) (by simpa using hex) hpc h₂
      (show t₂.regs left = rho a by simp [t₂,State.put]) hw
      (by rw [hpc]; simpa using hc'.suffix)
      (show projectTrace stack (atomTrace x s ++ [.randomRead a (rho a)]) = [.randomRead a (rho a)] by
        rw [project_append, atom_project stack hf.framePointer (fun i hi => hf.slotInside hi) hx,
          project_random, List.nil_append])
      ((AccessPolicy.allowsTrace_append _).mpr ⟨atom_policy hf hx,hsep.policy⟩)
    simpa [primitive,spill,Nat.add_assoc] using hh
  | store x y =>
    obtain ⟨a,v,hx,hy,hl,hm,hevent⟩ := Primitive.store_ok he
    subst locals' mem' event
    simp only [Option.toList_some] at hsep ⊢
    have hout := separated_write hsep
    let t₁ := afterAtom left x s
    let t₂ := afterAtom right y t₁
    let t₃ : State w registers := { t₂ with pc := t₂.pc+1, mem := update t₂.mem a v }
    have h₁ : FrameState stack base locals savedFP returnPC mem t₁ :=
      hf.afterAtom (by decide) (by decide) (by decide)
    have h₂ : FrameState stack base locals savedFP returnPC mem t₂ :=
      h₁.afterAtom (by decide) (by decide) (by decide)
    have hv := pair_values hf hx hy
    have hs : WordRam.Step p rho t₂ t₃ (some (.dataWrite a v)) := by
      unfold WordRam.Step WordRam.step
      rw [show t₂.pc = s.pc + (atom left x ++ atom right y).length by
        simp only [t₂,t₁,afterAtom_pc,List.length_append]; omega, hc.suffix.head]
      simp only [Operand.eval]
      rw [hv.1,hv.2]
      simp only [t₃,t₂,t₁,afterAtom_pc,List.length_append,Nat.add_assoc]
    refine ⟨t₃,(atomTrace x s ++ atomTrace y t₁) ++ [.dataWrite a v], ?_, ?_,
      h₂.store a v hout, ?_, ?_⟩
    · simpa [primitive] using (pair_steps hc.prefix).trans (WordRam.Steps.cons hs (.refl _))
    · simp [t₃,t₂,t₁,afterAtom_pc,primitive,Nat.add_assoc]
    · rw [project_append,project_append,
        atom_project stack hf.framePointer (fun i hi => hf.slotInside hi) hx,
        atom_project stack h₁.framePointer (fun i hi => h₁.slotInside hi) hy,hsep.project]
      rfl
    · exact (AccessPolicy.allowsTrace_append _).mpr
        ⟨(AccessPolicy.allowsTrace_append _).mpr ⟨atom_policy hf hx,atom_policy h₁ hy⟩,hsep.policy⟩

end RamLang.Compiler
