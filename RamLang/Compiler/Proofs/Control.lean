import RamLang.Compiler.Proofs.Calls
import RamLang.Compiler.Resources

namespace RamLang.Compiler
open WordRam ABI

variable {w base returnPC target pc : Nat} {stack : Region} {locals : Locals w}
  {savedFP v : Word w} {mem : DataMemory w} {s : State w registers}
  {p : WordRam.Program registers} {rho : RandomMemory w}

/-- Inverting a successful condition exposes the old-local operand values. -/
theorem condition_values {c : Condition} {b : Bool} (he : c.eval locals = .ok b) :
    ∃ x y, c.left.eval locals = .ok x ∧ c.right.eval locals = .ok y ∧ c.comparison.test x y = b := by
  cases hx : c.left.eval locals with
  | error e => simp [Condition.eval,hx,bind,Except.bind] at he
  | ok x =>
    cases hy : c.right.eval locals with
    | error e => simp [Condition.eval,hx,hy,bind,Except.bind] at he
    | ok y =>
      simp only [Condition.eval,hx,hy,bind,pure,Except.bind,Except.pure,Except.ok.injEq] at he
      exact ⟨x,y,rfl,rfl,he⟩

/-- Both operand loads and the conditional branch preserve the invocation frame. -/
theorem condition_steps {c : Condition} {b : Bool}
    (he : c.eval locals = .ok b) (hf : FrameState stack base locals savedFP returnPC mem s)
    (hc : CodeAt p s.pc ((atom left c.left ++ atom right c.right) ++
      [.branch c.comparison (.reg left) (.reg right) target])) :
    ∃ t trace, WordRam.Steps p rho (conditionCost c+1) s t trace ∧
      t.pc = (if b then target else s.pc+conditionCost c+1) ∧
      FrameState stack base locals savedFP returnPC mem t ∧
      projectTrace stack trace = [] ∧
      (framePolicy stack base (base+2+locals.length)).AllowsTrace trace := by
  obtain ⟨x,y,hx,hy,hb⟩ := condition_values he
  let t₁ := afterAtom left c.left s
  let t₂ := afterAtom right c.right t₁
  let t₃ : State w registers := { t₂ with pc := if b then target else t₂.pc+1 }
  have h₁ : FrameState stack base locals savedFP returnPC mem t₁ := hf.afterAtom (by decide) (by decide) (by decide)
  have h₂ : FrameState stack base locals savedFP returnPC mem t₂ := h₁.afterAtom (by decide) (by decide) (by decide)
  have hv : t₂.regs left = x ∧ t₂.regs right = y := pair_values hf hx hy
  have hpc : t₂.pc = s.pc+conditionCost c := by
    simp only [t₂,t₁,afterAtom_pc,conditionCost]; omega
  have hs : WordRam.Step p rho t₂ t₃ none := by
    unfold WordRam.Step WordRam.step
    rw [hpc,show s.pc+conditionCost c = s.pc+(atom left c.left ++ atom right c.right).length by
      simp [conditionCost],hc.suffix.head]
    simp only [Operand.eval,hv.1,hv.2,hb,t₃,hpc,conditionCost,List.length_append]
  refine ⟨t₃,atomTrace c.left s ++ atomTrace c.right t₁,?_,?_,h₂.pc _,?_,?_⟩
  · simpa using (pair_steps hc.prefix).trans (.cons hs (.refl _))
  · simp only [t₃,hpc]
  · rw [project_append,atom_project stack hf.framePointer (fun i hi => hf.slotInside hi) hx,
      atom_project stack h₁.framePointer (fun i hi => h₁.slotInside hi) hy]
    rfl
  · exact (AccessPolicy.allowsTrace_append _).mpr ⟨atom_policy hf hx,atom_policy h₁ hy⟩

theorem jump_step (hc : CodeAt p s.pc [.jump target]) :
    WordRam.Step p rho s {s with pc := target} none := by
  unfold WordRam.Step WordRam.step
  rw [hc.head]

/-- Return implements early exit directly through the saved linked continuation. -/
theorem return_steps {x : Atom} (he : x.eval locals = .ok v)
    (hf : FrameState stack base locals savedFP returnPC mem s) (hret : returnPC < modulus w)
    (hc : CodeAt p s.pc (atom result x ++ epilogue)) :
    ∃ t trace, WordRam.Steps p rho ((atom result x).length+6) s t trace ∧
      t.pc = returnPC ∧ t.regs fp = savedFP ∧ t.regs sp = word w base ∧ t.regs result = v ∧
      t.regs limit = word w (stack.base+stack.size) ∧ ApplicationMemory stack mem t.mem ∧
      projectTrace stack trace = [] ∧
      (framePolicy stack base (base+2+locals.length)).AllowsTrace trace := by
  let t₁ := afterAtom result x s
  let t₂ := afterEpilogue t₁
  have h₁ : FrameState stack base locals savedFP returnPC mem t₁ := hf.afterAtom (by decide) (by decide) (by decide)
  have hv : t₁.regs result = v := atom_value hf.framePointer hf.localValues he
  have hh := epilogue_restores h₁.framePointer h₁.savedLink h₁.savedFrame hret
  have hlim : t₂.regs limit = word w (stack.base+stack.size) := by
    change (afterEpilogue t₁).regs limit = _
    simp only [afterEpilogue]
    simp only [update_other _ _ _ _ (show limit ≠ fp by decide),
      update_other _ _ _ _ (show limit ≠ sp by decide),update_other _ _ _ _ (show limit ≠ caller by decide),
      update_other _ _ _ _ (show limit ≠ link by decide),update_other _ _ _ _ (show limit ≠ address by decide),
      h₁.stackLimit]
  have htrace : returnTrace t₁ = [.dataRead (word w (base+1)) (word w returnPC),
      .dataRead (word w base) savedFP] := by
    simp only [returnTrace,h₁.framePointer,word_add,h₁.savedFrame,h₁.savedLink]
  have hproj : projectTrace stack (returnTrace t₁) = [] := by
    rw [htrace]
    change projectTrace stack ([.dataRead (word w (base+1)) (word w returnPC)] ++
      [.dataRead (word w base) savedFP]) = []
    rw [project_append,project_stack_read (h₁.headerInside (i := 1) (by decide)),
      project_stack_read (by simpa using h₁.headerInside (i := 0) (by decide))]
    rfl
  have hpol : (framePolicy stack base (base+2+locals.length)).AllowsTrace (returnTrace t₁) := by
    have hb₀ : base < modulus w := by have := hf.frameFits; unfold FrameFits at this; omega
    have hb₁ : base+1 < modulus w := by have := hf.frameFits; unfold FrameFits at this; omega
    rw [htrace]
    intro e hevent
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hevent
    rcases hevent with rfl | rfl <;> apply Or.inr
    · rw [word_toNat_of_lt hb₁]; omega
    · rw [word_toNat_of_lt hb₀]; omega
  refine ⟨t₂,atomTrace x s ++ returnTrace t₁,?_,hh.1,hh.2.1,hh.2.2.1,
    hh.2.2.2.1.trans hv,hlim,h₁.applicationMemory,?_,?_⟩
  · exact (atom_steps hc.prefix).trans (epilogue_steps (by rw [afterAtom_pc]; exact hc.suffix))
  · rw [project_append,atom_project stack hf.framePointer (fun i hi => hf.slotInside hi) he,hproj]; rfl
  · exact (AccessPolicy.allowsTrace_append _).mpr ⟨atom_policy hf he,hpol⟩

end RamLang.Compiler
