import WordRam.Execution

namespace WordRam

/-- Rename only register operands; final code addresses and immediates stay fixed. -/
def Operand.rename (f : Reg R → Reg S) : Operand R → Operand S
  | .reg r => .reg (f r)
  | .imm n => .imm n

/-- Embed a program into a larger register file without relocating any code or
introducing instructions, memory effects, or hidden execution state. -/
def Instr.rename (f : Reg R → Reg S) : Instr R → Instr S
  | .mov d x => .mov (f d) (x.rename f)
  | .add d x y => .add (f d) (x.rename f) (y.rename f)
  | .sub d x y => .sub (f d) (x.rename f) (y.rename f)
  | .mul d x y => .mul (f d) (x.rename f) (y.rename f)
  | .mod d x y => .mod (f d) (x.rename f) (y.rename f)
  | .shr d x y => .shr (f d) (x.rename f) (y.rename f)
  | .load d a => .load (f d) (a.rename f)
  | .store a x => .store (a.rename f) (x.rename f)
  | .rload d a => .rload (f d) (a.rename f)
  | .branch c x y pc => .branch c (x.rename f) (y.rename f) pc
  | .jump pc => .jump pc
  | .call link pc => .call (f link) pc
  | .jumpReg pc => .jumpReg (pc.rename f)
  | .halt => .halt

/-- Observe the embedded registers and the unchanged physical memory and PC. -/
def State.project (f : Reg R → Reg S) (s : State w S) : State w R :=
  ⟨s.pc,fun r => s.regs (f r),s.mem⟩

/-- Projection preserves each instruction's optional ordinary or random event. -/
def StepResult.project (f : Reg R → Reg S) : StepResult w S → StepResult w R
  | .next s event => .next (s.project f) event
  | .halt => .halt
  | .fault e => .fault e

/-- A run projection changes only the register-file view. -/
def RunResult.project (f : Reg R → Reg S) (r : RunResult w S) : RunResult w R :=
  ⟨r.state.project f,r.steps,r.trace,r.reason⟩

/-- Operand evaluation commutes with an arbitrary register renaming. -/
theorem Operand.eval_rename (f : Reg R → Reg S) (rs : Registers w S) (x : Operand R) :
    (x.rename f).eval rs = x.eval (fun r => rs (f r)) := by cases x <;> rfl

/-- An injective renaming commutes with updating an embedded register. -/
theorem registers_project_update (f : Reg R → Reg S) (hf : Function.Injective f)
    (rs : Registers w S) (r : Reg R) (value : Word w) :
    (fun i => update rs (f r) value (f i)) = update (fun i => rs (f i)) r value := by
  funext i
  have he : f i = f r ↔ i = r := ⟨fun h => hf h,congrArg f⟩
  simp [update,he]

/-- Injectivity ensures a write never aliases another embedded register. -/
theorem State.project_put (f : Reg R → Reg S) (hf : Function.Injective f)
    (s : State w S) (r : Reg R) (value : Word w) :
    (s.put (f r) value).project f = (s.project f).put r value := by
  simp only [State.put,State.project,registers_project_update f hf]

/-- The authoritative machine transition commutes with injective register
embedding for all instructions, including calls and indirect returns. -/
theorem step_project (f : Reg R → Reg S) (hf : Function.Injective f)
    (p : Program R) (rho : RandomMemory w) (s : State w S) :
    (step (p.map (Instr.rename f)) rho s).project f = step p rho (s.project f) := by
  cases hp : p[s.pc]? with
  | none => simp [step,Array.getElem?_map,hp,StepResult.project,State.project]
  | some instruction =>
    cases instruction <;>
      simp [step,Array.getElem?_map,hp,Instr.rename,Operand.eval_rename,StepResult.project,
        State.project,State.put,registers_project_update f hf]

/-- Every finite run has exactly the same time, stop reason, full trace and
ordinary memory after embedding; the caller may supply arbitrary extra registers. -/
theorem run_project (f : Reg R → Reg S) (hf : Function.Injective f)
    (p : Program R) (rho : RandomMemory w) (fuel : Nat) (s : State w S) :
    (run (p.map (Instr.rename f)) rho fuel s).project f = run p rho fuel (s.project f) := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
    have h := step_project f hf p rho s
    cases hs : step (p.map (Instr.rename f)) rho s with
    | halt => simp [hs,StepResult.project] at h; simp only [run,hs,←h,RunResult.project]
    | fault e => simp [hs,StepResult.project] at h; simp only [run,hs,←h,RunResult.project]
    | next t event =>
      simp only [hs,StepResult.project] at h
      simp only [run,hs,←h,RunResult.prepend,RunResult.project]
      have ht := ih t
      cases hr : run (p.map (Instr.rename f)) rho fuel t
      simp only [hr,RunResult.project] at ht ⊢
      rw [←ht]

/-- Terminating execution transfers to the larger public register file with
identical time and trace and exactly the projected final state. -/
theorem TerminatesIn.rename (f : Reg R → Reg S) (hf : Function.Injective f)
    {p : Program R} {rho : RandomMemory w} {s : State w S} {k : Nat} {t : State w R} {log : List (Access w)}
    (h : TerminatesIn p rho (s.project f) k t log) :
    ∃ u, TerminatesIn (p.map (Instr.rename f)) rho s k u log ∧ u.project f = t := by
  have he := run_project f hf p rho k s
  rw [h.run_eq] at he
  have hh := congrArg RunResult.reason he
  have hk := congrArg RunResult.steps he
  have hl := congrArg RunResult.trace he
  have hs := congrArg RunResult.state he
  change (run (p.map (Instr.rename f)) rho k s).reason = .halted at hh
  change (run (p.map (Instr.rename f)) rho k s).steps = k at hk
  change (run (p.map (Instr.rename f)) rho k s).trace = log at hl
  exact ⟨_,by simpa only [hk,hl] using terminatesIn_of_halted hh,hs⟩

end WordRam
