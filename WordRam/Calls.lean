import WordRam.Refinement

/-! Calls use ordinary word links. The frozen pre-extension interpreter below
makes conservativity explicit, including faults, costs, and access traces. -/
namespace WordRam.Legacy

/-- The original instruction transition; extension instructions are unsupported. -/
def step (p : Program R) (rho : RandomMemory w) (s : State w R) : StepResult w R :=
  let val := Operand.eval s.regs
  match p[s.pc]? with
  | none => .fault (.invalidPC s.pc)
  | some (.mov d x) => .next (s.put d (val x)) none
  | some (.add d x y) => .next (s.put d (val x + val y)) none
  | some (.sub d x y) => .next (s.put d (val x - val y)) none
  | some (.mul d x y) => .next (s.put d (val x * val y)) none
  | some (.mod d x y) => .next (s.put d (unsignedMod (val x) (val y))) none
  | some (.shr d x count) => .next (s.put d (unsignedShiftRight (val x) (val count))) none
  | some (.load d a) => .next (s.put d (s.mem (val a))) (some (.dataRead (val a) (s.mem (val a))))
  | some (.store a x) =>
      .next { s with pc := s.pc + 1, mem := update s.mem (val a) (val x) }
        (some (.dataWrite (val a) (val x)))
  | some (.rload d a) => .next (s.put d (rho (val a))) (some (.randomRead (val a) (rho (val a))))
  | some (.branch cmp x y target) =>
      .next { s with pc := if cmp.test (val x) (val y) then target else s.pc + 1 } none
  | some (.jump target) => .next { s with pc := target } none
  | some .halt => .halt
  | some (.call _ _) | some (.jumpReg _) => .fault (.invalidPC s.pc)


/-- The original fuelled evaluator, using only the frozen legacy transition. -/
def run (p : Program R) (rho : RandomMemory w) : Nat → State w R → RunResult w R
  | 0, s => ⟨s, 0, [], .fuelExhausted⟩
  | fuel+1, s =>
    match step p rho s with
    | .fault f => ⟨s, 0, [], .fault f⟩
    | .halt => ⟨s, 1, [], .halted⟩
    | .next t a => (run p rho fuel t).prepend 1 a.toList

end WordRam.Legacy

namespace WordRam

/-- Old instruction arrays have precisely their original transition at every PC,
including out-of-range PCs. No word-width or code-length premise is added. -/
theorem step_conservative (p : Program R) (hc : p.PCRelocatable)
    (rho : RandomMemory w) (s : State w R) : step p rho s = Legacy.step p rho s := by
  unfold step Legacy.step
  cases hi : p[s.pc]? with
  | none => rfl
  | some i =>
    have hs := hc.fetch hi
    cases i <;> simp_all [Instr.pcRelocatable]

/-- Every old execution retains exactly its state, trace, cost, and stop reason. -/
theorem run_conservative (p : Program R) (hc : p.PCRelocatable)
    (rho : RandomMemory w) (fuel : Nat) (s : State w R) :
    run p rho fuel s = Legacy.run p rho fuel s := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
    simp only [run, Legacy.run, step_conservative p hc]
    split <;> simp_all

/-- Direct call writes the wrapped successor PC and leaves ordinary memory alone. -/
theorem step_call {p : Program R} {s : State w R} (h : p[s.pc]? = some (.call link target)) :
    step p rho s = .next
      { s with pc := target, regs := update s.regs link (word w (s.pc+1)) } none := by
  simp [step, h]

/-- A computed jump evaluates its operand in the pre-instruction register state. -/
theorem step_jumpReg {p : Program R} {s : State w R} (h : p[s.pc]? = some (.jumpReg target)) :
    step p rho s = .next { s with pc := (target.eval s.regs).toNat } none := by
  simp [step, h]

namespace CallExamples

/-- Two runtime calls; the outer callee spills its link and a live local to RAM. -/
def nested : Program 4 := #[
  .mov ⟨1, by decide⟩ (.imm 7), .call ⟨0, by decide⟩ 5, .add ⟨2, by decide⟩ (.reg ⟨2, by decide⟩) (.reg ⟨1, by decide⟩), .halt, .halt,
  .store (.imm 100) (.reg ⟨0, by decide⟩), .store (.imm 101) (.reg ⟨1, by decide⟩),
  .mov ⟨1, by decide⟩ (.imm 99), .call ⟨0, by decide⟩ 14, .load ⟨1, by decide⟩ (.imm 101), .load ⟨0, by decide⟩ (.imm 100),
  .add ⟨2, by decide⟩ (.reg ⟨2, by decide⟩) (.reg ⟨1, by decide⟩), .jumpReg (.reg ⟨0, by decide⟩), .halt,
  .mov ⟨2, by decide⟩ (.imm 3), .jumpReg (.reg ⟨0, by decide⟩)]

/-- Both calls return, preserve the live local, and charge spills and final halt. -/
theorem nested_correct (rho : RandomMemory 8) (regs : Registers 8 4) (mem : DataMemory 8) :
    let r := run nested rho 20 (.initial regs mem)
    r.reason = .halted ∧ r.steps = 14 ∧ r.state.regs 2 = word 8 17 ∧
    r.state.regs 1 = word 8 7 ∧
    r.trace = [.dataWrite (word 8 100) (word 8 2),
      .dataWrite (word 8 101) (word 8 7),
      .dataRead (word 8 101) (word 8 7), .dataRead (word 8 100) (word 8 2)] := by
  simp [nested, run, step, State.initial, State.put, Operand.eval, update,
    RunResult.prepend, word]

/-- The low-level ISA deliberately wraps overflowing saved links. -/
theorem link_wraps :
    let p : Program 1 := (Array.replicate 15 .halt).push (.call 0 3)
    let s : State 4 1 := { State.zero 4 1 with pc := 15 }
    match step p (zeroMemory 4) s with
    | .next t none => t.pc = 3 ∧ t.regs 0 = 0
    | _ => False := by
  change 3 = 3 ∧ word 4 16 = 0
  decide

/-- Indirectly jumping outside code faults on the following fetch, not the jump. -/
theorem invalid_computed_pc :
    let r := run (#[.jumpReg (.imm 7)] : Program 1) (zeroMemory 4) 2 (State.zero 4 1)
    r.reason = .fault (.invalidPC 7) ∧ r.steps = 1 := by decide

/-- Direct-call labels are resolved without expanding the callee. -/
theorem symbolic_call : Assembly.compile 0 ([.instruction (.call 0 9), .instruction (.emit .halt),
    .label 9, .instruction (.emit (.jumpReg (.reg 0)))] : List (Assembly.Item 1 Nat)) =
    some #[.call 0 2, .halt, .jumpReg (.reg 0)] := by decide

end CallExamples
end WordRam
