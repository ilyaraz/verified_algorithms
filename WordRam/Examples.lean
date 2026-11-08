import WordRam.Properties

/-! Small assembly programs, with kernel-checked boundary cases. -/
namespace WordRam.Examples

-- Explicit bounded constructors keep these program constants axiom-free.
private def r0 {n : Nat} : Reg (n+1) := ⟨0, Nat.zero_lt_succ n⟩
private def r1 : Reg 2 := ⟨1, by decide⟩

/-- Arithmetic aliases the destination with its first source. -/
def arithmetic : Program 1 := #[
  .mov r0 (.imm 255),
  .add r0 (.reg r0) (.imm 1),
  .sub r0 (.reg r0) (.imm 1),
  .mul r0 (.reg r0) (.imm 2),
  .mod r0 (.reg r0) (.imm 0),
  .halt]

theorem arithmetic_check :
    let r := run arithmetic (zeroMemory 8) 6 (State.zero 8 1)
    r.reason = .halted ∧ r.steps = 6 ∧ r.state.regs 0 = word 8 254 := by decide

def mulMod : Program 1 := #[
  .mul r0 (.imm 7) (.imm 3),
  .mod r0 (.reg r0) (.imm 5),
  .halt]

theorem mulMod_overflow :
    (run mulMod (zeroMemory 4) 3 (State.zero 4 1)).state.regs 0 = word 4 0 := by decide

theorem mulMod_fits :
    (run mulMod (zeroMemory 8) 3 (State.zero 8 1)).state.regs 0 = word 8 1 := by decide

/-- The store affects ordinary memory, while the two random reads agree. -/
def randomRoundTrip : Program 2 := #[
  .rload r0 (.imm 3),
  .store (.imm 3) (.imm 99),
  .rload r1 (.imm 3),
  .halt]

theorem randomRoundTrip_spec (rho : RandomMemory w) (regs : Registers w 2)
    (mem : DataMemory w) :
    let r := run randomRoundTrip rho 4 (.initial regs mem)
    r.reason = .halted ∧ r.steps = 4 ∧
      r.state.regs 0 = rho (word w 3) ∧ r.state.regs 1 = rho (word w 3) ∧
      r.state.mem (word w 3) = word w 99 := by
  simp [run, step, randomRoundTrip, State.initial, State.put, Operand.eval,
    update, RunResult.prepend, r0, r1]

theorem randomRoundTrip_resources :
    let r := run randomRoundTrip (fun a => a + 1) 4 (State.zero 8 2)
    r.randomReads = 2 ∧ r.randomFootprint.length = 1 ∧ r.randomBitsExposed = 8 ∧
      r.dataFootprint.length = 1 ∧ r.writeFootprint.length = 1 := by decide

def countdown : Program 1 := #[
  .branch .eq (.reg r0) (.imm 0) 3,
  .sub r0 (.reg r0) (.imm 1),
  .jump 0,
  .halt]

theorem countdown_three :
    let r := run countdown (zeroMemory 4) 20 (.initial (fun _ => word 4 3) (zeroMemory 4))
    r.reason = .halted ∧ r.steps = 11 ∧ r.state.regs 0 = word 4 0 := by decide

theorem countdown_exact_budget :
    (run countdown (zeroMemory 4) 10 (.initial (fun _ => word 4 3) (zeroMemory 4))).reason =
      .fuelExhausted := by decide

def spin : Program 0 := #[.jump 0]

theorem spin_diverges (rho : RandomMemory w) (s : State w 0) (hpc : s.pc = 0) :
    Diverges spin rho s := by
  intro fuel
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
    simpa [run, step, spin, hpc, RunResult.prepend] using
      ih { s with pc := 0 } rfl

def branchExample (cmp : Comparison) (x y : Nat) : Program 1 := #[
  .branch cmp (.imm x) (.imm y) 3,
  .mov r0 (.imm 7), .halt,
  .mov r0 (.imm 9), .halt]

def branchResult (cmp : Comparison) (x y : Nat) : Nat :=
  (run (branchExample cmp x y) (zeroMemory 8) 3 (State.zero 8 1)).state.regs 0 |>.toNat

theorem branch_checks :
    branchResult .eq 4 4 = 9 ∧ branchResult .eq 4 5 = 7 ∧
    branchResult .ne 4 5 = 9 ∧ branchResult .ne 4 4 = 7 ∧
    branchResult .lt 127 128 = 9 ∧ branchResult .lt 128 127 = 7 ∧
    branchResult .le 4 4 = 9 ∧ branchResult .le 5 4 = 7 := by decide

theorem load_alias :
    let p : Program 1 := #[.mov r0 (.imm 5), .load r0 (.reg r0), .halt]
    (run p (zeroMemory 8) 3 (.initial (fun _ => 0) (fun a => a + 2))).state.regs 0 =
      word 8 7 := by decide

theorem random_load_alias :
    let p : Program 1 := #[.mov r0 (.imm 5), .rload r0 (.reg r0), .halt]
    (run p (fun a => a + 2) 3 (State.zero 8 1)).state.regs 0 = word 8 7 := by decide

theorem store_alias :
    let p : Program 1 := #[.mov r0 (.imm 5), .store (.reg r0) (.reg r0), .halt]
    (run p (zeroMemory 8) 3 (State.zero 8 1)).state.mem (word 8 5) = word 8 5 := by decide

theorem zero_fuel_halt :
    let r := run (#[.halt] : Program 0) (zeroMemory 8) 0 (State.zero 8 0)
    r.reason = .fuelExhausted ∧ r.steps = 0 := by decide

theorem one_fuel_halt :
    let r := run (#[.halt] : Program 0) (zeroMemory 8) 1 (State.zero 8 0)
    r.reason = .halted ∧ r.steps = 1 := by decide

theorem empty_fault :
    let r := run (#[] : Program 0) (zeroMemory 8) 1 (State.zero 8 0)
    r.reason = .fault (.invalidPC 0) ∧ r.steps = 0 := by decide

theorem fallthrough_fault :
    let r := run (#[.mov r0 (.imm 42)] : Program 1) (zeroMemory 8) 2 (State.zero 8 1)
    r.reason = .fault (.invalidPC 1) ∧ r.steps = 1 ∧ r.state.regs 0 = word 8 42 := by decide

theorem jump_exhausted :
    let r := run (#[.jump 99] : Program 0) (zeroMemory 8) 1 (State.zero 8 0)
    r.reason = .fuelExhausted ∧ r.steps = 1 ∧ r.state.pc = 99 := by decide

theorem jump_fault :
    let r := run (#[.jump 99] : Program 0) (zeroMemory 8) 2 (State.zero 8 0)
    r.reason = .fault (.invalidPC 99) ∧ r.steps = 1 := by decide

theorem fault_keeps_store :
    let p : Program 0 := #[.store (.imm 5) (.imm 42), .jump 99]
    let r := run p (zeroMemory 8) 3 (State.zero 8 0)
    r.reason = .fault (.invalidPC 99) ∧ r.steps = 2 ∧
      r.state.mem (word 8 5) = word 8 42 ∧
      r.trace = [.dataWrite (word 8 5) (word 8 42)] := by decide

theorem exhausted_keeps_store :
    let p : Program 0 := #[.store (.imm 5) (.imm 42), .halt]
    let r := run p (zeroMemory 8) 1 (State.zero 8 0)
    r.reason = .fuelExhausted ∧ r.steps = 1 ∧
      r.state.mem (word 8 5) = word 8 42 ∧
      r.trace = [.dataWrite (word 8 5) (word 8 42)] := by decide

theorem zero_width :
    (run arithmetic (zeroMemory 0) 6 (State.zero 0 1)).state.regs 0 = word 0 0 := by decide

end WordRam.Examples
