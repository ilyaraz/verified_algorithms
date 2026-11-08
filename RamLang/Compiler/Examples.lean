import RamLang.Compiler.Link
import RamLang.Examples
import WordRam.Execution

namespace RamLang.Compiler.Examples
open WordRam ABI

/-- Dirty initial registers and RAM exercise initialization rather than assuming it. -/
def initial (base capacity : Nat) (args : List (Word 8)) : State 8 registers :=
  .initial (fun r =>
    if r.val = 0 then word 8 base
    else if r.val = 2 then word 8 (base+capacity)
    else if 12 ≤ r.val then args[r.val-12]?.getD (word 8 213)
    else word 8 213) (fun _ => word 8 213)

/-- Observe a compiled run without discarding compiler failure. -/
def execute (p : Program) (base capacity fuel : Nat) (args : List (Word 8)) :
    Except CompileError (WordRam.RunResult 8 registers) := do
  let c ← compile p
  return WordRam.run c.code (zeroMemory 8) fuel (initial base capacity args)

/-- Finite summary suitable for kernel-checked execution examples. -/
def summary (p : Program) (base capacity fuel : Nat) (args : List (Word 8)) :
    Option (StopReason × Nat × Nat × Nat × Nat × Bool) :=
  match execute p base capacity fuel args with
  | .error _ => none
  | .ok r => some (r.reason, (r.state.regs status).toNat, (r.state.regs result).toNat,
      (r.state.regs sp).toNat, r.steps,
      r.trace.all (fun e => e.dataAddress.all (fun a => base ≤ a.toNat && a.toNat < base+capacity)))

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-- The recursive body occurs once; its physical frame contains five words. -/
theorem sum_layout :
    ((compile RamLang.Examples.sum).toOption.map (fun c =>
      (c.code.size, c.functions))) = some (65, [⟨14, 51, 5⟩]) := by decide

/-- Exact capacity succeeds, restores sp, and preserves a local across recursion. -/
theorem sum_exact_fit :
    summary RamLang.Examples.sum 100 25 1000 [word 8 4] =
      some (.halted, 1, 10, 100, 197, true) := by decide

/-- One word short halts before writing the next frame; all accesses fit. -/
theorem sum_one_word_short :
    summary RamLang.Examples.sum 100 24 1000 [word 8 4] =
      some (.halted, 2, 213, 120, 108, true) := by decide

/-- Entry exhaustion likewise checks before storing even the frame header. -/
theorem entry_exhaustion :
    summary RamLang.Examples.sum 100 4 1000 [word 8 4] =
      some (.halted, 2, 213, 100, 6, true) := by decide

/-- Mutually recursive bodies link in both directions and share a fixed register file. -/
theorem mutual_recursion :
    summary RamLang.Examples.parity 100 28 1000 [word 8 6] =
      some (.halted, 1, 1, 100, 217, true) := by decide

/-- Early return skips unreachable application stores and restores the wrapper frame. -/
theorem early_return :
    summary RamLang.Examples.earlyReturn 100 2 1000 [] =
      some (.halted, 1, 7, 100, 22, true) := by decide

/-- Two calls use the same released stack reservation, retaining the first result. -/
def reuse : Program := ⟨#[RamLang.Examples.sumFunction,
  ⟨"twice", ["n"], ["first", "second"],
    .seq (.call 1 0 [.local 0])
      (.seq (.call 2 0 [.local 0])
        (.seq (.primitive (.binary 1 .add (.local 1) (.local 2))) (.ret (.local 1))))⟩], 1⟩

theorem stack_reuse :
    summary reuse 100 30 1000 [word 8 4] = some (.halted, 1, 20, 100, 423, true) := by decide

/-- A counter loop exercises both the backward jump and the false exit branch. -/
def fill : Program := ⟨#[⟨"fill", ["p", "n"], [],
  .seq (.while ⟨.ne, .local 1, .literal 0⟩
    (.seq (.primitive (.store (.local 0) (.literal 7)))
      (.seq (.primitive (.binary 0 .add (.local 0) (.literal 1)))
        (.primitive (.binary 1 .sub (.local 1) (.literal 1)))))) (.ret (.literal 0))⟩], 0⟩

/-- Application writes are retained by projection; all compiler stack accesses disappear. -/
theorem fill_loop :
    ((execute fill 100 4 200 [word 8 40, word 8 3]).toOption.map (fun r =>
      (r.reason, r.steps, projectTrace ⟨100, 4⟩ r.trace,
        (List.range 4).map (fun i => (r.state.mem (word 8 (40+i))).toNat)))) =
      some (.halted, 91, [.dataWrite (word 8 40) (word 8 7),
        .dataWrite (word 8 41) (word 8 7), .dataWrite (word 8 42) (word 8 7)], [7,7,7,213]) := by decide

end RamLang.Compiler.Examples
