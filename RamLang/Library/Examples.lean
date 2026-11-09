import RamLang.Library.Fill
import RamLang.Library.Copy
import RamLang.Library.RetryExample
import RamLang.DSL.Examples

set_option maxRecDepth 10000

namespace RamLang.Library.Fixtures
open WordRam Compiler ABI

/-- Observe arbitrary initial application RAM and random images with dirty
registers and stack slots, preserving compile errors as explicit outcomes. -/
def execute (p : Program) (rho : RandomMemory 8) (mem : DataMemory 8)
    (base capacity fuel : Nat) (args : List (Word 8)) : Except CompileError (WordRam.RunResult 8 registers) := do
  let c ← compile p
  let s := Compiler.Examples.initial base capacity args
  return WordRam.run c.code rho fuel {s with mem := mem}

/-- Distinct source values make load/store ordering and actual copying observable. -/
def copyMemory : DataMemory 8 := fun a =>
  if a.toNat = 40 then word 8 11 else if a.toNat = 41 then word 8 22
  else if a.toNat = 42 then word 8 33 else word 8 213

/-- Two possible successes follow a rejected sample; only the first is consumed. -/
def retryImage : RandomMemory 8 := fun a =>
  if a.toNat = 11 then word 8 7 else if a.toNat = 12 then word 8 9 else word 8 0

/-- Copy executes with an exact-fit stack, initializes dirty destination cells,
and retains the original source words and both boundary cells. -/
theorem copy_execution :
    ((execute Copy.program (zeroMemory 8) copyMemory 100 6 200
      [word 8 50,word 8 40,word 8 3]).toOption.map (fun r =>
      (r.reason,r.steps,(List.range 4).map (fun i => (r.state.mem (word 8 (50+i))).toNat),
        (List.range 3).map (fun i => (r.state.mem (word 8 (40+i))).toNat)))) =
      some (.halted,129,[11,22,33,213],[11,22,33]) := by decide

/-- Bounded retry stops after the second sample succeeds, without touching the
third random address or any application-memory cell. -/
theorem retry_success :
    ((execute FirstNonzero.program retryImage copyMemory 100 5 200
      [word 8 3,word 8 10]).toOption.map (fun r =>
      (r.reason,r.steps,(r.state.regs status).toNat,(r.state.regs result).toNat,
        projectTrace ⟨100,5⟩ r.trace))) =
      some (.halted,70,1,7,[.randomRead (word 8 10) (word 8 0),.randomRead (word 8 11) (word 8 7)]) := by decide

/-- Budget failure returns zero with runtime success status, distinctly from
stack exhaustion, after exactly the reserved three sample addresses. -/
theorem retry_budget_failure :
    ((execute FirstNonzero.program (zeroMemory 8) copyMemory 100 5 200
      [word 8 3,word 8 10]).toOption.map (fun r =>
      (r.reason,r.steps,(r.state.regs status).toNat,(r.state.regs result).toNat,
        Retry.randomAddresses r.trace))) =
      some (.halted,109,1,0,[word 8 10,word 8 11,word 8 12]) := by decide

/-- Rich loop-condition reads are reevaluated after each mutable-memory update,
while body expressions retain their specified left-to-right evaluation order. -/
theorem rich_loop :
    ((execute DSL.Examples.richLoop (zeroMemory 8) (fun _ => word 8 2) 100 10 250
      [word 8 40]).toOption.map (fun r =>
      (r.reason,(r.state.regs result).toNat,projectTrace ⟨100,10⟩ r.trace))) =
      some (.halted,9,[.dataRead (word 8 40) (word 8 2),.dataRead (word 8 40) (word 8 2),
        .dataWrite (word 8 40) (word 8 1),.dataRead (word 8 40) (word 8 1),
        .dataRead (word 8 40) (word 8 1),.dataWrite (word 8 40) (word 8 0),
        .dataRead (word 8 40) (word 8 0)]) := by decide

end RamLang.Library.Fixtures
