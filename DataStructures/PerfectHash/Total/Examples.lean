import DataStructures.PerfectHash.Total.Contract
import DataStructures.PerfectHash.Bounded.Examples

namespace PerfectHash.Total.Examples
open WordRam
open Bounded.Examples

set_option maxRecDepth 65536
set_option maxHeartbeats 100000000

/-- Multiplication by three clusters seven distinct keys; multiplier one is an
accepted root. Zero and the maximum word are both real dictionary keys. -/
def fallbackKeys : List (Word 12) := [0,2731,1366,1,2732,1367,2,4095,0,4095,0]

def execute (xs : List (Word 12)) (l : Layout) (rho : RandomMemory 12) : RunResult 12 64 :=
  run Total.program rho 100000 (.initial
    (buildRegisters 12 xs.length l (fun _ => word 12 4095)) (memory xs l))

def rootImage : RandomMemory 12 := fun a =>
  if 1 ≤ a.toNat ∧ a.toNat ≤ 12 then word 12 2 else word 12 128

def emptyBudgetState : State 12 64 := ⟨86,
  (fun r => if r.val = 32 ∨ r.val = 34 ∨ r.val = 40 then word 12 0 else word 12 4095),
  (fun _ => word 12 4095)⟩

/-- Exhaustion executes the first enumerated seed, without an additional sample
or a failure halt. This small control-flow check is kernel reduced. -/
theorem zero_budget_enters_enumeration :
    (run Total.program (zeroMemory 12) 7 emptyBudgetState).reason = .fuelExhausted ∧
    (run Total.program (zeroMemory 12) 7 emptyBudgetState).state.pc = 93 ∧
    (run Total.program (zeroMemory 12) 7 emptyBudgetState).state.regs Construction.Registers.seed = word 12 1 ∧
    (run Total.program (zeroMemory 12) 7 emptyBudgetState).randomReads = 0 := by decide

/-- Integration checks evaluate the same proved interpreter and instruction
array. They report errors, rather than introducing native proof axioms. -/
def checkRun (name : String) (xs : List (Word 12)) (l : Layout) (rho : RandomMemory 12)
    (steps distinct : Nat) (addresses : List (Addr 12)) (queries : List (Word 12)) (answers : List Nat) : IO Unit := do
  let r := execute xs l rho
  unless decide (r.reason = .halted) && decide (r.steps = steps) &&
      decide (r.state.regs Construction.Registers.status = word 12 1) &&
      decide ((r.state.regs Construction.Registers.directory).toNat = distinct) &&
      decide (r.randomAddresses = addresses) do
    throw (IO.userError (name ++ ": construction result mismatch"))
  let actual := queries.map (fun q => (queryAnswer r (overwritten r) q).toNat)
  unless decide (actual = answers) do
    throw (IO.userError (name ++ ": query-after-overwrite mismatch"))
  IO.println (name ++ ": passed (" ++ toString r.steps ++ " instructions)")

#eval checkRun "root and child fallback" fallbackKeys (canonicalLayout fallbackKeys.length) rootImage
  23294 8 (((List.range 14)++List.range' 37 12++List.range' 73 12).map (word 12))
  [0,2731,1366,1,2732,1367,2,4095,3,42,4094] [1,1,1,1,1,1,1,1,0,0,0]

#eval checkRun "child fallback" [0,2731,0,2731] (canonicalLayout 4) (fun _ => word 12 2)
  1991 2 (([0,1]++List.range' 13 12).map (word 12)) [0,2731,1,4095] [1,1,0,0]

#eval checkRun "random success" repeatedKeys (canonicalLayout repeatedKeys.length) (fun _ => word 12 128)
  1981 8 [0,1,13,25] [0,1,2,3,4,5,6,7,8,4095] [1,1,1,1,1,1,1,1,0,0]

#eval checkRun "empty" [] (canonicalLayout 0) (fun _ => word 12 0)
  148 0 [0,1] [0,4095] [0,0]

#eval checkRun "all equal" (List.replicate 20 (word 12 4095)) (canonicalLayout 20) (fun _ => word 12 0)
  700 1 [0,1] [0,4095] [0,1]

#eval checkRun "near-end regions" [0,4095,0,4095] ⟨4000,2000,3000,3800⟩ (fun _ => word 12 0)
  413 2 [3800,3801] [0,4095,1,4094] [1,1,0,0]

end PerfectHash.Total.Examples
