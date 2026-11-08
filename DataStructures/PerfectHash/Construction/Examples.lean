import DataStructures.PerfectHash.Construction.Refinement

namespace PerfectHash.Construction.Examples
open WordRam Registers

set_option maxRecDepth 65536
set_option maxHeartbeats 10000000

/-- The root receives eight distinct full-word keys and dirty directory/nodes. -/
def rootMemory : DataMemory 10 := fun a =>
  if 8 ≤ a.toNat ∧ a.toNat < 16 then word 10 (a.toNat-8) else word 10 1023

def rootRegisters (seedValue : Nat) : Registers 10 64 := fun r => word 10 <|
  if r.val = 0 then 8 else if r.val = 1 then 8 else if r.val = 2 then 100
  else if r.val = 3 then 200 else if r.val = 4 then 10 else if r.val = 5 then seedValue
  else if r.val = 6 then 7 else if r.val = 22 then 8 else 1023

def rootRun (seedValue : Nat) : RunResult 10 64 :=
  run Root.program (zeroMemory 10) 1000 (.initial (rootRegisters seedValue) rootMemory)

theorem root_rejection : (rootRun 1).reason = .halted ∧ (rootRun 1).steps = 328 ∧
    (rootRun 1).state.regs status = word 10 0 ∧
    (rootRun 1).state.mem (word 10 100) = word 10 6 := by decide

theorem root_acceptance : (rootRun 23).reason = .halted ∧ (rootRun 23).steps = 369 ∧
    (rootRun 23).state.regs status = word 10 1 ∧
    (rootRun 23).state.mem (word 10 100) = word 10 6 ∧
    (rootRun 23).state.mem (word 10 101) = word 10 6 := by decide

def childRegisters (seedValue : Nat) : Registers 10 64 := fun r => word 10 <|
  if r.val = 3 then 200 else if r.val = 5 then seedValue else if r.val = 6 then 3
  else if r.val = 21 then 400 else if r.val = 23 then 128 else if r.val = 27 then 6 else 1023

def childRun (seedValue : Nat) : RunResult 10 64 :=
  run Child.program (zeroMemory 10) 2000
    (.initial (childRegisters seedValue) (rootRun 23).state.mem)

theorem child_rejection : (childRun 1).reason = .halted ∧ (childRun 1).steps = 1314 ∧
    (childRun 1).state.regs status = word 10 0 ∧
    (childRun 1).state.mem (word 10 700) = word 10 1023 := by decide

theorem child_acceptance : (childRun 9).reason = .halted ∧ (childRun 9).steps = 1389 ∧
    (childRun 9).state.regs status = word 10 1 ∧
    (childRun 9).state.mem (word 10 400) = word 10 1 ∧
    (childRun 9).state.mem (word 10 401) = word 10 0 ∧
    (childRun 9).state.mem (word 10 411) = word 10 5 := by decide

def allocationRegisters (dir tableBase : Nat) : Registers 10 64 := fun r => word 10 <|
  if r.val = 4 then 10 else if r.val = 12 then dir else if r.val = 21 then tableBase else 1023

def allocationRun (dir tableBase : Nat) : RunResult 10 64 :=
  run Allocation.program (zeroMemory 10) 100
    (.initial (allocationRegisters dir tableBase) (rootRun 23).state.mem)

theorem allocation_boundary : (allocationRun 100 767).reason = .halted ∧
    (allocationRun 100 767).steps = 46 ∧
    (allocationRun 100 767).state.regs slots = word 10 128 ∧
    (allocationRun 100 767).state.regs tableEnd = word 10 1023 ∧
    (allocationRun 100 767).state.mem (word 10 102) = word 10 3 ∧
    (allocationRun 100 767).state.mem (word 10 103) = word 10 767 := by decide

theorem allocation_empty : (allocationRun 108 1023).reason = .halted ∧
    (allocationRun 108 1023).steps = 13 ∧
    (allocationRun 108 1023).state.regs slots = word 10 0 ∧
    (allocationRun 108 1023).state.regs tableEnd = word 10 1023 := by decide

def singletonMemory : DataMemory 10 := fun a => if a.toNat = 201 then word 10 0 else word 10 1023

def singletonRegisters : Registers 10 64 := fun r => word 10 <|
  if r.val = 3 then 200 else if r.val = 5 then 1 else if r.val = 6 then 10
  else if r.val = 21 then 1021 else if r.val = 23 then 1 else if r.val = 27 then 1 else 1023

def singletonRun : RunResult 10 64 :=
  run Child.program (zeroMemory 10) 40 (.initial singletonRegisters singletonMemory)

theorem maximum_word : singletonRun.reason = .halted ∧ singletonRun.steps = 34 ∧
    singletonRun.state.regs status = word 10 1 ∧
    singletonRun.state.mem (word 10 1021) = word 10 1 ∧
    singletonRun.state.mem (word 10 1022) = word 10 1023 := by decide

def largeRootMemory : DataMemory 14 := fun a =>
  if 1000 ≤ a.toNat ∧ a.toNat < 1128 then word 14 (a.toNat-1000) else word 14 16383

def largeRootRegisters : Registers 14 64 := fun r => word 14 <|
  if r.val = 0 then 1000 else if r.val = 1 then 128 else if r.val = 2 then 2000
  else if r.val = 3 then 3000 else if r.val = 4 then 14 else if r.val = 5 then 1
  else if r.val = 6 then 7 else if r.val = 22 then 128 else 16383

def largeRootRun : RunResult 14 64 :=
  run Root.program (zeroMemory 14) 3500 (.initial largeRootRegisters largeRootMemory)

/-- Here d squared does not fit in one word, but the rejected trial is safe. -/
theorem rejected_before_overflow : 64*(128+1) < modulus 14 ∧ ¬ 128^2 < modulus 14 ∧
    largeRootRun.reason = .halted ∧ largeRootRun.steps = 3253 ∧
    largeRootRun.state.regs status = word 14 0 ∧
    largeRootRun.state.regs budget = word 14 39 ∧
    largeRootRun.state.mem (word 14 2000) = word 14 27 := by decide

theorem tiny_enumeration :
    (run Enumeration.program (zeroMemory 4) 25 (.zero 4 64)).reason = .halted ∧
    (run Enumeration.program (zeroMemory 4) 25 (.zero 4 64)).state.regs seed = word 4 1 ∧
    (run Enumeration.program (zeroMemory 4) 25 (.zero 4 64)).trace = [] := by decide

end PerfectHash.Construction.Examples
