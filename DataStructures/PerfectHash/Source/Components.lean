import DataStructures.PerfectHash.Source.Root
import DataStructures.PerfectHash.Source.Child
import DataStructures.PerfectHash.Source.Allocation
import Algorithms.Dedup.Source.Pass
import Hashing.Source.Sampling
import RamLang.Logic.EarlyReturn

namespace PerfectHash.Source.Components
open WordRam RamLang RamLang.Compiler RamLang.ABI
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000
set_option synthInstance.maxSize 256

/-- Finite fixture cells over dirty ordinary memory. Unspecified words contain
the maximum key value, so accidental reliance on initially empty RAM is visible. -/
def memory (cells : List (Nat × Nat)) : DataMemory 12 := fun a =>
  word 12 ((cells.find? (fun p => p.1 == a.toNat)).map Prod.snd |>.getD 4095)

/-- Execute a component through its real entry wrapper and ordinary call stack.
The component drivers unpack configuration cells; the reusable contracts above
apply directly to their callable bodies in a larger constructor. -/
def execute (p : RamLang.Program) (mem : DataMemory 12) (args : List Nat) (capacity : Nat) :
    Except CompileError (WordRam.RunResult 12 registers) := do
  let c ← compile p
  let s : State 12 registers := .initial (fun r =>
    if r.val = 0 then word 12 3000 else if r.val = 2 then word 12 (3000+capacity)
    else if 12 ≤ r.val then word 12 (args[r.val-12]?.getD 4095) else word 12 4095) mem
  return WordRam.run c.code (fun _ => word 12 4095) 12000 s

/-- Observe status separately from the algorithm's zero/one result, together
with exact instruction work, selected memory cells, and random-read addresses. -/
def observe (p : RamLang.Program) (cells : List (Nat × Nat)) (args : List Nat)
    (capacity : Nat) (probes : List Nat) :=
  (execute p (memory cells) args capacity).toOption.map (fun r =>
    (r.reason,r.steps,(r.state.regs status).toNat,(r.state.regs result).toNat,
      probes.map (fun a => (r.state.mem (word 12 a)).toNat),r.randomAddresses.map BitVec.toNat))

/-- Zero, maximum keys, and duplicates exercise full-key deduplication. -/
def duplicateCells : List (Nat × Nat) :=
  [(0,0),(1,4095),(2,0),(3,7),(4,4095),(200,0),(201,5),(202,100),(203,8)]

/-- A successful root trial uses the same keys but a distinct node reservation. -/
def rootCells : List (Nat × Nat) := duplicateCells ++ [(204,8)]

/-- A chain with three distinct child slots, surrounded by completed siblings. -/
def childCells : List (Nat × Nat) :=
  [(200,300),(201,3),(202,500),(203,8),(300,0),(301,0),(302,1024),(303,1),(304,4095),(305,2),
   (499,777),(516,888)]

/-- Duplicate removal retains input order in the compact array, including zero
and the maximum key, and leaves the first unused compact word dirty. -/
theorem dedup_execution : observe Dedup.Source.Pass.program duplicateCells [200,1,9] 100
    [0,1,2,3,4,122,123,124,125] =
    some (.halted,1063,1,3,[0,4095,0,7,4095,0,4095,7,4095],[]) := by decide

/-- Grouping uses one-based heads and retains every full key, including duplicates. -/
theorem root_success : observe Root.program ([(203,300)] ++ rootCells) [200,1,9] 100
    [100,101,128,129,300,302,304,306,308] =
    some (.halted,1642,1,1,[3,4,2,5,0,4095,0,7,4095],[]) := by decide

/-- The seventh colliding key would exceed the energy allowance. It is rejected
before insertion; the unused seventh node remains dirty and status is success. -/
theorem root_rejection : observe Root.program
    [(0,0),(1,1),(2,2),(3,3),(4,4),(5,5),(6,6),(200,0),(201,7),(202,100),(203,300),(204,1)]
    [200,1,12] 100 [100,101,310,312] =
    some (.halted,1232,1,0,[6,6,5,4095],[]) := by decide

/-- Successful insertion initializes occupancy, handles both extreme keys and
preserves the linked nodes and both neighboring completed-table cells. -/
theorem child_success : observe Child.program childCells [200,1,9] 100
    [499,500,501,504,505,514,515,516,300,304] =
    some (.halted,777,1,1,[777,1,0,1,1024,1,4095,888,0,4095],[]) := by decide

/-- A collision rejects without overwriting the first occupied slot or either
neighboring sibling. Ordinary failure remains distinct from stack exhaustion. -/
theorem child_rejection : observe Child.program ([(201,2),(302,1)] ++ childCells) [200,1,9] 100
    [499,500,501,516,300,302] = some (.halted,652,1,0,[777,1,1,888,0,1],[]) := by decide

/-- Exact stack capacity allows a nested rounding call. The two initialized
directory fields describe thirty-two slots and leave existing table data alone. -/
theorem allocation_exact_stack : observe Allocation.program [(100,3),(101,99),(500,777)]
    [100,500,12] 20 [100,101,102,103,500] = some (.halted,222,1,564,[3,99,7,500,777],[]) := by decide

/-- One word short reaches runtime exhaustion before rounding or directory
writes; the algorithm result register is not mistaken for a failure return. -/
theorem allocation_short_stack : observe Allocation.program [(100,3),(101,99),(500,777)]
    [100,500,12] 19 [100,101,102,103,500] = some (.halted,52,2,4095,[3,99,4095,4095,777],[]) := by decide

/-- Compiled component drivers emit each helper once, with fixed frame sizes.
The public constructor later links the callable functions in one shared table. -/
theorem layouts : [Root.program,Child.program,Dedup.Source.Pass.program,Allocation.program].map (fun p =>
    (compile p).toOption.map (fun c => (c.code.size,c.functions.map (fun f => f.frameWords)))) =
    [some (349,[15,29,5]),some (264,[13,21,5]),some (423,[13,26,5,7,10]),some (154,[14,6])] := by decide

end PerfectHash.Source.Components
