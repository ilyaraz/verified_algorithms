import DataStructures.PerfectHash.Bounded.Interface

namespace PerfectHash.Bounded.Examples
open WordRam

set_option maxRecDepth 65536
set_option maxHeartbeats 100000000

def repeatedKeys : List (Word 12) := [0,1,2,3,4,5,6,7,0,7,0]

def memory (xs : List (Word 12)) (l : Layout) : DataMemory 12 := fun a =>
  if l.inputBase ≤ a.toNat then xs[a.toNat-l.inputBase]?.getD (word 12 4095) else word 12 4095

def execute (xs : List (Word 12)) (l : Layout) (rho : RandomMemory 12) : RunResult 12 64 :=
  run program rho 7000 (.initial (buildRegisters 12 xs.length l (fun _ => word 12 4095)) (memory xs l))

def goodRun : RunResult 12 64 := execute repeatedKeys (canonicalLayout repeatedKeys.length) (fun _ => word 12 128)

theorem repeated_success : goodRun.reason = .halted ∧ goodRun.steps = 1981 ∧
    goodRun.state.regs Construction.Registers.status = word 12 1 ∧
    StaticSet.readDescriptor goodRun.state.regs = ⟨11,164⟩ ∧
    goodRun.state.regs Construction.Registers.directory = word 12 8 ∧
    goodRun.randomAddresses = [0,1,13,25] := by decide

def queryAnswer (r : RunResult 12 64) (mem : DataMemory 12) (q : Word 12) : Word 12 :=
  (run Query.program (zeroMemory 12) Query.cost (.initial
    (fun i => if i.val = 0 then r.state.regs ⟨0,by decide⟩ else if i.val = 1 then r.state.regs ⟨1,by decide⟩
      else if i.val = 2 then q else word 12 4095) mem)).state.regs ⟨0,by decide⟩

theorem repeated_queries :
    ([0,1,2,3,4,5,6,7,8,9,4095] : List (Word 12)).map (queryAnswer goodRun goodRun.state.mem) =
      [1,1,1,1,1,1,1,1,0,0,0] := by decide

def overwritten (r : RunResult 12 64) : DataMemory 12 := fun a =>
  let desc := StaticSet.readDescriptor r.state.regs
  if desc.base ≤ a.toNat ∧ a.toNat < desc.base+desc.size then r.state.mem a else word 12 3333

theorem after_overwrite :
    ([0,7,8,4095] : List (Word 12)).map (queryAnswer goodRun (overwritten goodRun)) = [1,1,0,0] := by decide

def rootFailure : RunResult 12 64 := execute repeatedKeys (canonicalLayout repeatedKeys.length) (fun _ => word 12 0)

theorem root_budget_exhausted : rootFailure.reason = .halted ∧ rootFailure.steps = 4809 ∧
    rootFailure.state.regs Construction.Registers.status = word 12 0 ∧
    rootFailure.randomAddresses = (List.range 13).map (word 12) := by decide

def childFailure : RunResult 12 64 := execute repeatedKeys (canonicalLayout repeatedKeys.length)
  (fun a => if a.toNat ≤ 1 then word 12 128 else word 12 0)

theorem child_budget_exhausted : childFailure.reason = .halted ∧ childFailure.steps = 5224 ∧
    childFailure.state.regs Construction.Registers.status = word 12 0 ∧
    childFailure.randomAddresses = [0,1,13,14,15,16,17,18,19,20,21,22,23,24] := by decide

def lastRootAttempt : RunResult 12 64 := execute repeatedKeys (canonicalLayout repeatedKeys.length)
  (fun a => if a.toNat < 12 then word 12 0 else word 12 128)

theorem last_attempt_success : lastRootAttempt.reason = .halted ∧ lastRootAttempt.steps = 6023 ∧
    lastRootAttempt.state.regs Construction.Registers.status = word 12 1 ∧
    lastRootAttempt.randomAddresses = [0,1,2,3,4,5,6,7,8,9,10,11,12,13,25] := by decide

theorem zero_budget_no_read :
    let s : State 12 64 := ⟨location .rootChoose,fun r => if r.val = 32 then 0 else word 12 4095,fun _ => word 12 4095⟩
    (run program (zeroMemory 12) 3 s).reason = .halted ∧
    (run program (zeroMemory 12) 3 s).state.regs Construction.Registers.status = word 12 0 ∧
    (run program (zeroMemory 12) 3 s).trace = [] := by decide

def emptyRun : RunResult 12 64 := execute [] (canonicalLayout 0) (fun _ => word 12 0)

theorem empty_success : emptyRun.reason = .halted ∧ emptyRun.steps = 148 ∧
    StaticSet.readDescriptor emptyRun.state.regs = ⟨0,8⟩ ∧ emptyRun.randomAddresses = [0,1] ∧
    queryAnswer emptyRun emptyRun.state.mem 0 = 0 ∧ queryAnswer emptyRun emptyRun.state.mem 4095 = 0 := by decide

def equalRun : RunResult 12 64 := execute (List.replicate 20 (word 12 4095)) (canonicalLayout 20) (fun _ => word 12 0)

theorem all_equal_success : equalRun.reason = .halted ∧ equalRun.steps = 700 ∧
    StaticSet.readDescriptor equalRun.state.regs = ⟨20,10⟩ ∧ equalRun.randomAddresses = [0,1] ∧
    queryAnswer equalRun equalRun.state.mem 4095 = 1 ∧ queryAnswer equalRun equalRun.state.mem 0 = 0 := by decide

def boundaryRun : RunResult 12 64 := execute [0,4095,0,4095] ⟨4000,2000,3000,3800⟩ (fun _ => word 12 0)

theorem boundary_admissible : Admissible 12 4 ⟨4000,2000,3000,3800⟩ := by
  constructor
  · constructor <;> simp [Layout.input, Layout.output, Layout.scratch,
      dictionaryCapacity, workspaceCapacity, Region.Fits, Region.Separated, modulus]
  · constructor <;> decide
  · simp [RandomFit, Layout.random, randomCapacity, bucketCapacity, Region.Fits, modulus]

theorem boundary_success : boundaryRun.reason = .halted ∧ boundaryRun.steps = 413 ∧
    StaticSet.readDescriptor boundaryRun.state.regs = ⟨2000,16⟩ ∧ boundaryRun.randomAddresses = [3800,3801] ∧
    ([0,4095,1,4094] : List (Word 12)).map (queryAnswer boundaryRun (overwritten boundaryRun)) = [1,1,0,0] := by decide

end PerfectHash.Bounded.Examples
