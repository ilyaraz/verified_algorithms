import DataStructures.PerfectHash.Source.Bounded.Interface

namespace PerfectHash.Source.Bounded.Examples
open WordRam RamLang
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000

/-- Repeated full-word keys exercise computed deduplication before grouping. -/
def repeatedKeys : List (Word 12) := [0,1,2,3,4,5,6,7,0,7,0]

/-- Every cell outside the supplied occurrence array initially contains the
maximum word, including every application workspace and stack word. -/
def memory (xs : List (Word 12)) (l : Layout) : DataMemory 12 := fun a =>
  if l.inputBase ≤ a.toNat then xs[a.toNat-l.inputBase]?.getD (word 12 4095) else word 12 4095

/-- Run the actual compiled public constructor from its original input ABI. -/
def execute (xs : List (Word 12)) (l : Layout) (rho : RandomMemory 12) : WordRam.RunResult 12 64 :=
  WordRam.run program rho 100000 (.initial (buildRegisters 12 xs.length l (fun _ => word 12 4095)) (memory xs l))

/-- Release and overwrite every ordinary word outside the retained extent. -/
def overwritten (r : WordRam.RunResult 12 64) : DataMemory 12 := fun a =>
  let desc := StaticSet.readDescriptor r.state.regs
  if desc.base ≤ a.toNat ∧ a.toNat < desc.base+desc.size then r.state.mem a else word 12 3333

/-- The query uses ordinary calls on the released, overwritten construction
stack and returns the full source-query result for inspection. -/
def query (r : WordRam.RunResult 12 64) (l : Layout) (N : Nat) (key : Word 12) : WordRam.RunResult 12 ABI.registers :=
  let stack := Entry.stack l N
  WordRam.run Query.compiled.code (fun _ => word 12 777) Query.cost (.initial (fun reg =>
    if reg.val = 0 then word 12 stack.base else if reg.val = 2 then word 12 (stack.base+stack.size)
    else if reg.val = 12 then r.state.regs ⟨0,by decide⟩ else if reg.val = 13 then key else word 12 4095)
    (overwritten r))

/-- Integration observations include exact instruction work and the actual
addressed random schedule. These evaluate the same interpreter as the theorems. -/
def observe (xs : List (Word 12)) (l : Layout) (rho : RandomMemory 12) :=
  let r := execute xs l rho
  (r.reason,r.steps,(r.state.regs ⟨18,by decide⟩).toNat,(r.state.regs ⟨2,by decide⟩).toNat,
    StaticSet.readDescriptor r.state.regs,r.randomAddresses.map BitVec.toNat)

/-- Executable regression checks report errors and introduce no proof axioms.
All runs check normal runtime status, exact work, algorithm outcome, descriptor,
random addresses, unchanged input and sentinel, and queries after overwrite. -/
def checkRun (name : String) (xs : List (Word 12)) (l : Layout) (rho : RandomMemory 12)
    (steps status distinct extent : Nat) (addresses : List Nat) (keys : List (Word 12)) (answers : List Nat) : IO Unit := do
  let r := execute xs l rho
  let desc := StaticSet.readDescriptor r.state.regs
  unless decide (r.reason = .halted) && decide (r.steps = steps) &&
      decide (r.state.regs ⟨5,by decide⟩ = word 12 1) &&
      decide (r.state.regs ⟨18,by decide⟩ = word 12 status) &&
      decide (r.state.regs ⟨2,by decide⟩ = word 12 distinct) &&
      decide (desc = ⟨if status = 1 then l.outputBase else 0,extent⟩) &&
      decide (r.randomAddresses.map BitVec.toNat = addresses) do
    throw (IO.userError (name ++ ": construction mismatch"))
  unless (List.range xs.length).all (fun i => r.state.mem (word 12 (l.inputBase+i)) == xs[i]!) &&
      r.state.mem (word 12 4095) == word 12 4095 do
    throw (IO.userError (name ++ ": preservation mismatch"))
  let results := keys.map (query r l xs.length)
  unless decide (results.map (fun q => (q.state.regs ABI.result).toNat) = answers) &&
      results.all (fun q => decide (q.reason = .halted) && q.state.regs ABI.status == word 12 1 &&
        q.steps ≤ Query.cost && q.randomReads == 0) do
    throw (IO.userError (name ++ ": query after overwrite mismatch"))
  IO.println (name ++ ": passed (" ++ toString r.steps ++ " instructions)")

/-- Original strict endpoint assumptions remain feasible with scratch and random
reservations ending at the last representable address, plus generated-code fit. -/
theorem boundary_admissible : Admissible 12 4 ⟨0,2000,3775,3962⟩ := by
  constructor
  · constructor
    · constructor <;> simp [Layout.input,Layout.output,Layout.scratch,dictionaryCapacity,
        workspaceCapacity,Region.Fits,Region.Separated,modulus]
    · constructor <;> decide
    · simp [RandomFit,Layout.random,randomCapacity,bucketCapacity,Region.Fits,modulus]
  · decide

#eval checkRun "source repeated keys" repeatedKeys (canonicalLayout 11) (fun _ => word 12 128)
  10703 1 8 164 [0,1,13,25] [0,1,2,3,4,5,6,7,8,4095] [1,1,1,1,1,1,1,1,0,0]
#eval checkRun "source root budget failure" repeatedKeys (canonicalLayout 11) (fun _ => word 12 0)
  26471 0 0 0 (List.range 13) [] []
#eval checkRun "source child budget failure" repeatedKeys (canonicalLayout 11)
  (fun a => if a.toNat ≤ 1 then word 12 128 else word 12 0)
  25781 0 0 0 ([0,1]++List.range' 13 12) [] []
#eval checkRun "source last root attempt" repeatedKeys (canonicalLayout 11)
  (fun a => if a.toNat < 12 then word 12 0 else word 12 128)
  32610 1 8 164 (List.range 13++[13,25]) [0,7,8,4095] [1,1,0,0]
#eval checkRun "source empty" [] (canonicalLayout 0) (fun _ => word 12 0)
  355 1 0 8 [] [0,4095] [0,0]
#eval checkRun "source singleton maximum key" [4095] (canonicalLayout 1) (fun _ => word 12 0)
  1567 1 1 10 [0,1] [0,4095] [0,1]
#eval checkRun "source all equal" (List.replicate 20 (word 12 4095)) (canonicalLayout 20) (fun _ => word 12 0)
  4529 1 1 10 [0,1] [0,4095] [0,1]
#eval checkRun "source near-end input" [0,4095,0,4095] ⟨4000,2000,3000,3800⟩ (fun _ => word 12 0)
  2736 1 2 16 [3800,3801] [0,4095,1,4094] [1,1,0,0]
#eval checkRun "source last fitting endpoints" [0,4095,0,4095] ⟨0,2000,3775,3962⟩ (fun _ => word 12 0)
  2736 1 2 16 [3962,3963] [0,4095,1,4094] [1,1,0,0]

end PerfectHash.Source.Bounded.Examples
