import DataStructures.PerfectHash.Source.Total.Contract
import DataStructures.PerfectHash.Source.Bounded.Examples

namespace PerfectHash.Source.Total.Examples
open WordRam RamLang Source.Bounded.Examples
set_option maxRecDepth 65536
set_option maxHeartbeats 10000000

/-- Multiplier three clusters these keys; the random phase exhausts before enumeration succeeds. -/
def fallbackKeys : List (Word 12) := [0,2731,1366,1,2732,1367,2,4095,0,4095,0]

/-- Root retries exhaust; child blocks use multiplier 1025. -/
def rootImage : RandomMemory 12 := fun a =>
  if 1 ≤ a.toNat ∧ a.toNat ≤ 12 then word 12 2
  else word 12 1024

/-- Run the actual compiled public constructor from its original input ABI. -/
def execute (xs : List (Word 12)) (l : Layout) (rho : RandomMemory 12) : WordRam.RunResult 12 64 :=
  WordRam.run program rho 1000000 (.initial (buildRegisters 12 xs.length l (fun _ => word 12 4095)) (memory xs l))

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


/-- The stronger generated-code bound still permits the strict last-address layout. -/
theorem boundary_admissible : Admissible 12 4 ⟨0,2000,3775,3962⟩ :=
  ⟨Source.Bounded.Examples.boundary_admissible.toAdmissible,by decide⟩

#eval checkRun "total source root fallback" fallbackKeys (canonicalLayout 11) rootImage
  32127 1 8 134 (List.range 14++[37,73])
  [0,2731,1366,1,2732,1367,2,4095,3,42,4094] [1,1,1,1,1,1,1,1,0,0,0]
#eval checkRun "total source child fallback" [0,2731,0,2731] (canonicalLayout 4) (fun _ => word 12 2)
  11003 1 2 28 ([0,1]++List.range' 13 12) [0,2731,1,4095] [1,1,0,0]
#eval checkRun "total source repeated keys" repeatedKeys (canonicalLayout 11) (fun _ => word 12 128)
  10703 1 8 164 [0,1,13,25] [0,1,2,3,4,5,6,7,8,4095] [1,1,1,1,1,1,1,1,0,0]
#eval checkRun "total source last root attempt" repeatedKeys (canonicalLayout 11)
  (fun a => if a.toNat < 12 then word 12 0 else word 12 128)
  32610 1 8 164 (List.range 13++[13,25]) [0,7,8,4095] [1,1,0,0]
#eval checkRun "total source empty" [] (canonicalLayout 0) (fun _ => word 12 0)
  355 1 0 8 [] [0,4095] [0,0]
#eval checkRun "total source singleton maximum key" [4095] (canonicalLayout 1) (fun _ => word 12 0)
  1567 1 1 10 [0,1] [0,4095] [0,1]
#eval checkRun "total source all equal" (List.replicate 20 (word 12 4095)) (canonicalLayout 20) (fun _ => word 12 0)
  4529 1 1 10 [0,1] [0,4095] [0,1]
#eval checkRun "total source near-end input" [0,4095,0,4095] ⟨4000,2000,3000,3800⟩ (fun _ => word 12 0)
  2736 1 2 16 [3800,3801] [0,4095,1,4094] [1,1,0,0]
#eval checkRun "total source last fitting endpoints" [0,4095,0,4095] ⟨0,2000,3775,3962⟩ (fun _ => word 12 0)
  2736 1 2 16 [3962,3963] [0,4095,1,4094] [1,1,0,0]


end PerfectHash.Source.Total.Examples
