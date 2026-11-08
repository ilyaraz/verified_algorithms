import DataStructures.PerfectHash.Certified

namespace PerfectHash.Demo
open WordRam

/-- Repeated full-word input includes both boundary word values. -/
def keys : List (Word 12) := [0,4095,0,4095]

def layout : Layout := canonicalLayout keys.length

def memory : DataMemory 12 := fun a => keys[a.toNat]?.getD (word 12 4095)

def initial : State 12 64 := .initial
  (buildRegisters 12 keys.length layout (fun _ => word 12 4095)) memory

theorem admissible : Admissible 12 keys.length layout :=
  canonical_admissible (by decide) (by decide) (by decide)

theorem input_array : ArrayAt memory layout.inputBase keys := by
  unfold ArrayAt
  decide

/-- A small evaluator guard is sufficient for this particular demonstration;
the public theorem uses the general frozen construction fuel. -/
def built : RunResult 12 64 := run fksCode.preprocess (zeroMemory 12) 1000 initial

def query (key : Word 12) : Word 12 :=
  let descriptor := StaticSet.readDescriptor built.state.regs
  (run fksCode.query (zeroMemory 12) Total.bounds.query (.initial
    (fun r => if r.val = 0 then word 12 descriptor.base
      else if r.val = 1 then word 12 descriptor.size
      else if r.val = 2 then key else word 12 4095) built.state.mem)).state.regs ⟨0,by decide⟩

/-- Execute both projected code arrays and fail if the advertised demo answers
or successful halt differ from the actual interpreter result. -/
def run : IO Unit := do
  let result := built
  unless decide (result.reason = .halted) do
    throw (IO.userError "Construction did not halt successfully")
  let descriptor := StaticSet.readDescriptor result.state.regs
  IO.println ("Programs: " ++ toString fksCode.preprocess.size ++ " build instructions, " ++
    toString fksCode.query.size ++ " query instructions")
  IO.println ("Build: " ++ toString result.steps ++ " instructions; " ++
    toString (result.state.regs ⟨2,by decide⟩).toNat ++ " distinct keys; " ++
    toString descriptor.size ++ " retained words")
  ([0,4095,1,4094] : List (Word 12)).forM fun q => do
    let answer := query q
    unless decide (answer.toNat = if keys.contains q then 1 else 0) do
      throw (IO.userError "Query result mismatch")
    IO.println ("contains(" ++ toString q.toNat ++ ") = " ++ toString answer.toNat)

end PerfectHash.Demo
