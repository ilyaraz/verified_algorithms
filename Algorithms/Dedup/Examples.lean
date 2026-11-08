import Algorithms.Dedup.Expected

namespace Dedup.Examples
open WordRam

set_option maxRecDepth 65536
set_option maxHeartbeats 10000000

/-- A dirty-memory fixture whose scratch endpoint is the last word. -/
def layout (N : Nat) : Layout := ⟨8,4095-workspaceCapacity N,2⟩

def memory (xs : List (Word 12)) : DataMemory 12 := fun a =>
  if 8 ≤ a.toNat then (xs[a.toNat-8]?).getD (word 12 4095) else word 12 4095

def registers (N : Nat) : Registers 12 64 := fun r =>
  if r.val = 0 then word 12 8
  else if r.val = 1 then word 12 N
  else if r.val = 2 then word 12 (layout N).scratch
  else if r.val = 3 then word 12 2
  else if r.val = 4 then word 12 12
  else word 12 4095

def execute (xs : List (Word 12)) (raw : Nat) : RunResult 12 64 :=
  run program (fun _ => word 12 raw) (fuel xs.length) (.initial (registers xs.length) (memory xs))

def values (xs : List (Word 12)) (raw : Nat) : List (Word 12) :=
  let r := execute xs raw
  (List.range (r.state.regs Registers.count).toNat).map
    (fun i => r.state.mem (word 12 ((r.state.regs Registers.input).toNat+i)))

theorem empty : (execute [] 0).reason = .halted ∧ values [] 0 = [] := by decide

theorem repeated : values [word 12 9,word 12 9,word 12 9,word 12 9] 0 = [word 12 9] := by decide

theorem alternating : values [word 12 1,word 12 2,word 12 1,word 12 2,word 12 1] 0 =
    [word 12 1,word 12 2] := by decide

theorem endpoints : values [word 12 0,word 12 4095,word 12 0,word 12 4095] 4094 =
    [word 12 0,word 12 4095] := by decide

theorem distinct : values [word 12 4,word 12 3,word 12 2,word 12 1] 0 =
    [word 12 4,word 12 3,word 12 2,word 12 1] := by decide

theorem one_random_read : (execute [word 12 0,word 12 4095,word 12 0] 0).randomAddresses =
    [word 12 2] := by decide

theorem input_preserved :
    (execute [word 12 0,word 12 4095,word 12 0] 0).state.mem (word 12 8) = word 12 0 ∧
    (execute [word 12 0,word 12 4095,word 12 0] 0).state.mem (word 12 9) = word 12 4095 := by decide

theorem boundary_admissible : Admissible 12 5 (layout 5) := by
  constructor <;> norm_num [Region.Fits,Region.Separated,Layout.inputRegion,Layout.workspace,
    layout,workspaceCapacity,modulus]

theorem registers_valid : Input 12 5 (layout 5) (registers 5) := by unfold Input; decide

end Dedup.Examples
