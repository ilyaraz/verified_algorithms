import DataStructures.PerfectHash.Source.Query.Correctness
import DataStructures.PerfectHash.Query.Examples
open WordRam RamLang RamLang.Compiler PerfectHash.Source.Query
namespace PerfectHash.Source.Query.Examples
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000
/-- Machine entry with a dirty stack and otherwise unconstrained scratch registers. -/
def initial (r : Region) (q : Word 8) (mem : DataMemory 8) (stack : Region := ⟨32,28⟩) : State 8 ABI.registers :=
  .initial (fun i => if i.val = 0 then word 8 stack.base
    else if i.val = 2 then word 8 (stack.base+stack.size)
    else if i.val = 12 then word 8 r.base else if i.val = 13 then q else word 8 255) mem
/-- Execute the new compiled query on the original hashed dictionary fixture. -/
def execute (q : Word 8) := WordRam.run compiled.code (fun _ => word 8 255) cost
  (initial PerfectHash.Query.Examples.hashedRegion q PerfectHash.Query.Examples.hashedMemory)

/-- Dirty registers and stack satisfy the public entry convention. -/
theorem input (r : Region) (q : Word 8) (mem : DataMemory 8) (stack : Region) :
    Input r stack q (initial r q mem stack) := by
  constructor <;> simp [initial,State.initial,ABI.sp,ABI.limit,ABI.argument]

/-- Zero and one are found in hashed children through ordinary helper calls. -/
theorem hashed_members :
    (execute (word 8 0)).state.regs ABI.result = word 8 1 ∧
    (execute (word 8 1)).state.regs ABI.result = word 8 1 ∧
    (execute (word 8 0)).steps = 236 := by decide

/-- An occupied slot with a different full key is rejected on the longest path. -/
theorem occupied_nonmember :
    (execute (word 8 2)).state.regs ABI.result = word 8 0 ∧
    (execute (word 8 2)).steps = 237 := by decide

/-- Unoccupied slots do not inspect their dirty key word. -/
theorem dirty_empty_slot :
    (execute (word 8 255)).state.regs ABI.result = word 8 0 ∧
    (execute (word 8 255)).steps = 219 := by decide

/-- The relaxed contract permits real stack writes, but no random reads. -/
theorem charged_stack :
    0 < (execute (word 8 2)).writeFootprint.length ∧
    (execute (word 8 2)).randomReads = 0 ∧
    (execute (word 8 2)).state.regs ABI.status = word 8 1 := by decide

/-- An empty dictionary can still occupy the last fitting retained extent. -/
theorem empty_boundary :
    let result := WordRam.run compiled.code (fun _ => word 8 255) cost
      (initial ⟨247,8⟩ (word 8 255) PerfectHash.Query.Examples.emptyMemory)
    result.reason = .halted ∧ result.state.regs ABI.result = word 8 0 ∧ result.steps = 111 := by decide

/-- A maximum-word singleton works with an exact-fit stack ending at word 255. -/
theorem maximum_singleton :
    let result := WordRam.run compiled.code (fun _ => word 8 0) cost
      (initial ⟨200,16⟩ (word 8 255) PerfectHash.Query.Examples.singletonMemory ⟨227,28⟩)
    result.reason = .halted ∧ result.state.regs ABI.result = word 8 1 ∧ result.steps = 158 := by decide

/-- One missing helper-frame word causes defined runtime exhaustion, distinct
from the ordinary zero membership answer. -/
theorem short_stack :
    let result := WordRam.run compiled.code (fun _ => word 8 0) cost
      (initial PerfectHash.Query.Examples.hashedRegion (word 8 0)
        PerfectHash.Query.Examples.hashedMemory ⟨32,27⟩)
    result.reason = .halted ∧ result.state.regs ABI.status = word 8 2 := by decide

/-- The generic theorem covers every query after the original input, scratch
and previous stack have all been overwritten with zero. -/
theorem overwritten_outside (q : Word 8) :
    let mem : DataMemory 8 := fun a => if 220 ≤ a.toNat ∧ a.toNat < 244 then
      PerfectHash.Query.Examples.hashedMemory a else word 8 0
    let s := initial PerfectHash.Query.Examples.hashedRegion q mem
    Output PerfectHash.Query.Examples.hashedSet PerfectHash.Query.Examples.hashedRegion
      ⟨32,28⟩ q mem (WordRam.run compiled.code (fun _ => word 8 0) cost s) := by
  dsimp only
  apply after_overwrite _ (initial PerfectHash.Query.Examples.hashedRegion q _) q
    PerfectHash.Query.Examples.hashed_view
  · intro a ha
    change 220 ≤ a.toNat ∧ a.toNat < 244 at ha
    change PerfectHash.Query.Examples.hashedMemory a =
      (if 220 ≤ a.toNat ∧ a.toNat < 244 then PerfectHash.Query.Examples.hashedMemory a else word 8 0)
    rw [if_pos ha]
  · constructor <;> dsimp [Region.Fits,Region.Separated,stackWords,PerfectHash.Query.Examples.hashedRegion] <;> decide
  · exact input _ _ _ _

end PerfectHash.Source.Query.Examples
