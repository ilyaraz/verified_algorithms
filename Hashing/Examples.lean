import Hashing.MultiplyShiftCollision
import Hashing.MultiplyShiftProbability
import Hashing.MultiplyShiftRam
import Hashing.PowerOfTwo

namespace Hashing.Examples
open WordRam MultiplyShift

/-- Exhaustive arithmetic collision check using explicit, executable lists.
The general theorem is collision_bound; this is an independent boundary check. -/
def collisionCheck (width : Nat) : Bool :=
  (List.range (width+1)).all fun bits =>
    (List.range (Nat.pow 2 width)).all fun x =>
      (List.range (Nat.pow 2 width)).all fun y =>
        x == y ||
          ((List.range (Nat.pow 2 (width-1))).filter fun i =>
            eval (word width (2*i+1)) (word width x) bits ==
              eval (word width (2*i+1)) (word width y) bits).length * Nat.pow 2 bits ≤
                2 * Nat.pow 2 (width-1)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2000000 in
theorem small_width_collisions :
    collisionCheck 1 = true ∧ collisionCheck 2 = true ∧
    collisionCheck 3 = true ∧ collisionCheck 4 = true := by decide

theorem sampler_boundary :
    sample (word 1 0) = word 1 1 ∧ sample (word 1 1) = word 1 1 ∧
    sample (word 4 0) = word 4 1 ∧ sample (word 4 15) = word 4 15 ∧
    sample (word 4 14) = word 4 15 := by decide

theorem enumeration_boundary :
    (List.range 8).map (fun i => (candidate 3 i).toNat) = [1,3,5,7,9,11,13,15] ∧
    candidate 3 8 = first 3 := by decide

theorem full_width_hash :
    eval (word 4 3) (word 4 15) 4 = word 4 13 ∧
    eval (word 4 3) (word 4 15) 0 = word 4 0 ∧
    eval (word 4 15) (word 4 0) 4 = word 4 0 := by decide

def evaluatorRegisters : Registers 4 4 := fun r =>
  word 4 (if r.val = 1 then 3 else if r.val = 2 then 15 else if r.val = 3 then 2 else 7)

theorem evaluator_boundary :
    let result := run MultiplyShiftRam.evaluator (zeroMemory 4) 3
      (.initial evaluatorRegisters (fun a => a+1))
    result.reason = .halted ∧ result.steps = 3 ∧ result.trace = [] ∧
    result.state.regs MultiplyShiftRam.result = word 4 3 ∧
    result.state.regs MultiplyShiftRam.seed = word 4 3 := by decide

theorem zero_is_not_uniform : ∀ a : Seed 3, eval (encode a) (word 4 0) 3 = word 4 0 := by
  intro a
  apply BitVec.eq_of_toNat_eq
  simp [eval_toNat, word]

end Hashing.Examples
