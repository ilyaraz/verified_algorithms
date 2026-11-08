import Hashing.MultiplyShiftCollision
import Hashing.PowerOfTwo

namespace Hashing.MultiplyShift
open WordRam PowerOfTwo

/-- Range remains valid even for an oversized mathematical bucket count: the
zero shift then returns a full-width word in the larger index range. -/
theorem eval_range_all (a x : Word w) (bits : Nat) : (eval a x bits).toNat < 2^bits := by
  by_cases hb : bits ≤ w
  · exact eval_range a x hb
  · exact (word_bound (eval a x bits)).trans_le
      (Nat.pow_le_pow_right (n := 2) (by decide) (by omega))

/-- A rounded-size mathematical family. Collision bounds below require that the
chosen bit count fits the word, as proved for every accepted-root child. -/
def roundedFamily (w n : Nat) : Family (Word (w+1)) (Seed w) (computeSize n) where
  eval a x := ⟨(eval (encode a) x (computeBits n)).toNat,eval_range_all _ _ _⟩

theorem roundedFamily_collision (hn : n ≤ 2^(w+1)) : CollisionBound (roundedFamily w n) 2 := by
  have hb : computeBits n ≤ w+1 := by rw [computeBits_eq]; exact least hn
  change CollisionBound (family w (computeBits n) hb) 2
  exact collision_bound w (computeBits n) hb

end Hashing.MultiplyShift
