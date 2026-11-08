import DataStructures.PerfectHash.Build.Bounds
import Hashing.MultiplyShiftRounding

namespace PerfectHash.Build
open WordRam Hashing.PowerOfTwo Hashing.MultiplyShift Buckets

/-- The concrete full-word mathematical model uses the same sampler seed domain
and bit selection as the fixed RAM hash evaluator. -/
def multiplyShiftModel (w : Nat) (xs : List (Word (w+1))) :
    Model (Word (w+1)) (Seed w) (computeSize xs.length) xs where
  root := roundedFamily w xs.length
  child a b := roundedFamily w (2*(count ((roundedFamily w xs.length).eval a) xs b)*
    (count ((roundedFamily w xs.length).eval a) xs b))
  enumeration := List.finRange (Nat.pow 2 w)
  attempts := w+1

theorem multiplyShift_hypotheses (xs : List (Word (w+1))) (hx : xs.Nodup)
    (hf : 64*(xs.length+1) < modulus (w+1)) : Hypotheses (multiplyShiftModel w xs) := by
  have rootfit : xs.length ≤ 2^(w+1) := by change _ < 2^(w+1) at hf; omega
  constructor
  · exact hx
  · change 0 < computeSize xs.length
    rw [computeSize_eq]
    exact positive _
  · change xs.length ≤ computeSize xs.length
    rw [computeSize_eq]
    exact covers _
  · change computeSize xs.length ≤ 2*(xs.length+1)
    rw [computeSize_eq]
    exact conservative _
  · exact roundedFamily_collision rootfit
  · intro a ha b
    apply roundedFamily_collision
    have he := accepted_energy (multiplyShiftModel w xs) ha
    have hc := count_square_le_energy ((multiplyShiftModel w xs).root.eval a) xs b
    change _ ≤ energy ((multiplyShiftModel w xs).root.eval a) xs at hc
    change 2*count ((roundedFamily w xs.length).eval a) xs b *
      count ((roundedFamily w xs.length).eval a) xs b ≤ 2^(w+1)
    change energy ((roundedFamily w xs.length).eval a) xs ≤ 6*xs.length at he
    change (count ((roundedFamily w xs.length).eval a) xs b)^2 ≤
      energy ((roundedFamily w xs.length).eval a) xs at hc
    change _ < 2^(w+1) at hf
    nlinarith
  · intro a
    exact List.mem_finRange a
  · simp [multiplyShiftModel]

end PerfectHash.Build
