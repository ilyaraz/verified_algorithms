import Mathlib.Data.Nat.Log

/-! Mathematical rounding bounds; the constructor must separately charge the
RAM doubling loop that realizes these values. -/
namespace Hashing.PowerOfTwo

def bits (n : Nat) : Nat := Nat.clog 2 n

def size (n : Nat) : Nat := 2 ^ bits n

@[simp] theorem size_zero : size 0 = 1 := by simp [size, bits]
@[simp] theorem size_one : size 1 = 1 := by simp [size, bits]

theorem positive (n : Nat) : 0 < size n := Nat.two_pow_pos _

theorem covers (n : Nat) : n ≤ size n := Nat.le_pow_clog (by decide) n

theorem least (hn : n ≤ 2^k) : bits n ≤ k :=
  (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mpr hn

theorem less_than_twice (hn : 0 < n) : size n < 2*n := by
  by_cases hb : bits n = 0
  · simp [size, hb]
    omega
  · have hprev : 2^(bits n-1) < n := by
      apply Nat.lt_of_not_ge
      intro h
      have := least h
      omega
    have he : bits n = (bits n-1)+1 := by omega
    unfold size
    rw [he, Nat.pow_succ]
    omega

theorem conservative (n : Nat) : size n ≤ 2*(n+1) := by
  cases n with
  | zero => simp
  | succ n =>
    have h : size (n+1) < 2*(n+1) := less_than_twice (by omega)
    omega

/-- Explicit bounded search for the ceiling base-two logarithm. This computation
uses natural powers directly and does not depend on the proof-side clog implementation. -/
def computeBitsAux (n : Nat) : Nat → Nat → Nat
  | 0,k => k
  | fuel+1,k => if n ≤ Nat.pow 2 k then k else computeBitsAux n fuel (k+1)

def computeBits (n : Nat) : Nat := computeBitsAux n (n+1) 0

def computeSize (n : Nat) : Nat := Nat.pow 2 (computeBits n)

theorem computeBitsAux_eq (n fuel k : Nat) (hk : k ≤ bits n) (hf : bits n ≤ k+fuel) :
    computeBitsAux n fuel k = bits n := by
  induction fuel generalizing k with
  | zero => simp only [computeBitsAux]; omega
  | succ fuel ih =>
    simp only [computeBitsAux]
    split
    · rename_i h
      have hh := least h
      omega
    · rename_i h
      have hl : k < bits n := by
        by_contra hn
        have he : k = bits n := by omega
        exact h (he ▸ covers n)
      exact ih (k+1) (by omega) (by omega)

theorem computeBits_eq (n : Nat) : computeBits n = bits n := by
  apply computeBitsAux_eq n (n+1) 0 (Nat.zero_le _)
  have hh : bits n ≤ n := least (Nat.le_of_lt Nat.lt_two_pow_self)
  omega

theorem computeSize_eq (n : Nat) : computeSize n = size n := by
  simp only [computeSize,computeBits_eq,size]
  rfl

end Hashing.PowerOfTwo
