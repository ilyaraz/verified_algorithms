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

end Hashing.PowerOfTwo
