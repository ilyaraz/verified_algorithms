import Std

/-! Unsigned fixed-width words. Arithmetic is Lean's `BitVec` arithmetic. -/
namespace WordRam

abbrev Word (w : Nat) := BitVec w
abbrev Addr (w : Nat) := Word w
abbrev modulus (w : Nat) := 2 ^ w

def word (w n : Nat) : Word w := BitVec.ofNat w n

/-- Unsigned remainder, constructed through modular conversion to keep the
executable definition independent of axioms used by `BitVec.umod`'s bound proof. -/
def unsignedMod (x y : Word w) : Word w := word w (x.toNat % y.toNat)

@[simp] theorem unsignedMod_eq (x y : Word w) : unsignedMod x y = x % y :=
  BitVec.umod_def.symm

@[simp] theorem word_toNat (w n : Nat) : (word w n).toNat = n % modulus w := rfl

theorem word_toNat_of_lt {w n : Nat} (h : n < modulus w) :
    (word w n).toNat = n := Nat.mod_eq_of_lt h

theorem word_bound (x : Word w) : x.toNat < modulus w := x.isLt

theorem add_toNat (x y : Word w) :
    (x + y).toNat = (x.toNat + y.toNat) % modulus w := rfl

theorem sub_toNat (x y : Word w) :
    (x - y).toNat = (x.toNat + modulus w - y.toNat) % modulus w := by
  rw [BitVec.toNat_sub]
  have := y.isLt
  congr 1
  unfold modulus
  omega

theorem mul_toNat (x y : Word w) :
    (x * y).toNat = (x.toNat * y.toNat) % modulus w := rfl

theorem mod_toNat (x y : Word w) : (x % y).toNat = x.toNat % y.toNat := rfl

@[simp] theorem mod_zero (x : Word w) : x % (0 : Word w) = x := BitVec.umod_zero

theorem mod_lt (x y : Word w) (hy : 0 < y.toNat) :
    (x % y).toNat < y.toNat := Nat.mod_lt _ hy

theorem add_toNat_of_lt (x y : Word w) (h : x.toNat + y.toNat < modulus w) :
    (x + y).toNat = x.toNat + y.toNat := Nat.mod_eq_of_lt h

theorem mul_toNat_of_lt (x y : Word w) (h : x.toNat * y.toNat < modulus w) :
    (x * y).toNat = x.toNat * y.toNat := Nat.mod_eq_of_lt h

end WordRam
