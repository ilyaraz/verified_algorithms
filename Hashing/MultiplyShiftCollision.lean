import Hashing.MultiplyShift
import Hashing.Modular
import Hashing.Family

namespace Hashing.MultiplyShift
open WordRam

@[simp] theorem eval_toNat (a x : Word w) (bits : Nat) :
    (eval a x bits).toNat = (a*x).toNat / 2^(w-bits) := by
  change ((a*x).toNat >>> (w-bits)) % 2^w = _
  rw [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) (a*x).isLt),
    Nat.shiftRight_eq_div_pow]

theorem collision_tail (a x y : Word w)
    (he : eval a x bits = eval a y bits) :
    (a.toNat*(y-x).toNat)%2^w < 2^(w-bits) ∨
      2^w-2^(w-bits) < (a.toNat*(y-x).toNat)%2^w := by
  have hq := congrArg BitVec.toNat he
  simp only [eval_toNat] at hq
  have ht := Modular.same_quotient_tail (a*x).isLt (a*y).isLt
    (Nat.two_pow_pos (w-bits))
    (Nat.pow_le_pow_right (by decide) (Nat.sub_le w bits)) hq
  have hp : (a.toNat*(y-x).toNat)%2^w =
      ((a*y).toNat+2^w-(a*x).toNat)%2^w := by
    change (a*(y-x)).toNat = _
    rw [BitVec.mul_sub, sub_toNat]
  rwa [← hp] at ht

/-- For a positive output-bit count, at most 2^(w+1-bits) odd seeds collide. -/
theorem collision_count (x y : Word (w+1)) (hne : x ≠ y)
    (hpos : 0 < bits) (hb : bits ≤ w+1) :
    Nat.card {a : Seed w // eval (encode a) x bits = eval (encode a) y bits} ≤
      2^(w+1-bits) := by
  classical
  have hd : 0 < (y-x).toNat := by
    by_contra hn
    have hz : y-x = 0 := BitVec.eq_of_toNat_eq (by change (y-x).toNat = 0; omega)
    have hxy := BitVec.sub_eq_iff_eq_add.mp hz
    apply hne
    simpa using hxy.symm
  let f : {a : Seed w // eval (encode a) x bits = eval (encode a) y bits} →
      {a : Fin (2^(w+1)) // a.val%2 = 1 ∧
        (a.val*(y-x).toNat%2^(w+1) < 2^(w+1-bits) ∨
        2^(w+1)-2^(w+1-bits) < a.val*(y-x).toNat%2^(w+1))} := fun a =>
    ⟨(encode a.val).toFin, encode_odd a.val, collision_tail _ _ _ a.property⟩
  have hinj : Function.Injective f := by
    intro a b he
    apply Subtype.ext
    apply encode_injective
    apply BitVec.eq_of_toNat_eq
    exact congrArg (fun c => c.val.val) he
  exact (Nat.card_le_card_of_injective f hinj).trans
    (Modular.odd_multiple_tail_count (w+1) (w+1-bits) (y-x).toNat
      (by omega) hd (y-x).isLt)

/-- Concrete, computable range-valued family, independent of any RAM program. -/
def family (w bits : Nat) (hb : bits ≤ w+1) : Family (Word (w+1)) (Seed w) (2^bits) where
  eval a x := ⟨(eval (encode a) x bits).toNat, eval_range _ _ hb⟩

/-- Full-word multiply-shift has collision constant two for every admissible
power-of-two output range. Zero is an ordinary key; output uniformity is not assumed. -/
theorem collision_bound (w bits : Nat) (hb : bits ≤ w+1) :
    CollisionBound (family w bits hb) 2 := by
  intro x y hne
  by_cases hp : 0 < bits
  · have hc := collision_count x y hne hp hb
    have he : {a : Seed w // (family w bits hb).eval a x = (family w bits hb).eval a y} ≃
        {a : Seed w // eval (encode a) x bits = eval (encode a) y bits} :=
      Equiv.subtypeEquivRight (fun a => by
        simp only [family, Fin.mk.injEq, BitVec.toNat_inj])
    rw [Nat.card_congr he]
    have hm := Nat.mul_le_mul_right (2^bits) hc
    calc
      _ ≤ 2^(w+1-bits) * 2^bits := hm
      _ = 2 * Fintype.card (Seed w) := by
        simp only [Seed, Fintype.card_fin, ← Nat.pow_add, Nat.sub_add_cancel hb, Nat.pow_succ]
        change 2^w * 2 = 2 * 2^w
        omega
  · have hz : bits = 0 := by omega
    subst bits
    have hc : Nat.card {a : Seed w // (family w 0 hb).eval a x = (family w 0 hb).eval a y} ≤
        Fintype.card (Seed w) := by
      rw [Nat.card_eq_fintype_card]
      exact Fintype.card_subtype_le _
    simp only [Nat.pow_zero, Nat.mul_one]
    omega

end Hashing.MultiplyShift
