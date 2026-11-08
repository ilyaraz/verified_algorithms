import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Counting odd residues in two short intervals at the ends of a modulus. -/
namespace Hashing.Modular

/-- Compress the lower and upper odd residues into disjoint halves of one index
range. This is a proof-side counting map, never runtime hashing advice. -/
def tailIndex (H L r : Nat) : Nat :=
  if r < 2*L then r/2 else r/2 - (H-L) + L

theorem tailIndex_bounds (hsep : 2*L ≤ H) (hr : r < 2*H)
    (ho : r%2 = 1) (ht : r < 2*L ∨ 2*H-2*L < r) :
    tailIndex H L r < 2*L := by
  have hd := Nat.mod_add_div r 2
  unfold tailIndex
  split <;> omega

theorem tailIndex_injective (hsep : 2*L ≤ H)
    (hor : r%2 = 1) (hos : s%2 = 1)
    (htr : r < 2*L ∨ 2*H-2*L < r) (hts : s < 2*L ∨ 2*H-2*L < s)
    (he : tailIndex H L r = tailIndex H L s) : r = s := by
  have hdr := Nat.mod_add_div r 2
  have hds := Nat.mod_add_div s 2
  unfold tailIndex at he
  split at he <;> split at he <;> omega

/-- Among g periods, the two tails contain at most g*(2*L) odd residues. -/
theorem odd_tail_count (g H L : Nat) (hH : 0 < H) (hsep : 2*L ≤ H) :
    Nat.card {b : Fin (g*(2*H)) // b.val % 2 = 1 ∧
      (b.val % (2*H) < 2*L ∨ 2*H-2*L < b.val % (2*H))} ≤ g*(2*L) := by
  classical
  let f : {b : Fin (g*(2*H)) // b.val % 2 = 1 ∧
      (b.val % (2*H) < 2*L ∨ 2*H-2*L < b.val % (2*H))} → Fin g × Fin (2*L) :=
    fun b => (⟨b.val.val / (2*H), (Nat.div_lt_iff_lt_mul (by omega)).mpr b.val.isLt⟩,
      ⟨tailIndex H L (b.val.val % (2*H)), tailIndex_bounds hsep
        (Nat.mod_lt _ (by omega)) (by simpa [Nat.mod_mul_left_mod] using b.property.1)
        b.property.2⟩)
  have hinj : Function.Injective f := by
    intro a b he
    have hq := congrArg (fun v : Fin g × Fin (2*L) => v.1.val) he
    have ht := congrArg (fun v : Fin g × Fin (2*L) => v.2.val) he
    dsimp [f] at hq ht
    have hr := tailIndex_injective hsep
      (by simpa [Nat.mod_mul_left_mod] using a.property.1)
      (by simpa [Nat.mod_mul_left_mod] using b.property.1)
      a.property.2 b.property.2 ht
    apply Subtype.ext
    apply Fin.ext
    have ha := Nat.mod_add_div a.val.val (2*H)
    have hb := Nat.mod_add_div b.val.val (2*H)
    rw [hq, hr] at ha
    omega
  simpa [Nat.card_eq_fintype_card] using Fintype.card_le_of_injective f hinj

/-- Multiplication by an odd factor is injective on residues modulo a power of two. -/
theorem odd_mul_injective (hz : z%2 = 1) :
    Function.Injective (fun a : Fin (2^w) => (a.val*z) % 2^w) := by
  intro a b he
  have hc : Nat.Coprime (2^w) z := by
    apply Nat.Coprime.pow_left
    exact Nat.prime_two.coprime_iff_not_dvd.mpr (by omega)
  have hmod : Nat.ModEq (2^w) a.val b.val := Nat.ModEq.cancel_right_of_coprime hc he
  have hval : a.val = b.val := by
    simpa [Nat.ModEq, Nat.mod_eq_of_lt a.isLt, Nat.mod_eq_of_lt b.isLt] using hmod
  exact Fin.ext hval

/-- Dividing two values into the same bucket puts their modular difference in
one of the short intervals on either side of zero. -/
theorem same_quotient_tail (hu : u < U) (hv : v < U) (hB : 0 < B)
    (hB' : B ≤ U) (he : u/B = v/B) :
    (v+U-u)%U < B ∨ U-B < (v+U-u)%U := by
  have hur := Nat.mod_lt u hB
  have hvr := Nat.mod_lt v hB
  have hud := Nat.mod_add_div u B
  have hvd := Nat.mod_add_div v B
  rw [he] at hud
  by_cases huv : u ≤ v
  · left
    have ht : v+U-u = v-u+U := by omega
    rw [ht, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : v-u < U)]
    omega
  · right
    rw [Nat.mod_eq_of_lt (by omega : v+U-u < U)]
    omega

/-- Powers of two split at any lower exponent, in the multiplication orientation
used by residue and storage bounds. -/
theorem power_split (h : k ≤ W) : 2^W = 2^k * 2^(W-k) := by
  rw [← Nat.pow_add, Nat.add_sub_of_le h]

theorem odd_mod_power (hW : 0 < W) (ha : a%2 = 1) : (a % 2^W)%2 = 1 := by
  have he : 2^W = 2 * 2^(W-1) := by
    simpa using power_split (k := 1) (W := W) hW
  rw [he, Nat.mod_mul_right_mod, ha]

/-- Collision-relevant multiples of a nonzero difference occupy at most 2^s
odd seeds modulo 2^W. This includes differences with arbitrary trailing zeros. -/
theorem odd_multiple_tail_count (W s d : Nat) (hs : s < W)
    (hd : 0 < d) (hdU : d < 2^W) :
    Nat.card {a : Fin (2^W) // a.val%2 = 1 ∧
      ((a.val*d)%2^W < 2^s ∨ 2^W-2^s < (a.val*d)%2^W)} ≤ 2^s := by
  classical
  obtain ⟨k, z, hz, he⟩ := Nat.exists_eq_two_pow_mul_odd (Nat.ne_of_gt hd)
  have hzmod : z%2 = 1 := Nat.odd_iff.mp hz
  have hzpos : 0 < z := by omega
  have hk : k < W := by
    by_contra hn
    have hp := Nat.pow_le_pow_right (n := 2) (by decide) (show W ≤ k by omega)
    have hp' := Nat.two_pow_pos k
    nlinarith
  have hU := power_split (Nat.le_of_lt hk)
  have hM : 0 < 2^(W-k) := Nat.two_pow_pos _
  have hG : 0 < 2^k := Nat.two_pow_pos _
  have product (a : Nat) : (a*d)%2^W = 2^k * ((a*z)%2^(W-k)) := by
    rw [he, hU]
    rw [show a*(2^k*z) = 2^k*(a*z) by ring, Nat.mul_mod_mul_left]
  by_cases hks : s ≤ k
  · have hB : 2^s ≤ 2^k := Nat.pow_le_pow_right (by decide) hks
    have hempty : IsEmpty {a : Fin (2^W) // a.val%2 = 1 ∧
        ((a.val*d)%2^W < 2^s ∨ 2^W-2^s < (a.val*d)%2^W)} := by
      constructor
      rintro ⟨a, ha, ht⟩
      have hodd := odd_mod_power (show 0 < W-k by omega) (Nat.odd_mul_odd ha hzmod)
      have hlt := Nat.mod_lt (a.val*z) hM
      have hpos : 0 < (a.val*z)%2^(W-k) := by omega
      rw [product] at ht
      rcases ht with ht | ht
      · nlinarith
      · have hmax : (a.val*z)%2^(W-k)+1 ≤ 2^(W-k) := by omega
        have := Nat.mul_le_mul_left (2^k) hmax
        have hbU : 2^s ≤ 2^W := Nat.pow_le_pow_right (by decide) (Nat.le_of_lt hs)
        have hsub := Nat.sub_add_cancel hbU
        nlinarith
    letI := hempty
    simp
  · have hks' : k < s := by omega
    let H := 2^(W-k-1)
    let L := 2^(s-k-1)
    have hMH : 2^(W-k) = 2*H := by
      simpa [H] using power_split (k := 1) (W := W-k) (by omega)
    have hTL : 2^(s-k) = 2*L := by
      simpa [L] using power_split (k := 1) (W := s-k) (by omega)
    have hB := power_split (Nat.le_of_lt hks')
    have hH : 0 < H := Nat.two_pow_pos _
    have hsep : 2*L ≤ H := by
      rw [← hTL]
      exact Nat.pow_le_pow_right (by decide) (by omega : s-k ≤ W-k-1)
    have hUU : 2^W = 2^k*(2*H) := hU.trans (congrArg (2^k * ·) hMH)
    let f : {a : Fin (2^W) // a.val%2 = 1 ∧
        ((a.val*d)%2^W < 2^s ∨ 2^W-2^s < (a.val*d)%2^W)} →
        {b : Fin (2^k*(2*H)) // b.val%2 = 1 ∧
          (b.val%(2*H) < 2*L ∨ 2*H-2*L < b.val%(2*H))} := fun a =>
      ⟨⟨(a.val.val*z)%2^W, by rw [← hUU]; exact Nat.mod_lt _ (Nat.two_pow_pos W)⟩, by
        constructor
        · exact odd_mod_power (by omega) (Nat.odd_mul_odd a.property.1 hzmod)
        · have hm : ((a.val.val*z)%2^W)%(2*H) = (a.val.val*z)%(2*H) := by
            simp only [hUU, Nat.mod_mul_left_mod]
          rw [hm, ← hMH, ← hTL]
          have ht := a.property.2
          rw [product] at ht
          rcases ht with ht | ht
          · left
            simp only [hB] at ht
            exact (Nat.mul_lt_mul_left hG).mp ht
          · right
            have hle : 2^(s-k) ≤ 2^(W-k) := Nat.pow_le_pow_right (by decide) (by omega)
            simp only [hU, hB, ← Nat.mul_sub_left_distrib] at ht
            exact (Nat.mul_lt_mul_left hG).mp ht⟩
    have hinj : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      apply odd_mul_injective hzmod
      exact congrArg (fun c => c.val.val) hab
    calc
      _ ≤ Nat.card {b : Fin (2^k*(2*H)) // b.val%2 = 1 ∧
          (b.val%(2*H) < 2*L ∨ 2*H-2*L < b.val%(2*H))} :=
        Nat.card_le_card_of_injective f hinj
      _ ≤ 2^k*(2*L) := odd_tail_count _ _ _ hH hsep
      _ = 2^s := by rw [← hTL, ← hB]

end Hashing.Modular
