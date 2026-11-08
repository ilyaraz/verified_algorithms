import WordRam.Word
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Ring

namespace Hashing.MultiplyShift
open WordRam

/-- Odd seeds at positive width w+1 have exactly 2^w indices. -/
abbrev Seed (w : Nat) := Fin (Nat.pow 2 w)

/-- Runtime seed encoding uses the index's ordinary numeric value. -/
def encode (a : Seed w) : Word (w+1) := word (w+1) (2*a.val+1)

/-- Clear the raw word's low bit and set it to one, using the frozen arithmetic
sampler rather than a new bitwise instruction. -/
def sample (r : Word w) : Word w := r - unsignedMod r (word w 2) + word w 1

/-- Taking high bits deliberately follows a wrapping multiplication. -/
def eval (a x : Word w) (bits : Nat) : Word w :=
  word w ((a*x).toNat >>> (w-bits))

@[simp] theorem encode_toNat (a : Seed w) : (encode a).toNat = 2*a.val+1 := by
  apply word_toNat_of_lt
  have ha : a.val < 2^w := a.isLt
  simp only [modulus, Nat.pow_succ]
  omega

theorem encode_injective : Function.Injective (encode (w := w)) := by
  intro a b he
  have := congrArg BitVec.toNat he
  simp only [encode_toNat] at this
  apply Fin.ext
  omega

@[simp] theorem encode_odd (a : Seed w) : (encode a).toNat % 2 = 1 := by
  simp [encode_toNat]

theorem encode_covers (a : Word (w+1)) (ha : a.toNat % 2 = 1) :
    ∃ i : Seed w, encode i = a := by
  have hb := a.isLt
  have hp := Nat.two_pow_pos w
  have hd := Nat.mod_add_div a.toNat 2
  have hi : a.toNat / 2 < 2^w := by
    simp only [Nat.pow_succ] at hb
    omega
  refine ⟨⟨a.toNat / 2, hi⟩, ?_⟩
  apply BitVec.eq_of_toNat_eq
  simp only [encode_toNat]
  omega

/-- For positive width, each seed index corresponds to precisely two raw words. -/
def rawIndex (r : Word (w+1)) : Seed w :=
  ⟨r.toNat / 2, by
    change r.toNat / 2 < 2^w
    have := r.isLt
    simp only [Nat.pow_succ] at this
    omega⟩

theorem sample_eq_encode (r : Word (w+1)) : sample r = encode (rawIndex r) := by
  apply BitVec.eq_of_toNat_eq
  have hr := r.isLt
  have hp := Nat.two_pow_pos w
  have hd := Nat.mod_add_div r.toNat 2
  have hm := Nat.mod_lt r.toNat (by decide : 0 < 2)
  cases w with
  | zero =>
    have : r.toNat < 2 := by simpa using hr
    interval_cases h : r.toNat <;>
      simp [sample, unsignedMod, word, BitVec.toNat_add, BitVec.toNat_sub, encode_toNat, rawIndex, h]
  | succ w =>
    have htwo : 2 < 2^(w+1+1) := by
      have := Nat.two_pow_pos w
      simp only [Nat.pow_succ]
      omega
    have hmod : (unsignedMod r (word (w+1+1) 2)).toNat = r.toNat % 2 := by
      rw [unsignedMod_eq, mod_toNat, word_toNat_of_lt htwo]
    have hsub : (r - unsignedMod r (word (w+1+1) 2)).toNat = r.toNat - r.toNat % 2 := by
      rw [BitVec.toNat_sub, hmod]
      have he : (2^(w+1+1) - r.toNat % 2 + r.toNat) =
          (r.toNat - r.toNat % 2) + 2^(w+1+1) := by omega
      rw [he, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    change (r - unsignedMod r (word (w+1+1) 2) + word (w+1+1) 1).toNat = _
    rw [add_toNat, hsub, word_toNat_of_lt (show 1 < modulus (w+1+1) from Nat.lt_trans (by decide) htwo), encode_toNat]
    dsimp only [rawIndex]
    rw [Nat.mod_eq_of_lt (by
      simp only [modulus, Nat.pow_succ] at *
      omega)]
    omega

/-- The range proof needs no seed parity assumption. -/
theorem eval_range (a x : Word w) (hb : bits ≤ w) : (eval a x bits).toNat < 2^bits := by
  have he : eval a x bits = (a*x) >>> (w-bits) := by
    apply BitVec.eq_of_toNat_eq
    change ((a*x).toNat >>> (w-bits)) % 2^w = (a*x).toNat >>> (w-bits)
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.shiftRight_le _ _) (a*x).isLt)
  rw [he]
  have hr := BitVec.toNat_ushiftRight_lt (a*x) (w-bits) (Nat.sub_le _ _)
  simpa [Nat.sub_sub_self hb] using hr

/-- Enumeration starts at one and advances by two, with no word-sized counter
representing the modulus and no materialized list of seeds. -/
def first (w : Nat) : Word (w+1) := word (w+1) 1

def advance (a : Word w) : Word w := a + word w 2

def candidate (w i : Nat) : Word (w+1) := word (w+1) (2*i+1)

theorem candidate_zero : candidate w 0 = first w := rfl

theorem candidate_succ (i : Nat) : candidate w (i+1) = advance (candidate w i) := by
  unfold candidate advance word
  rw [BitVec.ofNat_add_ofNat]
  congr 1

theorem candidate_encode (a : Seed w) : candidate w a.val = encode a := rfl

theorem candidate_covers (a : Word (w+1)) (ha : a.toNat%2 = 1) :
    ∃ i < 2^w, candidate w i = a := by
  obtain ⟨i, hi⟩ := encode_covers a ha
  exact ⟨i.val, i.isLt, hi⟩

theorem candidate_before_wrap (hi : i < 2^w) :
    (candidate w i).toNat = 2*i+1 := encode_toNat ⟨i, hi⟩

theorem candidate_wrap : candidate w (2^w) = first w := by
  unfold candidate first word
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_ofNat, Nat.pow_succ, Nat.mul_comm]

end Hashing.MultiplyShift
