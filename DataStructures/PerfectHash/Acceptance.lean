import DataStructures.PerfectHash.Buckets
import Probability.FiniteSearch

namespace PerfectHash
open Buckets

/-- Root trials accept at the explicit linear energy threshold six times d. -/
def rootAccept (family : Hashing.Family Key Seed m) (xs : List Key) (a : Seed) : Bool :=
  decide (xs.length+2*pairs (family.eval a) xs ≤ 6*xs.length)

/-- Child trials accept precisely when no two distinct input positions collide. -/
def childAccept (family : Hashing.Family Key Seed m) (xs : List Key) (a : Seed) : Bool :=
  decide (pairs (family.eval a) xs = 0)

noncomputable section
open FiniteProbability
open scoped Classical
variable {Key Seed : Type} [DecidableEq Key] [Fintype Seed] [Nonempty Seed]

theorem expected_root_energy (family : Hashing.Family Key Seed m)
    (hc : Hashing.CollisionBound family 2) (hm : 0 < m)
    (xs : List Key) (hx : xs.Nodup) (hs : xs.length ≤ m) :
    mean (fun a => (energy (family.eval a) xs : ℝ)) ≤ 3*xs.length := by
  have he := expected_energy family hc hm xs hx
  have hmp : (0 : ℝ) < m := by exact_mod_cast hm
  have hsp : (xs.length : ℝ) ≤ m := by exact_mod_cast hs
  have hh : (2 : ℝ)/m*xs.length ≤ 2 := by
    have hh := mul_le_mul_of_nonneg_left hsp (show (0 : ℝ) ≤ 2/m by positivity)
    simpa [hmp.ne'] using hh
  have hn : (0 : ℝ) ≤ xs.length := Nat.cast_nonneg _
  have hc0 : (0 : ℝ) ≤ 2/m := by positivity
  have hbound := mul_le_mul_of_nonneg_right hh hn
  push_cast at he
  nlinarith

/-- Markov's inequality proves at least one-half root acceptance, with empty
input handled directly rather than dividing by a zero threshold. -/
theorem root_rejection (family : Hashing.Family Key Seed m)
    (hc : Hashing.CollisionBound family 2) (hm : 0 < m)
    (xs : List Key) (hx : xs.Nodup) (hs : xs.length ≤ m) :
    Retry.rejection (rootAccept family xs) ≤ 1/2 := by
  by_cases hn : xs.length = 0
  · have hx : xs = [] := List.length_eq_zero_iff.mp hn
    simp [Retry.rejection,rootAccept,hx,pairs]
  · have hn' : (0 : ℝ) < xs.length := by exact_mod_cast (Nat.pos_of_ne_zero hn)
    have he := expected_root_energy family hc hm xs hx hs
    have hp := probability_ge_le (fun a => (energy (family.eval a) xs : ℝ))
      (fun _ => Nat.cast_nonneg _) (show (0 : ℝ) < 6*xs.length by positivity)
    have hs' : Retry.rejection (rootAccept family xs) ≤
        probability (fun a => (6 : ℝ)*xs.length ≤ (energy (family.eval a) xs : ℝ)) := by
      apply probability_mono
      intro a ha
      simp only [rootAccept,decide_eq_false_iff_not,not_le] at ha
      rw [← energy_identity] at ha
      exact_mod_cast (Nat.le_of_lt ha)
    have hb : (mean fun a => (energy (family.eval a) xs : ℝ))/(6*xs.length) ≤ 1/2 := by
      apply (div_le_iff₀ (by positivity)).mpr
      linarith
    exact hs'.trans (hp.trans hb)

/-- Union over unordered pairs gives the exact b(b-1) child failure bound. -/
theorem child_rejection_bound (family : Hashing.Family Key Seed m)
    (hc : Hashing.CollisionBound family 2) (hm : 0 < m)
    (xs : List Key) (hx : xs.Nodup) :
    Retry.rejection (childAccept family xs) ≤ (xs.length : ℝ)*(xs.length-1)/m := by
  have he := expected_pairs family hc hm xs hx
  have hp := probability_ge_le (fun a => (pairs (family.eval a) xs : ℝ))
    (fun _ => Nat.cast_nonneg _) (show (0 : ℝ) < 1 by norm_num)
  have hh : Retry.rejection (childAccept family xs) ≤
      probability (fun a => (1 : ℝ) ≤ (pairs (family.eval a) xs : ℝ)) := by
    apply probability_mono
    intro a ha
    simp only [childAccept,decide_eq_false_iff_not] at ha
    exact_mod_cast (Nat.one_le_iff_ne_zero.mpr ha)
  have ht := hh.trans hp
  simp only [div_one,Nat.cast_ofNat] at ht he
  calc
    _ ≤ mean (fun a => (pairs (family.eval a) xs : ℝ)) := ht
    _ ≤ (2 : ℝ)/m*xs.length*(xs.length-1)/2 := he
    _ = _ := by ring

theorem child_rejection (family : Hashing.Family Key Seed m)
    (hc : Hashing.CollisionBound family 2) (hm : 0 < m)
    (xs : List Key) (hx : xs.Nodup) (hs : 2*xs.length^2 ≤ m) :
    Retry.rejection (childAccept family xs) ≤ 1/2 := by
  have he := child_rejection_bound family hc hm xs hx
  have hmp : (0 : ℝ) < m := by exact_mod_cast hm
  have hsp : (2 : ℝ)*(xs.length : ℝ)^2 ≤ m := by exact_mod_cast hs
  have hn : (0 : ℝ) ≤ xs.length := Nat.cast_nonneg _
  apply he.trans
  apply (div_le_iff₀ hmp).mpr
  nlinarith

theorem child_rejection_strict (family : Hashing.Family Key Seed m)
    (hc : Hashing.CollisionBound family 2) (hm : 0 < m)
    (xs : List Key) (hx : xs.Nodup) (hs : 2*xs.length^2 ≤ m) (hn : 0 < xs.length) :
    Retry.rejection (childAccept family xs) < 1/2 := by
  have he := child_rejection_bound family hc hm xs hx
  have hmp : (0 : ℝ) < m := by exact_mod_cast hm
  have hsp : (2 : ℝ)*(xs.length : ℝ)^2 ≤ m := by exact_mod_cast hs
  have hn' : (0 : ℝ) < xs.length := by exact_mod_cast hn
  apply lt_of_le_of_lt he
  apply (div_lt_iff₀ hmp).mpr
  nlinarith

end
end PerfectHash
