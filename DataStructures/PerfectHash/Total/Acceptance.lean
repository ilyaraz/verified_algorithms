import DataStructures.PerfectHash.Total.Selection
import Hashing.MultiplyShiftProbability

namespace PerfectHash.Total
open WordRam Bounded Hashing.MultiplyShift Hashing.PowerOfTwo FiniteProbability

variable {v : Nat} {xs : List (Word (v+1))} {l : Layout}

theorem root_acceptance (xs : List (Word (v+1))) (a : Seed v) :
    rootAccepted xs (encode a) = rootAccept (roundedFamily v (values xs).length) (values xs) a := by
  apply Bool.eq_iff_iff.mpr
  simp only [rootAccepted,rootAccept,decide_eq_true_eq]
  rw [← Buckets.energy_identity]
  rfl

theorem root_seed_rejection (ha : Admissible (v+1) xs.length l) :
    Retry.rejection (fun a : Seed v => rootAccepted xs (encode a)) ≤ 1/2 := by
  have hf : (values xs).length ≤ 2^(v+1) := by
    have := ha.arithmetic.linearSizes
    have := values_length_le xs
    change 64*(xs.length+1) < 2^(v+1) at *
    omega
  simp only [root_acceptance]
  exact PerfectHash.root_rejection _ (roundedFamily_collision hf)
    (by rw [computeSize_eq]; exact positive _) _ (values_nodup xs)
    (by rw [computeSize_eq]; exact covers _)

/-- The machine sampler's two-to-one fibers preserve each seed acceptance law. -/
theorem raw_rejection (accept : Word (v+1) → Bool) :
    Retry.rejection (fun raw => accept (sample raw)) =
      Retry.rejection (fun a : Seed v => accept (encode a)) := by
  classical
  unfold Retry.rejection FiniteProbability.probability
  simp only [sample_eq_encode]
  convert mean_rawSeed (fun a => if accept (encode a) = false then 1 else 0) using 1 <;>
    apply mean_congr <;> intro a <;> split <;> simp_all

theorem root_raw_rejection (ha : Admissible (v+1) xs.length l) :
    Retry.rejection (fun raw => rootAccepted xs (sample raw)) ≤ 1/2 := by
  rw [raw_rejection]
  exact root_seed_rejection ha



theorem child_hash_family (hw : v+1 < modulus (v+1)) (hb : ¬ b ≤ 1)
    (a : Seed v) (x : Word (v+1)) :
    childHash (v+1) b (encode a) x = ((roundedFamily v (2*b*b)).eval a x).val := by
  simp only [childHash,Construction.Allocation.childShift,hb,↓reduceIte,unsignedShiftRight,
    roundedFamily,Hashing.MultiplyShift.eval,
    word_toNat_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hw)]

theorem child_acceptance (ha : Admissible (v+1) xs.length l) (root : Word (v+1))
    (b : Fin (rootSlots xs)) (hb : ¬ bucketCount xs root b ≤ 1) (a : Seed v) :
    childAccepted xs root b (encode a) =
      childAccept (roundedFamily v (2*bucketCount xs root b*bucketCount xs root b)) (bucketKeys xs root b) a := by
  unfold childAccepted
  rw [show childHash (v+1) (bucketCount xs root b) (encode a) =
    (fun x => ((roundedFamily v (2*bucketCount xs root b*bucketCount xs root b)).eval a x).val) from
    funext (child_hash_family ha.arithmetic.widthValue hb a)]
  exact Construction.child_acceptance _ _ (bucket_nodup xs root b) a

theorem child_seed_rejection (ha : Admissible (v+1) xs.length l) {root : Word (v+1)}
    (hr : rootAccepted xs root = true) (b : Fin (rootSlots xs)) :
    Retry.rejection (fun a : Seed v => childAccepted xs root b (encode a)) ≤ 1/2 := by
  classical
  by_cases hb : bucketCount xs root b ≤ 1
  · have hg : ∀ a : Seed v, childAccepted xs root b (encode a) = true :=
      fun a => child_direct_accepted ha hb (encode a)
    simp [Retry.rejection,FiniteProbability.probability,hg]
  · have hq := (bucket_fit ha hr b).2
    have hc := covers (2*bucketCount xs root b*bucketCount xs root b)
    rw [← computeSize_eq] at hc
    simp only [childCapacity,Sizes.childSlots,hb,↓reduceIte] at hq
    have hfit : 2*bucketCount xs root b*bucketCount xs root b ≤ 2^(v+1) := by
      change _ < 2^(v+1) at hq
      omega
    have he : (fun a : Seed v => childAccepted xs root b (encode a)) =
        childAccept (roundedFamily v (2*bucketCount xs root b*bucketCount xs root b)) (bucketKeys xs root b) := by
      funext a; exact child_acceptance ha root b hb a
    rw [he]
    apply PerfectHash.child_rejection _ (roundedFamily_collision hfit)
      (by rw [computeSize_eq]; exact positive _) _ (bucket_nodup xs root b)
    rw [bucket_length]
    nlinarith

theorem child_raw_rejection (ha : Admissible (v+1) xs.length l) {root : Word (v+1)}
    (hr : rootAccepted xs root = true) (b : Fin (rootSlots xs)) :
    Retry.rejection (fun raw => childAccepted xs root b (sample raw)) ≤ 1/2 := by
  rw [raw_rejection]
  exact child_seed_rejection ha hr b


/-- Every admissible width has an accepted root among the enumerated odd seeds. -/
theorem root_fallback_total {w : Nat} {xs : List (Word w)} {l : Layout}
    (ha : Admissible w xs.length l) :
    ∃ a, fallbackChoice (rootAccepted xs) = some a ∧ rootAccepted xs a = true := by
  cases w with
  | zero => have := ha.arithmetic.positiveWidth; omega
  | succ v => exact fallback_total (FiniteSearch.good_exists _ (root_seed_rejection ha))

theorem child_fallback_total {w : Nat} {xs : List (Word w)} {l : Layout}
    (ha : Admissible w xs.length l) {a : Word w} (hr : rootAccepted xs a = true)
    (b : Fin (rootSlots xs)) :
    ∃ chosen, fallbackChoice (childAccepted xs a b) = some chosen ∧ childAccepted xs a b chosen = true := by
  cases w with
  | zero => have := ha.arithmetic.positiveWidth; omega
  | succ v => exact fallback_total (FiniteSearch.good_exists _ (child_seed_rejection ha hr b))

theorem root_rejection_all {w : Nat} {xs : List (Word w)} {l : Layout}
    (ha : Admissible w xs.length l) :
    Retry.rejection (fun raw => rootAccepted xs (sample raw)) ≤ 1/2 := by
  cases w with
  | zero => have := ha.arithmetic.positiveWidth; omega
  | succ v => exact root_raw_rejection ha

theorem child_rejection_all {w : Nat} {xs : List (Word w)} {l : Layout}
    (ha : Admissible w xs.length l) {a : Word w} (hr : rootAccepted xs a = true)
    (b : Fin (rootSlots xs)) :
    Retry.rejection (fun raw => childAccepted xs a b (sample raw)) ≤ 1/2 := by
  cases w with
  | zero => have := ha.arithmetic.positiveWidth; omega
  | succ v => exact child_raw_rejection ha hr b

end PerfectHash.Total

