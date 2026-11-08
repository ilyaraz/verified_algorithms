import DataStructures.PerfectHash.Total.Program
import Probability.RetryTransform
import Probability.FiniteSearch

namespace PerfectHash.Total
open WordRam FiniteProbability

/-- Size of the complete odd-multiplier enumeration; no seed array is allocated. -/
def seedCount (w : Nat) : Nat := Nat.pow 2 (w-1)

def candidate (w i : Nat) : Word w := word w (2*i+1)

theorem candidate_next (w i : Nat) : candidate w i+word w 2 = candidate w (i+1) := by
  unfold candidate
  rw [word_add]
  congr 1

theorem seed_count_pos (w : Nat) : 0 < seedCount w := Nat.two_pow_pos _

/-- Proof-side stopping rule for the register-only deterministic enumeration. -/
def fallbackChoice (accept : Word w → Bool) : Option (Word w) :=
  Retry.find accept (seedCount w) (fun i => candidate w i.val)

/-- The exact two-phase stopping rule, expressed on the raw addressed samples. -/
def searchChoice (accept : Word w → Bool) (samples : Fin w → Word w) : Option (Word w) :=
  (Retry.find accept w (fun i => Hashing.MultiplyShift.sample (samples i))).orElse
    (fun _ => fallbackChoice accept)

def selected (accept : Word w → Bool) (samples : Fin w → Word w) : Word w :=
  (searchChoice accept samples).getD (word w 1)

/-- Full enumeration covers every encoded multiplier at positive width. -/
theorem fallback_total {accept : Word (v+1) → Bool}
    (hg : ∃ a : Hashing.MultiplyShift.Seed v, accept (Hashing.MultiplyShift.encode a) = true) :
    ∃ a, fallbackChoice accept = some a ∧ accept a = true := by
  apply Retry.find_exists
  obtain ⟨a,ha⟩ := hg
  refine ⟨⟨a.val,by simpa [seedCount] using a.isLt⟩,?_⟩
  exact ha

theorem search_total (accept : Word w → Bool) (samples : Fin w → Word w)
    (hg : ∃ a, fallbackChoice accept = some a ∧ accept a = true) :
    searchChoice accept samples = some (selected accept samples) ∧ accept (selected accept samples) = true := by
  cases he : Retry.find accept w (fun i => Hashing.MultiplyShift.sample (samples i)) with
  | some a =>
    have hs : searchChoice accept samples = some a := by simp [searchChoice,he]
    simp only [selected,hs,Option.getD_some]
    exact ⟨trivial,Retry.find_sound _ _ _ he⟩
  | none =>
    obtain ⟨a,ha,hgood⟩ := hg
    have hs : searchChoice accept samples = some a := by simp [searchChoice,he,ha]
    simp only [selected,hs,Option.getD_some]
    exact ⟨trivial,hgood⟩


/-- Actual random attempts plus the full fallback upper bound, charged only on
exhaustion. This majorant includes every random-memory image. -/
def trialWork (accept : Word w → Bool) (B : Nat) (samples : Fin w → Word w) : Nat :=
  FiniteSearch.work (fun raw => accept (Hashing.MultiplyShift.sample raw)) (seedCount w) B w samples

theorem trial_work_eq (accept : Word w → Bool) (B : Nat) (samples : Fin w → Word w) :
    trialWork accept B samples = B *
      (Retry.attempts accept w (fun i => Hashing.MultiplyShift.sample (samples i)) +
       if Retry.failed accept w (fun i => Hashing.MultiplyShift.sample (samples i)) then seedCount w else 0) := by
  simp only [trialWork,FiniteSearch.work,Retry.attempts_map,Retry.failed_map]

theorem selected_random (accept : Word w → Bool) (samples : Fin w → Word w)
    (h : Retry.find accept w (fun i => Hashing.MultiplyShift.sample (samples i)) = some a) :
    selected accept samples = a := by simp [selected,searchChoice,h]

theorem selected_fallback (accept : Word w → Bool) (samples : Fin w → Word w)
    (h : Retry.find accept w (fun i => Hashing.MultiplyShift.sample (samples i)) = none)
    (hf : fallbackChoice accept = some a) : selected accept samples = a := by
  simp [selected,searchChoice,h,hf]

theorem trial_work_random (accept : Word w → Bool) (B : Nat) (samples : Fin w → Word w)
    (h : Retry.find accept w (fun i => Hashing.MultiplyShift.sample (samples i)) = some a) :
    trialWork accept B samples = B*Retry.attempts accept w (fun i => Hashing.MultiplyShift.sample (samples i)) := by
  rw [trial_work_eq]
  have hf : Retry.failed accept w (fun i => Hashing.MultiplyShift.sample (samples i)) = false := by
    apply Bool.eq_false_iff.mpr
    intro hf
    have hh := (Retry.find_none_iff _ _ _).mpr hf
    rw [h] at hh
    cases hh
  simp [hf]

theorem trial_work_fallback (accept : Word w → Bool) (B : Nat) (samples : Fin w → Word w)
    (h : Retry.find accept w (fun i => Hashing.MultiplyShift.sample (samples i)) = none) :
    trialWork accept B samples = B*
      (Retry.attempts accept w (fun i => Hashing.MultiplyShift.sample (samples i))+seedCount w) := by
  rw [trial_work_eq]
  simp [(Retry.find_none_iff _ _ _).mp h]

end PerfectHash.Total

