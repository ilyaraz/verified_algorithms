import Probability.Finite
import Mathlib.Data.Fin.Tuple.Basic

/-! Capped retries over a finite tuple of independent uniform samples. Rejected
attempts are charged, and the fallback event is visible rather than truncated. -/
namespace FiniteProbability.Retry
open FiniteProbability
open scoped Classical

variable {α : Type*}

/-- Number of random attempts, stopping on the first accepted candidate. -/
def attempts (accept : α → Bool) : (r : Nat) → (Fin r → α) → Nat
  | 0, _ => 0
  | r+1, samples => if accept (samples ⟨0, Nat.zero_lt_succ r⟩) then 1 else 1 + attempts accept r (fun i => samples i.succ)

/-- Reaching fallback means every available random attempt was rejected. -/
def failed (accept : α → Bool) : (r : Nat) → (Fin r → α) → Bool
  | 0, _ => true
  | r+1, samples => !accept (samples ⟨0, Nat.zero_lt_succ r⟩) && failed accept r (fun i => samples i.succ)

/-- Successful random search returns the actual accepted sample. -/
def find (accept : α → Bool) : (r : Nat) → (Fin r → α) → Option α
  | 0, _ => none
  | r+1, samples => if accept (samples ⟨0, Nat.zero_lt_succ r⟩) then some (samples ⟨0, Nat.zero_lt_succ r⟩)
      else find accept r (fun i => samples i.succ)

theorem attempts_le (accept : α → Bool) (r : Nat) (samples : Fin r → α) :
    attempts accept r samples ≤ r := by
  induction r with
  | zero => rfl
  | succ r ih =>
    simp only [attempts]
    split
    · omega
    · have := ih (fun i => samples i.succ); omega

theorem find_none_iff (accept : α → Bool) (r : Nat) (samples : Fin r → α) :
    find accept r samples = none ↔ failed accept r samples = true := by
  induction r with
  | zero => simp [find, failed]
  | succ r ih =>
    simp only [find, failed]
    split <;> simp_all

theorem find_sound (accept : α → Bool) (r : Nat) (samples : Fin r → α)
    (h : find accept r samples = some a) : accept a = true := by
  induction r with
  | zero => simp [find] at h
  | succ r ih =>
    simp only [find] at h
    split at h
    · cases h; assumption
    · exact ih _ h

noncomputable section
variable [Fintype α] [Nonempty α]

omit [Nonempty α] in
/-- Splitting a finite tuple into its head and tail gives the product average. -/
theorem mean_cons (f : (Fin (r+1) → α) → ℝ) :
    mean f = mean (fun a => mean (fun tail => f (Fin.cons a tail))) := by
  rw [← mean_equiv (Fin.consEquiv (fun _ : Fin (r+1) => α)) f, mean_prod]
  rfl

def rejection (accept : α → Bool) : ℝ := probability (fun a => accept a = false)

theorem failed_probability (accept : α → Bool) (r : Nat) :
    probability (fun samples : Fin r → α => failed accept r samples = true) =
      rejection accept ^ r := by
  induction r with
  | zero => simp [failed, probability]
  | succ r ih =>
    calc
      _ = mean (fun a => if accept a = false then rejection accept ^ r else 0) := by
        rw [probability, mean_cons]
        apply mean_congr
        intro a
        cases ha : accept a
        · simp only [if_true]
          calc
            _ = probability (fun tail : Fin r → α => failed accept r tail = true) := by
              apply mean_congr
              intro tail
              simp [failed, ha]
            _ = _ := ih
        · simp [failed, ha]
      _ = rejection accept * rejection accept ^ r + (1-rejection accept)*0 :=
        mean_ite (fun a => accept a = false) _ _
      _ = _ := by simp [pow_succ, mul_comm]

theorem attempts_recurrence (accept : α → Bool) (r : Nat) :
    mean (fun samples : Fin (r+1) → α => (attempts accept (r+1) samples : ℝ)) =
      1 + rejection accept * mean (fun samples : Fin r → α => (attempts accept r samples : ℝ)) := by
  rw [mean_cons]
  have he : ∀ a, mean (fun tail : Fin r → α =>
      (attempts accept (r+1) (Fin.cons a tail) : ℝ)) =
      if accept a = false then 1 + mean (fun tail : Fin r → α => (attempts accept r tail : ℝ))
      else 1 := by
    intro a
    cases ha : accept a <;> simp [attempts, ha, mean_add]
  rw [mean_congr he, mean_ite]
  unfold rejection
  ring

/-- At failure probability at most one half, expected random attempts never
exceed two; the sharper bound retains the unused geometric tail. -/
theorem expected_attempts (accept : α → Bool) (hq : rejection accept ≤ 1/2) (r : Nat) :
    mean (fun samples : Fin r → α => (attempts accept r samples : ℝ)) ≤
      2 * (1 - rejection accept ^ r) := by
  have hq0 : 0 ≤ rejection accept := probability_nonneg _
  induction r with
  | zero => simp [attempts]
  | succ r ih =>
    rw [attempts_recurrence, pow_succ]
    have hm := mul_le_mul_of_nonneg_left ih hq0
    nlinarith

theorem fallback_bound (accept : α → Bool) (hq : rejection accept ≤ 1/2) (r : Nat) :
    probability (fun samples : Fin r → α => failed accept r samples = true) ≤ (1/2 : ℝ)^r := by
  rw [failed_probability]
  exact pow_le_pow_left₀ (probability_nonneg _) hq r

end
end FiniteProbability.Retry
