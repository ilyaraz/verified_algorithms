import Probability.Retry

/-! A bounded random phase followed by a complete deterministic enumeration.
The abstract enumeration is proof-side data; RAM enumeration is implemented by
incrementing an encoded seed, not by allocating this list. -/
namespace FiniteProbability.FiniteSearch
open FiniteProbability
open scoped Classical

variable {α : Type*}

/-- Random search returns an accepted input sample; fallback searches the actual
provided enumeration. No existential proof chooses the returned candidate. -/
def search (accept : α → Bool) (enumeration : List α) (r : Nat) (samples : Fin r → α) : Option α :=
  (Retry.find accept r samples).orElse (fun _ => enumeration.find? accept)

theorem enumeration_succeeds (accept : α → Bool) (enumeration : List α)
    (covers : ∀ a, a ∈ enumeration) (good : ∃ a, accept a = true) :
    ∃ a, enumeration.find? accept = some a ∧ accept a = true := by
  cases he : enumeration.find? accept with
  | none =>
    have hnone := List.find?_eq_none.mp he
    obtain ⟨a, ha⟩ := good
    exact False.elim (hnone a (covers a) ha)
  | some a => exact ⟨a, rfl, List.find?_some he⟩

theorem total (accept : α → Bool) (enumeration : List α)
    (covers : ∀ a, a ∈ enumeration) (good : ∃ a, accept a = true)
    (r : Nat) (samples : Fin r → α) :
    ∃ a, search accept enumeration r samples = some a ∧ accept a = true := by
  cases hr : Retry.find accept r samples with
  | some a => exact ⟨a, by simp [search, hr], Retry.find_sound _ _ _ hr⟩
  | none =>
    obtain ⟨a, ha, hg⟩ := enumeration_succeeds accept enumeration covers good
    exact ⟨a, by simp [search, hr, ha], hg⟩

/-- Count the candidates actually tested by the deterministic fallback. -/
def enumerationAttempts (accept : α → Bool) : List α → Nat
  | [] => 0
  | a :: tail => if accept a then 1 else 1 + enumerationAttempts accept tail

theorem enumerationAttempts_le (accept : α → Bool) (enumeration : List α) :
    enumerationAttempts accept enumeration ≤ enumeration.length := by
  induction enumeration with
  | nil => rfl
  | cons a tail ih => simp only [enumerationAttempts, List.length_cons]; split <;> omega

/-- Cost of the actual abstract search, charging B for every tested candidate. -/
def searchWork (accept : α → Bool) (enumeration : List α) (B r : Nat) (samples : Fin r → α) : Nat :=
  B * (Retry.attempts accept r samples +
    if Retry.failed accept r samples then enumerationAttempts accept enumeration else 0)

/-- Every random trial and every possible fallback trial is charged at B. Any
initialization/finishing costs must be added by the caller; retry overhead belongs
in B. Work on all rejected candidates remains included. -/
def work (accept : α → Bool) (H B r : Nat) (samples : Fin r → α) : Nat :=
  B * (Retry.attempts accept r samples + if Retry.failed accept r samples then H else 0)

theorem work_le (accept : α → Bool) (H B r : Nat) (samples : Fin r → α) :
    work accept H B r samples ≤ B*(r+H) := by
  apply Nat.mul_le_mul_left
  have := Retry.attempts_le accept r samples
  split <;> omega

theorem searchWork_le (accept : α → Bool) (enumeration : List α) (B r : Nat)
    (samples : Fin r → α) :
    searchWork accept enumeration B r samples ≤ work accept enumeration.length B r samples := by
  unfold searchWork work
  apply Nat.mul_le_mul_left
  have := enumerationAttempts_le accept enumeration
  split <;> omega

noncomputable section
variable [Fintype α] [Nonempty α]

theorem good_exists (accept : α → Bool) (hq : Retry.rejection accept ≤ 1/2) :
    ∃ a, accept a = true := by
  by_contra hn
  have hfalse : ∀ a, accept a = false := by simpa using hn
  have he : Retry.rejection accept = 1 := by
    simp [Retry.rejection, probability, hfalse]
  rw [he] at hq
  norm_num at hq

omit [Nonempty α] in
theorem expected_work_eq (accept : α → Bool) (H B r : Nat) :
    mean (fun samples : Fin r → α => (work accept H B r samples : ℝ)) =
      B * mean (fun samples : Fin r → α => (Retry.attempts accept r samples : ℝ)) +
        (B*H : Nat) * probability (fun samples : Fin r → α => Retry.failed accept r samples = true) := by
  have he : ∀ samples : Fin r → α, (work accept H B r samples : ℝ) =
      (B : ℝ) * (Retry.attempts accept r samples : ℝ) +
        (B*H : Nat) * (if Retry.failed accept r samples = true then 1 else 0) := by
    intro samples
    cases hf : Retry.failed accept r samples <;> simp [work, hf, Nat.cast_mul, Nat.cast_add]
    ring
  rw [mean_congr he, mean_add, mean_mul, mean_mul, mean_indicator]

theorem expected_work (accept : α → Bool) (hq : Retry.rejection accept ≤ 1/2)
    (H B r : Nat) :
    mean (fun samples : Fin r → α => (work accept H B r samples : ℝ)) ≤
      2*B + (1/2 : ℝ)^r * H * B := by
  rw [expected_work_eq]
  have ha := Retry.expected_attempts accept hq r
  have hq0 : 0 ≤ Retry.rejection accept := probability_nonneg _
  have hpow := pow_nonneg hq0 r
  have hat : mean (fun samples : Fin r → α => (Retry.attempts accept r samples : ℝ)) ≤ 2 := by
    nlinarith
  have hf := Retry.fallback_bound accept hq r
  have h₁ := mul_le_mul_of_nonneg_left hat (Nat.cast_nonneg B : (0 : ℝ) ≤ B)
  have h₂ := mul_le_mul_of_nonneg_left hf (Nat.cast_nonneg (B*H) : (0 : ℝ) ≤ (B*H : Nat))
  push_cast at *
  nlinarith

/-- With w random attempts and at most 2^(w-1) fallback candidates, the entire
trial work is at most 3B in expectation, including every random image. -/
theorem expected_work_word (accept : α → Bool) (hq : Retry.rejection accept ≤ 1/2)
    (B w : Nat) :
    mean (fun samples : Fin w → α => (work accept (2^(w-1)) B w samples : ℝ)) ≤ 3*B := by
  have h := expected_work accept hq (2^(w-1)) B w
  have he : (1/2 : ℝ)^w * 2^w = 1 := by rw [← mul_pow]; norm_num
  have hp : (2 : ℝ)^(w-1) ≤ 2^w := by
    exact pow_le_pow_right₀ (by norm_num) (Nat.sub_le w 1)
  have hm := mul_le_mul_of_nonneg_left hp (show 0 ≤ (1/2 : ℝ)^w by positivity)
  rw [he] at hm
  have hB := mul_le_mul_of_nonneg_right hm (Nat.cast_nonneg B : (0 : ℝ) ≤ B)
  push_cast at h
  nlinarith

theorem expected_searchWork (accept : α → Bool) (hq : Retry.rejection accept ≤ 1/2)
    (enumeration : List α) (B r : Nat) :
    mean (fun samples : Fin r → α => (searchWork accept enumeration B r samples : ℝ)) ≤
      2*B + (1/2 : ℝ)^r * enumeration.length * B := by
  apply le_trans _ (expected_work accept hq enumeration.length B r)
  apply mean_mono
  intro samples
  exact_mod_cast searchWork_le accept enumeration B r samples

end
end FiniteProbability.FiniteSearch
