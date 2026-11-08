import Probability.Retry

namespace FiniteProbability.Retry
variable {α β : Type*}

/-- Sampling transformations commute with the deterministic stopping rule. -/
theorem find_map (f : α → β) (accept : β → Bool) (n : Nat) (samples : Fin n → α) :
    find accept n (fun i => f (samples i)) =
      (find (fun a => accept (f a)) n samples).map f := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [find]; split <;> simp_all

theorem attempts_map (f : α → β) (accept : β → Bool) (n : Nat) (samples : Fin n → α) :
    attempts accept n (fun i => f (samples i)) =
      attempts (fun a => accept (f a)) n samples := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [attempts]; split <;> simp_all

theorem failed_map (f : α → β) (accept : β → Bool) (n : Nat) (samples : Fin n → α) :
    failed accept n (fun i => f (samples i)) =
      failed (fun a => accept (f a)) n samples := by
  induction n with
  | zero => rfl
  | succ n ih => simp [failed,ih]

theorem failed_iff (accept : α → Bool) (n : Nat) (samples : Fin n → α) :
    failed accept n samples = true ↔ ∀ i, accept (samples i) = false := by
  induction n with
  | zero => simp [failed]
  | succ n ih => simp [failed,ih,Fin.forall_fin_succ]

/-- Exhausting a list known to contain an accepted candidate is impossible. -/
theorem find_exists (accept : α → Bool) (n : Nat) (samples : Fin n → α)
    (hg : ∃ i, accept (samples i) = true) : ∃ a, find accept n samples = some a ∧ accept a = true := by
  cases he : find accept n samples with
  | none =>
    have hf := (failed_iff accept n samples).mp ((find_none_iff accept n samples).mp he)
    obtain ⟨i,hi⟩ := hg
    rw [hf i] at hi
    cases hi
  | some a => exact ⟨a,rfl,find_sound accept n samples he⟩

end FiniteProbability.Retry
