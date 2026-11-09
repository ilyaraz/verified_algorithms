import DataStructures.PerfectHash.Source.Search.Model
import DataStructures.PerfectHash.Total.Selection

namespace PerfectHash.Source.Total
open WordRam FiniteProbability

/-- The ghost finite prefix is exactly the established odd-seed enumeration. -/
theorem fallback_eq (accept : Word w → Bool) :
    RamLang.Library.Search.choice (PerfectHash.Total.candidate w) accept 0 (PerfectHash.Total.seedCount w) =
      PerfectHash.Total.fallbackChoice accept := by
  rw [Source.Search.choice_eq]
  simp only [Nat.zero_add]
  rfl

/-- The source continuation selects the same multiplier as the pure two-phase model. -/
theorem selection_eq (rho : RandomMemory w) (accept : Word w → Bool) (c : Nat) (fallback : Word w)
    (hf : PerfectHash.Total.fallbackChoice accept = some fallback) :
    (RamLang.Library.Search.choice (Source.Search.Root.sample rho) accept c w).getD fallback =
      PerfectHash.Total.selected accept (fun i => rho (word w (c+i.val))) := by
  rw [Source.Search.choice_eq]
  unfold Source.Search.Root.sample PerfectHash.Total.selected PerfectHash.Total.searchChoice
  cases he : Retry.find accept w (fun i => Hashing.MultiplyShift.sample (rho (word w (c+i.val)))) <;> simp [he,hf]

/-- Source random-prefix counts and fallback charges agree with the probability model. -/
theorem trial_work_eq (rho : RandomMemory w) (accept : Word w → Bool) (c B : Nat) :
    B*(RamLang.Library.Search.attempts (Source.Search.Root.sample rho) accept c w +
      if (RamLang.Library.Search.choice (Source.Search.Root.sample rho) accept c w).isNone
        then PerfectHash.Total.seedCount w else 0) =
      PerfectHash.Total.trialWork accept B (fun i => rho (word w (c+i.val))) := by
  rw [Source.Search.choice_eq,Source.Search.attempts_eq,PerfectHash.Total.trial_work_eq]
  unfold Source.Search.Root.sample
  congr 2
  apply ite_congr ?_ (fun _ => rfl) (fun _ => rfl)
  simp only [Option.isNone_iff_eq_none]
  exact propext (Retry.find_none_iff _ _ _)

/-- Enumeration never uses zero at positive width. -/
theorem fallback_nonzero (hw : 0 < w) (accept : Word w → Bool)
    (hf : PerfectHash.Total.fallbackChoice accept = some a) : a ≠ word w 0 := by
  rw [← fallback_eq] at hf
  obtain ⟨i,hi,rfl⟩ := Source.Search.choice_member hf
  cases w with
  | zero => omega
  | succ v =>
    have hi' : i < 2^v := by simpa [PerfectHash.Total.seedCount] using hi
    have he : PerfectHash.Total.candidate (v+1) (0+i) =
        Hashing.MultiplyShift.encode (⟨i,hi'⟩ : Hashing.MultiplyShift.Seed v) := by simp [PerfectHash.Total.candidate,Hashing.MultiplyShift.encode]
    rw [he]
    intro hz
    have ho := Hashing.MultiplyShift.encode_odd (⟨i,hi'⟩ : Hashing.MultiplyShift.Seed v)
    rw [hz] at ho
    simp [word_toNat] at ho

/-- Every successful two-phase selection can be stored in the nonzero seed field. -/
theorem selection_nonzero (hw : 0 < w) (rho : RandomMemory w) (accept : Word w → Bool) (c : Nat)
    (hg : ∃ a, PerfectHash.Total.fallbackChoice accept = some a ∧ accept a = true) :
    PerfectHash.Total.selected accept (fun i => rho (word w (c+i.val))) ≠ word w 0 := by
  obtain ⟨fallback,hf,_⟩ := hg
  rw [← selection_eq rho accept c fallback hf]
  cases he : RamLang.Library.Search.choice (Source.Search.Root.sample rho) accept c w with
  | none => exact fallback_nonzero hw accept hf
  | some a => exact Source.Search.choice_ne_zero hw he

end PerfectHash.Source.Total
