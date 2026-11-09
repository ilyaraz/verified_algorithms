import DataStructures.PerfectHash.Source.Search.Child
import Probability.Retry
import DataStructures.PerfectHash.Bounded.Work

namespace PerfectHash.Source.Search
open WordRam RamLang.Compiler

/-- The source loop's first-success model is the existing finite-tuple model.
This equality permits reuse of probability lemmas without using assembly runs. -/
theorem choice_eq (sample : Nat → Word w) (accept : Word w → Bool) (c n : Nat) :
    RamLang.Library.Search.choice sample accept c n =
      FiniteProbability.Retry.find accept n (fun i => sample (c+i.val)) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    simp only [RamLang.Library.Search.choice,FiniteProbability.Retry.find,Nat.add_zero]
    split
    · rfl
    · rw [ih]
      congr 1
      funext i
      congr 1
      simp [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

/-- Exact source trial counts coincide with the probability library's stopping
time, including rejected attempts and the final successful attempt. -/
theorem attempts_eq (sample : Nat → Word w) (accept : Word w → Bool) (c n : Nat) :
    RamLang.Library.Search.attempts sample accept c n =
      FiniteProbability.Retry.attempts accept n (fun i => sample (c+i.val)) := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih =>
    simp only [RamLang.Library.Search.attempts,FiniteProbability.Retry.attempts,Nat.add_zero]
    split
    · rfl
    · rw [ih]
      congr 2
      funext i
      congr 1
      simp [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

/-- At positive width, the source sampler never returns the failure sentinel. -/
theorem sample_ne_zero (hw : 0 < w) (rho : RandomMemory w) (c : Nat) :
    Root.sample rho c ≠ word w 0 := by
  cases w with
  | zero => omega
  | succ v =>
    unfold Root.sample
    rw [Hashing.MultiplyShift.sample_eq_encode]
    intro he
    have hh := Hashing.MultiplyShift.encode_odd (Hashing.MultiplyShift.rawIndex (rho (word (v+1) c)))
    rw [he] at hh
    simp [word_toNat] at hh

/-- A selected candidate was produced at an actual position in its prefix. -/
theorem choice_member {sample : Nat → Word w} {accept : Word w → Bool} {c n : Nat} {a : Word w}
    (h : RamLang.Library.Search.choice sample accept c n = some a) :
    ∃ i, i < n ∧ a = sample (c+i) := by
  induction n generalizing c with
  | zero => cases h
  | succ n ih =>
    simp only [RamLang.Library.Search.choice] at h
    split at h
    · cases h; exact ⟨0,by omega,by simp⟩
    · obtain ⟨i,hi,he⟩ := ih h
      exact ⟨i+1,by omega,by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using he⟩

/-- Successful sampled searches return nonzero; zero denotes budget failure. -/
theorem choice_ne_zero (hw : 0 < w) {rho : RandomMemory w} {accept : Word w → Bool} {c n : Nat}
    (h : RamLang.Library.Search.choice (Root.sample rho) accept c n = some a) : a ≠ word w 0 := by
  obtain ⟨i,_,rfl⟩ := choice_member h
  exact sample_ne_zero hw rho _

/-- Root grouping's early energy check matches the existing total energy model. -/
theorem root_accept (xs : List (Word w)) (seed : Word w) :
    Root.accept (PerfectHash.Bounded.rootHash xs) (PerfectHash.Bounded.values xs) seed =
      PerfectHash.Bounded.rootAccepted xs seed := by
  apply Bool.eq_iff_iff.mpr
  rw [Root.accept,PerfectHash.Construction.groupAccepted_iff]
  simp only [Buckets.energy_nil,Nat.zero_add,List.append_nil,PerfectHash.Bounded.rootAccepted,decide_eq_true_eq]
  rw [PerfectHash.Construction.energy_perm _ (List.reverse_perm _)]

/-- Child slot insertion uses precisely the bucket-chain order of the original
mathematical acceptance predicate. -/
theorem child_accept (xs : List (Word w)) (a : Word w) (b : Fin (PerfectHash.Bounded.rootSlots xs)) :
    Child.accept (PerfectHash.Bounded.childHash w (PerfectHash.Bounded.bucketCount xs a b))
      (PerfectHash.Bounded.bucketChain xs a b) = PerfectHash.Bounded.childAccepted xs a b := rfl

/-- The source trace observer uses the same consecutive-address lists as the
public random-reservation API. -/
theorem addresses_eq (w c n : Nat) : RamLang.Library.Retry.addresses w c n = consecutiveAddresses w c n := by
  induction n generalizing c with
  | zero => rfl
  | succ n ih => simp only [RamLang.Library.Retry.addresses,consecutiveAddresses,ih]

end PerfectHash.Source.Search
