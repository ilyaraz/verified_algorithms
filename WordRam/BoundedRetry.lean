import WordRam.Refinement
import Probability.Retry

namespace WordRam

/-- Addresses exposed by a retry prefix, in execution order. -/
def consecutiveAddresses (w start : Nat) : Nat → List (Addr w)
  | 0 => []
  | n+1 => word w start :: consecutiveAddresses w (start+1) n

@[simp] theorem consecutiveAddresses_length (w start n : Nat) :
    (consecutiveAddresses w start n).length = n := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih => simp [consecutiveAddresses,ih]

theorem consecutiveAddresses_member (h : a ∈ consecutiveAddresses w start n) :
    ∃ i < n, a = word w (start+i) := by
  induction n generalizing start with
  | zero => simp [consecutiveAddresses] at h
  | succ n ih =>
    simp only [consecutiveAddresses,List.mem_cons] at h
    rcases h with h | h
    · exact ⟨0,by omega,by simpa using h⟩
    · obtain ⟨i,hi,he⟩ := ih h
      exact ⟨i+1,by omega,by simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using he⟩

theorem consecutiveAddresses_nodup (hf : start+n < modulus w) :
    (consecutiveAddresses w start n).Nodup := by
  induction n generalizing start with
  | zero => simp [consecutiveAddresses]
  | succ n ih =>
    rw [consecutiveAddresses,List.nodup_cons]
    refine ⟨?_,ih (by omega)⟩
    intro hm
    obtain ⟨i,hi,he⟩ := consecutiveAddresses_member hm
    have := (word_eq_iff_of_lt (by omega : start < modulus w) (by omega : start+1+i < modulus w)).mp he
    omega

theorem consecutiveAddresses_append (w start n m : Nat) :
    consecutiveAddresses w start (n+m) =
      consecutiveAddresses w start n ++ consecutiveAddresses w (start+n) m := by
  induction n generalizing start with
  | zero => simp [consecutiveAddresses]
  | succ n ih =>
    rw [show n+1+m = (n+m)+1 by omega,consecutiveAddresses,ih,consecutiveAddresses]
    simp [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem consecutiveAddresses_sublist (w start : Nat) (h : n ≤ m) :
    (consecutiveAddresses w start n).Sublist (consecutiveAddresses w start m) := by
  rw [show m = n+(m-n) by omega,consecutiveAddresses_append]
  exact List.sublist_append_left _ _

/-- A concrete retry step must charge its sampling, candidate trial, and both
continuation branches. The invariant includes the actual budget and cursor.
The generic theorem does not supply an uncharged sampler or hash evaluator. -/
structure RetryStepContract (p : Program R) (rho : RandomMemory w)
    (sample : Nat → α) (accept : α → Bool) (B : Nat) (policy : AccessPolicy w)
    (Inv : Nat → Nat → State w R → Prop) (Success : α → State w R → Prop) : Prop where
  step : ∀ c n s, Inv c (n+1) s →
    ∃ k t log, Steps p rho k s t log ∧ k ≤ B ∧ policy.AllowsTrace log ∧
      log.filterMap Access.randomAddress = [word w c] ∧
      if accept (sample c) then Success (sample c) t else Inv (c+1) n t

variable {w R B c n : Nat} {p : Program R} {rho : RandomMemory w} {α : Type*}
  {sample : Nat → α} {accept : α → Bool} {policy : AccessPolicy w}
  {Inv : Nat → Nat → State w R → Prop} {Success : α → State w R → Prop} {s : State w R}

/-- Refinement of bounded RAM retries to the same finite stopping rule used by
the probability library. Both cost and exposed addresses stop at first success. -/
theorem RetryStepContract.run (h : RetryStepContract p rho sample accept B policy Inv Success)
    (hin : Inv c n s) :
    ∃ k t log, Steps p rho k s t log ∧
      k ≤ B * FiniteProbability.Retry.attempts accept n (fun i => sample (c+i.val)) ∧
      policy.AllowsTrace log ∧
      log.filterMap Access.randomAddress = consecutiveAddresses w c
        (FiniteProbability.Retry.attempts accept n (fun i => sample (c+i.val))) ∧
      match FiniteProbability.Retry.find accept n (fun i => sample (c+i.val)) with
      | none => Inv (c+n) 0 t
      | some a => Success a t := by
  induction n generalizing c s with
  | zero =>
    exact ⟨0,s,[],.refl _,by simp [FiniteProbability.Retry.attempts],by simp [AccessPolicy.AllowsTrace],
      rfl,by simpa [FiniteProbability.Retry.find] using hin⟩
  | succ n ih =>
    obtain ⟨k,t,log,ht,hk,hpol,hr,hpost⟩ := h.step c n s hin
    cases ha : accept (sample c)
    · simp only [ha,Bool.false_eq_true,↓reduceIte] at hpost
      obtain ⟨k',u,log',hu,hk',hpol',hr',hpost'⟩ := ih hpost
      refine ⟨k+k',u,log++log',ht.trans hu,?_,
        (AccessPolicy.allowsTrace_append _).mpr ⟨hpol,hpol'⟩,?_,?_⟩
      · simp only [FiniteProbability.Retry.attempts,Fin.val_zero,Nat.add_zero,ha,Bool.false_eq_true,↓reduceIte,Fin.val_succ]
        have he : (fun i : Fin n => sample (c+(i.val+1))) = (fun i : Fin n => sample (c+1+i.val)) := by
          funext i; congr 1; omega
        rw [he,Nat.mul_add,Nat.mul_one]
        omega
      · simp only [List.filterMap_append,hr,hr',FiniteProbability.Retry.attempts,
          Fin.val_zero,Nat.add_zero,ha,Bool.false_eq_true,↓reduceIte,Fin.val_succ]
        have he : (fun i : Fin n => sample (c+(i.val+1))) = (fun i : Fin n => sample (c+1+i.val)) := by
          funext i; congr 1; omega
        rw [he,Nat.add_comm 1,consecutiveAddresses]
        rfl
      · simpa only [FiniteProbability.Retry.find,Fin.val_zero,Nat.add_zero,ha,Bool.false_eq_true,
          ↓reduceIte,Fin.val_succ,Nat.add_assoc,Nat.add_comm 1] using hpost'
    · simp only [ha,↓reduceIte] at hpost
      refine ⟨k,t,log,ht,?_,hpol,?_,?_⟩
      · simpa [FiniteProbability.Retry.attempts,ha] using hk
      · simpa [FiniteProbability.Retry.attempts,ha,consecutiveAddresses] using hr
      · simpa [FiniteProbability.Retry.find,ha] using hpost

end WordRam
