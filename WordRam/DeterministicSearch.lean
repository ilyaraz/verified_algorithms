import WordRam.BoundedRetry

namespace WordRam

/-- A deterministic candidate trial charges its control flow and preserves the
caller policy. Candidate generation executes in the implementation of `step`. -/
structure SearchStepContract (p : Program R) (rho : RandomMemory w)
    (candidate : Nat → α) (accept : α → Bool) (B : Nat) (policy : AccessPolicy w)
    (Inv : Nat → State w R → Prop) (Success : α → State w R → Prop) : Prop where
  step : ∀ i s, Inv i s →
    ∃ k t log, Steps p rho k s t log ∧ k ≤ B ∧ policy.AllowsTrace log ∧
      log.filterMap Access.randomAddress = [] ∧
      if accept (candidate i) then Success (candidate i) t else Inv (i+1) t

variable {w R B i n : Nat} {p : Program R} {rho : RandomMemory w} {α : Type*}
  {candidate : Nat → α} {accept : α → Bool} {policy : AccessPolicy w}
  {Inv : Nat → State w R → Prop} {Success : α → State w R → Prop} {s : State w R}

/-- Finite deterministic search is a charged RAM execution, including all
rejected candidates. It exposes no random cells. -/
theorem SearchStepContract.run (h : SearchStepContract p rho candidate accept B policy Inv Success)
    (hin : Inv i s) (n : Nat) :
    ∃ k t log, Steps p rho k s t log ∧ k ≤ B*n ∧ policy.AllowsTrace log ∧
      log.filterMap Access.randomAddress = [] ∧
      match FiniteProbability.Retry.find accept n (fun j => candidate (i+j.val)) with
      | none => Inv (i+n) t
      | some a => Success a t := by
  induction n generalizing i s with
  | zero =>
    exact ⟨0,s,[],.refl _,by simp,by simp [AccessPolicy.AllowsTrace],rfl,
      by simpa [FiniteProbability.Retry.find] using hin⟩
  | succ n ih =>
    obtain ⟨k,t,log,ht,hk,hpol,hr,hpost⟩ := h.step i s hin
    cases ha : accept (candidate i)
    · simp only [ha,Bool.false_eq_true,↓reduceIte] at hpost
      obtain ⟨k',u,log',hu,hk',hpol',hr',hpost'⟩ := ih hpost
      refine ⟨k+k',u,log++log',ht.trans hu,?_,
        (AccessPolicy.allowsTrace_append _).mpr ⟨hpol,hpol'⟩,?_,?_⟩
      · rw [Nat.mul_add,Nat.mul_one]; omega
      · simp only [List.filterMap_append,hr,hr',List.nil_append]
      · simpa only [FiniteProbability.Retry.find,Fin.val_zero,Nat.add_zero,ha,Bool.false_eq_true,
          ↓reduceIte,Fin.val_succ,Nat.add_assoc,Nat.add_comm 1] using hpost'
    · simp only [ha,↓reduceIte] at hpost
      refine ⟨k,t,log,ht,by nlinarith,hpol,hr,?_⟩
      simpa [FiniteProbability.Retry.find,ha] using hpost

end WordRam
