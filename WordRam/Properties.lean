import WordRam.Execution

namespace WordRam

/-- Stop results remain exactly the same when more fuel is provided. -/
theorem run_stable (h : (run p rho fuel s).reason ≠ .fuelExhausted) (extra : Nat) :
    run p rho (fuel+extra) s = run p rho fuel s := by
  induction fuel generalizing s with
  | zero => simp [run] at h
  | succ fuel ih =>
    cases hs : step p rho s with
    | fault f => simp [Nat.succ_add, run, hs]
    | halt => simp [Nat.succ_add, run, hs]
    | next t a =>
      simp only [run, hs, RunResult.prepend] at h
      simp only [Nat.succ_add, run, hs, ih h]

/-- Resume a partial run without sampling another random memory. -/
theorem run_resume (h : (run p rho fuel s).reason = .fuelExhausted) (extra : Nat) :
    run p rho (fuel+extra) s =
      (run p rho extra (run p rho fuel s).state).prepend
        (run p rho fuel s).steps (run p rho fuel s).trace := by
  rw [run_exhausted_steps h]
  exact (steps_of_exhausted h).run_eq extra

theorem terminatesIn_iff_run :
    TerminatesIn p rho s k t log ↔ run p rho k s = ⟨t, k, log, .halted⟩ := by
  constructor
  · exact TerminatesIn.run_eq
  · intro h
    have hh : (run p rho k s).reason = .halted := by rw [h]
    have ht := terminatesIn_of_halted hh
    simpa [h] using ht

theorem steps_iff_run :
    Steps p rho k s t log ↔ run p rho k s = ⟨t, k, log, .fuelExhausted⟩ := by
  constructor
  · exact Steps.exhausted
  · intro h
    have hh : (run p rho k s).reason = .fuelExhausted := by rw [h]
    have ht := steps_of_exhausted hh
    simpa [h] using ht

theorem Steps.deterministic (h : Steps p rho k s t a) (g : Steps p rho k s u b) :
    t = u ∧ a = b := by
  have he := h.exhausted.symm.trans g.exhausted
  exact ⟨congrArg RunResult.state he, congrArg RunResult.trace he⟩

/-- Cells not written by a step are preserved, even if they were read. -/
theorem step_frame (hs : Step p rho s t event)
    (ha : a ∉ event.toList.filterMap Access.writeAddress) : t.mem a = s.mem a := by
  unfold Step step at hs
  cases hi : p[s.pc]? with
  | none => simp [hi] at hs
  | some i =>
    cases i <;> simp only [hi, StepResult.next.injEq] at hs
    all_goals try { cases hs }
    all_goals rcases hs with ⟨rfl, rfl⟩
    all_goals try rfl
    simp only [Option.toList_some, List.filterMap_cons, Access.writeAddress,
      List.filterMap_nil, List.mem_singleton] at ha
    exact update_other _ _ _ _ ha

theorem run_frame (p : Program R) (rho : RandomMemory w) (fuel : Nat) (s : State w R)
    (a : Addr w) (ha : a ∉ (run p rho fuel s).trace.filterMap Access.writeAddress) :
    (run p rho fuel s).state.mem a = s.mem a := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
    cases hs : step p rho s with
    | fault f => simp [run, hs]
    | halt => simp [run, hs]
    | next t event =>
      have hh : a ∉ event.toList.filterMap Access.writeAddress ∧
          a ∉ (run p rho fuel t).trace.filterMap Access.writeAddress := by
        simpa [run, hs, RunResult.prepend, List.filterMap_append, List.mem_append,
          not_or] using ha
      simpa only [run, hs, RunResult.prepend] using
        (ih t hh.2).trans (step_frame hs hh.1)

theorem step_random_consistent
    (h : Access.randomRead a v ∈ (step p rho s).accesses) : rho a = v := by
  unfold step at h
  cases hi : p[s.pc]? with
  | none => simp [hi, StepResult.accesses] at h
  | some i =>
    cases i <;> simp [hi, StepResult.accesses] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl

theorem run_random_consistent (p : Program R) (rho : RandomMemory w) (fuel : Nat)
    (s : State w R) (h : Access.randomRead a v ∈ (run p rho fuel s).trace) : rho a = v := by
  induction fuel generalizing s with
  | zero => simp [run] at h
  | succ fuel ih =>
    cases hs : step p rho s with
    | fault f => simp [run, hs] at h
    | halt => simp [run, hs] at h
    | next t event =>
      have hh : Access.randomRead a v ∈ event.toList ∨
          Access.randomRead a v ∈ (run p rho fuel t).trace := by
        simpa [run, hs, RunResult.prepend] using h
      rcases hh with hh | hh
      · exact step_random_consistent (p := p) (s := s)
          (by simpa [hs, StepResult.accesses] using hh)
      · exact ih t hh

theorem repeated_random_read (h : Access.randomRead a x ∈ (run p rho fuel s).trace)
    (h' : Access.randomRead a y ∈ (run p rho fuel s).trace) : x = y :=
  (run_random_consistent _ _ _ _ h).symm.trans (run_random_consistent _ _ _ _ h')

theorem step_random_agreement (p : Program R) (rho rho' : RandomMemory w) (s : State w R)
    (h : ∀ a v, Access.randomRead a v ∈ (step p rho s).accesses → rho' a = rho a) :
    step p rho' s = step p rho s := by
  unfold step at h ⊢
  cases hi : p[s.pc]? with
  | none => rfl
  | some i =>
    cases i
    all_goals try rfl
    rename_i d addr
    have he := h (addr.eval s.regs) (rho (addr.eval s.regs)) (by
      simp [hi, StepResult.accesses])
    dsimp only
    rw [he]

/-- Agreement is required only on addresses read in the reference run. -/
theorem run_random_agreement (p : Program R) (rho rho' : RandomMemory w)
    (fuel : Nat) (s : State w R)
    (h : ∀ a v, Access.randomRead a v ∈ (run p rho fuel s).trace → rho' a = rho a) :
    run p rho' fuel s = run p rho fuel s := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
    have hstep : step p rho' s = step p rho s := by
      apply step_random_agreement
      intro a v ha
      apply h a v
      cases hs : step p rho s with
      | fault f => simp [hs, StepResult.accesses] at ha
      | halt => simp [hs, StepResult.accesses] at ha
      | next t event =>
        simp only [hs, StepResult.accesses] at ha
        simp only [run, hs, RunResult.prepend, List.mem_append]
        exact Or.inl ha
    cases hs : step p rho s with
    | fault f => simp [run, hstep, hs]
    | halt => simp [run, hstep, hs]
    | next t event =>
      have ht : ∀ a v, Access.randomRead a v ∈ (run p rho fuel t).trace → rho' a = rho a := by
        intro a v ha
        apply h a v
        simp only [run, hs, RunResult.prepend, List.mem_append]
        exact Or.inr ha
      simp only [run, hstep, hs, ih t ht]

theorem run_without_random_reads (p : Program R) (rho rho' : RandomMemory w)
    (fuel : Nat) (s : State w R)
    (h : ∀ a v, Access.randomRead a v ∉ (run p rho fuel s).trace) :
    run p rho' fuel s = run p rho fuel s := by
  apply run_random_agreement
  intro a v ha
  exact False.elim (h a v ha)

/-- Resource observations count addresses, not values. Lists represent finite sets
after duplicate removal so the executable layer needs no Mathlib imports. -/
def RunResult.dataFootprint (r : RunResult w R) : List (Addr w) :=
  (r.trace.filterMap Access.dataAddress).eraseDups

def RunResult.writeFootprint (r : RunResult w R) : List (Addr w) :=
  (r.trace.filterMap Access.writeAddress).eraseDups

def RunResult.randomAddresses (r : RunResult w R) : List (Addr w) :=
  r.trace.filterMap Access.randomAddress

def RunResult.randomReads (r : RunResult w R) : Nat := r.randomAddresses.length

def RunResult.randomFootprint (r : RunResult w R) : List (Addr w) :=
  r.randomAddresses.eraseDups

def RunResult.randomBitsExposed (r : RunResult w R) : Nat := w * r.randomFootprint.length

end WordRam
