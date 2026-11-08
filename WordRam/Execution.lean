import WordRam.Machine

namespace WordRam

inductive StopReason where
  | halted
  | fault (reason : Fault)
  | fuelExhausted
  deriving DecidableEq, Repr

structure RunResult (w R : Nat) where
  state : State w R
  steps : Nat
  trace : List (Access w)
  reason : StopReason

def RunResult.prepend (k : Nat) (log : List (Access w)) (r : RunResult w R) : RunResult w R :=
  { r with steps := k + r.steps, trace := log ++ r.trace }

@[simp] theorem RunResult.prepend_zero (r : RunResult w R) : r.prepend 0 [] = r := by
  cases r
  simp [prepend]

theorem RunResult.prepend_prepend (r : RunResult w R) (k l : Nat)
    (a b : List (Access w)) :
    (r.prepend l b).prepend k a = r.prepend (k+l) (a++b) := by
  simp [prepend, Nat.add_assoc, List.append_assoc]

/-- Fuel is an evaluator budget. Halt costs one; invalid fetch costs zero.
All partial effects and all executed work are retained. -/
def run (p : Program R) (rho : RandomMemory w) : Nat → State w R → RunResult w R
  | 0, s => ⟨s, 0, [], .fuelExhausted⟩
  | fuel+1, s =>
    match step p rho s with
    | .fault f => ⟨s, 0, [], .fault f⟩
    | .halt => ⟨s, 1, [], .halted⟩
    | .next t a => (run p rho fuel t).prepend 1 a.toList

theorem run_steps_le (p : Program R) (rho : RandomMemory w) (fuel : Nat) (s : State w R) :
    (run p rho fuel s).steps ≤ fuel := by
  induction fuel generalizing s with
  | zero => simp [run]
  | succ fuel ih =>
    cases h : step p rho s <;> simp [run, h, RunResult.prepend]
    rename_i t a
    have := ih t
    omega

theorem run_exhausted_steps (h : (run p rho fuel s).reason = .fuelExhausted) :
    (run p rho fuel s).steps = fuel := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
    cases hs : step p rho s with
    | fault f => simp [run, hs] at h
    | halt => simp [run, hs] at h
    | next t a =>
      simp only [run, hs, RunResult.prepend] at h ⊢
      rw [ih h, Nat.add_comm]

/-- Exactly `n` continuing instructions, with their access trace. -/
inductive Steps (p : Program R) (rho : RandomMemory w) :
    Nat → State w R → State w R → List (Access w) → Prop where
  | refl (s) : Steps p rho 0 s s []
  | cons (h : Step p rho s t a) (tail : Steps p rho n t u log) :
      Steps p rho (n+1) s u (a.toList ++ log)

theorem Steps.trans (h : Steps p rho k s t a) (g : Steps p rho l t u b) :
    Steps p rho (k+l) s u (a++b) := by
  induction h with
  | refl => simpa using g
  | cons hs ht ih =>
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm, List.append_assoc]
      using Steps.cons hs (ih g)

/-- A finite execution fragment can be followed by any bounded continuation. -/
theorem Steps.run_eq (h : Steps p rho k s t log) (fuel : Nat) :
    run p rho (k+fuel) s = (run p rho fuel t).prepend k log := by
  induction h with
  | refl => simp
  | @cons s t a n u log hs ht ih =>
    change step p rho s = .next t a at hs
    simp only [Nat.succ_add, run, hs]
    rw [ih, RunResult.prepend_prepend]
    congr 1
    omega

theorem Steps.exhausted (h : Steps p rho k s t log) :
    run p rho k s = ⟨t, k, log, .fuelExhausted⟩ := by
  simpa [run, RunResult.prepend] using h.run_eq 0

theorem steps_of_exhausted (h : (run p rho fuel s).reason = .fuelExhausted) :
    Steps p rho fuel s (run p rho fuel s).state (run p rho fuel s).trace := by
  induction fuel generalizing s with
  | zero => exact .refl s
  | succ fuel ih =>
    cases hs : step p rho s with
    | fault f => simp [run, hs] at h
    | halt => simp [run, hs] at h
    | next t a =>
      simp only [run, hs, RunResult.prepend] at h ⊢
      exact .cons hs (ih h)

/-- Exact termination time includes the final halt instruction. -/
def TerminatesIn (p : Program R) (rho : RandomMemory w) (s : State w R)
    (k : Nat) (t : State w R) (log : List (Access w)) : Prop :=
  ∃ n, k = n+1 ∧ Steps p rho n s t log ∧ step p rho t = .halt

def Terminates (p : Program R) (rho : RandomMemory w) (s : State w R) : Prop :=
  ∃ k t log, TerminatesIn p rho s k t log

def Diverges (p : Program R) (rho : RandomMemory w) (s : State w R) : Prop :=
  ∀ fuel, (run p rho fuel s).reason = .fuelExhausted

theorem TerminatesIn.run_eq (h : TerminatesIn p rho s k t log) :
    run p rho k s = ⟨t, k, log, .halted⟩ := by
  obtain ⟨n, rfl, hs, ht⟩ := h
  rw [hs.run_eq 1]
  simp [run, ht, RunResult.prepend]

theorem terminatesIn_of_halted (h : (run p rho fuel s).reason = .halted) :
    TerminatesIn p rho s (run p rho fuel s).steps
      (run p rho fuel s).state (run p rho fuel s).trace := by
  induction fuel generalizing s with
  | zero => simp [run] at h
  | succ fuel ih =>
    cases hs : step p rho s with
    | fault f => simp [run, hs] at h
    | halt =>
      simp only [run, hs]
      exact ⟨0, rfl, .refl s, hs⟩
    | next t a =>
      simp only [run, hs, RunResult.prepend] at h ⊢
      obtain ⟨n, hn, ht, hu⟩ := ih h
      exact ⟨n+1, by omega, .cons hs ht, hu⟩

theorem terminates_iff_halted :
    Terminates p rho s ↔ ∃ fuel, (run p rho fuel s).reason = .halted := by
  constructor
  · rintro ⟨k, t, log, h⟩
    exact ⟨k, by rw [h.run_eq]⟩
  · rintro ⟨fuel, h⟩
    exact ⟨_, _, _, terminatesIn_of_halted h⟩

theorem diverges_iff_steps : Diverges p rho s ↔ ∀ n, ∃ t log, Steps p rho n s t log := by
  constructor
  · intro h n
    exact ⟨_, _, steps_of_exhausted (h n)⟩
  · intro h n
    obtain ⟨t, log, ht⟩ := h n
    rw [ht.exhausted]

theorem diverges_not_terminates (h : Diverges p rho s) : ¬ Terminates p rho s := by
  intro ht
  obtain ⟨fuel, hf⟩ := terminates_iff_halted.mp ht
  rw [h fuel] at hf
  contradiction

end WordRam
