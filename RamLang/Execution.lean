import RamLang.Semantics

namespace RamLang
open WordRam

inductive Stop (w : Nat) where
  | runtime (outcome : Outcome w)
  | fuelExhausted
  deriving DecidableEq, Repr

/-- Source step counts are evaluator observations, not target instruction costs. -/
structure RunResult (w : Nat) where
  state : Config w
  steps : Nat
  trace : List (Access w)
  peak : Nat
  reason : Stop w

def RunResult.prepend (s : Config w) (event : Option (Access w)) (r : RunResult w) : RunResult w :=
  { r with steps := r.steps + 1, trace := event.toList ++ r.trace, peak := max s.stackWords r.peak }

/-- Fuel limits observation only. Recursive programs need no termination proof. -/
def run (p : Program) (rho : RandomMemory w) (capacity : Option Nat) :
    Nat → Config w → RunResult w
  | 0, s => ⟨s, 0, [], s.stackWords, .fuelExhausted⟩
  | n+1, s =>
    match step p rho capacity s with
    | .stop outcome => ⟨s, 1, [], s.stackWords, .runtime outcome⟩
    | .next t event => (run p rho capacity n t).prepend s event

/-- Finite source execution with its exact ordered application trace. -/
inductive Steps (p : Program) (rho : RandomMemory w) (capacity : Option Nat) :
    Nat → Config w → Config w → List (Access w) → Prop where
  | refl (s) : Steps p rho capacity 0 s s []
  | cons (head : Step p rho capacity s t event)
      (tail : Steps p rho capacity n t u log) :
      Steps p rho capacity (n+1) s u (event.toList ++ log)

theorem Steps.trans (h : Steps p rho cap n s t log) (g : Steps p rho cap m t u tail) :
    Steps p rho cap (n+m) s u (log++tail) := by
  induction h with
  | refl => simpa using g
  | cons hs ht ih => simpa [Nat.add_assoc, Nat.add_comm, List.append_assoc] using Steps.cons hs (ih g)

/-- The executable evaluator agrees with every finite relational prefix. -/
theorem Steps.run_prefix (h : Steps p rho cap n s t log) :
    (run p rho cap n s).state = t ∧
    (run p rho cap n s).trace = log ∧
    (run p rho cap n s).reason = .fuelExhausted := by
  induction h with
  | refl => simp [run]
  | cons hs ht ih =>
    unfold Step at hs
    simp [run, hs, RunResult.prepend, ih.1, ih.2.1, ih.2.2]

/-- Relational prefixes compose with further executable observation. -/
theorem Steps.run_suffix (h : Steps p rho cap n s t log) (fuel : Nat) :
    (run p rho cap (n+fuel) s).state = (run p rho cap fuel t).state ∧
    (run p rho cap (n+fuel) s).trace = log ++ (run p rho cap fuel t).trace ∧
    (run p rho cap (n+fuel) s).reason = (run p rho cap fuel t).reason := by
  induction h with
  | refl => simp
  | cons hs ht ih =>
    unfold Step at hs
    simp [Nat.succ_add, run, hs, RunResult.prepend, List.append_assoc,
      ih.1, ih.2.1, ih.2.2]

/-- Fuel exhaustion is witnessed by that many steps of the source relation. -/
theorem steps_of_exhausted (h : (run p rho cap n s).reason = .fuelExhausted) :
    Steps p rho cap n s (run p rho cap n s).state (run p rho cap n s).trace := by
  induction n generalizing s with
  | zero => exact .refl _
  | succ n ih =>
    cases hs : step p rho cap s with
    | stop outcome => simp [run, hs] at h
    | next t event =>
      have ht : (run p rho cap n t).reason = .fuelExhausted := by
        simpa [run, hs, RunResult.prepend] using h
      simpa [run, hs, RunResult.prepend] using Steps.cons hs (ih ht)

theorem run_steps_le (p : Program) (rho : RandomMemory w) (cap : Option Nat)
    (n : Nat) (s : Config w) : (run p rho cap n s).steps ≤ n := by
  induction n generalizing s with
  | zero => simp [run]
  | succ n ih =>
    cases hs : step p rho cap s with
    | stop _ => simp [run, hs]
    | next t e => simpa [run, hs, RunResult.prepend] using Nat.add_le_add_right (ih t) 1

/-- A terminating execution includes the source return observation. -/
def Returns (p : Program) (rho : RandomMemory w) (cap : Option Nat)
    (s : Config w) (value : Word w) (t : Config w) (trace : List (Access w)) : Prop :=
  ∃ n, Steps p rho cap n s t trace ∧ step p rho cap t = .stop (.returned value)

/-- A relational return is observable with finite fuel and the same memory/trace. -/
theorem Returns.observed (h : Returns p rho cap s value t trace) :
    ∃ fuel, (run p rho cap fuel s).reason = .runtime (.returned value) ∧
      (run p rho cap fuel s).state = t ∧ (run p rho cap fuel s).trace = trace := by
  obtain ⟨n, hs, ht⟩ := h
  have hr := hs.run_suffix 1
  refine ⟨n+1, ?_⟩
  simp only [run, ht, List.append_nil] at hr
  exact ⟨hr.2.2, hr.1, hr.2.1⟩

/-- Every ideal prefix whose allocations fit also runs with finite capacity. -/
theorem Steps.capacity (h : Steps p rho none n s t log)
    (fits : ∀ k u trace, Steps p rho none k s u trace → FitsNext p cap u) :
    Steps p rho (some cap) n s t log := by
  induction h with
  | refl => exact .refl _
  | @cons s t event n u log hs ht ih =>
    have first : Step p rho (some cap) s t event := by
      unfold Step
      rw [step_ideal_of_fits (fits 0 s [] (.refl s))]
      exact hs
    apply Steps.cons first
    apply ih
    intro k v trace hv
    exact fits (k+1) v (event.toList++trace) (.cons hs hv)

/-- A bounded-stack infinite loop is divergence, not stack exhaustion. -/
def Diverges (p : Program) (rho : RandomMemory w) (cap : Option Nat) (s : Config w) : Prop :=
  ∀ fuel, (run p rho cap fuel s).reason = .fuelExhausted

end RamLang
