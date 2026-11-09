import RamLang.Compiler.Proofs.Linking

namespace RamLang.Compiler
open WordRam ABI

variable {w n fuel base top returnPC endPC : Nat} {code : WordRam.Program registers}
  {rho : RandomMemory w} {s t : State w registers} {trace observed : List (Access w)}
  {stack : Region} {savedFP : Word w} {flow : Flow w} {mem : DataMemory w}
  {policy : AccessPolicy w}

/-- Every interrupted prefix of a continuing execution obeys its complete trace policy. -/
theorem steps_prefix_policy (hs : WordRam.Steps code rho n s t trace)
    (hp : policy.AllowsTrace trace) (hf : fuel ≤ n) :
    policy.AllowsTrace (WordRam.run code rho fuel s).trace := by
  have hprefix := WordRam.run_trace_prefix code rho fuel (n-fuel) s
  rw [Nat.add_sub_of_le hf,hs.exhausted] at hprefix
  exact fun e he => hp e (List.IsPrefix.subset hprefix he)

/-- A continuing execution's earlier observation cannot already have halted or faulted. -/
theorem steps_prefix_exhausted (hs : WordRam.Steps code rho n s t trace) (hf : fuel ≤ n) :
    (WordRam.run code rho fuel s).reason = .fuelExhausted := by
  by_cases hh : (WordRam.run code rho fuel s).reason = .fuelExhausted
  · exact hh
  apply False.elim
  have hstable := WordRam.run_stable (p := code) (rho := rho) (fuel := fuel) (s := s) hh (n-fuel)
  rw [Nat.add_sub_of_le hf,hs.exhausted] at hstable
  exact hh (congrArg WordRam.RunResult.reason hstable).symm

/-- Every finite simulated fragment is safe at every instruction interruption,
including setup, partially initialized frames, and a terminal exhaustion path. -/
theorem Fragment.prefix_policy
    (h : Fragment code rho stack base top savedFP returnPC endPC flow mem observed n s t trace)
    (hf : fuel ≤ n) :
    (framePolicy stack base top).AllowsTrace (WordRam.run code rho fuel s).trace := by
  cases flow with
  | next _ => exact steps_prefix_policy h.execution h.policy hf
  | returned _ => exact steps_prefix_policy h.execution h.policy hf
  | exhausted => exact WordRam.TerminatesIn.prefix_policy h.execution h.policy fuel

theorem Fragment.prefix_noFault
    (h : Fragment code rho stack base top savedFP returnPC endPC flow mem observed n s t trace)
    (hf : fuel ≤ n) (fault : WordRam.Fault) :
    (WordRam.run code rho fuel s).reason ≠ .fault fault := by
  cases flow with
  | next _ => rw [steps_prefix_exhausted h.execution hf]; intro hh; cases hh
  | returned _ => rw [steps_prefix_exhausted h.execution hf]; intro hh; cases hh
  | exhausted => exact WordRam.TerminatesIn.noFault h.execution fuel fault

/-- Reserve ordinary stack traffic while retaining the application's separate
read, write, and immutable-random policies. -/
def withStack (stack : Region) (policy : AccessPolicy w) : AccessPolicy w where
  read a := stack.Contains a ∨ policy.read a
  write a := stack.Contains a ∨ policy.write a
  random a := policy.random a

/-- Projection erases no random event, even at numerically overlapping addresses. -/
theorem project_random_addresses (stack : Region) (trace : List (Access w)) :
    (projectTrace stack trace).filterMap Access.randomAddress = trace.filterMap Access.randomAddress := by
  induction trace with
  | nil => rfl
  | cons e rest ih =>
    cases e with
    | randomRead a v => simpa [projectTrace,applicationEvent,Access.randomAddress] using congrArg (List.cons a) ih
    | dataRead a v =>
      simp only [projectTrace,List.filter_cons,Access.randomAddress,List.filterMap_cons_none] at *
      split <;> simp_all [Access.randomAddress]
    | dataWrite a v =>
      simp only [projectTrace,List.filter_cons,Access.randomAddress,List.filterMap_cons_none] at *
      split <;> simp_all [Access.randomAddress]

/-- A source access contract lifts to concrete stack plus application effects. -/
theorem projected_policy (hp : policy.AllowsTrace (projectTrace stack trace)) :
    (withStack stack policy).AllowsTrace trace := by
  intro e he
  by_cases hinside : applicationEvent stack e = true
  · have hh := hp e (List.mem_filter.mpr ⟨he,hinside⟩)
    cases e with
    | dataRead a v => exact Or.inr hh
    | dataWrite a v => exact Or.inr hh
    | randomRead a v => exact hh
  · cases e with
    | dataRead a v =>
      apply Or.inl
      simp [applicationEvent] at hinside
      exact hinside
    | dataWrite a v =>
      apply Or.inl
      simp [applicationEvent] at hinside
      exact hinside
    | randomRead a v => simp [applicationEvent] at hinside

/-- Finite simulation transfers application access contracts to all target prefixes. -/
theorem Fragment.application_prefix_policy
    (h : Fragment code rho stack base top savedFP returnPC endPC flow mem observed n s t trace)
    (hp : policy.AllowsTrace observed) (hf : fuel ≤ n) :
    (withStack stack policy).AllowsTrace (WordRam.run code rho fuel s).trace := by
  have hwhole : (withStack stack policy).AllowsTrace trace := projected_policy (by rw [h.projection]; exact hp)
  cases flow with
  | next _ => exact steps_prefix_policy h.execution hwhole hf
  | returned _ => exact steps_prefix_policy h.execution hwhole hf
  | exhausted => exact WordRam.TerminatesIn.prefix_policy h.execution hwhole fuel

/-- The ghost peak is an upper bound on the actual sp value at every target
instruction, including all intermediate call-setup and return states. -/
theorem Fragment.prefix_stack
    (h : Fragment code rho stack base top savedFP returnPC endPC flow mem observed n s t trace)
    (hf : fuel ≤ n) : ((WordRam.run code rho fuel s).state.regs sp).toNat ≤ top :=
  h.stackBound fuel hf

end RamLang.Compiler
