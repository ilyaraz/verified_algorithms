import WordRam.Properties
import WordRam.Regions

namespace WordRam

/-- Per-access permissions compose without discarding rejected or partial work. -/
structure AccessPolicy (w : Nat) where
  read : Addr w → Prop
  write : Addr w → Prop
  random : Addr w → Prop

def AccessPolicy.Allows (p : AccessPolicy w) : Access w → Prop
  | .dataRead a _ => p.read a
  | .dataWrite a _ => p.write a
  | .randomRead a _ => p.random a

def AccessPolicy.AllowsTrace (p : AccessPolicy w) (log : List (Access w)) : Prop :=
  ∀ e ∈ log, p.Allows e

@[simp] theorem AccessPolicy.allowsTrace_append (p : AccessPolicy w) :
    p.AllowsTrace (a ++ b) ↔ p.AllowsTrace a ∧ p.AllowsTrace b := by
  simp [AllowsTrace, List.mem_append, or_imp, forall_and]

variable {w R : Nat} {p : Program R} {rho : RandomMemory w}
  {s t : State w R} {k : Nat} {log : List (Access w)} {a : Addr w}
  {policy : AccessPolicy w}

theorem Steps.frame (h : Steps p rho k s t log)
    (ha : a ∉ log.filterMap Access.writeAddress) : t.mem a = s.mem a := by
  have hr := run_frame p rho k s a
  simpa [h.exhausted] using hr (by simpa [h.exhausted] using ha)

theorem Steps.frame_of_policy (h : Steps p rho k s t log)
    (hp : policy.AllowsTrace log) (ha : ¬ policy.write a) : t.mem a = s.mem a := by
  apply h.frame
  intro hm
  obtain ⟨e, he, ha'⟩ := List.mem_filterMap.mp hm
  have := hp e he
  cases e <;> simp_all [Access.writeAddress, AccessPolicy.Allows]

/-- A block has an explicit continuation state, charged continuing instructions,
and an access policy. Halt is supplied by its continuation, not hidden in cost. -/
def BlockSpec (p : Program R) (rho : RandomMemory w)
    (pre post : State w R → Prop) (cost : Nat) (policy : AccessPolicy w) : Prop :=
  ∀ s, pre s → ∃ k t log, k ≤ cost ∧ Steps p rho k s t log ∧
    post t ∧ policy.AllowsTrace log

theorem BlockSpec.then (h : BlockSpec p rho pre mid k policy)
    (g : BlockSpec p rho mid post l policy) : BlockSpec p rho pre post (k+l) policy := by
  intro s hs
  obtain ⟨a, t, log₁, ha, ht, hm, hp⟩ := h s hs
  obtain ⟨b, u, log₂, hb, hu, hf, hq⟩ := g t hm
  exact ⟨a+b, u, log₁++log₂, Nat.add_le_add ha hb, ht.trans hu, hf,
    (AccessPolicy.allowsTrace_append policy).mpr ⟨hp, hq⟩⟩

/-- Increasing fuel can only append access events, including in halted/faulted runs. -/
theorem run_trace_prefix (p : Program R) (rho : RandomMemory w)
    (fuel extra : Nat) (s : State w R) :
    (run p rho fuel s).trace.IsPrefix (run p rho (fuel+extra) s).trace := by
  induction fuel generalizing s with
  | zero => simp [run]
  | succ fuel ih =>
    cases hs : step p rho s <;> simp only [Nat.succ_add, run, hs, RunResult.prepend]
    · rename_i t event
      obtain ⟨tail, ht⟩ := ih t
      exact ⟨tail, by simp only [List.append_assoc, ht]⟩
    · exact ⟨[], by simp⟩
    · exact ⟨[], by simp⟩

theorem TerminatesIn.prefix_policy (h : TerminatesIn p rho s k t log)
    (hp : policy.AllowsTrace log) (fuel : Nat) :
    policy.AllowsTrace (run p rho fuel s).trace := by
  by_cases hf : fuel ≤ k
  · have ht := run_trace_prefix p rho fuel (k-fuel) s
    rw [Nat.add_sub_of_le hf, h.run_eq] at ht
    intro e he
    exact hp e (List.IsPrefix.subset ht he)
  · have hs := run_stable (p := p) (rho := rho) (fuel := k) (s := s)
        (by simp [h.run_eq]) (fuel-k)
    rw [Nat.add_sub_of_le (by omega), h.run_eq] at hs
    simpa [hs] using hp

theorem TerminatesIn.noFault (h : TerminatesIn p rho s k t log) (fuel : Nat) (f : Fault) :
    (run p rho fuel s).reason ≠ .fault f := by
  intro hf
  by_cases hk : fuel ≤ k
  · have hs := run_stable (p := p) (rho := rho) (fuel := fuel) (s := s)
        (by rw [hf]; simp) (k-fuel)
    rw [Nat.add_sub_of_le hk, h.run_eq] at hs
    have := congrArg RunResult.reason hs
    simp [hf] at this
  · have hs := run_stable (p := p) (rho := rho) (fuel := k) (s := s)
        (by simp [h.run_eq]) (fuel-k)
    rw [Nat.add_sub_of_le (by omega), h.run_eq] at hs
    rw [hs] at hf
    cases hf

end WordRam
