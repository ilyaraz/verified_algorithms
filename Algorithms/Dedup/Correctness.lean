import Algorithms.Dedup.Initialization

namespace Dedup
open WordRam Registers Blocks

/-- Full ordinary and random access contract, also inherited by every prefix. -/
def policy (l : Layout) (N : Nat) : AccessPolicy w :=
  ⟨fun a => (l.inputRegion N).Contains a ∨ (l.workspace N).Contains a,
    (l.workspace N).Contains, fun a => a = word w l.random⟩

theorem loop_random {log : List (Access w)} (ht : (loopPolicy l N).AllowsTrace log) :
    log.filterMap Access.randomAddress = [] := by
  apply List.filterMap_eq_nil_iff.mpr
  intro e he
  have hh := ht e he
  cases e <;> simp_all [Access.randomAddress,AccessPolicy.Allows,loopPolicy]

/-- Concrete total deduplication. The compact order is first-occurrence order;
the comparison model appears only in the proved instruction upper bound. -/
theorem total (xs : List (Word w)) (l : Layout) (ha : Admissible w xs.length l)
    (rho : RandomMemory w) {s : State w 64} (hp : s.pc = 0)
    (hin : Input w xs.length l s.regs) (arr : ArrayAt s.mem l.input xs) :
    ∃ k t log, TerminatesIn program rho s k t log ∧
      k ≤ 40*(xs.length+1)+9*comparisons (parameters ha (rho (word w l.random))).hash xs [] ∧
      Output xs (collect xs []).reverse l s.mem ⟨t,k,log,.halted⟩ ∧
      (policy l xs.length).AllowsTrace log := by
  obtain ⟨a,u,la,hs,hcost,inv,htrace,hrandom⟩ := initialization ha rho xs rfl hp hin arr
  obtain ⟨b,t,lb,ht,hbound,post,htrace'⟩ := loop_total rho ha inv
  obtain ⟨b',hb',hsteps,hhalt⟩ := ht
  have hfull := hs.trans hsteps
  have hpfull : (policy l xs.length).AllowsTrace (la++lb) := by
    rw [AccessPolicy.allowsTrace_append]
    constructor
    · intro e he
      have hh := htrace e he
      cases e <;> simp_all [AccessPolicy.Allows,policy]
    · intro e he
      have hh := htrace' e he
      cases e <;> simp_all [AccessPolicy.Allows,policy,loopPolicy]
  refine ⟨a+b,t,la++lb,⟨a+b',by omega,hfull,hhalt⟩,?_,?_,hpfull⟩
  · omega
  · refine ⟨rfl,?_,?_,post.base,?_,post.representation.compact,?_,?_⟩
    · simpa using post.representation.distinct
    · intro x
      simp
    · have hc := collect_length xs ([] : List (Word w))
      simp only [List.length_nil,Nat.zero_add] at hc
      change (t.regs count).toNat = _
      rw [post.count,word_toNat_of_lt (hc.trans_lt ha.count_fit)]
      simp
    · intro a had
      exact hfull.frame_of_policy hpfull had
    · change (la++lb).filterMap Access.randomAddress = _
      rw [List.filterMap_append,hrandom,loop_random htrace',List.append_nil]

/-- A uniform quadratic evaluator guard is sufficient for every random image. -/
def fuel (N : Nat) : Nat := 40*(N+1)+9*N*N

theorem run_correct (xs : List (Word w)) (l : Layout) (ha : Admissible w xs.length l)
    (rho : RandomMemory w) {s : State w 64} (hp : s.pc = 0)
    (hin : Input w xs.length l s.regs) (arr : ArrayAt s.mem l.input xs) :
    Output xs (collect xs []).reverse l s.mem (run program rho (fuel xs.length) s) ∧
      (run program rho (fuel xs.length) s).steps ≤
        40*(xs.length+1)+9*comparisons (parameters ha (rho (word w l.random))).hash xs [] ∧
      (policy l xs.length).AllowsTrace (run program rho (fuel xs.length) s).trace := by
  obtain ⟨k,t,log,ht,hk,out,trace⟩ := total xs l ha rho hp hin arr
  have hh := comparisons_worst (parameters ha (rho (word w l.random))).hash xs []
  have hf : k ≤ fuel xs.length := by simp only [List.length_nil,Nat.zero_add] at hh; unfold fuel; nlinarith
  have stable := run_stable (p := program) (rho := rho) (s := s) (fuel := k)
    (by simp [ht.run_eq]) (fuel xs.length-k)
  rw [Nat.add_sub_of_le hf,ht.run_eq] at stable
  rw [stable]
  exact ⟨out,hk,trace⟩

/-- Original input preservation and scratch-only writes hold before completion
as well as after it; no finite prefix faults. -/
theorem prefixes (xs : List (Word w)) (l : Layout) (ha : Admissible w xs.length l)
    (rho : RandomMemory w) {s : State w 64} (hp : s.pc = 0)
    (hin : Input w xs.length l s.regs) (arr : ArrayAt s.mem l.input xs) (f : Nat) :
    (policy l xs.length).AllowsTrace (run program rho f s).trace ∧
      (∀ fault, (run program rho f s).reason ≠ .fault fault) := by
  obtain ⟨k,t,log,ht,_,_,trace⟩ := total xs l ha rho hp hin arr
  exact ⟨ht.prefix_policy trace f,ht.noFault f⟩

end Dedup
