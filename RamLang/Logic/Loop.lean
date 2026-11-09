import RamLang.Logic.Contract

namespace RamLang.Logic
open WordRam Compiler

/-- A decreasing-loop rule with an invariant, explicit application access
policy, a time potential, and a uniform stack peak. The measure is ghost data;
the executable loop still tests its ordinary word-valued condition. -/
theorem while_total {w free : Nat} {p : Program} {rho : RandomMemory w}
    {condition : Condition} {body : Stmt} (I : Nat → Locals w → DataMemory w → Prop)
    (policy : AccessPolicy w) (budget iteration : Nat → Nat) (peak : Nat)
    (test : ∀ n locals mem, I n locals mem → ∃ b, condition.eval locals = .ok b)
    (baseCost : ∀ n, conditionCost condition+2 ≤ budget n)
    (decreaseCost : ∀ n m, m < n → conditionCost condition+2+iteration n+budget m ≤ budget n)
    (bodyRule : ∀ n locals mem, I n locals mem → condition.eval locals = .ok true →
      Contract p rho free body locals mem
        (fun flow mem' trace => ∃ out m, flow = .next out ∧ m < n ∧ I m out mem' ∧ policy.AllowsTrace trace)
        (iteration n) peak) :
    ∀ n locals mem, I n locals mem → Contract p rho free (.while condition body) locals mem
      (fun flow mem' trace => ∃ out m, flow = .next out ∧ I m out mem' ∧
        condition.eval out = .ok false ∧ policy.AllowsTrace trace) (budget n) peak := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro locals mem hi
    obtain ⟨b,hb⟩ := test n locals mem hi
    cases b with
    | false =>
      refine ⟨.next locals,mem,[],.whileFalse hb,⟨locals,n,rfl,hi,hb,?_⟩,baseCost n,?_⟩
      · intro e he; cases he
      · exact Nat.zero_le _
    | true =>
      obtain ⟨flow,mem₁,trace₁,d₁,⟨out,m,rfl,hm,hmi,hpolicy₁⟩,ht₁,hs₁⟩ := bodyRule n locals mem hi hb
      obtain ⟨flow,mem₂,trace₂,d₂,⟨last,k,rfl,hki,hfalse,hpolicy₂⟩,ht₂,hs₂⟩ := ih m hm out mem₁ hmi
      refine ⟨.next last,mem₂,trace₁++trace₂,.whileContinue hb d₁ d₂,
        ⟨last,k,rfl,hki,hfalse,?_⟩,?_,?_⟩
      · intro e he
        rcases List.mem_append.mp he with he | he
        · exact hpolicy₁ e he
        · exact hpolicy₂ e he
      · have hd := decreaseCost n m hm
        simp only [instructions]; omega
      · exact Nat.max_le.mpr ⟨hs₁,hs₂⟩

/-- A branch is proved under its evaluated source condition; its target charge
includes operand loads and the conditional branch instruction. -/
theorem Contract.ifTrue {w free work peak : Nat} {p : Program} {rho : RandomMemory w}
    {condition : Condition} {yes no : Stmt} {locals : Locals w} {mem : DataMemory w}
    {post : Flow w → DataMemory w → List (Access w) → Prop}
    (test : condition.eval locals = .ok true)
    (branch : Contract p rho free yes locals mem post work peak) :
    Contract p rho free (.ite condition yes no) locals mem post
      (conditionCost condition+1+work) peak := by
  obtain ⟨flow,mem',trace,d,hq,ht,hs⟩ := branch
  exact ⟨flow,mem',trace,.ifTrue test d,hq,by simp only [instructions]; omega,hs⟩

/-- The false branch reserves one extra instruction for the fall-through jump.
A returning or exhausted branch skips that jump and satisfies the same bound. -/
theorem Contract.ifFalse {w free work peak : Nat} {p : Program} {rho : RandomMemory w}
    {condition : Condition} {yes no : Stmt} {locals : Locals w} {mem : DataMemory w}
    {post : Flow w → DataMemory w → List (Access w) → Prop}
    (test : condition.eval locals = .ok false)
    (branch : Contract p rho free no locals mem post work peak) :
    Contract p rho free (.ite condition yes no) locals mem post
      (conditionCost condition+2+work) peak := by
  obtain ⟨flow,mem',trace,d,hq,ht,hs⟩ := branch
  refine ⟨flow,mem',trace,.ifFalse test d,hq,?_,hs⟩
  simp only [instructions]
  split <;> omega

end RamLang.Logic
