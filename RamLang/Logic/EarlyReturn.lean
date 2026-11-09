import RamLang.Logic.Loop

namespace RamLang.Logic
open WordRam Compiler

/-- A total loop may either decrease its ghost measure and continue or return
an established result immediately. Every branch retains its actual instruction,
stack and access costs; exhaustion is excluded by the body contract. -/
theorem while_total_return {w free : Nat} {p : Program} {rho : RandomMemory w}
    {condition : Condition} {body : Stmt} (I : Nat → Locals w → DataMemory w → Prop)
    (Q : Word w → DataMemory w → Prop) (policy : AccessPolicy w)
    (budget iteration : Nat → Nat) (peak : Nat)
    (test : ∀ n locals mem, I n locals mem → ∃ b, condition.eval locals = .ok b)
    (baseCost : ∀ n, conditionCost condition+2 ≤ budget n)
    (stopCost : ∀ n, conditionCost condition+1+iteration n ≤ budget n)
    (decreaseCost : ∀ n m, m < n → conditionCost condition+2+iteration n+budget m ≤ budget n)
    (bodyRule : ∀ n locals mem, I n locals mem → condition.eval locals = .ok true →
      Contract p rho free body locals mem
        (fun flow mem' trace => policy.AllowsTrace trace ∧ match flow with
          | .next out => ∃ m, m < n ∧ I m out mem'
          | .returned value => Q value mem'
          | .exhausted => False) (iteration n) peak) :
    ∀ n locals mem, I n locals mem → Contract p rho free (.while condition body) locals mem
      (fun flow mem' trace => policy.AllowsTrace trace ∧ match flow with
        | .next out => ∃ m, I m out mem' ∧ condition.eval out = .ok false
        | .returned value => Q value mem'
        | .exhausted => False) (budget n) peak := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    intro locals mem hi
    obtain ⟨b,hb⟩ := test n locals mem hi
    cases b with
    | false =>
      refine Contract.ofEvaluation (.whileFalse hb) ⟨?_,n,hi,hb⟩ (baseCost n) (Nat.zero_le _)
      intro e he
      cases he
    | true =>
      obtain ⟨flow,mem₁,trace₁,d₁,⟨hp₁,hpost⟩,ht₁,hs₁⟩ := bodyRule n locals mem hi hb
      cases flow with
      | next out =>
        obtain ⟨m,hm,hmi⟩ := hpost
        obtain ⟨flow,mem₂,trace₂,d₂,⟨hp₂,hq⟩,ht₂,hs₂⟩ := ih m hm out mem₁ hmi
        refine Contract.ofEvaluation (.whileContinue hb d₁ d₂) ⟨?_,hq⟩ ?_ ?_
        · exact (AccessPolicy.allowsTrace_append _).mpr ⟨hp₁,hp₂⟩
        · have hd := decreaseCost n m hm
          simp only [instructions]
          omega
        · exact Nat.max_le.mpr ⟨hs₁,hs₂⟩
      | returned value =>
        refine Contract.ofEvaluation (.whileStop hb d₁ (by trivial)) ⟨hp₁,hpost⟩ ?_ (by simpa only [extraStack] using hs₁)
        have hd := stopCost n
        simp only [instructions]
        omega
      | exhausted => exact False.elim hpost

/-- Compose a possibly returning block with a continuation. Prior returns keep
both their result and their trace; only continuing paths execute the second
statement. Sequential time adds and stack peaks combine by maximum. -/
theorem Contract.sequence_cases {w free : Nat} {p : Program} {rho : RandomMemory w}
    {a b : Stmt} {locals : Locals w} {mem : DataMemory w}
    {post : Flow w → DataMemory w → List (Access w) → Prop}
    {middle : Locals w → DataMemory w → List (Access w) → Prop}
    {work₁ work₂ peak₁ peak₂ : Nat}
    (first : Contract p rho free a locals mem
      (fun flow mem' trace => match flow with
        | .next out => middle out mem' trace
        | _ => post flow mem' trace) work₁ peak₁)
    (second : ∀ out mem' prior, middle out mem' prior →
      Contract p rho free b out mem'
        (fun flow mem'' suffix => post flow mem'' (prior++suffix)) work₂ peak₂) :
    Contract p rho free (.seq a b) locals mem post (work₁+work₂) (max peak₁ peak₂) := by
  obtain ⟨flow,mem₁,trace₁,d₁,hmid,ht₁,hs₁⟩ := first
  cases flow with
  | next out =>
    obtain ⟨flow,mem₂,trace₂,d₂,hpost,ht₂,hs₂⟩ := second out mem₁ trace₁ hmid
    refine Contract.ofEvaluation (.sequence d₁ d₂) hpost ?_ ?_
    · simp only [instructions]; omega
    · exact Nat.max_le.mpr ⟨Nat.le_trans hs₁ (Nat.le_max_left _ _),Nat.le_trans hs₂ (Nat.le_max_right _ _)⟩
  | returned value =>
    exact Contract.ofEvaluation (.sequenceStop d₁ (by trivial)) hmid (by simpa [instructions] using Nat.le_trans ht₁ (Nat.le_add_right _ _))
      (Nat.le_trans hs₁ (Nat.le_max_left _ _))
  | exhausted =>
    exact Contract.ofEvaluation (.sequenceStop d₁ (by trivial)) hmid (by simpa [instructions] using Nat.le_trans ht₁ (Nat.le_add_right _ _))
      (Nat.le_trans hs₁ (Nat.le_max_left _ _))

end RamLang.Logic
