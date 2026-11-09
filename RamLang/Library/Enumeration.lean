import RamLang.Library.Search

namespace RamLang.Library.Enumeration
open WordRam Compiler Logic

/-- Exhaustive search has no runtime upper-bound parameter. A proved successful
finite candidate prefix supplies the ghost termination measure; all candidate
computation, updates and trials remain ordinary charged source statements. -/
theorem loop_contract {w free : Nat} {p : Program} {rho : RandomMemory w}
    (body : Stmt) (candidate : Nat → Word w) (accept : Word w → Bool)
    (I : Nat → Locals w → DataMemory w → Prop) (good : Word w → DataMemory w → Prop)
    (policy : AccessPolicy w) (trialWork peak : Nat) (hw : 1 < modulus w)
    (trial : ∀ i locals mem, I i locals mem →
      Contract p rho free body locals mem
        (fun flow mem' log => policy.AllowsTrace log ∧ Retry.randomAddresses log = [] ∧
          if accept (candidate i) then flow = .returned (candidate i) ∧ good (candidate i) mem'
          else ∃ out, flow = .next out ∧ I (i+1) out mem') trialWork peak) :
    ∀ i n locals mem value, I i locals mem → Search.choice candidate accept i n = some value →
      Contract p rho free (.while ⟨.ne,.literal 1,.literal 0⟩ body) locals mem
        (fun flow mem' log => flow = .returned value ∧ good value mem' ∧
          policy.AllowsTrace log ∧ Retry.randomAddresses log = []) ((trialWork+4)*n) peak := by
  intro i n
  induction n generalizing i with
  | zero => intro locals mem value hi hc; cases hc
  | succ n ih =>
    intro locals mem value hi hc
    have hone : word w 1 ≠ word w 0 := by
      intro he
      have h := (word_eq_iff_of_lt hw (by omega : 0 < modulus w)).mp he
      omega
    have ht : Condition.eval locals ⟨.ne,.literal 1,.literal 0⟩ = .ok true := by
      simp [Condition.eval,Atom.eval,Comparison.test,hone,bind,pure,Except.bind,Except.pure]
    obtain ⟨flow,mem₁,log₁,d₁,⟨hp₁,hr₁,hq₁⟩,hw₁,hs₁⟩ := trial i locals mem hi
    cases hy : accept (candidate i) with
    | true =>
      simp only [Search.choice,hy,↓reduceIte,Option.some.injEq] at hc
      subst value
      simp only [hy,↓reduceIte] at hq₁
      obtain ⟨rfl,hgood⟩ := hq₁
      refine Contract.ofEvaluation (.whileStop ht d₁ (by trivial)) ⟨rfl,hgood,hp₁,hr₁⟩ ?_
        (by simpa [extraStack] using hs₁)
      change 3+instructions d₁ ≤ (trialWork+4)*(n+1)
      rw [Nat.mul_succ]
      omega
    | false =>
      simp only [Search.choice,hy,Bool.false_eq_true,↓reduceIte] at hc
      simp only [hy,Bool.false_eq_true,↓reduceIte] at hq₁
      obtain ⟨out,rfl,hnext⟩ := hq₁
      obtain ⟨flow,mem₂,log₂,d₂,⟨rfl,hgood,hp₂,hr₂⟩,hw₂,hs₂⟩ := ih (i+1) out mem₁ value hnext hc
      refine Contract.ofEvaluation (.whileContinue ht d₁ d₂) ⟨rfl,hgood,?_,?_⟩ ?_ ?_
      · exact (AccessPolicy.allowsTrace_append _).mpr ⟨hp₁,hp₂⟩
      · rw [Retry.randomAddresses_append,hr₁,hr₂]; rfl
      · change 4+instructions d₁+instructions d₂ ≤ (trialWork+4)*(n+1)
        rw [Nat.mul_succ]
        omega
      · exact Nat.max_le.mpr ⟨hs₁,hs₂⟩

end RamLang.Library.Enumeration
