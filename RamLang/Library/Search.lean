import RamLang.Library.Retry

namespace RamLang.Library.Search
open WordRam Compiler Logic

/-- First accepted value among a consecutive, finite sequence of candidates.
This is a proof model; source programs compute candidates and execute trials. -/
def choice (sample : Nat → Word w) (accept : Word w → Bool) (start : Nat) : Nat → Option (Word w)
  | 0 => none
  | n+1 => if accept (sample start) then some (sample start) else choice sample accept (start+1) n

/-- Number of trials actually reached, including the successful trial. -/
def attempts (sample : Nat → Word w) (accept : Word w → Bool) (start : Nat) : Nat → Nat
  | 0 => 0
  | n+1 => if accept (sample start) then 1 else 1+attempts sample accept (start+1) n

/-- No capped search uses more candidates than its supplied budget. -/
theorem attempts_le (sample : Nat → Word w) (accept : Word w → Bool) (start n : Nat) :
    attempts sample accept start n ≤ n := by
  induction n generalizing start with
  | zero => exact Nat.le_refl _
  | succ n ih => simp only [attempts]; split <;> have := ih (start+1) <;> omega

/-- A search result distinguishes exhaustion of the algorithm's budget from an
early accepted return; it never contains runtime stack exhaustion. -/
def Post (sample : Nat → Word w) (accept : Word w → Bool)
    (I : Nat → Nat → Locals w → DataMemory w → Prop) (good : Word w → DataMemory w → Prop)
    (start n : Nat) (flow : Flow w) (mem : DataMemory w) : Prop :=
  match choice sample accept start n with
  | none => ∃ out, flow = .next out ∧ I (start+n) 0 out mem
  | some a => flow = .returned a ∧ good a mem

/-- Exact stopping-time rule for a source retry loop. The trial premise proves
one real candidate computation, its effects and result. Successful prefixes
charge only reached trials, which permits subsequent expectation analysis. -/
theorem loop_contract {w free : Nat} {p : Program} {rho : RandomMemory w}
    (counter : Local) (body : Stmt) (sample : Nat → Word w) (accept : Word w → Bool)
    (I : Nat → Nat → Locals w → DataMemory w → Prop) (good : Word w → DataMemory w → Prop)
    (policy : AccessPolicy w) (trialWork peak : Nat)
    (counterValue : ∀ c n locals mem, I c n locals mem →
      (.local counter : Atom).eval locals = .ok (word w n) ∧ n < modulus w)
    (trial : ∀ c n locals mem, I c (n+1) locals mem →
      Contract p rho free body locals mem
        (fun flow mem' log => policy.AllowsTrace log ∧ Retry.randomAddresses log = [word w c] ∧
          if accept (sample c) then flow = .returned (sample c) ∧ good (sample c) mem'
          else ∃ out, flow = .next out ∧ I (c+1) n out mem') trialWork peak) :
    ∀ c n locals mem, I c n locals mem →
      Contract p rho free (.while ⟨.ne,.local counter,.literal 0⟩ body) locals mem
        (fun flow mem' log => Post sample accept I good c n flow mem' ∧ policy.AllowsTrace log ∧
          Retry.randomAddresses log = Retry.addresses w c (attempts sample accept c n))
        ((trialWork+5)*attempts sample accept c n+5) peak := by
  intro c n
  induction n generalizing c with
  | zero =>
    intro locals mem hi
    have ht : Condition.eval locals ⟨.ne,.local counter,.literal 0⟩ = .ok false := by
      simp only [Condition.eval]
      rw [(counterValue c 0 locals mem hi).1]
      simp [Atom.eval,Comparison.test,bind,pure,Except.bind,Except.pure]
    refine Contract.ofEvaluation (.whileFalse ht) ⟨⟨locals,rfl,?_⟩,?_,rfl⟩ (by simp [instructions,conditionCost,atom,attempts]) (Nat.zero_le _)
    · simpa using hi
    · intro e he; cases he
  | succ n ih =>
    intro locals mem hi
    have hfit := (counterValue c (n+1) locals mem hi).2
    have hne : word w (n+1) ≠ word w 0 := by
      intro he
      have := (word_eq_iff_of_lt hfit (by omega : 0 < modulus w)).mp he
      omega
    have ht : Condition.eval locals ⟨.ne,.local counter,.literal 0⟩ = .ok true := by
      simp only [Condition.eval]
      rw [(counterValue c (n+1) locals mem hi).1]
      simp [Atom.eval,Comparison.test,hne,bind,pure,Except.bind,Except.pure]
    obtain ⟨flow,mem₁,log₁,d₁,⟨hp₁,hr₁,hq₁⟩,hw₁,hs₁⟩ := trial c n locals mem hi
    cases hy : accept (sample c) with
    | true =>
      simp only [hy,↓reduceIte] at hq₁
      obtain ⟨rfl,hgood⟩ := hq₁
      refine Contract.ofEvaluation (.whileStop ht d₁ (by trivial)) ⟨?_,hp₁,?_⟩ ?_ (by simpa [extraStack] using hs₁)
      · simpa [Post,choice,hy] using hgood
      · simpa [attempts,hy,Retry.addresses] using hr₁
      · simp only [instructions,conditionCost,atom,List.length_cons,List.length_nil,attempts,hy,Bool.false_eq_true,↓reduceIte]
        omega
    | false =>
      simp only [hy,↓reduceIte] at hq₁
      obtain ⟨out,rfl,hnext⟩ := hq₁
      obtain ⟨flow,mem₂,log₂,d₂,⟨hq₂,hp₂,hr₂⟩,hw₂,hs₂⟩ := ih (c+1) out mem₁ hnext
      refine Contract.ofEvaluation (.whileContinue ht d₁ d₂) ⟨?_,?_,?_⟩ ?_ ?_
      · simpa [Post,choice,hy,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hq₂
      · exact (AccessPolicy.allowsTrace_append _).mpr ⟨hp₁,hp₂⟩
      · rw [Retry.randomAddresses_append,hr₁,hr₂]
        simp [attempts,hy,Retry.addresses,Nat.add_comm 1]
      · simp only [instructions,conditionCost,atom,List.length_cons,List.length_nil,attempts,hy,Bool.false_eq_true,↓reduceIte,Nat.mul_add,Nat.mul_one]
        omega
      · exact Nat.max_le.mpr ⟨hs₁,hs₂⟩

end RamLang.Library.Search
