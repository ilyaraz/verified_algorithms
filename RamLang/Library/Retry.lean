import RamLang.Logic.Loop

namespace RamLang.Library.Retry
open WordRam Compiler Logic

/-- Consecutive immutable-random addresses, specified independently of any
probability distribution or random-memory contents. -/
def addresses (w start : Nat) : Nat → List (Addr w)
  | 0 => []
  | n+1 => word w start :: addresses w (start+1) n

/-- Observe all random addresses in execution order, retaining repeated reads. -/
def randomAddresses (trace : List (Access w)) : List (Addr w) := trace.filterMap Access.randomAddress

/-- Random-address observation commutes with sequential composition. -/
theorem randomAddresses_append (a b : List (Access w)) :
    randomAddresses (a++b) = randomAddresses a ++ randomAddresses b := List.filterMap_append

/-- The bounded retry combinator returns zero on budget failure. An attempt may
return a nonzero success early, or continue after decrementing the counter. -/
def body (counter : Local) (attempt : Stmt) : Stmt :=
  .seq (.while ⟨.ne,.local counter,.literal 0⟩ attempt) (.ret (.literal 0))

/-- The intermediate loop contract distinguishes early success from exhaustion
of the algorithmic attempt budget, and records exactly which samples were read. -/
def LoopPost (w start total remaining : Nat) (I : Nat → Locals w → DataMemory w → Prop)
    (good : Word w → DataMemory w → Prop) (policy : AccessPolicy w)
    (flow : Flow w) (mem : DataMemory w) (trace : List (Access w)) : Prop :=
  ∃ used, used ≤ remaining ∧ randomAddresses trace = addresses w (start+(total-remaining)) used ∧
    policy.AllowsTrace trace ∧
    match flow with
    | .next locals => used = remaining ∧ I 0 locals mem
    | .returned value => value ≠ word w 0 ∧ good value mem
    | .exhausted => False

/-- A probability-free retry loop rule. Every attempt's contract must supply
one sample at its explicit fresh address, a result or decreasing counter, and
its own actual instruction and stack bounds. Recursive attempts are permitted. -/
theorem loop_contract {w free : Nat} {p : Program} {rho : RandomMemory w}
    (counter : Local) (attempt : Stmt) (start total trialWork peak : Nat)
    (I : Nat → Locals w → DataMemory w → Prop) (good : Word w → DataMemory w → Prop)
    (policy : AccessPolicy w)
    (counterValue : ∀ n locals mem, I n locals mem → (.local counter : Atom).eval locals = .ok (word w n) ∧ n < modulus w)
    (trial : ∀ n locals mem, n+1 ≤ total → I (n+1) locals mem →
      Contract p rho free attempt locals mem
        (fun flow mem' trace => randomAddresses trace = [word w (start+(total-(n+1)))] ∧
          policy.AllowsTrace trace ∧
          match flow with
          | .next out => I n out mem'
          | .returned value => value ≠ word w 0 ∧ good value mem'
          | .exhausted => False) trialWork peak) :
    ∀ n locals mem, n ≤ total → I n locals mem →
      Contract p rho free (.while ⟨.ne,.local counter,.literal 0⟩ attempt) locals mem
        (LoopPost w start total n I good policy) ((trialWork+5)*n+5) peak := by
  intro n
  induction n with
  | zero =>
    intro locals mem _ hi
    have ht : Condition.eval locals ⟨.ne,.local counter,.literal 0⟩ = .ok false := by
      simp only [Condition.eval]
      rw [(counterValue 0 locals mem hi).1]
      simp [Atom.eval,Comparison.test,bind,pure,Except.bind,Except.pure]
    exact Contract.ofEvaluation (.whileFalse ht) ⟨0,Nat.le_refl _,rfl,(by intro e he; cases he),rfl,hi⟩
      (Nat.le_refl _) (Nat.zero_le _)
  | succ n ih =>
    intro locals mem hn hi
    have hne : word w (n+1) ≠ word w 0 := by
      intro he
      have hh := (word_eq_iff_of_lt (counterValue (n+1) locals mem hi).2
        (by have := (counterValue (n+1) locals mem hi).2; omega : 0 < modulus w)).mp he
      omega
    have ht : Condition.eval locals ⟨.ne,.local counter,.literal 0⟩ = .ok true := by
      simp only [Condition.eval]
      rw [(counterValue (n+1) locals mem hi).1]
      simp [Atom.eval,Comparison.test,hne,bind,pure,Except.bind,Except.pure]
    obtain ⟨flow,mem₁,trace₁,d₁,⟨hr₁,hp₁,hflow⟩,hw₁,hpeak₁⟩ := trial n locals mem hn hi
    cases flow with
    | exhausted => exact False.elim hflow
    | returned value =>
      let d := Evaluation.whileStop ht d₁ (by trivial)
      refine Contract.ofEvaluation d ⟨1,by omega,hr₁,hp₁,hflow⟩ ?_ hpeak₁
      simp only [d,instructions,conditionCost,atom,List.length_cons,List.length_nil]
      have hmul := Nat.mul_le_mul_left (trialWork+5) (show 1 ≤ n+1 by omega)
      simp only [Nat.mul_one] at hmul
      omega
    | next out =>
      obtain ⟨flow,mem₂,trace₂,d₂,⟨used,hu,hr₂,hp₂,hflow₂⟩,hw₂,hpeak₂⟩ := ih out mem₁ (by omega) hflow
      let d := Evaluation.whileContinue ht d₁ d₂
      refine Contract.ofEvaluation d ⟨used+1,by omega,?_,?_,?_⟩ ?_ ?_
      · rw [randomAddresses_append,hr₁,hr₂]
        simp only [addresses,List.singleton_append]
        have he : start+(total-(n+1))+1 = start+(total-n) := by omega
        rw [he]
      · intro e he
        rcases List.mem_append.mp he with he | he
        · exact hp₁ e he
        · exact hp₂ e he
      · cases flow with
        | next last => exact ⟨by obtain ⟨h,_⟩ := hflow₂; omega,hflow₂.2⟩
        | returned value => exact hflow₂
        | exhausted => exact hflow₂
      · simp only [d,instructions,conditionCost,atom,List.length_cons,List.length_nil,Nat.mul_add,Nat.mul_one]
        omega
      · exact Nat.max_le.mpr ⟨hpeak₁,hpeak₂⟩

/-- Adding the final budget-failure return yields a complete retry contract.
Samples are charged once per attempt; caller/callee stack costs are supplied by
the attempt contract, and no probability assumption enters the execution proof. -/
theorem contract {w free : Nat} {p : Program} {rho : RandomMemory w}
    (counter : Local) (attempt : Stmt) (start total trialWork peak : Nat)
    (I : Nat → Locals w → DataMemory w → Prop) (good : Word w → DataMemory w → Prop)
    (policy : AccessPolicy w)
    (counterValue : ∀ n locals mem, I n locals mem → (.local counter : Atom).eval locals = .ok (word w n) ∧ n < modulus w)
    (trial : ∀ n locals mem, n+1 ≤ total → I (n+1) locals mem →
      Contract p rho free attempt locals mem
        (fun flow mem' trace => randomAddresses trace = [word w (start+(total-(n+1)))] ∧
          policy.AllowsTrace trace ∧
          match flow with
          | .next out => I n out mem'
          | .returned value => value ≠ word w 0 ∧ good value mem'
          | .exhausted => False) trialWork peak)
    (locals : Locals w) (mem : DataMemory w) (hi : I total locals mem) :
    Contract p rho free (body counter attempt) locals mem
      (fun flow mem' trace => ∃ value used, flow = .returned value ∧ used ≤ total ∧
        (value = word w 0 → used = total) ∧ (value ≠ word w 0 → good value mem') ∧
        randomAddresses trace = addresses w start used ∧ policy.AllowsTrace trace)
      ((trialWork+5)*total+12) peak := by
  obtain ⟨flow,mem',trace,d,⟨used,hu,hr,hp,hflow⟩,hw,hpeak⟩ :=
    loop_contract counter attempt start total trialWork peak I good policy counterValue trial
      total locals mem (Nat.le_refl _) hi
  have hr' : randomAddresses trace = addresses w start used := by simpa using hr
  cases flow with
  | exhausted => exact False.elim hflow
  | returned value =>
    refine Contract.ofEvaluation (.sequenceStop (b := .ret (.literal 0)) d (by trivial))
      ⟨value,used,rfl,hu,(by intro hz; exact False.elim (hflow.1 hz)),(fun _ => hflow.2),hr',hp⟩ ?_ (by simpa [extraStack] using hpeak)
    simp only [instructions]
    omega
  | next out =>
    let result := Evaluation.sequence d (Evaluation.ret (atom := .literal 0) (v := word w 0) rfl)
    refine Contract.ofEvaluation result ⟨word w 0,used,rfl,hu,(fun _ => hflow.1),?_,?_,?_⟩ ?_ ?_
    · intro h; exact False.elim (h rfl)
    · simpa using hr'
    · simpa using hp
    · simp only [result,instructions,atom,epilogue,List.length_cons,List.length_nil]
      omega
    · simpa [result,extraStack] using hpeak

/-- Every reported sample belongs to the specified consecutive address range. -/
theorem mem_addresses {w start n : Nat} {a : Addr w} :
    a ∈ addresses w start n ↔ ∃ i, i < n ∧ a = word w (start+i) := by
  induction n generalizing start with
  | zero => simp [addresses]
  | succ n ih =>
    simp only [addresses,List.mem_cons,ih]
    constructor
    · rintro (rfl | ⟨i,hi,rfl⟩)
      · exact ⟨0,by omega,by simp⟩
      · exact ⟨i+1,by omega,by congr 1; omega⟩
    · rintro ⟨i,hi,rfl⟩
      cases i with
      | zero => exact Or.inl (by simp)
      | succ i => exact Or.inr ⟨i,by omega,by congr 1; omega⟩

/-- A representable reservation gives fresh random addresses, not merely a
bound on how many calls to random memory are performed. -/
theorem addresses_nodup {w start n : Nat} (hfit : start+n < modulus w) :
    (addresses w start n).Nodup := by
  induction n generalizing start with
  | zero => exact List.nodup_nil
  | succ n ih =>
    apply List.nodup_cons.mpr
    constructor
    · intro h
      obtain ⟨i,hi,he⟩ := mem_addresses.mp h
      have hh := (word_eq_iff_of_lt (by omega : start < modulus w)
        (by omega : start+1+i < modulus w)).mp he
      omega
    · exact ih (by omega)

end RamLang.Library.Retry
