import RamLang.Logic.Loop

namespace RamLang.Library.Traversal
open WordRam Compiler Logic

/-- Traverse while an ordinary word counter is nonzero. The visit body owns
its pointer updates and counter decrement, permitting arbitrary array layouts. -/
def loop (counter : Local) (visit : Stmt) : Stmt :=
  .while ⟨.ne,.local counter,.literal 0⟩ visit

/-- A generic linear traversal contract. Each visit decreases the represented
counter by one, preserves the client invariant, and supplies its own access
policy, instruction allowance, and stack peak. -/
theorem contract {w free : Nat} {p : Program} {rho : RandomMemory w} (counter : Local) (visit : Stmt)
    (I : Nat → Locals w → DataMemory w → Prop) (policy : AccessPolicy w) (visitWork peak : Nat)
    (counterValue : ∀ n locals mem, I n locals mem → (.local counter : Atom).eval locals = .ok (word w n) ∧ n < modulus w)
    (body : ∀ n locals mem, I (n+1) locals mem → Contract p rho free visit locals mem
      (fun flow mem' trace => ∃ out, flow = .next out ∧ I n out mem' ∧ policy.AllowsTrace trace) visitWork peak) :
    ∀ n locals mem, I n locals mem → Contract p rho free (loop counter visit) locals mem
      (fun flow mem' trace => ∃ out, flow = .next out ∧ I 0 out mem' ∧ policy.AllowsTrace trace)
      ((visitWork+5)*n+5) peak := by
  let c : Condition := ⟨.ne,.local counter,.literal 0⟩
  have evaluate {n locals mem} (hi : I n locals mem) :
      c.eval locals = .ok (!(word w n == word w 0)) := by
    simp only [c,Condition.eval]
    rw [(counterValue n locals mem hi).1]
    rfl
  have h := while_total (p := p) (rho := rho) (free := free) (condition := c) (body := visit)
    I policy (fun n => (visitWork+5)*n+5) (fun _ => visitWork) peak
    (fun _ _ _ hi => ⟨_,evaluate hi⟩)
    (by intro n; change 3+2 ≤ (visitWork+5)*n+5; omega)
    (by
      intro n m hm
      have hmul := Nat.mul_le_mul_left (visitWork+5) (show m+1 ≤ n by omega)
      simp only [Nat.mul_add,Nat.mul_one] at hmul
      change 3+2+visitWork+((visitWork+5)*m+5) ≤ (visitWork+5)*n+5
      omega)
    (by
      intro n locals mem hi ht
      cases n with
      | zero => rw [evaluate hi] at ht; simp at ht
      | succ n =>
        exact (body n locals mem hi).consequence
          (by rintro _ _ _ ⟨out,hf,hI,hp⟩; exact ⟨out,n,hf,by omega,hI,hp⟩)
          (Nat.le_refl _) (Nat.le_refl _))
  intro n locals mem hi
  apply (h n locals mem hi).consequence
  · rintro _ mem' _ ⟨out,k,hflow,hI,hfalse,hpolicy⟩
    rw [evaluate hI] at hfalse
    have hz : word w k = word w 0 := by simpa using hfalse
    have hk := (word_eq_iff_of_lt (counterValue k out mem' hI).2
      (by have := (counterValue k out mem' hI).2; omega : 0 < modulus w)).mp hz
    subst k
    exact ⟨out,hflow,hI,hpolicy⟩
  · exact Nat.le_refl _
  · exact Nat.le_refl _

end RamLang.Library.Traversal
