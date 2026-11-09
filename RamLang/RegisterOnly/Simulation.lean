import RamLang.RegisterOnly.CallProof

namespace RamLang.RegisterOnly
open WordRam Compiler

/-- The full eligible entry implements every successful source derivation with
an identical application trace and exact straight-line instruction length.
Register-only execution requires neither a stack reservation nor code-address
representability in a machine word, because it saves no return addresses. -/
theorem plan_steps {capacity callerSlots free : Nat} {source : Program} {rho : RandomMemory w}
    {p : WordRam.Program (capacity+2)} (plan : Plan)
    {locals : Locals w} {s : State w (capacity+2)} {value : Word w}
    {mem' : DataMemory w} {trace : List (Access w)}
    (hlinked : plan.Linked source) (hbudget : callerSlots+plan.extra ≤ capacity)
    (hslots : locals.length = callerSlots) (hl : LocalsAt s.regs 0 locals)
    (hc : CodeAt p s.pc (plan.code capacity callerSlots))
    (d : Evaluation source rho free plan.toStmt locals s.mem (.returned value) mem' trace) :
    ∃ t, WordRam.Steps p rho (plan.code capacity callerSlots).length s t trace ∧
      t.pc = s.pc+(plan.code capacity callerSlots).length ∧
      t.regs (result capacity) = value ∧ t.mem = mem' := by
  have hf : Fits capacity 0 locals.length := by unfold Fits; omega
  induction plan generalizing locals s trace with
  | ret a =>
    obtain ⟨t,hs,hpc,hvalue,hmem,_⟩ := leaf_steps (.ret a) (result capacity) hc hf hl d
    exact ⟨t,hs,hpc,hvalue,hmem⟩
  | step op next ih =>
    cases d with
    | sequence first second =>
      cases first with
      | primitive he =>
        obtain ⟨t,hs,htpc,htlocals,htmem,_⟩ := primitive_step hc.head hf hl he
        have hlen := Primitive.length he
        obtain ⟨u,hu,hupc,huvalue,humem⟩ := ih hlinked hbudget (by omega) htlocals
          (by rw [htpc]; exact hc.tail) (by rw [htmem]; exact second) (by simpa [hlen] using hf)
        refine ⟨u,WordRam.Steps.cons hs hu,?_,huvalue,humem⟩
        simp only [Plan.code,List.length_cons]
        omega
    | sequenceStop first _ => cases first
  | call dst callee args f leaf next ih =>
    obtain ⟨hlookup,hleaf,htail⟩ := hlinked
    have hhelper : Fits capacity callerSlots f.slots := by
      unfold Fits
      change callerSlots+max f.slots next.extra ≤ capacity at hbudget
      have := Nat.le_max_left f.slots next.extra
      omega
    have hnextBudget : callerSlots+next.extra ≤ capacity := by
      change callerSlots+max f.slots next.extra ≤ capacity at hbudget
      have := Nat.le_max_right f.slots next.extra
      omega
    change CodeAt p s.pc (arguments capacity 0 callerSlots args ++
      leaf.code capacity callerSlots (slot capacity 0 dst) ++ next.code capacity callerSlots) at hc
    cases d with
    | sequence first second =>
      cases first with
      | call lookup hargs harity _ child assign =>
        have he := Option.some.inj (hlookup.symm.trans lookup)
        cases he
        obtain ⟨t,hs,htpc,htlocals,htmem⟩ := call_steps hc.prefix hslots hf hhelper hl hleaf hargs harity child assign
        have hlen := writeLocal_preserves_length assign
        have hctail : CodeAt p t.pc (next.code capacity callerSlots) := by
          rw [htpc]
          simpa [List.length_append,arguments,argumentsFrom_length,Nat.add_assoc] using hc.suffix
        obtain ⟨u,hu,hupc,huvalue,humem⟩ := ih htail hnextBudget (by omega) htlocals hctail
          (by rw [htmem]; exact second) (by simpa [hlen] using hf)
        refine ⟨u,?_,?_,huvalue,humem⟩
        · simpa [Plan.code,List.length_append,arguments,argumentsFrom_length,Nat.add_assoc] using hs.trans hu
        · simp only [Plan.code,List.length_append,arguments,argumentsFrom_length]
          omega
    | sequenceStop first _ => cases first

end RamLang.RegisterOnly
