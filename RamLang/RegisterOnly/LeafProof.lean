import RamLang.RegisterOnly.Primitives
import RamLang.Evaluation

namespace RamLang.RegisterOnly
open WordRam Compiler

/-- Inline execution preserves all registers outside its helper interval except
the explicitly designated caller result register. -/
def PreservesExcept (before after : Registers w (capacity+2)) (base count : Nat)
    (destination : Reg (capacity+2)) : Prop :=
  ∀ r, Outside capacity base count r → r ≠ destination → after r = before r

/-- Every finite source proof for an eligible helper transfers to its inline
code, with exact instruction length and the full source trace unchanged. -/
theorem leaf_steps {capacity base free : Nat} {source : Program} {rho : RandomMemory w}
    {p : WordRam.Program (capacity+2)} (leaf : Leaf) (destination : Reg (capacity+2))
    {locals : Locals w} {s : State w (capacity+2)} {value : Word w}
    {mem' : DataMemory w} {trace : List (Access w)}
    (hc : CodeAt p s.pc (leaf.code capacity base destination))
    (hf : Fits capacity base locals.length) (hl : LocalsAt s.regs base locals)
    (d : Evaluation source rho free leaf.toStmt locals s.mem (.returned value) mem' trace) :
    ∃ t, WordRam.Steps p rho (leaf.code capacity base destination).length s t trace ∧
      t.pc = s.pc+(leaf.code capacity base destination).length ∧ t.regs destination = value ∧ t.mem = mem' ∧
      PreservesExcept s.regs t.regs base locals.length destination := by
  induction leaf generalizing locals s trace with
  | ret a =>
    cases d with
    | ret hv =>
      let t := s.put destination value
      have hs : WordRam.Step p rho s t none := by
        unfold WordRam.Step WordRam.step
        rw [hc.head]
        simp only [atom_value hl hv]
        rfl
      refine ⟨t,?_,rfl,?_,rfl,?_⟩
      · exact .cons hs (.refl t)
      · exact update_same _ _ _
      · intro r _ hr
        exact update_other _ _ _ _ hr
  | step op next ih =>
    cases d with
    | sequence first second =>
      cases first with
      | primitive he =>
        rename_i out middle trace event
        obtain ⟨t,hstep,htpc,htlocals,htmem,htframe⟩ := primitive_step hc.head hf hl he
        have hlen := Primitive.length he
        have hc' : CodeAt p t.pc (next.code capacity base destination) := by rw [htpc]; exact hc.tail
        have hf' : Fits capacity base out.length := by rw [hlen]; exact hf
        obtain ⟨u,hsteps,hupc,huvalue,humem,huframe⟩ := ih hc' hf' htlocals (by rw [htmem]; exact second)
        refine ⟨u,WordRam.Steps.cons hstep hsteps,?_,huvalue,humem,?_⟩
        · simp only [Leaf.code,List.length_cons]
          omega
        · intro r hr hdst
          exact (huframe r (by simpa [hlen] using hr) hdst).trans (htframe r hr)
    | sequenceStop first _ => cases first

end RamLang.RegisterOnly
