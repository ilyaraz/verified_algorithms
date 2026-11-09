import RamLang.RegisterOnly.Arguments

namespace RamLang.RegisterOnly
open WordRam Compiler

/-- Inline calls copy arguments before execution, keep all caller locals live,
and overwrite only the designated caller result. Their trace is exactly the
callee's application trace, with no stack traffic or hidden random reads. -/
theorem call_steps {capacity callerSlots free dst : Nat} {source : Program} {rho : RandomMemory w}
    {p : WordRam.Program (capacity+2)} {s : State w (capacity+2)} {f : Function} {leaf : Leaf}
    {args : List Atom} {values : List (Word w)} {locals out : Locals w}
    {value : Word w} {mem' : DataMemory w} {trace : List (Access w)}
    (hc : CodeAt p s.pc (arguments capacity 0 callerSlots args ++ leaf.code capacity callerSlots (slot capacity 0 dst)))
    (hslots : locals.length = callerSlots) (hf : Fits capacity 0 locals.length)
    (hh : Fits capacity callerSlots f.slots) (hl : LocalsAt s.regs 0 locals)
    (hbody : leaf.toStmt = f.body) (hargs : args.mapM (Atom.eval locals) = .ok values)
    (harity : values.length = f.parameters.length)
    (d : Evaluation source rho free f.body (values.map some ++ List.replicate f.locals.length none)
      s.mem (.returned value) mem' trace)
    (assign : writeLocal locals dst value = .ok out) :
    ∃ t, WordRam.Steps p rho (args.length+(leaf.code capacity callerSlots (slot capacity 0 dst)).length) s t trace ∧
      t.pc = s.pc+args.length+(leaf.code capacity callerSlots (slot capacity 0 dst)).length ∧
      LocalsAt t.regs 0 out ∧ t.mem = mem' := by
  have harglen := arguments_values_length hargs
  obtain ⟨t,hcopy,htpc,htlocals,htmem,htvalues,_⟩ := arguments_steps
    (slots := f.slots) hc.prefix hf hh (by omega)
    (by simp only [Function.slots]; omega) hl hargs
  have hinitial : (values.map some ++ List.replicate f.locals.length (none : Option (Word w))).length = f.slots := by
    simp [Function.slots,harity]
  have hleaf : CodeAt p t.pc (leaf.code capacity callerSlots (slot capacity 0 dst)) := by
    rw [htpc]
    simpa [arguments,argumentsFrom_length] using hc.suffix
  obtain ⟨u,hsteps,hupc,huvalue,humem,huframe⟩ := leaf_steps leaf (slot capacity 0 dst) hleaf
    (by rw [hinitial]; exact hh) htvalues.locals (by rw [hbody,htmem]; exact d)
  refine ⟨u,?_,by rw [hupc,htpc],?_,humem⟩
  · simpa only [List.nil_append] using hcopy.trans hsteps
  · apply htlocals.restore hf assign huvalue
    intro i hi hne
    apply huframe
    · intro j hj
      rw [hinitial] at hj
      exact slot_disjoint hf hh (by omega) hi hj
    · exact fun he => hne ((slot_injective hf hi (writeLocal_ok assign).1).mp he)

end RamLang.RegisterOnly
