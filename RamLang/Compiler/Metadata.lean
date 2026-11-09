import RamLang.Compiler.Link

namespace RamLang.Compiler

/-- Frame and entry metadata are computed from syntax without reducing the
emitted instruction array. This also keeps client resource proofs inexpensive. -/
theorem compile_layouts (h : compile p = .ok c) :
    c.functions = layouts (wrapperSize (((p.functions[p.entry]?).map (fun f => f.parameters.length)).getD 0)) p.functions.toList := by
  have hc := compile_checked h
  unfold WellFormed at hc
  simp only [compile,hc,Except.ok.injEq] at h
  subst c
  rfl

end RamLang.Compiler
