import RamLang.Compiler.Proofs.Linking

namespace RamLang.Compiler
open WordRam ABI

/-- Install an application-specific entry adapter after the linked code and
redirect PC zero to it. Function bodies, saved links and all existing final
addresses remain fixed. The adapter supplies its own charged entry convention. -/
def withEntry (code : WordRam.Program R) (adapter : List (Instr R)) : WordRam.Program R :=
  code.setIfInBounds 0 (.jump code.size) ++ adapter.toArray

/-- Appending an entry adapter adds precisely its instruction count. -/
theorem withEntry_size (code : WordRam.Program R) (adapter : List (Instr R)) :
    (withEntry code adapter).size = code.size+adapter.length := by simp [withEntry]

/-- Every linked positive-address fragment survives the new entry unchanged. -/
theorem CodeAt.withEntry {code : WordRam.Program R} {pc : Nat} {fragment : List (Instr R)}
    (h : CodeAt code pc fragment) (hp : 0 < pc) (adapter : List (Instr R)) :
    CodeAt (withEntry code adapter) pc fragment := by
  intro i instruction hi
  have hh := h i instruction hi
  have hb := (Array.getElem?_eq_some_iff.mp hh).1
  unfold RamLang.Compiler.withEntry
  rw [Array.getElem?_append_left (by simpa using hb)]
  simpa [Array.getElem?_setIfInBounds_ne (by omega : 0 ≠ pc+i)] using hh

/-- The appended adapter is fetched at the original linked code extent. -/
theorem withEntry_adapter (code : WordRam.Program R) (adapter : List (Instr R)) :
    CodeAt (withEntry code adapter) code.size adapter := by
  intro i instruction hi
  unfold RamLang.Compiler.withEntry
  rw [Array.getElem?_append_right (by simp)]
  simpa using hi

/-- The public PC-zero entry takes one charged jump to the adapter. -/
theorem withEntry_zero (code : WordRam.Program R) (adapter : List (Instr R)) (h : 0 < code.size) :
    (withEntry code adapter)[0]? = some (.jump code.size) := by
  unfold RamLang.Compiler.withEntry
  rw [Array.getElem?_append_left (by simpa using h)]
  exact Array.getElem?_setIfInBounds_self_of_lt h

/-- The standard wrapper's first instruction is independent of entry arity. -/
theorem compile_zero {source : Program} {c : CompiledProgram} (h : compile source = .ok c) :
    c.code[0]? = some (.mov status (.imm 0)) := by
  have hc := compile_checked h
  unfold WellFormed at hc
  simp only [compile,hc,Except.ok.injEq] at h
  subst c
  rfl

/-- A compiled function begins strictly after PC zero: its prologue cannot be
the standard wrapper's initial status assignment. -/
theorem compile_entry_positive {source : Program} {c : CompiledProgram} {id : FunctionId} {f : Function}
    (h : compile source = .ok c) (hi : source.functions[id]? = some f) :
    0 < (c.functions[id]?.map FunctionLayout.entry).getD 0 := by
  have hb := (compile_linked h id f hi).2.head
  have hz := compile_zero h
  cases he : (c.functions[id]?.map FunctionLayout.entry).getD 0 with
  | zero => dsimp only at hb; rw [he,hz] at hb; cases hb
  | succ n => omega

/-- The shared runtime-exhaustion handler also has a positive fixed address. -/
theorem compile_exhaustion_positive {source : Program} {c : CompiledProgram}
    (h : compile source = .ok c) : 0 < c.exhaustion := by
  have hc := compile_checked h
  unfold WellFormed at hc
  simp only [compile,hc,Except.ok.injEq] at h
  subst c
  simp only [exhaustionPC]
  omega

/-- Ordinary and recursive calls continue using the same final label map when
an application replaces the public entry convention. -/
theorem withEntry_linked {source : Program} {c : CompiledProgram}
    (h : compile source = .ok c) (adapter : Code) :
    LinkedFunctions source (withEntry c.code adapter)
      (fun id => (source.functions[id]?.map Function.frameSize).getD 0)
      (fun id => (c.functions[id]?.map FunctionLayout.entry).getD 0) c.exhaustion := by
  intro id f hi
  have hb := compile_linked h id f hi
  exact ⟨hb.1,hb.2.withEntry (compile_entry_positive h hi) adapter⟩

/-- Source body simulation is available inside a custom entry wrapper. All
adapter instructions and its initial frame must be verified separately; this
theorem adds no uncharged initialization or implicit calling arguments. -/
theorem withEntry_evaluation {w free : Nat} {source : Program} {c : CompiledProgram} {adapter : Code}
    {rho : RandomMemory w} {stmt : Stmt} {locals : Locals w} {mem mem' : DataMemory w}
    {flow : Flow w} {log : List (Access w)} {stack : Region}
    (hcompile : compile source = .ok c) (hfit : c.Fits w)
    (hcode : (withEntry c.code adapter).size < modulus w)
    (d : Evaluation source rho free stmt locals mem flow mem' log) (hsep : Separated stack log) :
    Implements (withEntry c.code adapter) rho
      (fun id => (source.functions[id]?.map Function.frameSize).getD 0)
      (fun id => (c.functions[id]?.map FunctionLayout.entry).getD 0) c.exhaustion stack
      free stmt locals mem flow mem' log (instructions d) (extraStack d) :=
  evaluation_simulation (withEntry_linked hcompile adapter) hcode
    (fun _ _ hi => compile_frame_fit hcompile hfit hi)
    ((compile_error hcompile).withEntry (compile_exhaustion_positive hcompile) adapter) d hsep

end RamLang.Compiler
