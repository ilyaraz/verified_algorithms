import RamLang.Compiler.Link
import WordRam.Execution

/-! Local proof infrastructure for code at its final linked addresses. These
lemmas do not relocate saved links or claim whole-compiler correctness. -/
namespace RamLang.Compiler
open WordRam

/-- Exact emitted instructions at final PCs, including direct-call targets. -/
def CodeAt (p : WordRam.Program R) (pc : Nat) (code : List (Instr R)) : Prop :=
  ∀ i instruction, code[i]? = some instruction → p[pc+i]? = some instruction

theorem CodeAt.head (h : CodeAt p pc (instruction :: rest)) : p[pc]? = some instruction := by
  simpa using h 0 instruction rfl

theorem CodeAt.tail (h : CodeAt p pc (instruction :: rest)) : CodeAt p (pc+1) rest := by
  intro i instruction hi
  simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h (i+1) instruction hi

theorem CodeAt.prefix (h : CodeAt p pc (first ++ second)) : CodeAt p pc first := by
  intro i instruction hi
  apply h i instruction
  obtain ⟨hb, he⟩ := List.getElem?_eq_some_iff.mp hi
  simp [List.getElem?_append_left hb, hi]

theorem CodeAt.suffix (h : CodeAt p pc (first ++ second)) : CodeAt p (pc+first.length) second := by
  intro i instruction hi
  have hh : (first++second)[first.length+i]? = some instruction := by
    rw [List.getElem?_append_right (by omega)]
    simpa using hi
  simpa [Nat.add_assoc] using h (first.length+i) instruction hh

/-- Lists emitted at the front of an array have their literal linked addresses. -/
theorem CodeAt.toArray (code : List (Instr R)) : CodeAt code.toArray 0 code := by
  intro i instruction hi
  simpa using hi

/-- Padding on the left changes only the physical fetch position. Instructions
already contain their final targets and are not relocated by this lemma. -/
theorem CodeAt.append (leading code trailing : List (Instr R)) :
    CodeAt (leading ++ code ++ trailing).toArray leading.length code := by
  have h := CodeAt.toArray (leading ++ (code ++ trailing))
  simpa [List.append_assoc] using h.suffix.prefix

/-- A state whose PC identifies this template fetches its first instruction. -/
theorem CodeAt.fetch {s : State w R} (h : CodeAt p pc (instruction :: rest))
    (hs : s.pc = pc) : p[s.pc]? = some instruction := by
  rw [hs]
  exact h.head

end RamLang.Compiler
