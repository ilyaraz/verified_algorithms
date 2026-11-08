import WordRam.Regions
import WordRam.Machine
import RamLang.Syntax

namespace RamLang.ABI
open WordRam

abbrev registers := 16
abbrev sp : Reg registers := ⟨0, by decide⟩
abbrev fp : Reg registers := ⟨1, by decide⟩
abbrev limit : Reg registers := ⟨2, by decide⟩
abbrev link : Reg registers := ⟨3, by decide⟩
abbrev result : Reg registers := ⟨4, by decide⟩
abbrev status : Reg registers := ⟨5, by decide⟩
abbrev left : Reg registers := ⟨6, by decide⟩
abbrev right : Reg registers := ⟨7, by decide⟩
abbrev address : Reg registers := ⟨8, by decide⟩
abbrev caller : Reg registers := ⟨9, by decide⟩

/-- The four entry-only argument registers; ordinary calls have arbitrary arity. -/
def argument (i : Fin 4) : Reg registers := ⟨12+i.val, Nat.add_lt_add_left i.isLt 12⟩

/-- Source application accesses cannot alias the reserved ordinary stack. Random
memory is separate, even when its addresses have the same numerical values. -/
def applicationEvent (stack : Region) : Access w → Bool
  | .dataRead a _ | .dataWrite a _ => !(stack.base ≤ a.toNat && a.toNat < stack.base + stack.size)
  | .randomRead _ _ => true

def projectTrace (stack : Region) (trace : List (Access w)) : List (Access w) :=
  trace.filter (applicationEvent stack)

@[simp] theorem project_random (stack : Region) (a : Addr w) (v : Word w) :
    projectTrace stack [.randomRead a v] = [.randomRead a v] := by
  simp [projectTrace, applicationEvent]

end RamLang.ABI
