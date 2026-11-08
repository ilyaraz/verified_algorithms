import DataStructures.PerfectHash.Construction.Clear

namespace PerfectHash.Construction.Child
open WordRam Registers

inductive Label where
  | clear | cleared | loop | accept | reject
  deriving DecidableEq, Repr

/-- One child trial clears only its own table, traverses its root bucket's linked
nodes, and rejects on the first occupied slot. Sibling tables are untouched. -/
def assembly : List (Assembly.Item 64 Label) := [
  .instruction (.emit (.mov clearCursor (.reg table))),
  .instruction (.emit (.mul clearRemaining (.reg slots) (.imm 2))),
  .label .clear,
  .instruction (.branch .eq (.reg clearRemaining) (.imm 0) .cleared),
  .instruction (.emit (.store (.reg clearCursor) (.imm 0))),
  .instruction (.emit (.add clearCursor (.reg clearCursor) (.imm 1))),
  .instruction (.emit (.sub clearRemaining (.reg clearRemaining) (.imm 1))),
  .instruction (.jump .clear),
  .label .cleared,
  .instruction (.emit (.mov cursor (.reg rootHead))),
  .label .loop,
  .instruction (.branch .eq (.reg cursor) (.imm 0) .accept),
  .instruction (.emit (.sub node (.reg cursor) (.imm 1))),
  .instruction (.emit (.mul node (.reg node) (.imm 2))),
  .instruction (.emit (.add node (.reg nodes) (.reg node))),
  .instruction (.emit (.load key (.reg node))),
  .instruction (.emit (.mul Registers.hash (.reg seed) (.reg key))),
  .instruction (.emit (.shr Registers.hash (.reg Registers.hash) (.reg shift))),
  .instruction (.emit (.mul slot (.reg Registers.hash) (.imm 2))),
  .instruction (.emit (.add slot (.reg table) (.reg slot))),
  .instruction (.emit (.load flag (.reg slot))),
  .instruction (.branch .ne (.reg flag) (.imm 0) .reject),
  .instruction (.emit (.store (.reg slot) (.imm 1))),
  .instruction (.emit (.add slot (.reg slot) (.imm 1))),
  .instruction (.emit (.store (.reg slot) (.reg key))),
  .instruction (.emit (.add node (.reg node) (.imm 1))),
  .instruction (.emit (.load cursor (.reg node))),
  .instruction (.jump .loop),
  .label .accept,
  .instruction (.emit (.mov status (.imm 1))),
  .instruction (.emit .halt),
  .label .reject,
  .instruction (.emit (.mov status (.imm 0))),
  .instruction (.emit .halt)]

def location (l : Label) : Nat := (Assembly.labelOffset l assembly).getD 0

def program : Program 64 := Assembly.assemble 0 location (Assembly.instructions assembly).toArray

theorem compile_eq : Assembly.compile 0 assembly = some program := by decide

theorem program_size : program.size = 29 := by decide

theorem clear_embedded : BodyEmbedded Clear.program program 2 := by
  apply BodyEmbedded.of_check
  decide

end PerfectHash.Construction.Child
