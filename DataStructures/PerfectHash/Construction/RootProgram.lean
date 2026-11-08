import DataStructures.PerfectHash.Construction.Clear

namespace PerfectHash.Construction.Root
open WordRam Registers

inductive Label where
  | clear | loop | accept | reject
  deriving DecidableEq, Repr

/-- One root trial. The caller supplies the distinct array, directory/node
regions, bucket count, odd seed and shift. The program clears dirty directory
cells, groups each key once, and checks energy before any possibly unsafe sum. -/
def assembly : List (Assembly.Item 64 Label) := [
  .instruction (.emit (.mov remaining (.reg count))),
  .instruction (.emit (.mov distinct (.imm 0))),
  .instruction (.emit (.mul budget (.reg count) (.imm 6))),
  .instruction (.emit (.mov clearCursor (.reg directory))),
  .instruction (.emit (.mul clearRemaining (.reg buckets) (.imm 4))),
  .label .clear,
  .instruction (.branch .eq (.reg clearRemaining) (.imm 0) .loop),
  .instruction (.emit (.store (.reg clearCursor) (.imm 0))),
  .instruction (.emit (.add clearCursor (.reg clearCursor) (.imm 1))),
  .instruction (.emit (.sub clearRemaining (.reg clearRemaining) (.imm 1))),
  .instruction (.jump .clear),
  .label .loop,
  .instruction (.branch .eq (.reg remaining) (.imm 0) .accept),
  .instruction (.emit (.load key (.reg input))),
  .instruction (.emit (.mul Registers.hash (.reg seed) (.reg key))),
  .instruction (.emit (.shr Registers.hash (.reg Registers.hash) (.reg shift))),
  .instruction (.emit (.mul address (.reg Registers.hash) (.imm 4))),
  .instruction (.emit (.add address (.reg directory) (.reg address))),
  .instruction (.emit (.load oldCount (.reg address))),
  .instruction (.emit (.mul increment (.reg oldCount) (.imm 2))),
  .instruction (.emit (.add increment (.reg increment) (.imm 1))),
  .instruction (.branch .lt (.reg budget) (.reg increment) .reject),
  .instruction (.emit (.sub budget (.reg budget) (.reg increment))),
  .instruction (.emit (.add temp (.reg address) (.imm 1))),
  .instruction (.emit (.load oldHead (.reg temp))),
  .instruction (.emit (.mul node (.reg distinct) (.imm 2))),
  .instruction (.emit (.add node (.reg nodes) (.reg node))),
  .instruction (.emit (.store (.reg node) (.reg key))),
  .instruction (.emit (.add node (.reg node) (.imm 1))),
  .instruction (.emit (.store (.reg node) (.reg oldHead))),
  .instruction (.emit (.add distinct (.reg distinct) (.imm 1))),
  .instruction (.emit (.store (.reg temp) (.reg distinct))),
  .instruction (.emit (.add oldCount (.reg oldCount) (.imm 1))),
  .instruction (.emit (.store (.reg address) (.reg oldCount))),
  .instruction (.emit (.add input (.reg input) (.imm 1))),
  .instruction (.emit (.sub remaining (.reg remaining) (.imm 1))),
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

theorem program_size : program.size = 39 := by decide

theorem clear_embedded : BodyEmbedded Clear.program program 5 := by
  apply BodyEmbedded.of_check
  decide

end PerfectHash.Construction.Root
