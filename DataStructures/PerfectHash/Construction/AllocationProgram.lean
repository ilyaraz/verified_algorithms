import DataStructures.PerfectHash.Construction.Round
import DataStructures.PerfectHash.Sizes

namespace PerfectHash.Construction.Allocation
open WordRam Registers

inductive Label where
  | round | rounded | finish
  deriving DecidableEq, Repr

/-- Prepare one accepted root bucket: load its computed count and head, calculate
its child capacity, and record the shift and absolute packed table address. -/
def assembly : List (Assembly.Item 64 Label) := [
  .instruction (.emit (.load childCount (.reg address))),
  .instruction (.emit (.add temp (.reg address) (.imm 1))),
  .instruction (.emit (.load rootHead (.reg temp))),
  .instruction (.emit (.mov shift (.reg width))),
  .instruction (.emit (.mov slots (.reg childCount))),
  .instruction (.branch .le (.reg childCount) (.imm 1) .finish),
  .instruction (.emit (.mul roundTarget (.reg childCount) (.reg childCount))),
  .instruction (.emit (.mul roundTarget (.reg roundTarget) (.imm 2))),
  .instruction (.emit (.mov size (.imm 1))),
  .label .round,
  .instruction (.branch .le (.reg roundTarget) (.reg size) .rounded),
  .instruction (.emit (.add size (.reg size) (.reg size))),
  .instruction (.emit (.sub shift (.reg shift) (.imm 1))),
  .instruction (.jump .round),
  .label .rounded,
  .instruction (.emit (.mov slots (.reg size))),
  .label .finish,
  .instruction (.emit (.mul temp (.reg slots) (.imm 2))),
  .instruction (.emit (.add tableEnd (.reg table) (.reg temp))),
  .instruction (.emit (.add temp (.reg address) (.imm 3))),
  .instruction (.emit (.store (.reg temp) (.reg table))),
  .instruction (.emit (.add temp (.reg address) (.imm 2))),
  .instruction (.emit (.store (.reg temp) (.reg shift))),
  .instruction (.emit .halt)]

def location (l : Label) : Nat := (Assembly.labelOffset l assembly).getD 0

def program : Program 64 := Assembly.assemble 0 location (Assembly.instructions assembly).toArray

theorem compile_eq : Assembly.compile 0 assembly = some program := by decide

theorem program_size : program.size = 21 := by decide

theorem round_embedded : BodyEmbedded Round.program program 9 := by
  apply BodyEmbedded.of_check
  decide

end PerfectHash.Construction.Allocation
