import DataStructures.PerfectHash.Bounded.Interface

namespace PerfectHash.Total
open WordRam Construction.Registers Bounded.Registers

/-- The fixed exhaustive-search continuation replaces only the bounded failure
halt. It enumerates odd multipliers in registers and allocates no seed list. -/
def fallbackCode : List (Instr 64) := [
  .jump 231,
  .branch .eq (.reg fallbackMode) (.imm 0) 234,
  .add seed (.reg seed) (.imm 2),
  .jump 236,
  .mov seed (.imm 1),
  .mov fallbackMode (.imm 1),
  .branch .eq (.reg stage) (.imm 0) (Bounded.location .rootTrial),
  .jump (Bounded.location .childTrial)]

/-- A single width-independent program: the bounded body, with total fallback. -/
def program : Program 64 := ⟨Bounded.program.toList.take 230 ++ fallbackCode⟩

set_option maxRecDepth 50000
set_option maxHeartbeats 20000000

theorem program_size : program.size = 238 := by decide

theorem bounded_embedded : BodyEmbedded Bounded.program program 0 := by
  apply BodyEmbedded.of_check
  decide

/-- Every continuing bounded execution has exactly the same cost and trace in
the total constructor. The unsuccessful halt is the only replaced instruction. -/
theorem lift_steps (h : Steps Bounded.program rho k s t log) : Steps program rho k s t log := by
  simpa [State.relocate] using h.relocate_body bounded_embedded

end PerfectHash.Total
