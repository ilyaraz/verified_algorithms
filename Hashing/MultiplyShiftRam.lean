import Hashing.MultiplyShift
import WordRam.Blocks

namespace Hashing.MultiplyShiftRam
open WordRam

def result : Reg 4 := ⟨0, by decide⟩
def seed : Reg 4 := ⟨1, by decide⟩
def key : Reg 4 := ⟨2, by decide⟩
def shift : Reg 4 := ⟨3, by decide⟩

/-- Fixed code. Shift amount is stored with the seed, not recomputed by query. -/
def evaluator : Program 4 := #[
  .mul result (.reg seed) (.reg key),
  .shr result (.reg result) (.reg shift),
  .halt]

/-- One raw word in seed; result is its odd encoding. key is the only temporary. -/
def sampler : Program 4 := #[
  .mod key (.reg seed) (.imm 2),
  .sub result (.reg seed) (.reg key),
  .add result (.reg result) (.imm 1),
  .halt]

theorem evaluator_exact (rho : RandomMemory w) (rs : Registers w 4) (mem : DataMemory w) :
    run evaluator rho 3 (.initial rs mem) =
      ⟨⟨2, update rs result (unsignedShiftRight (rs seed * rs key) (rs shift)), mem⟩,
       3, [], .halted⟩ := by
  simp [evaluator, run, step, State.initial, State.put, Operand.eval, result, seed,
    key, shift, update, RunResult.prepend, update_shadow]

theorem sampler_exact (rho : RandomMemory w) (rs : Registers w 4) (mem : DataMemory w) :
    run sampler rho 4 (.initial rs mem) =
      ⟨⟨3, update (update rs key (unsignedMod (rs seed) (word w 2))) result
        (MultiplyShift.sample (rs seed)), mem⟩, 4, [], .halted⟩ := by
  simp [sampler, run, step, State.initial, State.put, Operand.eval, result, seed,
    key, update, RunResult.prepend, MultiplyShift.sample, update_shadow]

theorem evaluator_correct (rho : RandomMemory w) (rs : Registers w 4) (mem : DataMemory w)
    (hw : w < modulus w) (hc : rs shift = word w (w-bits)) :
    (run evaluator rho 3 (.initial rs mem)).state.regs result =
      MultiplyShift.eval (rs seed) (rs key) bits := by
  rw [evaluator_exact]
  simp only [update_same]
  rw [unsignedShiftRight, hc, word_toNat_of_lt (Nat.lt_of_le_of_lt (Nat.sub_le _ _) hw)]
  rfl

/-- A fallback enumerator can use this one charged instruction between trials. -/
def advanceSeed : Program 4 := #[.add seed (.reg seed) (.imm 2), .halt]

theorem advanceSeed_exact (rho : RandomMemory w) (rs : Registers w 4) (mem : DataMemory w) :
    run advanceSeed rho 2 (.initial rs mem) =
      ⟨⟨1, update rs seed (MultiplyShift.advance (rs seed)), mem⟩, 2, [], .halted⟩ := by
  simp [advanceSeed, run, step, State.initial, State.put, Operand.eval,
    MultiplyShift.advance, RunResult.prepend]

end Hashing.MultiplyShiftRam
