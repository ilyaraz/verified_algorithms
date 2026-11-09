import Hashing.Source.MultiplyShift

namespace PerfectHash.Source.Query
open RamLang
set_option maxRecDepth 65536

/-- Membership in the existing packed dictionary. Hash helpers are ordinary
runtime calls; occupancy and full-key comparison distinguish absent keys. -/
def program : Program := ram_program query {
  fn query(base, key) {
    let seed = load(base);
    let shift = load(base + 1);
    let index = hash(seed, key, shift);
    let directory = base + 4 + 4 * index;
    let count = load(directory);
    if (count == 0) { return 0; }
    let table = load(directory + 3);
    let slot = table;
    if (count != 1) {
      seed = load(directory + 1);
      shift = load(directory + 2);
      index = hash(seed, key, shift);
      slot = table + 2 * index;
    }
    let flag = load(slot);
    if (flag == 0) { return 0; }
    let stored = load(slot + 1);
    if (stored == key) { return 1; }
    return 0;
  }
  fn hash(seed, key, shift) {
    let product = seed * key;
    return product >> shift;
  }
}

/-- Entry metadata includes every expression temporary as a charged local. -/
def function : Function := program.functions[0]'(by decide)

/-- The callable helper is exactly the reusable multiply-shift source function. -/
theorem hash_eq : program.functions[1]? = some Hashing.Source.MultiplyShift.function := by rfl

/-- Deterministically linked fixed instruction array, independent of width. -/
def compiled : Compiler.CompiledProgram :=
  match Compiler.compile program with
  | .ok c => c
  | .error _ => ⟨#[],[],0⟩

/-- The DSL checker and baseline compiler accept the membership program. -/
theorem compiles : Compiler.compile program = .ok compiled := by rfl

/-- Fixed code extent of the two linked functions and entry/error wrappers. -/
theorem code_size : compiled.code.size = 237 := by decide

/-- The entry and reusable hash helper occupy exactly 21 and 7 frame words. -/
theorem frame_sizes : function.frameSize = 21 ∧ Hashing.Source.MultiplyShift.function.frameSize = 7 := by decide

end PerfectHash.Source.Query
