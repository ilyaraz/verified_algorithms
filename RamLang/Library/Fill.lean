import RamLang.DSL.Elaborate
import RamLang.Logic.ArrayExample

namespace RamLang.Library.Fill
open WordRam Compiler Logic

/-- A checked C-like array-fill definition. Parameters, mutable assignments, and
memory effects are explicit, and the function has a fixed five-word frame. -/
def program : Program := ram_program fill {
  fn fill(p, n, value) {
    while (n != 0) {
      store(p, value);
      p = p + 1;
      n = n - 1;
    }
    return 0;
  }
}

/-- Elaboration produces exactly the core verified by the invariant proof. -/
theorem core : program = Logic.Fill.program := by rfl

/-- The DSL definition inherits the generic source fill contract by definitional
 equality, with a linear instruction allowance and no extra stack allocation. -/
theorem contract {w free : Nat} (rho : RandomMemory w) (initial : DataMemory w)
    (base count : Nat) (value : Word w) (hfit : base+count < modulus w) :
    Contract program rho free Logic.Fill.function.body [some (word w base),some (word w count),some value] initial
      (fun flow mem' trace => flow = .returned (word w 0) ∧ mem' = Logic.Fill.filled initial base count value ∧
        (Logic.Fill.policy base count).AllowsTrace trace) (22*count+12) 0 :=
  Logic.Fill.contract rho initial base count value hfit

end RamLang.Library.Fill
