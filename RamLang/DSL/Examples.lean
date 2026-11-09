import RamLang.DSL.Elaborate
import RamLang.Logic.RecursionExample
import RamLang.Logic.ArrayExample
import RamLang.Compiler.Examples

set_option maxRecDepth 10000

namespace RamLang.DSL.Examples
open WordRam

/-- Readable non-tail recursion elaborates to the same core that already has a
general functional, exact-time, and stack-space proof. -/
def sum : Program := ram_program sum {
  fn sum(n) {
    if (n == 0) {
      return 0;
    } else {
      let saved = n;
      n = n - 1;
      let result = sum(n);
      result = result + saved;
      return result;
    }
  }
}

theorem sum_core : sum = RamLang.Examples.sum := by rfl

/-- The iterative invariant proof applies directly to this C-like array routine. -/
def fill : Program := ram_program fill {
  fn fill(p, n, value) {
    while (n != 0) {
      store(p, value);
      p = p + 1;
      n = n - 1;
    }
    return 0;
  }
}

theorem fill_core : fill = Logic.Fill.program := by rfl

/-- Function signatures are resolved before bodies, including forward mutual
references and early returns through nested control flow. -/
def parity : Program := ram_program even {
  fn even(n) {
    if (n == 0) { return 1; }
    return odd(n - 1);
  }
  fn odd(n) {
    if (n == 0) { return 0; }
    return even(n - 1);
  }
}

/-- The left call's result survives the right call and its memory mutation. -/
def ordered : Program := ram_program main {
  fn main(p) {
    let value = touch(p, 11) + touch(p, 22);
    return value;
  }
  fn touch(p, value) {
    store(p, value);
    return load(p);
  }
}

/-- A rich loop test is reevaluated on entry and after each body execution. -/
def richLoop : Program := ram_program main {
  fn main(p) {
    while (load(p) != 0) {
      store(p, load(p) - 1);
    }
    return 9;
  }
}

/-- Executing nested calls confirms left-to-right effects and live temporaries. -/
theorem ordered_execution :
    ((Compiler.Examples.execute ordered 100 20 1000 [word 8 40]).toOption.map (fun r =>
      (r.reason,(r.state.regs ABI.result).toNat,ABI.projectTrace ⟨100,20⟩ r.trace))) =
      some (.halted,33,[.dataWrite (word 8 40) (word 8 11),.dataRead (word 8 40) (word 8 11),
        .dataWrite (word 8 40) (word 8 22),.dataRead (word 8 40) (word 8 22)]) := by decide

/-- Mutual calls share finite function bodies and execute through the same compiler. -/
theorem parity_execution :
    ((Compiler.Examples.execute parity 100 100 1000 [word 8 6]).toOption.map (fun r =>
      (r.reason,(r.state.regs ABI.result).toNat))) = some (.halted,1) := by decide

end RamLang.DSL.Examples
