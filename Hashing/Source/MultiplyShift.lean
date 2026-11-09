import RamLang.DSL.Derive
import Hashing.MultiplyShift

namespace Hashing.Source.MultiplyShift
open WordRam RamLang RamLang.Compiler RamLang.Logic

/-- Ordinary multiplication followed by a word-valued shift, in the C-like DSL.
The shift is an explicit runtime parameter, including oversized shifts. -/
def program : RamLang.Program := ram_program hash {
  fn hash(seed, key, shift) {
    let product = seed * key;
    return product >> shift;
  }
}

/-- Reusable source function, inserted into application function tables. -/
def function : RamLang.Function := program.functions[0]'(by decide)

/-- The independent source execution evaluates wrapping multiply-shift with
no data or random accesses, twenty-two charged instructions, and no nested frame. -/
def evaluation {w free : Nat} (p : RamLang.Program) (rho : RandomMemory w)
    (mem : DataMemory w) (seed key shift : Word w) :
    Evaluation p rho free function.body
      ([seed,key,shift].map some ++ List.replicate function.locals.length none) mem
      (.returned (unsignedShiftRight (seed*key) shift)) mem [] := by
  exact .sequence (.primitive (event := none) rfl)
    (.sequence (.primitive (event := none) rfl) (.ret rfl))

/-- Exact baseline instruction charge for the multiply-shift source body. -/
theorem evaluation_work {w free : Nat} (p : RamLang.Program) (rho : RandomMemory w)
    (mem : DataMemory w) (seed key shift : Word w) :
    instructions (evaluation (free := free) p rho mem seed key shift) = 22 := by rfl

/-- The helper itself allocates no further frame. -/
theorem evaluation_peak {w free : Nat} (p : RamLang.Program) (rho : RandomMemory w)
    (mem : DataMemory w) (seed key shift : Word w) :
    extraStack (evaluation (free := free) p rho mem seed key shift) = 0 := by rfl

end Hashing.Source.MultiplyShift
