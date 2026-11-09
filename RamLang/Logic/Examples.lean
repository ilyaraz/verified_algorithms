import RamLang.Logic.RecursionExample
import RamLang.Logic.ArrayExample
import RamLang.Compiler.Examples

namespace RamLang.Logic.Fixtures
open WordRam Compiler ABI

/-- Execute the generic fill with dirty RAM, an exact-fit stack, a maximum word
value, and an array near the address-space boundary. -/
theorem fill_exact_fit :
    ((Compiler.Examples.execute Fill.program 100 5 100
      [word 8 250,word 8 3,word 8 255]).toOption.map (fun r =>
      (r.reason,r.steps,(r.state.regs result).toNat,
        (List.range 4).map (fun i => (r.state.mem (word 8 (250+i))).toNat),
        projectTrace ⟨100,5⟩ r.trace))) =
      some (.halted,96,0,[255,255,255,213],
        [.dataWrite (word 8 250) (word 8 255),.dataWrite (word 8 251) (word 8 255),
          .dataWrite (word 8 252) (word 8 255)]) := by decide

/-- The zero-length branch still pays its wrapper, condition, and return costs,
while producing no application access. -/
theorem fill_empty :
    ((Compiler.Examples.execute Fill.program 100 5 40
      [word 8 255,word 8 0,word 8 1]).toOption.map (fun r =>
      (r.reason,r.steps,projectTrace ⟨100,5⟩ r.trace))) = some (.halted,30,[]) := by decide

end RamLang.Logic.Fixtures
