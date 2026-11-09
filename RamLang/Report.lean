import RamLang.Compiler.Link

namespace RamLang
open WordRam Compiler

/-- Human-readable linked code with absolute instruction addresses, function
names, frame sizes, and extents. Resource proofs remain separate from reporting. -/
def report (p : Program) : Except CompileError String := do
  let c ← compile p
  let functions := c.functions.zipIdx |>.map fun (layout,i) =>
    let name := (p.functions[i]?.map Function.name).getD "?"
    s!"fn {name}: pc={layout.entry}, instructions={layout.extent}, frame={layout.frameWords}"
  let code := c.code.toList.zipIdx |>.map fun (instruction,pc) => s!"{pc}: {reprStr instruction}"
  return c.report ++ "\n" ++ String.intercalate "\n" functions ++ "\n" ++ String.intercalate "\n" code

end RamLang
