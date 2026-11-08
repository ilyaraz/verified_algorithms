/- Appended to a temporary, example-named copy of Checks.lean by build_website.py.
   The real library and Checks.lean are never modified. -/
open Lean in
run_cmd do
  let env ← getEnv
  let mut rows : Array Json := #[]
  for (name, info) in env.constants.toList do
    let mod := (← findModuleOf? name).getD `Checks
    if mod.getRoot == `WordRam || mod == `Checks then
      let ranges ← findDeclarationRanges? name
      let kind := match info with
        | .thmInfo _ => "theorem"
        | .inductInfo _ => "inductive"
        | .ctorInfo _ => "constructor"
        | .recInfo _ => "recursor"
        | .axiomInfo _ => "axiom"
        | .opaqueInfo _ => "opaque"
        | .defnInfo _ => "definition"
        | .quotInfo _ => "quotient"
      rows := rows.push <| Json.mkObj [
        ("name", toJson name.toString),
        ("module", toJson mod.toString),
        ("kind", toJson kind),
        ("line", toJson (ranges.map (·.selectionRange.pos.line))),
        ("endLine", toJson (ranges.map (·.range.endPos.line))),
        ("typeDeps", toJson (info.type.getUsedConstants.map Name.toString)),
        ("valueDeps", toJson ((info.value?.map Expr.getUsedConstants).getD #[] |>.map Name.toString))]
  IO.FS.writeFile ".lake/website/declarations.json" (Json.arr rows).compress
