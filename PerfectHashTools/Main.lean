import PerfectHashTools.Export
import PerfectHashTools.Demo

/-- Small interpreter-based entry point for certified execution and exact Lean
source export. This does not claim correctness of an external native backend. -/
def main (args : List String) : IO Unit := do
  match args with
  | [] | ["demo"] => PerfectHash.Demo.run
  | ["export",path] => PerfectHash.Export.write path
  | _ => throw (IO.userError "Usage: demo | export OUTPUT.lean")
