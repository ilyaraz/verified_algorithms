import RamLang.WellFormed
import Lean

/-! C-like surface grammar. The elaborator resolves names, introduces temporary
locals, and checks the resulting small core before returning a Lean term. -/
namespace RamLang.DSL
open Lean

declare_syntax_cat ramExpr
syntax ident : ramExpr
syntax num : ramExpr
syntax "(" ramExpr ")" : ramExpr
syntax:65 ramExpr:65 " + " ramExpr:66 : ramExpr
syntax:65 ramExpr:65 " - " ramExpr:66 : ramExpr
syntax:70 ramExpr:70 " * " ramExpr:71 : ramExpr
syntax:70 ramExpr:70 " % " ramExpr:71 : ramExpr
syntax:60 ramExpr:60 " >> " ramExpr:61 : ramExpr
syntax ident "(" ramExpr,* ")" : ramExpr
syntax "load" "(" ramExpr ")" : ramExpr
syntax "random" "(" ramExpr ")" : ramExpr

declare_syntax_cat ramCond
syntax ramExpr " == " ramExpr : ramCond
syntax ramExpr " != " ramExpr : ramCond
syntax ramExpr " < " ramExpr : ramCond
syntax ramExpr " <= " ramExpr : ramCond

declare_syntax_cat ramStmt
syntax "let " ident " = " ramExpr ";" : ramStmt
syntax "let " ident ";" : ramStmt
syntax ident " = " ramExpr ";" : ramStmt
syntax "store" "(" ramExpr "," ramExpr ")" ";" : ramStmt
syntax "return " ramExpr ";" : ramStmt
syntax "if " "(" ramCond ")" "{" ramStmt* "}" "else " "{" ramStmt* "}" : ramStmt
syntax "if " "(" ramCond ")" "{" ramStmt* "}" : ramStmt
syntax "while " "(" ramCond ")" "{" ramStmt* "}" : ramStmt
syntax "{" ramStmt* "}" : ramStmt

declare_syntax_cat ramFn
syntax "fn " ident "(" ident,* ")" "{" ramStmt* "}" : ramFn
syntax (name := programSyntax) "ram_program " ident " {" ramFn* "}" : term

-- Reflection builds ordinary constructor terms; generated programs have no
-- dependency on parser state or on elaborator computations.
deriving instance ToExpr for WordRam.Comparison
deriving instance ToExpr for RamLang.Atom
deriving instance ToExpr for RamLang.Binary
deriving instance ToExpr for RamLang.Condition
deriving instance ToExpr for RamLang.Primitive
deriving instance ToExpr for RamLang.Stmt
deriving instance ToExpr for RamLang.Function
deriving instance ToExpr for RamLang.Program

end RamLang.DSL
