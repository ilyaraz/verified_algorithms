import RamLang.DSL.Syntax

namespace RamLang.DSL
open Lean Elab Term

/-- Compilation-time name environment and the invocation's fixed local list.
Only the resulting core program survives elaboration. -/
structure Context where
  functions : List (String × Nat)
  parameters : List String
  locals : List String := []
  scope : List (String × Local)

/-- Name lowering can report errors at the original source syntax. -/
abbrev Build := StateT Context TermElabM

/-- Sequence a source block without inserting trailing skips. -/
def block : List Stmt → Stmt
  | [] => .skip
  | [last] => last
  | first::rest => .seq first (block rest)

/-- Look up an invocation-local binding, reporting an undeclared identifier. -/
def resolveLocal (name : TSyntax `ident) : Build Local := do
  let ctx ← get
  match ctx.scope.find? (fun pair => pair.1 == name.getId.toString) with
  | some pair => return pair.2
  | none => throwErrorAt name "unknown local '{name.getId}'"

/-- Allocate a named local. Shadowing and duplicate declarations are rejected
throughout a function, while block-local names do not escape their scope. -/
def declare (name : TSyntax `ident) : Build Local := do
  let ctx ← get
  let value := name.getId.toString
  if (ctx.parameters ++ ctx.locals).contains value then
    throwErrorAt name "duplicate local '{name.getId}' (shadowing is not supported)"
  let index := ctx.parameters.length+ctx.locals.length
  set {ctx with locals := ctx.locals++[value],scope := (value,index)::ctx.scope}
  return index

/-- Compiler-generated expression temporaries are ordinary charged local slots. -/
def temporary : Build Local := do
  let ctx ← get
  let index := ctx.parameters.length+ctx.locals.length
  set {ctx with locals := ctx.locals++[s!"$tmp{index}"]}
  return index

mutual
/-- Lower an expression left to right, saving non-atomic results in caller-owned
locals so their values survive later function calls and memory effects. -/
partial def expression (stx : Syntax) : Build (List Stmt × Atom) := do
  match stx with
  | `(ramExpr| $n:num) => return ([],.literal n.getNat)
  | `(ramExpr| $name:ident) => return ([],.local (← resolveLocal name))
  | `(ramExpr| ($e:ramExpr)) => expression e
  | _ =>
    let dst ← temporary
    return (← assignment dst stx,.local dst)

/-- Lower directly into a specified destination when possible, avoiding an
unnecessary temporary and move for simple arithmetic, loads, and calls. -/
partial def assignment (dst : Local) (stx : Syntax) : Build (List Stmt) := do
  let binary (op : Binary) (x y : Syntax) : Build (List Stmt) := do
    let (xs,a) ← expression x
    let (ys,b) ← expression y
    return xs++ys++[.primitive (.binary dst op a b)]
  match stx with
  | `(ramExpr| ($e:ramExpr)) => assignment dst e
  | `(ramExpr| $x:ramExpr + $y:ramExpr) => binary .add x y
  | `(ramExpr| $x:ramExpr - $y:ramExpr) => binary .sub x y
  | `(ramExpr| $x:ramExpr * $y:ramExpr) => binary .mul x y
  | `(ramExpr| $x:ramExpr % $y:ramExpr) => binary .mod x y
  | `(ramExpr| $x:ramExpr >> $y:ramExpr) => binary .shr x y
  | `(ramExpr| load($address:ramExpr)) =>
    let (setup,a) ← expression address
    return setup++[.primitive (.load dst a)]
  | `(ramExpr| random($address:ramExpr)) =>
    let (setup,a) ← expression address
    return setup++[.primitive (.random dst a)]
  | `(ramExpr| $callee:ident($args:ramExpr,*)) =>
    let ctx ← get
    let id := ctx.functions.findIdx? (fun pair => pair.1 == callee.getId.toString)
    let some id := id | throwErrorAt callee "unknown function '{callee.getId}'"
    let arity := (ctx.functions[id]!).2
    if args.getElems.size != arity then
      throwErrorAt callee "function '{callee.getId}' expects {arity} arguments, got {args.getElems.size}"
    let lowered ← args.getElems.toList.mapM (fun (arg : TSyntax `ramExpr) => expression arg)
    return (lowered.flatMap Prod.fst)++[.call dst id (lowered.map Prod.snd)]
  | `(ramExpr| $n:num) => return [.primitive (.move dst (.literal n.getNat))]
  | `(ramExpr| $name:ident) => return [.primitive (.move dst (.local (← resolveLocal name)))]
  | _ => throwErrorAt stx "unsupported word expression"
end

/-- Lower both condition operands in source order; the prelude must execute
again at every loop test, since it may contain calls or addressed reads. -/
def condition (stx : Syntax) : Build (List Stmt × Condition) := do
  let make (op : WordRam.Comparison) (x y : Syntax) : Build (List Stmt × Condition) := do
    let (xs,a) ← expression x
    let (ys,b) ← expression y
    return (xs++ys,⟨op,a,b⟩)
  match stx with
  | `(ramCond| $x:ramExpr == $y:ramExpr) => make .eq x y
  | `(ramCond| $x:ramExpr != $y:ramExpr) => make .ne x y
  | `(ramCond| $x:ramExpr < $y:ramExpr) => make .lt x y
  | `(ramCond| $x:ramExpr <= $y:ramExpr) => make .le x y
  | _ => throwErrorAt stx "unsupported word comparison"

mutual
/-- Lower a lexical block, retaining its allocated slots but removing its local
names from the surrounding scope when the block ends. -/
partial def statements (items : Array Syntax) : Build (List Stmt) := do
  let saved := (← get).scope
  let result ← items.toList.flatMapM statement
  modify fun ctx => {ctx with scope := saved}
  return result

/-- Lower declarations, explicit memory effects, structured control, and early
returns. Rich loop tests are evaluated before entry and after each iteration. -/
partial def statement (stx : Syntax) : Build (List Stmt) := do
  match stx with
  | `(ramStmt| let $name:ident = $value:ramExpr;) =>
    let dst ← declare name
    assignment dst value
  | `(ramStmt| let $name:ident;) =>
    let _ ← declare name
    return []
  | `(ramStmt| $name:ident = $value:ramExpr;) => assignment (← resolveLocal name) value
  | `(ramStmt| store($address:ramExpr,$value:ramExpr);) =>
    let (xs,a) ← expression address
    let (ys,v) ← expression value
    return xs++ys++[.primitive (.store a v)]
  | `(ramStmt| $name:ident($args:ramExpr,*);) =>
    let (setup,_) ← expression (← `(ramExpr| $name:ident($args:ramExpr,*)))
    return setup
  | `(ramStmt| return $value:ramExpr;) =>
    let (setup,a) ← expression value
    return setup++[.ret a]
  | `(ramStmt| if ($test:ramCond) { $yes:ramStmt* } else { $no:ramStmt* }) =>
    let (setup,c) ← condition test
    let y ← statements yes
    let n ← statements no
    return setup++[.ite c (block y) (block n)]
  | `(ramStmt| if ($test:ramCond) { $yes:ramStmt* }) =>
    let (setup,c) ← condition test
    let y ← statements yes
    return setup++[.ite c (block y) .skip]
  | `(ramStmt| while ($test:ramCond) { $body:ramStmt* }) =>
    let (setup,c) ← condition test
    let b ← statements body
    return setup++[.while c (block (b++setup))]
  | `(ramStmt| { $body:ramStmt* }) => statements body
  | _ => throwErrorAt stx "unsupported source statement"
end

/-- Read all function signatures before lowering any body, allowing forward,
self-recursive, and mutually recursive calls without expanding their bodies. -/
def signatures (fns : Array Syntax) : TermElabM (List (String × Nat)) :=
  fns.toList.mapM fun declaration => do
    match declaration with
    | `(ramFn| fn $name:ident($params:ident,*) { $_body:ramStmt* }) =>
      return (name.getId.toString,params.getElems.size)
    | _ => throwErrorAt declaration "expected a function declaration"

/-- Elaborate one function using its own scope and temporary-slot allocation. -/
def function (functions : List (String × Nat)) (stx : Syntax) : TermElabM Function := do
  match stx with
  | `(ramFn| fn $name:ident($params:ident,*) { $body:ramStmt* }) =>
    let parameters := params.getElems.toList.map (fun p => p.getId.toString)
    if let some repeated := duplicate parameters then
      throwErrorAt name "duplicate parameter '{repeated}'"
    let scope := parameters.zip (List.range parameters.length)
    let (items,ctx) ← (statements body).run ⟨functions,parameters,[],scope⟩
    return ⟨name.getId.toString,parameters,ctx.locals,block items⟩
  | _ => throwErrorAt stx "expected a function declaration"

/-- Translate core checker failures back into source function and local names. -/
def diagnostic (p : Program) (error : CheckError) : String :=
  let bad := p.functions.toList.find? (fun f => (checkFunction p f).toOption.isNone)
  match error with
  | .uninitialized id =>
    match bad with
    | some f =>
      let name := (f.parameters++f.locals)[id]?.getD s!"slot {id}"
      s!"uninitialized local '{name}' in function '{f.name}'"
    | none => s!"uninitialized local slot {id}"
  | .missingReturn name => s!"function '{name}' does not return on every path"
  | .entryArity n => s!"entry function has {n} parameters; the public ABI supports at most 4"
  | _ => s!"invalid word-RAM program: {repr error}"

/-- Resolve the entry and all names, then run the existing arity, definite
initialization, and return checker before producing an ordinary Program term. -/
def elaborate (entry : TSyntax `ident) (fns : Array Syntax) : TermElabM Expr := do
  let table ← signatures fns
  if let some repeated := duplicate (table.map Prod.fst) then
    throwErrorAt entry "duplicate function '{repeated}'"
  let some index := table.findIdx? (fun pair => pair.1 == entry.getId.toString)
    | throwErrorAt entry "unknown entry function '{entry.getId}'"
  let functions ← fns.toList.mapM (function table)
  let p : Program := ⟨functions.toArray,index⟩
  match check p with
  | .ok () => return toExpr p
  | .error error => throwErrorAt entry "{diagnostic p error}"

/-- The ram_program term elaborator emits a checked core constructor term. -/
@[term_elab programSyntax] def elaborateProgram : TermElab := fun stx _ => do
  match stx with
  | `(ram_program $entry:ident { $fns:ramFn* }) => elaborate entry fns
  | _ => throwUnsupportedSyntax

end RamLang.DSL
