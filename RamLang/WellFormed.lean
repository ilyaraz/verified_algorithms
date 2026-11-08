import RamLang.Syntax

namespace RamLang

inductive CheckError where
  | duplicateFunction (name : String)
  | duplicateLocal (function name : String)
  | undefinedFunction (id : FunctionId)
  | wrongArity (id : FunctionId) (expected actual : Nat)
  | invalidLocal (id : Local)
  | uninitialized (id : Local)
  | missingReturn (function : String)
  | entryArity (actual : Nat)
  deriving DecidableEq, Repr

/-- Return the first duplicate in declaration order for stable diagnostics. -/
def duplicate : List String → Option String
  | [] => none
  | x :: xs => if xs.contains x then some x else duplicate xs

def checkLocal (slots : Nat) (id : Local) : Except CheckError Unit :=
  if id < slots then .ok () else .error (.invalidLocal id)

def checkAtom (slots : Nat) (initialized : List Local) : Atom → Except CheckError Unit
  | .literal _ => .ok ()
  | .local id => do
    checkLocal slots id
    if initialized.contains id then .ok () else .error (.uninitialized id)

def checkCondition (slots : Nat) (initialized : List Local) (c : Condition) :
    Except CheckError Unit := do
  checkAtom slots initialized c.left
  checkAtom slots initialized c.right

def checkPrimitive (slots : Nat) (initialized : List Local) :
    Primitive → Except CheckError (List Local)
  | .move d x | .load d x | .random d x => do
    checkAtom slots initialized x
    checkLocal slots d
    return d :: initialized
  | .binary d _ x y => do
    checkAtom slots initialized x
    checkAtom slots initialized y
    checkLocal slots d
    return d :: initialized
  | .store a x => do
    checkAtom slots initialized a
    checkAtom slots initialized x
    return initialized

/-- None means every path returns. At joins only continuing paths contribute. -/
def joinInitialized : Option (List Local) → Option (List Local) → Option (List Local)
  | none, y => y
  | x, none => x
  | some x, some y => some (x.filter y.contains)

/-- Conservative definite initialization. Loops may execute zero times; calls
initialize their destination only on a successful return. Unreachable syntax is
still checked, and valid self/mutual calls never cause recursive checking. -/
def checkStmt (p : Program) (slots : Nat) (initialized : List Local) :
    Stmt → Except CheckError (Option (List Local))
  | .skip => .ok (some initialized)
  | .primitive op => (checkPrimitive slots initialized op).map some
  | .seq first second => do
    let after ← checkStmt p slots initialized first
    let final ← checkStmt p slots (after.getD initialized) second
    return if after.isNone then none else final
  | .ite c yes no => do
    checkCondition slots initialized c
    let y ← checkStmt p slots initialized yes
    let n ← checkStmt p slots initialized no
    return joinInitialized y n
  | .while c body => do
    checkCondition slots initialized c
    let _ ← checkStmt p slots initialized body
    return some initialized
  | .call d id args => do
    checkLocal slots d
    let f ← requireSome (.undefinedFunction id) p.functions[id]?
    if args.length != f.parameters.length then
      throw (.wrongArity id f.parameters.length args.length)
    let _ ← args.mapM (checkAtom slots initialized)
    return some (d :: initialized)
  | .ret x => do
    checkAtom slots initialized x
    return none

def checkFunction (p : Program) (f : Function) : Except CheckError Unit := do
  if let some name := duplicate (f.parameters ++ f.locals) then
    throw (.duplicateLocal f.name name)
  let final ← checkStmt p f.slots (List.range f.parameters.length) f.body
  if final.isSome then throw (.missingReturn f.name)

def check (p : Program) : Except CheckError Unit := do
  if let some name := duplicate (p.functions.toList.map Function.name) then
    throw (.duplicateFunction name)
  let entry ← requireSome (.undefinedFunction p.entry) p.functions[p.entry]?
  if entry.parameters.length > 4 then throw (.entryArity entry.parameters.length)
  let _ ← p.functions.toList.mapM (checkFunction p)
  return ()

/-- Checking is executable and width independent; proof terms supply no code. -/
def WellFormed (p : Program) : Prop := check p = .ok ()

end RamLang
