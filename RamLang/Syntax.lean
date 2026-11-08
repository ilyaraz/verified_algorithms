import WordRam.Program

/-! Width-independent core syntax. Function references are finite table indices,
not recursive Lean definitions; neither syntax nor checking unfolds a call. -/
namespace RamLang

/-- Convert a missing table entry into an explicit diagnostic. -/
def requireSome (error : ε) : Option α → Except ε α
  | none => .error error
  | some value => .ok value

abbrev Local := Nat
abbrev FunctionId := Nat

inductive Atom where
  | local (id : Local)
  | literal (value : Nat)
  deriving DecidableEq, Repr

inductive Binary where
  | add | sub | mul | mod | shr
  deriving DecidableEq, Repr

/-- Pure primitive operators use exactly the machine's word arithmetic. -/
def Binary.eval (op : Binary) (x y : WordRam.Word w) : WordRam.Word w :=
  match op with
  | .add => x + y
  | .sub => x - y
  | .mul => x * y
  | .mod => WordRam.unsignedMod x y
  | .shr => WordRam.unsignedShiftRight x y

structure Condition where
  comparison : WordRam.Comparison
  left : Atom
  right : Atom
  deriving DecidableEq, Repr

inductive Primitive where
  | move (dst : Local) (value : Atom)
  | binary (dst : Local) (op : Binary) (left right : Atom)
  | load (dst : Local) (address : Atom)
  | store (address value : Atom)
  | random (dst : Local) (address : Atom)
  deriving DecidableEq, Repr

inductive Stmt where
  | skip
  | primitive (operation : Primitive)
  | seq (first second : Stmt)
  | ite (condition : Condition) (yes no : Stmt)
  | while (condition : Condition) (body : Stmt)
  | call (dst : Local) (callee : FunctionId) (arguments : List Atom)
  | ret (value : Atom)
  deriving DecidableEq, Repr

/-- Names are diagnostic metadata; runtime references use declaration order. -/
structure Function where
  name : String
  parameters : List String
  locals : List String
  body : Stmt
  deriving DecidableEq, Repr

def Function.slots (f : Function) : Nat := f.parameters.length + f.locals.length

/-- ABI v1 has two header words and one word for every declared slot. -/
def Function.frameSize (f : Function) : Nat := 2 + f.slots

structure Program where
  functions : Array Function
  entry : FunctionId
  deriving DecidableEq, Repr

end RamLang
