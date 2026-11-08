import RamLang.Syntax
import WordRam.Machine

/-! Independent source semantics. Logical activations are not target state, and
capacity is optional: none is the ideal unbounded semantics. -/
namespace RamLang
open WordRam

abbrev Locals (w : Nat) := List (Option (Word w))

inductive RuntimeError where
  | undefinedFunction (id : FunctionId)
  | wrongArity
  | uninitialized (id : Local)
  | invalidDestination (id : Local)
  | missingReturn
  deriving DecidableEq, Repr

def Atom.eval (locals : Locals w) : Atom → Except RuntimeError (Word w)
  | .literal n => .ok (word w n)
  | .local id => requireSome (.uninitialized id) ((locals[id]?).join)

def writeLocal (locals : Locals w) (id : Local) (v : Word w) :
    Except RuntimeError (Locals w) :=
  if id < locals.length then .ok (locals.set id (some v))
  else .error (.invalidDestination id)

def Condition.eval (locals : Locals w) (c : Condition) : Except RuntimeError Bool := do
  return c.comparison.test (← c.left.eval locals) (← c.right.eval locals)

/-- Both source operands are read before any destination update. -/
def Primitive.eval (rho : RandomMemory w) (locals : Locals w) (mem : DataMemory w) :
    Primitive → Except RuntimeError (Locals w × DataMemory w × Option (Access w))
  | .move d x => do
    return (← writeLocal locals d (← x.eval locals), mem, none)
  | .binary d op x y => do
    let left ← x.eval locals
    let right ← y.eval locals
    return (← writeLocal locals d (op.eval left right), mem, none)
  | .load d a => do
    let address ← a.eval locals
    return (← writeLocal locals d (mem address), mem, some (.dataRead address (mem address)))
  | .store a x => do
    let address ← a.eval locals
    let value ← x.eval locals
    return (locals, update mem address value, some (.dataWrite address value))
  | .random d a => do
    let address ← a.eval locals
    return (← writeLocal locals d (rho address), mem, some (.randomRead address (rho address)))

structure Activation (w : Nat) where
  function : FunctionId
  locals : Locals w
  todo : List Stmt
  deriving DecidableEq, Repr

structure Caller (w : Nat) where
  activation : Activation w
  destination : Local
  deriving DecidableEq, Repr

inductive Control (w : Nat) where
  | enter (callee : FunctionId) (arguments : List (Word w))
  | run (activation : Activation w)
  deriving DecidableEq, Repr

structure Config (w : Nat) where
  control : Control w
  callers : List (Caller w)
  mem : DataMemory w

def Config.initial (p : Program) (arguments : List (Word w)) (mem : DataMemory w) : Config w :=
  ⟨.enter p.entry arguments, [], mem⟩

/-- All simultaneously active frames, including callers suspended during entry. -/
def Config.stackWords (c : Config w) : Nat :=
  (match c.control with | .enter _ _ => 0 | .run a => 2 + a.locals.length) +
    (c.callers.map (fun a => 2 + a.activation.locals.length)).sum

inductive Outcome (w : Nat) where
  | returned (value : Word w)
  | stackExhausted
  | fault (reason : RuntimeError)
  deriving DecidableEq, Repr

inductive Transition (w : Nat) where
  | next (config : Config w) (access : Option (Access w))
  | stop (outcome : Outcome w)

/-- Capacity is checked before allocating an activation. This step makes no
application-memory writes and requires no zeroed stack. -/
def enter (p : Program) (capacity : Option Nat) (c : Config w)
    (id : FunctionId) (arguments : List (Word w)) : Transition w :=
  match p.functions[id]? with
  | none => .stop (.fault (.undefinedFunction id))
  | some f =>
    if arguments.length != f.parameters.length then .stop (.fault .wrongArity)
    else if capacity.all (fun limit => c.stackWords + f.frameSize ≤ limit) then
      .next { c with control := .run ⟨id,
        arguments.map some ++ List.replicate f.locals.length none, [f.body]⟩ } none
    else .stop .stackExhausted

/-- One independent small source step, with an explicit structured continuation
and suspended activations. This function never recursively interprets a call. -/
def step (p : Program) (rho : RandomMemory w) (capacity : Option Nat)
    (c : Config w) : Transition w :=
  match c.control with
  | .enter id args => enter p capacity c id args
  | .run a =>
    match a.todo with
    | [] => .stop (.fault .missingReturn)
    | head :: rest =>
      let resume := fun todo => { c with control := .run { a with todo := todo } }
      match head with
      | .skip => .next (resume rest) none
      | .seq first second => .next (resume (first :: second :: rest)) none
      | .primitive op =>
        match op.eval rho a.locals c.mem with
        | .error e => .stop (.fault e)
        | .ok (locals, mem, event) =>
          .next { c with control := .run { a with locals := locals, todo := rest }, mem := mem } event
      | .ite condition yes no =>
        match condition.eval a.locals with
        | .error e => .stop (.fault e)
        | .ok b => .next (resume ((if b then yes else no) :: rest)) none
      | .while condition body =>
        match condition.eval a.locals with
        | .error e => .stop (.fault e)
        | .ok b => .next (resume (if b then body :: head :: rest else rest)) none
      | .call dst id args =>
        if dst < a.locals.length then
          match args.mapM (Atom.eval a.locals) with
          | .error e => .stop (.fault e)
          | .ok values => .next { c with
              control := .enter id values
              callers := ⟨{ a with todo := rest }, dst⟩ :: c.callers } none
        else .stop (.fault (.invalidDestination dst))
      | .ret value =>
        match value.eval a.locals with
        | .error e => .stop (.fault e)
        | .ok v =>
          match c.callers with
          | [] => .stop (.returned v)
          | caller :: tail =>
            match writeLocal caller.activation.locals caller.destination v with
            | .error e => .stop (.fault e)
            | .ok locals => .next { c with
                control := .run { caller.activation with locals := locals }, callers := tail } none

/-- Relational semantics is derived from the executable source transition. -/
def Step (p : Program) (rho : RandomMemory w) (capacity : Option Nat)
    (s t : Config w) (event : Option (Access w)) : Prop :=
  step p rho capacity s = .next t event

theorem step_deterministic (h : Step p rho cap s t a) (g : Step p rho cap s u b) :
    t = u ∧ a = b := Transition.next.inj (h.symm.trans g)

/-- The only extra hypothesis needed for one ideal step to fit a finite stack. -/
def FitsNext (p : Program) (capacity : Nat) (c : Config w) : Prop :=
  ∀ id args, c.control = .enter id args → ∀ f, p.functions[id]? = some f →
    c.stackWords + f.frameSize ≤ capacity

/-- Capacity never changes arithmetic, memory effects, or control decisions when
the next allocation fits. This also covers nonterminating executions prefixwise. -/
theorem step_ideal_of_fits (h : FitsNext p capacity c) :
    step p rho (some capacity) c = step p rho none c := by
  cases hc : c.control with
  | enter id args =>
    simp only [step, hc, enter]
    cases hf : p.functions[id]? with
    | none => rfl
    | some f => simp [h id args hc f hf]
  | run a => simp [step, hc]

end RamLang
