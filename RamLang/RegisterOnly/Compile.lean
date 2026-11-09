import RamLang.RegisterOnly.Placement

namespace RamLang.RegisterOnly
open WordRam

/-- Explicit eligibility errors keep the register-only optimization separate
from the baseline compiler's unrestricted structured and recursive language. -/
inductive Error where
  | source (error : CheckError)
  | missingEntry
  | unsupportedEntry
  | undefinedCallee (id : FunctionId)
  | unsupportedCallee (id : FunctionId)
  | registerDemand (required available : Nat)
  deriving DecidableEq, Repr

/-- Eligible helpers are straight-line primitives followed by a word return.
In particular, helper recursion and nested helper calls are rejected. -/
inductive Leaf where
  | ret (value : Atom)
  | step (operation : Primitive) (next : Leaf)
  deriving DecidableEq, Repr

/-- The ordinary source core represented by an eligible helper. -/
def Leaf.toStmt : Leaf → Stmt
  | .ret a => .ret a
  | .step op next => .seq (.primitive op) next.toStmt

/-- Recognize the straight-line helper subset without executing any source code. -/
def parseLeaf : Stmt → Option Leaf
  | .ret a => some (.ret a)
  | .seq (.primitive op) next => (parseLeaf next).map (.step op)
  | _ => none

/-- A checked entry may interleave primitives and calls to eligible helpers.
Helper metadata is retained for register placement and the linking theorem. -/
inductive Plan where
  | ret (value : Atom)
  | step (operation : Primitive) (next : Plan)
  | call (dst : Local) (callee : FunctionId) (args : List Atom) (function : Function)
      (body : Leaf) (next : Plan)
  deriving DecidableEq, Repr

/-- Recover the source entry syntax, retaining ordinary source call statements. -/
def Plan.toStmt : Plan → Stmt
  | .ret a => .ret a
  | .step op next => .seq (.primitive op) next.toStmt
  | .call dst callee args _ _ next => .seq (.call dst callee args) next.toStmt

/-- Caller registers remain live while one reusable, disjoint helper interval
holds copied parameters and helper locals. Sequential calls reuse that interval. -/
def Plan.extra : Plan → Nat
  | .ret _ => 0
  | .step _ next => next.extra
  | .call _ _ _ f _ next => max f.slots next.extra

/-- Resolve each eligible call once for its inline expansion. Recursive or
structured callees fail recognition; no recursion depth or unrolling fuel exists. -/
def parsePlan (p : Program) : Stmt → Except Error Plan
  | .ret a => .ok (.ret a)
  | .seq (.primitive op) next => (parsePlan p next).map (.step op)
  | .seq (.call dst callee args) next => do
    let f ← requireSome (.undefinedCallee callee) p.functions[callee]?
    let leaf ← requireSome (.unsupportedCallee callee) (parseLeaf f.body)
    let rest ← parsePlan p next
    return .call dst callee args f leaf rest
  | _ => .error .unsupportedEntry

/-- One source primitive becomes exactly one target instruction; all operands
refer directly to placed registers or literal words. -/
def primitive (capacity base : Nat) : Primitive → Instr (capacity+2)
  | .move d a => .mov (slot capacity base d) (atom capacity base a)
  | .binary d op a b =>
    let dst := slot capacity base d
    let x := atom capacity base a
    let y := atom capacity base b
    match op with
    | .add => .add dst x y
    | .sub => .sub dst x y
    | .mul => .mul dst x y
    | .mod => .mod dst x y
    | .shr => .shr dst x y
  | .load d a => .load (slot capacity base d) (atom capacity base a)
  | .store a b => .store (atom capacity base a) (atom capacity base b)
  | .random d a => .rload (slot capacity base d) (atom capacity base a)

/-- Inline a helper using its disjoint register interval and copy the returned
word directly into the caller destination, without a link or stack access. -/
def Leaf.code (capacity base : Nat) (destination : Reg (capacity+2)) : Leaf → List (Instr (capacity+2))
  | .ret a => [.mov destination (atom capacity base a)]
  | .step op next => primitive capacity base op :: next.code capacity base destination

/-- Copy all arguments before running a helper. Distinct caller/helper intervals
preserve repeated arguments, argument permutations, and an aliased result slot. -/
def argumentsFrom (capacity caller helper start : Nat) : List Atom → List (Instr (capacity+2))
  | [] => []
  | a::rest => .mov (slot capacity helper start) (atom capacity caller a) ::
      argumentsFrom capacity caller helper (start+1) rest

/-- Argument copying starts at the first parameter slot of the helper interval. -/
def arguments (capacity caller helper : Nat) (args : List Atom) : List (Instr (capacity+2)) :=
  argumentsFrom capacity caller helper 0 args

/-- Deterministic straight-line emission, with a finite expansion for each
eligible helper call and no compiler-generated memory instruction. -/
def Plan.code (capacity callerSlots : Nat) : Plan → List (Instr (capacity+2))
  | .ret a => [.mov (result capacity) (atom capacity 0 a)]
  | .step op next => primitive capacity 0 op :: next.code capacity callerSlots
  | .call dst _ args _ leaf next => arguments capacity 0 callerSlots args ++
      leaf.code capacity callerSlots (slot capacity 0 dst) ++ next.code capacity callerSlots

/-- Runtime success needs only a status-register move and halt. -/
def finish (capacity : Nat) : List (Instr (capacity+2)) := [.mov (status capacity) (.imm 1),.halt]

/-- Checked register-only compilation retains source/layout metadata alongside
its finite plan; code is a deterministic projection of that metadata. -/
structure Compiled (capacity : Nat) where
  entry : Function
  plan : Plan
  deriving DecidableEq, Repr

/-- Actual emitted instruction array, including the final success and halt. -/
def Compiled.code (c : Compiled capacity) : WordRam.Program (capacity+2) :=
  (c.plan.code capacity c.entry.slots ++ finish capacity).toArray

/-- Required local registers, excluding the two reserved public result/status registers. -/
def Compiled.demand (c : Compiled capacity) : Nat := c.entry.slots+c.plan.extra

/-- Inspect exact emitted work, checked local-register demand, and the absence
of compiler stack allocation for this straight-line backend. -/
def Compiled.report (c : Compiled capacity) : String :=
  s!"{c.code.size} instructions; {c.demand}/{capacity} local registers; entry={c.entry.slots}; helper={c.plan.extra}; stack=0"

/-- Check the original source, the eligible subset, and the finite register
budget before returning an executable register-only plan. -/
def compile (capacity : Nat) (p : Program) : Except Error (Compiled capacity) := do
  match check p with
  | .error error => throw (.source error)
  | .ok () => pure ()
  let f ← requireSome .missingEntry p.functions[p.entry]?
  let plan ← parsePlan p f.body
  let c : Compiled capacity := ⟨f,plan⟩
  if c.demand ≤ capacity then return c
  else throw (.registerDemand c.demand capacity)

/-- Linking records precisely the callee definitions accepted by the source checker. -/
def Plan.Linked (p : Program) : Plan → Prop
  | .ret _ => True
  | .step _ next => next.Linked p
  | .call _ callee _ f leaf next => p.functions[callee]? = some f ∧ leaf.toStmt = f.body ∧ next.Linked p

/-- Successful helper recognition preserves the source syntax exactly. -/
theorem parseLeaf_sound {stmt : Stmt} {leaf : Leaf} (h : parseLeaf stmt = some leaf) : leaf.toStmt = stmt := by
  induction stmt generalizing leaf with
  | ret a => simp [parseLeaf] at h; subst leaf; rfl
  | seq first next iha ih =>
    clear iha
    cases first <;> simp only [parseLeaf] at h
    all_goals try cases h
    rename_i op
    cases hp : parseLeaf next with
    | none => simp [hp,Except.map] at h
    | some tail =>
      simp [hp,Except.map] at h
      subst leaf
      simp [Leaf.toStmt,ih hp]
  | _ => cases h

/-- Successful entry recognition preserves source syntax and links every inline
helper to its actual source function, not an assumed replacement implementation. -/
theorem parsePlan_sound {p : Program} {stmt : Stmt} {plan : Plan} (h : parsePlan p stmt = .ok plan) :
    plan.toStmt = stmt ∧ plan.Linked p := by
  induction stmt generalizing plan with
  | ret a => simp [parsePlan] at h; subst plan; exact ⟨rfl,trivial⟩
  | seq first next iha ih =>
    clear iha
    cases first <;> simp only [parsePlan] at h
    all_goals try cases h
    · rename_i op
      cases hp : parsePlan p next with
      | error e => simp [hp,Except.map] at h
      | ok tail =>
        simp [hp,Except.map] at h
        subst plan
        obtain ⟨he,hl⟩ := ih hp
        exact ⟨by simp [Plan.toStmt,he],hl⟩
    · rename_i dst callee args
      cases hf : p.functions[callee]? with
      | none => simp [hf,requireSome,bind,Except.bind] at h
      | some f =>
        cases hb : parseLeaf f.body with
        | none => simp [hf,hb,requireSome,bind,Except.bind] at h
        | some leaf =>
          cases ht : parsePlan p next with
          | error e => simp [hf,hb,ht,requireSome,bind,Except.bind] at h
          | ok tail =>
            simp [hf,hb,ht,requireSome,bind,pure,Except.bind,Except.pure] at h
            subst plan
            obtain ⟨he,hl⟩ := ih ht
            exact ⟨by simp [Plan.toStmt,he],hf,parseLeaf_sound hb,hl⟩
  | _ => cases h

/-- Compilation discharges source checking, entry lookup, source equivalence,
helper linking, and the register-placement bound. -/
theorem compile_sound {capacity : Nat} {p : Program} {c : Compiled capacity}
    (h : compile capacity p = .ok c) :
    WellFormed p ∧ p.functions[p.entry]? = some c.entry ∧ c.plan.toStmt = c.entry.body ∧
      c.plan.Linked p ∧ c.demand ≤ capacity := by
  cases hc : check p with
  | error error => simp [compile,hc,bind,Except.bind] at h
  | ok unit =>
    cases unit
    cases hf : p.functions[p.entry]? with
    | none => simp [compile,hc,hf,requireSome,bind,pure,Except.bind,Except.pure] at h
    | some f =>
      cases hp : parsePlan p f.body with
      | error error => simp [compile,hc,hf,hp,requireSome,bind,pure,Except.bind,Except.pure] at h
      | ok plan =>
        simp only [compile,hc,hf,hp,requireSome,bind,pure,Except.bind,Except.pure] at h
        split at h
        · rename_i hb
          cases h
          exact ⟨hc,rfl,(parsePlan_sound hp).1,(parsePlan_sound hp).2,hb⟩
        · cases h

end RamLang.RegisterOnly
