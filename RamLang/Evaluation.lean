import RamLang.Execution
import RamLang.Primitive

/-! Finite structured derivations for compositional proofs. These are ghost
witnesses, not an interpreter or compiler input. The small-step semantics remains
the operational definition; its connection to these derivations is separate. -/
namespace RamLang
open WordRam

inductive Flow (w : Nat) where
  | next (locals : Locals w)
  | returned (value : Word w)
  | exhausted
  deriving DecidableEq, Repr

def Flow.stops : Flow w → Prop
  | .next _ => False
  | _ => True

def Flow.continues : Flow w → Bool
  | .next _ => true
  | _ => false

/-- A finite capacity-aware derivation. free is additional stack capacity after
the current frame has been allocated. Derivations inhabit Type so resource
functions can inspect their finite structure; they are never supplied to compile. -/
inductive Evaluation (p : Program) (rho : RandomMemory w) :
    Nat → Stmt → Locals w → DataMemory w → Flow w → DataMemory w → List (Access w) → Type where
  | skip : Evaluation p rho free .skip locals mem (.next locals) mem []
  | primitive (h : op.eval rho locals mem = .ok (locals', mem', event)) :
      Evaluation p rho free (.primitive op) locals mem (.next locals') mem' event.toList
  | sequence (first : Evaluation p rho free a locals mem (.next middle) mem₁ trace₁)
      (second : Evaluation p rho free b middle mem₁ flow mem₂ trace₂) :
      Evaluation p rho free (.seq a b) locals mem flow mem₂ (trace₁++trace₂)
  | sequenceStop (first : Evaluation p rho free a locals mem flow mem' trace) (stop : flow.stops) :
      Evaluation p rho free (.seq a b) locals mem flow mem' trace
  | ifTrue (test : condition.eval locals = .ok true)
      (branch : Evaluation p rho free yes locals mem flow mem' trace) :
      Evaluation p rho free (.ite condition yes no) locals mem flow mem' trace
  | ifFalse (test : condition.eval locals = .ok false)
      (branch : Evaluation p rho free no locals mem flow mem' trace) :
      Evaluation p rho free (.ite condition yes no) locals mem flow mem' trace
  | whileFalse (test : condition.eval locals = .ok false) :
      Evaluation p rho free (.while condition body) locals mem (.next locals) mem []
  | whileContinue (test : condition.eval locals = .ok true)
      (iteration : Evaluation p rho free body locals mem (.next middle) mem₁ trace₁)
      (tail : Evaluation p rho free (.while condition body) middle mem₁ flow mem₂ trace₂) :
      Evaluation p rho free (.while condition body) locals mem flow mem₂ (trace₁++trace₂)
  | whileStop (test : condition.eval locals = .ok true)
      (iteration : Evaluation p rho free body locals mem flow mem' trace) (stop : flow.stops) :
      Evaluation p rho free (.while condition body) locals mem flow mem' trace
  | call (lookup : p.functions[callee]? = some f)
      (arguments : args.mapM (Atom.eval locals) = .ok values)
      (arity : values.length = f.parameters.length) (space : f.frameSize ≤ free)
      (body : Evaluation p rho (free-f.frameSize) f.body
        (values.map some ++ List.replicate f.locals.length none) mem (.returned v) mem' trace)
      (assign : writeLocal locals dst v = .ok locals') :
      Evaluation p rho free (.call dst callee args) locals mem (.next locals') mem' trace
  | callExhausts (lookup : p.functions[callee]? = some f)
      (arguments : args.mapM (Atom.eval locals) = .ok values)
      (arity : values.length = f.parameters.length) (destination : dst < locals.length)
      (space : free < f.frameSize) :
      Evaluation p rho free (.call dst callee args) locals mem .exhausted mem []
  | callBodyExhausts (lookup : p.functions[callee]? = some f)
      (arguments : args.mapM (Atom.eval locals) = .ok values)
      (arity : values.length = f.parameters.length) (destination : dst < locals.length)
      (space : f.frameSize ≤ free)
      (body : Evaluation p rho (free-f.frameSize) f.body
        (values.map some ++ List.replicate f.locals.length none) mem .exhausted mem' trace) :
      Evaluation p rho free (.call dst callee args) locals mem .exhausted mem' trace
  | ret (value : atom.eval locals = .ok v) :
      Evaluation p rho free (.ret atom) locals mem (.returned v) mem []

variable {w free : Nat} {p : Program} {rho : RandomMemory w} {stmt : Stmt}
  {locals : Locals w} {mem mem' : DataMemory w} {flow : Flow w} {trace : List (Access w)}

/-- Continuing structured execution preserves the invocation's fixed slot count. -/
theorem Evaluation.preserves_length
    (d : Evaluation p rho free stmt locals mem flow mem' trace) :
    match flow with | .next out => out.length = locals.length | _ => True := by
  induction d with
  | skip => rfl
  | primitive h => exact Primitive.length h
  | sequence first second ia ib =>
    cases ‹Flow _› with
    | next out => exact ib.trans ia
    | returned _ => trivial
    | exhausted => trivial
  | sequenceStop first stop ih =>
    cases ‹Flow _› <;> simp_all [Flow.stops]
  | ifTrue _ branch ih => cases ‹Flow _› <;> exact ih
  | ifFalse _ branch ih => cases ‹Flow _› <;> exact ih
  | whileFalse => rfl
  | whileContinue _ body tail ia ib =>
    cases ‹Flow _› with
    | next out => exact ib.trans ia
    | returned _ => trivial
    | exhausted => trivial
  | whileStop _ body stop ih => cases ‹Flow _› <;> simp_all [Flow.stops]
  | call _ _ _ _ body assign ih => exact writeLocal_preserves_length assign
  | callExhausts => trivial
  | callBodyExhausts => trivial
  | ret => trivial

end RamLang
