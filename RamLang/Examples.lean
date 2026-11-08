import RamLang.Execution
import RamLang.WellFormed

set_option maxRecDepth 10000

namespace RamLang.Examples
open WordRam

/-- Non-tail recursion: saved survives both an argument update and a recursive call. -/
def sumFunction : Function := ⟨"sum", ["n"], ["saved", "result"],
  .ite ⟨.eq, .local 0, .literal 0⟩ (.ret (.literal 0))
    (.seq (.primitive (.move 1 (.local 0)))
      (.seq (.primitive (.binary 0 .sub (.local 0) (.literal 1)))
        (.seq (.call 2 0 [.local 0])
          (.seq (.primitive (.binary 2 .add (.local 2) (.local 1))) (.ret (.local 2))))))⟩

def sum : Program := ⟨#[sumFunction], 0⟩

theorem sum_checked : check sum = .ok () := by rfl

/-- A concrete observation of the independent semantics, with no compiler involved. -/
def execute (p : Program) (capacity : Option Nat) (fuel : Nat) (args : List (Word 8)) : RunResult 8 :=
  run p (zeroMemory 8) capacity fuel (.initial p args (zeroMemory 8))

theorem sum_returns :
    (execute sum none 100 [word 8 4]).reason = .runtime (.returned (word 8 10)) ∧
    (execute sum none 100 [word 8 4]).peak = 25 ∧
    (execute sum none 100 [word 8 4]).trace = [] := by decide

theorem sum_exact_fit :
    (execute sum (some 25) 100 [word 8 4]).reason = .runtime (.returned (word 8 10)) := by decide

theorem sum_one_word_short :
    (execute sum (some 24) 100 [word 8 4]).reason = .runtime .stackExhausted ∧
    (execute sum (some 24) 100 [word 8 4]).peak = 20 := by decide

/-- Source observation fuel is not a recursion or stack budget. -/
theorem sum_observation_exhausted :
    (execute sum (some 25) 2 [word 8 4]).reason = .fuelExhausted := by decide

def parityFunction (name : String) (base : Nat) (other : FunctionId) : Function :=
  ⟨name, ["n"], ["result"],
    .ite ⟨.eq, .local 0, .literal 0⟩ (.ret (.literal base))
      (.seq (.primitive (.binary 0 .sub (.local 0) (.literal 1)))
        (.seq (.call 1 other [.local 0]) (.ret (.local 1))))⟩

/-- Both forward and backward references are legal, without expanding definitions. -/
def parity : Program := ⟨#[parityFunction "even" 1 1, parityFunction "odd" 0 0], 0⟩

theorem parity_checked : check parity = .ok () := by rfl

theorem mutual_recursion :
    (execute parity (some 28) 100 [word 8 6]).reason = .runtime (.returned (word 8 1)) ∧
    (execute parity none 100 [word 8 5]).reason = .runtime (.returned (word 8 0)) := by decide

/-- Return inside a loop discards the loop and the remaining function statements. -/
def earlyReturn : Program := ⟨#[⟨"early", [], [],
  .seq (.while ⟨.eq, .literal 1, .literal 1⟩ (.ret (.literal 7)))
    (.seq (.primitive (.store (.literal 99) (.literal 12))) (.ret (.literal 0)))⟩], 0⟩

theorem early_return :
    check earlyReturn = .ok () ∧
    (execute earlyReturn (some 2) 20 []).reason = .runtime (.returned (word 8 7)) ∧
    (execute earlyReturn (some 2) 20 []).trace = [] := by
  refine ⟨rfl, ?_⟩
  decide

/-- A divergent loop with a constant two-word frame and no application effects. -/
def spin : Program := ⟨#[⟨"spin", [], [],
  .seq (.while ⟨.eq, .literal 1, .literal 1⟩ .skip) (.ret (.literal 0))⟩], 0⟩

def spinState (inside : Bool) (mem : DataMemory w) : Config w :=
  let loop := Stmt.while ⟨.eq, .literal 1, .literal 1⟩ .skip
  ⟨.run ⟨0, [], if inside then [.skip, loop, .ret (.literal 0)] else [loop, .ret (.literal 0)]⟩, [], mem⟩

theorem spin_prefix (rho : RandomMemory w) (mem : DataMemory w) (cap : Option Nat) (fuel : Nat) :
    ∀ inside, (run spin rho cap fuel (spinState inside mem)).reason = .fuelExhausted ∧
      (run spin rho cap fuel (spinState inside mem)).peak = 2 := by
  induction fuel with
  | zero => intro inside; cases inside <;> simp [run, spinState, Config.stackWords]
  | succ fuel ih =>
    intro inside
    have hc : Condition.eval ([] : Locals w) ⟨.eq, .literal 1, .literal 1⟩ = .ok true := by
      change Except.ok (word w 1 == word w 1) = _
      simp
    have hfalse := ih false
    have htrue := ih true
    simp only [spinState, Bool.false_eq_true, ↓reduceIte] at hfalse htrue
    cases inside <;>
      simp [run, step, spinState, Config.stackWords, hc, RunResult.prepend, hfalse, htrue]

/-- Divergence is possible with bounded capacity; it is not runtime failure. -/
theorem spin_diverges (rho : RandomMemory w) (mem : DataMemory w) :
    Diverges spin rho (some 2) (spinState false mem) :=
  fun fuel => (spin_prefix rho mem (some 2) fuel false).1

theorem rejects_uninitialized :
    check ⟨#[⟨"bad", [], ["x"], .ret (.local 0)⟩], 0⟩ =
      .error (.uninitialized 0) := by rfl

theorem rejects_missing_return :
    check ⟨#[⟨"bad", [], [], .skip⟩], 0⟩ = .error (.missingReturn "bad") := by rfl

theorem rejects_duplicate_functions :
    check ⟨#[sumFunction, sumFunction], 0⟩ = .error (.duplicateFunction "sum") := by rfl

theorem rejects_duplicate_locals :
    check ⟨#[⟨"bad", ["x"], ["x"], .ret (.local 0)⟩], 0⟩ =
      .error (.duplicateLocal "bad" "x") := by rfl

theorem rejects_undefined_function :
    check ⟨#[⟨"bad", [], ["x"], .seq (.call 0 9 []) (.ret (.local 0))⟩], 0⟩ =
      .error (.undefinedFunction 9) := by rfl

theorem rejects_wrong_arity :
    check ⟨#[⟨"bad", [], ["x"], .seq (.call 0 0 [.literal 1]) (.ret (.local 0))⟩], 0⟩ =
      .error (.wrongArity 0 0 1) := by rfl

end RamLang.Examples
