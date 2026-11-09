import RamLang.RegisterOnly.Correctness
import RamLang.DSL.Automation

set_option maxRecDepth 10000

namespace RamLang.RegisterOnly.Examples
open WordRam

/-- Swap arguments, overwrite an argument with its call result, repeat an
argument, and retain a caller local across both inline calls. -/
def program : Program := ram_program main {
  fn main(x, y) {
    let saved = x;
    x = combine(y, x);
    let again = combine(x, x);
    return again + saved;
  }
  fn combine(a, b) { return a * 10 + b; }
}

/-- Ordinary word arithmetic, including wrapping, is the helper specification. -/
def combine (a b : Word w) : Word w := a * word w 10 + b

/-- The source entry and helper used by the compositional proof. -/
def entry : Function := program.functions[0]'(by decide)

def helper : Function := program.functions[1]'(by decide)

/-- A helper proof uses only independent source primitive and return rules. -/
def helper_evaluation {w free : Nat} {source : Program} (rho : RandomMemory w)
    (a b : Word w) (mem : DataMemory w) :
    Evaluation source rho free helper.body [some a,some b,none,none] mem (.returned (combine a b)) mem [] :=
  .sequence (.primitive (event := none) rfl)
    (.sequence (.primitive (event := none) rfl) (.ret rfl))

/-- The source proof keeps saved alive, evaluates swapped/repeated arguments
before calls, and reuses sufficient logical call capacity for sequential calls. -/
def entry_evaluation {w free : Nat} (rho : RandomMemory w) (x y : Word w)
    (mem : DataMemory w) (space : 6 ≤ free) :
    Evaluation program rho free entry.body [some x,some y,none,none,none] mem
      (.returned (combine (combine y x) (combine y x)+x)) mem [] := by
  let first : Evaluation program rho free (.call 0 1 [.local 1,.local 0])
      [some x,some y,some x,none,none] mem
      (.next [some (combine y x),some y,some x,none,none]) mem [] :=
    .call (f := helper) rfl rfl rfl space (helper_evaluation rho y x mem) rfl
  let second : Evaluation program rho free (.call 3 1 [.local 0,.local 0])
      [some (combine y x),some y,some x,none,none] mem
      (.next [some (combine y x),some y,some x,some (combine (combine y x) (combine y x)),none]) mem [] :=
    .call (f := helper) rfl rfl rfl space (helper_evaluation rho (combine y x) (combine y x) mem) rfl
  exact .sequence (.primitive (event := none) rfl)
    (.sequence first (.sequence second (.sequence (.primitive (event := none) rfl) (.ret rfl))))

/-- Nine local registers plus the two public result/status registers suffice. -/
def compiled : Compiled 9 :=
  match compile 9 program with
  | .ok c => c
  | .error _ => ⟨⟨"invalid",[],[],.ret (.literal 0)⟩,.ret (.literal 0)⟩

theorem compiles : compile 9 program = .ok compiled := by rfl

/-- The finite instruction count includes both helper expansions and final halt. -/
theorem code_size : compiled.code.size = 15 := by rfl

/-- All registers except the two source parameters start dirty; no stack region
or stack pointer is initialized because this backend uses only registers. -/
def initial (x y : Word w) (mem : DataMemory w) : State w 11 :=
  .initial (fun r => if r.val = 2 then x else if r.val = 3 then y else word w 213) mem

/-- The source proof transfers to every width, image, and initial memory. It
establishes the aliased-call result in fifteen instructions and forbids every
ordinary-memory write at every interrupted machine prefix. -/
theorem verified (rho : RandomMemory w) (x y : Word w) (mem : DataMemory w) :
    ∃ t, WordRam.TerminatesIn compiled.code rho (initial x y mem) 15 t [] ∧
      t.regs (result 9) = combine (combine y x) (combine y x)+x ∧ t.mem = mem ∧
      ∀ fuel a v, .dataWrite a v ∉ (WordRam.run compiled.code rho fuel (initial x y mem)).trace := by
  have d := entry_evaluation (free := 6) rho x y mem (Nat.le_refl _)
  exact compiled_readOnly (s := initial x y mem) compiles rfl d (by intro a v h; cases h)

/-- Repeated and permuted arguments, result overlap, and live caller values are
also checked by executing the emitted code from dirty registers and RAM. -/
theorem overlap_execution :
    let r := WordRam.run compiled.code (zeroMemory 8) 20 (initial (word 8 3) (word 8 7) (fun _ => word 8 213))
    r.reason = .halted ∧ r.steps = 15 ∧ r.state.regs (result 9) = word 8 38 ∧ r.trace = [] := by decide

/-- Register demand is checked explicitly instead of silently wrapping indices. -/
theorem rejects_register_shortage : compile 8 program = .error (.registerDemand 9 8) := by rfl

/-- Ordinary source loads remain visible in the full unprojected target trace. -/
def reading : Program := ram_program main {
  fn main(p) {
    let value = load(p);
    return add_one(value);
  }
  fn add_one(value) { return value + 1; }
}

/-- A single application load is the only memory event emitted by this call. -/
theorem reading_execution :
    ((compile 5 reading).toOption.map (fun c =>
      let r := WordRam.run c.code (zeroMemory 8) 50
        (.initial (fun _ => word 8 40) (fun _ => word 8 7))
      (r.reason,(r.state.regs (result 5)).toNat,r.trace))) =
      some (.halted,8,[.dataRead (word 8 40) (word 8 7)]) := by decide

/-- Recursive source remains valid, but cannot be mistaken for an eligible
finite helper expansion in the register-only backend. -/
def recursive : Program := ram_program main { fn main(x) { return main(x); } }

theorem rejects_recursion : compile 8 recursive = .error (.unsupportedCallee 0) := by rfl

/-- Structured entry control stays supported by the baseline recursive compiler;
this first register-only subset rejects it with an explicit eligibility error. -/
def branching : Program := ram_program main { fn main(x) { if (x == 0) { return 0; } else { return 1; } } }

theorem rejects_control : compile 8 branching = .error .unsupportedEntry := by rfl

end RamLang.RegisterOnly.Examples
