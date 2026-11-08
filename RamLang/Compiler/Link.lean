import RamLang.Compiler.Lower

namespace RamLang.Compiler
open WordRam ABI

structure FunctionLayout where
  entry : Nat
  extent : Nat
  frameWords : Nat
  deriving DecidableEq, Repr

/-- One range for each ordinary body, in declaration order. -/
def layouts (pc : Nat) : List Function → List FunctionLayout
  | [] => []
  | f :: rest =>
    let extent := prologue.length + size f.body
    ⟨pc, extent, f.frameSize⟩ :: layouts (pc + extent) rest

/-- Four explicit register values keep executable definitions free of proof axioms. -/
def entryArgument (i : Nat) : Reg registers :=
  (#[⟨12, by decide⟩, ⟨13, by decide⟩, ⟨14, by decide⟩, ⟨15, by decide⟩] : Array (Reg registers))[i]?.getD
    ⟨12, by decide⟩

def entryArguments (arity : Nat) : Code :=
  (List.range arity).flatMap (fun i =>
    [.add address (.reg sp) (.imm (2+i)), .store (.reg address) (.reg (entryArgument i))])

def wrapperSize (arity : Nat) : Nat := 12 + 2*arity

def exhaustionPC (arity : Nat) : Nat := 10 + 2*arity

/-- Entry setup, successful return, and a distinct non-unwinding runtime failure. -/
def wrapper (frame target arity : Nat) : Code :=
  [.mov status (.imm 0), .mov fp (.imm 0),
    .sub left (.reg limit) (.reg sp),
    .branch .lt (.reg left) (.imm frame) (exhaustionPC arity),
    .store (.reg sp) (.reg fp)] ++ entryArguments arity ++
  [.mov fp (.reg sp), .add sp (.reg sp) (.imm frame), .call link target,
    .mov status (.imm 1), .halt, .mov status (.imm 2), .halt]

/-- Emit each finite body once, using the same offsets as the layout pass. -/
def bodies (frames entries : FunctionId → Nat) (exhausted pc : Nat) : List Function → Code
  | [] => []
  | f :: rest => prologue ++ lower frames entries exhausted (pc + prologue.length) f.body ++
      bodies frames entries exhausted (pc + prologue.length + size f.body) rest

theorem layouts_length (pc : Nat) (fs : List Function) : (layouts pc fs).length = fs.length := by
  induction fs generalizing pc with
  | nil => rfl
  | cons f rest ih => simp [layouts, ih]

theorem bodies_length (frames entries : FunctionId → Nat) (exhausted pc : Nat) (fs : List Function) :
    (bodies frames entries exhausted pc fs).length =
      (fs.map (fun f => prologue.length + size f.body)).sum := by
  induction fs generalizing pc with
  | nil => rfl
  | cons f rest ih => simp [bodies, lower_length, ih, Nat.add_assoc]

theorem wrapper_length (frame target arity : Nat) :
    (wrapper frame target arity).length = wrapperSize arity := by
  have h : ∀ xs : List Nat, (xs.map (fun _ => 2)).sum = 2 * xs.length := by
    intro xs
    induction xs with
    | nil => rfl
    | cons x xs ih => simp [ih, Nat.mul_add, Nat.add_comm]
  simp [wrapper, wrapperSize, entryArguments, List.length_flatMap, h]
  omega

structure CompiledProgram where
  code : WordRam.Program registers
  functions : List FunctionLayout
  exhaustion : Nat
  deriving DecidableEq, Repr

inductive CompileError where
  | source (error : CheckError)
  deriving DecidableEq, Repr

/-- Two passes over the finite function table: assign ranges, then emit bodies.
Recursive references are integer lookups and never cause compiler recursion. -/
def compile (p : Program) : Except CompileError CompiledProgram :=
  match check p with
  | .error e => .error (.source e)
  | .ok () =>
    let fs := p.functions.toList
    let arity := ((p.functions[p.entry]?).map (fun f => f.parameters.length)).getD 0
    let table := layouts (wrapperSize arity) fs
    let entries := fun id => (table[id]?.map FunctionLayout.entry).getD 0
    let frames := fun id => (p.functions[id]?.map Function.frameSize).getD 0
    .ok ⟨(wrapper (frames p.entry) (entries p.entry) arity ++
      bodies frames entries (exhaustionPC arity) (wrapperSize arity) fs).toArray,
      table, exhaustionPC arity⟩

/-- Successful compilation always has an accepted source program. -/
theorem compile_checked (h : compile p = .ok c) : WellFormed p := by
  cases hc : check p with
  | error e => simp [compile, hc] at h
  | ok value => cases value; exact hc

/-- Recursion does not duplicate function bodies or metadata. -/
theorem compile_function_count (h : compile p = .ok c) : c.functions.length = p.functions.size := by
  have hc := compile_checked h
  unfold WellFormed at hc
  simp only [compile, hc, Except.ok.injEq] at h
  subst c
  simp [layouts_length]

/-- The generated size is a wrapper plus one finite template per function body. -/
theorem compile_code_size (h : compile p = .ok c) :
    c.code.size = wrapperSize (((p.functions[p.entry]?).map (fun f => f.parameters.length)).getD 0) +
      (p.functions.toList.map (fun f => prologue.length + size f.body)).sum := by
  have hc := compile_checked h
  unfold WellFormed at hc
  simp only [compile, hc, Except.ok.injEq] at h
  subst c
  simp [wrapper_length, bodies_length]

/-- Width-dependent execution premises; compilation itself does not depend on w. -/
def CompiledProgram.Fits (c : CompiledProgram) (w : Nat) : Prop :=
  c.code.size < modulus w ∧ ∀ layout ∈ c.functions, layout.frameWords < modulus w

/-- A stable, inspectable report of code and frame resources. -/
def CompiledProgram.report (c : CompiledProgram) : String :=
  "instructions: " ++ toString c.code.size ++ ", registers: 16\n" ++
    String.intercalate "\n" (c.functions.map (fun f =>
      "entry " ++ toString f.entry ++ ": " ++ toString f.extent ++
      " instructions, " ++ toString f.frameWords ++ " frame words"))

end RamLang.Compiler
