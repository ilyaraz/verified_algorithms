import RamLang.Compiler.Proofs.WholeProgram
import RamLang.Capacity

/-! Source contracts contain only source derivations and ghost resource bounds.
Their compiler transfer is a theorem, never part of a contract's premise. -/
namespace RamLang.Logic
open WordRam Compiler

/-- A total source contract at a specified invocation state. The postcondition
can describe return values, final memory, and the complete application trace. -/
def Contract (p : Program) (rho : RandomMemory w) (free : Nat) (stmt : Stmt)
    (locals : Locals w) (mem : DataMemory w)
    (post : Flow w → DataMemory w → List (Access w) → Prop) (work peak : Nat) : Prop :=
  ∃ flow mem' trace, ∃ d : Evaluation p rho free stmt locals mem flow mem' trace,
    post flow mem' trace ∧ instructions d ≤ work ∧ extraStack d ≤ peak

variable {w free work peak : Nat} {p : Program} {rho : RandomMemory w} {stmt : Stmt}
  {locals : Locals w} {mem : DataMemory w}
  {post post' : Flow w → DataMemory w → List (Access w) → Prop}

/-- Introduce a contract from a finite source proof and its checked resource bounds. -/
theorem Contract.ofEvaluation {flow : Flow w} {mem' : DataMemory w} {trace : List (Access w)}
    (d : Evaluation p rho free stmt locals mem flow mem' trace)
    (hq : post flow mem' trace) (ht : instructions d ≤ work) (hs : extraStack d ≤ peak) :
    Contract p rho free stmt locals mem post work peak := ⟨flow,mem',trace,d,hq,ht,hs⟩

/-- Weaken the functional postcondition and increase either resource allowance. -/
theorem Contract.consequence (h : Contract p rho free stmt locals mem post work peak)
    (hq : ∀ flow mem' trace, post flow mem' trace → post' flow mem' trace)
    {work' peak' : Nat} (ht : work ≤ work') (hs : peak ≤ peak') :
    Contract p rho free stmt locals mem post' work' peak' := by
  obtain ⟨flow,mem',trace,d,hpost,hd,he⟩ := h
  exact ⟨flow,mem',trace,d,hq _ _ _ hpost,Nat.le_trans hd ht,Nat.le_trans he hs⟩

/-- Sequential time adds, stack peaks combine by maximum, and traces concatenate
in execution order. The second proof may depend on the first trace and state. -/
theorem Contract.sequence {a b : Stmt} {work₁ work₂ peak₁ peak₂ : Nat}
    {middle : Locals w → DataMemory w → List (Access w) → Prop}
    (first : Contract p rho free a locals mem
      (fun flow mem' trace => ∃ out, flow = .next out ∧ middle out mem' trace) work₁ peak₁)
    (second : ∀ out mem' prior, middle out mem' prior →
      Contract p rho free b out mem'
        (fun flow mem'' suffix => post flow mem'' (prior++suffix)) work₂ peak₂) :
    Contract p rho free (.seq a b) locals mem post (work₁+work₂) (max peak₁ peak₂) := by
  obtain ⟨flow,mem₁,trace₁,d₁,⟨out,rfl,hmid⟩,ht₁,hs₁⟩ := first
  obtain ⟨flow,mem₂,trace₂,d₂,hpost,ht₂,hs₂⟩ := second out mem₁ trace₁ hmid
  refine ⟨flow,mem₂,trace₁++trace₂,.sequence d₁ d₂,hpost,?_,?_⟩
  · simp only [instructions]; omega
  · exact Nat.max_le.mpr ⟨Nat.le_trans hs₁ (Nat.le_max_left _ _),Nat.le_trans hs₂ (Nat.le_max_right _ _)⟩

/-- Return or exhaustion discards the rest of a sequence, without charging it. -/
theorem Contract.sequenceStop {a b : Stmt}
    (first : Contract p rho free a locals mem
      (fun flow mem' trace => flow.stops ∧ post flow mem' trace) work peak) :
    Contract p rho free (.seq a b) locals mem post work peak := by
  obtain ⟨flow,mem',trace,d,⟨stop,hpost⟩,ht,hs⟩ := first
  exact ⟨flow,mem',trace,.sequenceStop d stop,hpost,ht,hs⟩

/-- A successful callee contract composes with argument evaluation and a checked
caller assignment. Only the new frame and callee peak contribute extra space. -/
theorem Contract.call {callee dst : Nat} {f : Function} {args : List Atom}
    {values : List (Word w)} {calleePost : Word w → DataMemory w → List (Access w) → Prop}
    (lookup : p.functions[callee]? = some f)
    (arguments : args.mapM (Atom.eval locals) = .ok values)
    (arity : values.length = f.parameters.length) (space : f.frameSize ≤ free)
    (body : Contract p rho (free-f.frameSize) f.body
      (values.map some ++ List.replicate f.locals.length none) mem
      (fun flow mem' trace => ∃ value, flow = .returned value ∧ calleePost value mem' trace) work peak)
    (finish : ∀ value mem' trace, calleePost value mem' trace →
      ∃ out, writeLocal locals dst value = .ok out ∧ post (.next out) mem' trace) :
    Contract p rho free (.call dst callee args) locals mem post
      ((Compiler.arguments 0 args).length+10+work) (f.frameSize+peak) := by
  obtain ⟨flow,mem',trace,d,⟨value,rfl,hpost⟩,ht,hs⟩ := body
  obtain ⟨out,ha,hq⟩ := finish value mem' trace hpost
  refine ⟨.next out,mem',trace,.call lookup arguments arity space d ha,hq,?_,?_⟩
  · simp only [instructions]; omega
  · simp only [extraStack]; omega

/-- Well-founded contract induction supports self recursion or a family of
mutually recursive functions. Every assumed contract has a strictly smaller
natural rank; no circular contract assumptions escape this rule. -/
theorem recursion {ι : Sort u} (rank : ι → Nat) (contracts : ι → Prop)
    (step : ∀ i, (∀ j, rank j < rank i → contracts j) → contracts i) :
    ∀ i, contracts i := by
  intro i
  have all : ∀ n i, rank i = n → contracts i := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro i he
      apply step i
      intro j hj
      exact ih (rank j) (by omega) j rfl
  exact all (rank i) i rfl

/-- Mutual recursion uses one rank across function identifiers and ghost input
states. Calls may change function, but every assumed contract decreases rank. -/
theorem mutual_recursion {α : Type u} (rank : FunctionId → α → Nat)
    (contracts : FunctionId → α → Prop)
    (bodies : ∀ f x, (∀ g y, rank g y < rank f x → contracts g y) → contracts f x) :
    ∀ f x, contracts f x := by
  have h := recursion (fun key : FunctionId × α => rank key.1 key.2)
    (fun key => contracts key.1 key.2)
    (fun key ih => bodies key.1 key.2 (fun g y hlt => ih (g,y) hlt))
  exact fun f x => h (f,x)

/-- A return contract implies an independent ideal source execution, rather
than merely a statement about the compiled instruction array. -/
theorem Contract.sourceReturns {f : Function} {values : List (Word w)}
    {Q : Word w → DataMemory w → List (Access w) → Prop}
    (lookup : p.functions[p.entry]? = some f) (arity : values.length = f.parameters.length)
    (h : Contract p rho free f.body (values.map some ++ List.replicate f.locals.length none) mem
      (fun flow mem' trace => ∃ value, flow = .returned value ∧ Q value mem' trace) work peak) :
    ∃ value c trace, Returns p rho none (Config.initial p values mem) value c trace ∧
      Q value c.mem trace := by
  obtain ⟨flow,mem',trace,d,⟨value,rfl,hq⟩,_,_⟩ := h
  obtain ⟨c,hr,hm⟩ := Evaluation.invocationReturns (cap := free+f.frameSize) lookup arity
    (by omega) (by simpa using d)
  exact ⟨value,c,trace,hr.forgetCapacity,by simpa [hm] using hq⟩

/-- Transfer a source return contract to the emitted program, adding wrapper
cost and entry-frame space. Clients reason about source locals and memory;
function PCs and stack-slot stores are handled by the compiler theorem. -/
theorem Contract.compiled {c : CompiledProgram} {f : Function} {stack : Region}
    {s : State w ABI.registers} {Q : Word w → DataMemory w → List (Access w) → Prop}
    (hcompile : compile p = .ok c) (hfit : c.Fits w) (lookup : p.functions[p.entry]? = some f)
    (hpc : s.pc = 0) (hsp : s.regs ABI.sp = word w stack.base)
    (hlimit : s.regs ABI.limit = word w (stack.base+stack.size)) (hstack : stack.Fits w)
    (hspace : f.frameSize ≤ stack.size)
    (h : Contract p rho (stack.size-f.frameSize) f.body
      ((entryValues s f.parameters.length).map some ++ List.replicate f.locals.length none) s.mem
      (fun flow mem' trace => ∃ value, flow = .returned value ∧ Q value mem' trace ∧ Separated stack trace)
      work peak) :
    ∃ n t trace value mem' log,
      n ≤ 12+2*f.parameters.length+work ∧ WordRam.TerminatesIn c.code rho s n t trace ∧
      t.regs ABI.status = word w 1 ∧ t.regs ABI.result = value ∧
      Q value mem' log ∧ ApplicationMemory stack mem' t.mem ∧ ABI.projectTrace stack trace = log ∧
      StackBound c.code rho s n (stack.base+f.frameSize+peak) := by
  obtain ⟨flow,mem',log,d,⟨value,rfl,hq,hsep⟩,ht,hs⟩ := h
  obtain ⟨t,trace,hr,hstatus,hresult,_,hm,hlog,hpeak⟩ :=
    compiled_returns hcompile hfit lookup hpc hsp hlimit hstack hspace d hsep
  exact ⟨_,t,trace,value,mem',log,by omega,hr,hstatus,hresult,hq,hm,hlog,hpeak.mono (by omega)⟩

end RamLang.Logic
