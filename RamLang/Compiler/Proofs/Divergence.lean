import RamLang.Compiler.Proofs.WholeProgram

namespace RamLang
open WordRam

variable {w n k : Nat} {p : Program} {rho : RandomMemory w} {cap : Option Nat}
  {s t : Config w} {log : List (Access w)}

/-- Any shorter observation of a finite source execution is itself an execution. -/
theorem Steps.take (h : Steps p rho cap n s t log) (hk : k ≤ n) :
    ∃ u trace, Steps p rho cap k s u trace := by
  induction h generalizing k with
  | refl =>
    have : k = 0 := by omega
    subst k
    exact ⟨_,[],.refl _⟩
  | @cons s t event n u log hs ht ih =>
    cases k with
    | zero => exact ⟨s,[],.refl _⟩
    | succ k =>
      obtain ⟨v,trace,hv⟩ := ih (k := k) (by omega)
      exact ⟨v,event.toList++trace,.cons hs hv⟩

/-- Productive finite chunks certify genuine divergence of the source observer. -/
theorem diverges_of_chunks (I : Config w → Prop)
    (progress : ∀ s, I s → ∃ n t log, 0 < n ∧ Steps p rho cap n s t log ∧ I t)
    (initial : I s) : Diverges p rho cap s := by
  have prefixes : ∀ fuel s, I s → ∃ t log, Steps p rho cap fuel s t log := by
    intro fuel
    induction fuel using Nat.strongRecOn with
    | ind fuel ih =>
      intro s hs
      obtain ⟨n,t,log,hn,hsteps,hit⟩ := progress s hs
      by_cases hf : fuel ≤ n
      · exact hsteps.take hf
      · obtain ⟨u,tail,ht⟩ := ih (fuel-n) (by omega) t hit
        exact ⟨u,log++tail,by simpa only [Nat.add_sub_of_le (by omega : n ≤ fuel)] using hsteps.trans ht⟩
  intro fuel
  obtain ⟨t,log,hs⟩ := prefixes fuel s initial
  exact hs.run_prefix.2.2

end RamLang

namespace RamLang.Compiler
open WordRam ABI

variable {w : Nat} {code : WordRam.Program registers} {rho : RandomMemory w}
  {s : State w registers}

/-- A positive instruction count per preserved invariant excludes infinite
stuttering in the target simulation. -/
theorem target_diverges_of_chunks (I : State w registers → Prop)
    (progress : ∀ s, I s → ∃ n t log, 0 < n ∧ WordRam.Steps code rho n s t log ∧ I t)
    (initial : I s) : WordRam.Diverges code rho s := by
  intro fuel
  induction fuel using Nat.strongRecOn generalizing s with
  | ind fuel ih =>
    obtain ⟨n,t,log,hn,hs,hit⟩ := progress s initial
    by_cases hf : fuel ≤ n
    · exact steps_prefix_exhausted hs hf
    · have he : fuel = n+(fuel-n) := by omega
      rw [he,hs.run_eq]
      exact ih (fuel-n) (by omega) hit

/-- Finite setup can precede a genuinely divergent target execution. -/
theorem target_diverges_prepend {n : Nat} {t : State w registers} {trace : List (Access w)}
    (hs : WordRam.Steps code rho n s t trace) (ht : WordRam.Diverges code rho t) :
    WordRam.Diverges code rho s := by
  intro fuel
  by_cases hf : fuel ≤ n
  · exact steps_prefix_exhausted hs hf
  · have he : fuel = n+(fuel-n) := by omega
    rw [he,hs.run_eq]
    exact ht (fuel-n)

/-- Chunk bounds imply a bound at every target observation, without assuming
that the infinite execution eventually reaches a final state. -/
theorem target_chunks_stackBound (I : State w registers → Prop) (top : Nat)
    (progress : ∀ s, I s → ∃ n t log, 0 < n ∧ WordRam.Steps code rho n s t log ∧ I t ∧
      StackBound code rho s n top) (initial : I s) :
    ∀ fuel, ((WordRam.run code rho fuel s).state.regs sp).toNat ≤ top := by
  intro fuel
  induction fuel using Nat.strongRecOn generalizing s with
  | ind fuel ih =>
    obtain ⟨n,t,log,hn,hs,hit,hbound⟩ := progress s initial
    by_cases hf : fuel ≤ n
    · exact hbound fuel hf
    · have he : fuel = n+(fuel-n) := by omega
      rw [he,hs.run_eq]
      exact ih (fuel-n) (by omega) hit

/-- One true loop iteration is a productive target fragment at the same loop PC.
Its body may use arbitrary finite recursion within the proved capacity. -/
theorem while_cycle {source : Program} {compiled : CompiledProgram} {condition : Condition} {body : Stmt}
    {free base returnPC : Nat} {stack : Region} {savedFP : Word w}
    {locals out : Locals w} {mem mem' : DataMemory w} {log : List (Access w)}
    (hc : compile source = .ok compiled) (hfit : compiled.Fits w)
    (htest : condition.eval locals = .ok true)
    (d : Evaluation source rho free body locals mem (.next out) mem' log)
    (hsep : Separated stack log)
    (hf : FrameState stack base locals savedFP returnPC mem s)
    (hfree : free = stack.base+stack.size-(base+2+locals.length)) (hret : returnPC < modulus w)
    (hcode : CodeAt compiled.code s.pc
      (lower (fun id => (source.functions[id]?.map Function.frameSize).getD 0)
        (fun id => (compiled.functions[id]?.map FunctionLayout.entry).getD 0)
        compiled.exhaustion s.pc (.while condition body))) :
    ∃ t trace, WordRam.Steps compiled.code rho (conditionCost condition+2+instructions d) s t trace ∧
      t.pc = s.pc ∧ FrameState stack base out savedFP returnPC mem' t ∧
      projectTrace stack trace = log ∧
      StackBound compiled.code rho s (conditionCost condition+2+instructions d)
        (base+2+locals.length+extraStack d) := by
  obtain ⟨htestCode,hbodyCode,hbackCode⟩ := while_parts hcode
  obtain ⟨t,trace₁,hs,hpc,hf₁,hproj,hpol⟩ := condition_steps htest hf htestCode
  simp at hpc
  obtain ⟨u,trace₂,hu⟩ := compile_evaluation hc hfit d hsep base savedFP returnPC t hf₁ hfree hret
    (by rw [hpc]; exact hbodyCode)
  obtain ⟨hupc,huframe⟩ := hu.post
  have hjump : CodeAt compiled.code u.pc [.jump s.pc] := by rw [hupc,hpc]; exact hbackCode
  have hs₃ := jump_step (rho := rho) hjump
  have hn : conditionCost condition+1+instructions d+(0+1) = conditionCost condition+2+instructions d := by omega
  refine ⟨{u with pc := s.pc},trace₁++trace₂,?_,rfl,huframe.pc _,?_,?_⟩
  · simpa only [hn,Option.toList_none,List.nil_append,List.append_nil] using (hs.trans hu.execution).trans (.cons hs₃ (.refl _))
  · rw [project_append,hproj,hu.projection,List.nil_append]
  · have hub := hu.stackBound.end hu.execution
    have hb := StackBound.trans (hs.trans hu.execution)
      (StackBound.trans hs (condition_stackBound htestCode hs (hf.sp_le (by omega)) (hf₁.sp_le (by omega))) hu.stackBound)
      (StackBound.single hs₃ hub hub)
    simpa only [hn] using hb

/-- A source-level invariant for a persistent loop: each body iteration finishes
normally, preserves the invariant, and keeps application accesses off the stack. -/
def LoopProgress (source : Program) (rho : RandomMemory w) (stack : Region) (free : Nat)
    (condition : Condition) (body : Stmt) (I : Locals w → DataMemory w → Prop) : Prop :=
  ∀ locals mem, I locals mem → condition.eval locals = .ok true ∧
    ∃ out mem' log, ∃ _d : Evaluation source rho free body locals mem (.next out) mem' log,
      I out mem' ∧ Separated stack log

/-- Loop-progress certificates imply independent operational source divergence. -/
theorem source_loop_diverges {source : Program} {stack : Region} {free slots cap function : Nat}
    {condition : Condition} {body : Stmt} {I : Locals w → DataMemory w → Prop}
    {locals : Locals w} {mem : DataMemory w} {rest : List Stmt} {callers : List (Caller w)}
    (progress : LoopProgress source rho stack free condition body I) (hi : I locals mem)
    (hlen : locals.length = slots)
    (hcap : cap = free+2+slots+(callers.map (fun c => 2+c.activation.locals.length)).sum) :
    RamLang.Diverges source rho (some cap)
      (atStatement function locals (.while condition body::rest) callers mem) := by
  let J : Config w → Prop := fun c => ∃ ls m,
    c = atStatement function ls (.while condition body::rest) callers m ∧ I ls m ∧ ls.length = slots
  apply RamLang.diverges_of_chunks J _ ⟨locals,mem,rfl,hi,hlen⟩
  intro c hc
  obtain ⟨ls,m,rfl,hinv,hslots⟩ := hc
  obtain ⟨htest,out,m',log,d,hout,hsep⟩ := progress ls m hinv
  obtain ⟨n,t,hs,hpost⟩ := d.sound (cap := cap) (function := function) (rest := .while condition body::rest) (callers := callers)
    (by rw [hslots]; exact hcap)
  change t = atStatement function out (.while condition body::rest) callers m' at hpost
  subst t
  refine ⟨n+1,_,log,by omega,?_,out,m',rfl,hout,?_⟩
  · refine RamLang.Steps.cons (event := none) ?_ hs
    simp [RamLang.Step,RamLang.step,atStatement,htest]
  · exact d.preserves_length.trans hslots

/-- The same source invariant yields target divergence with arbitrary finite
recursive calls per iteration, using one fixed fitting physical stack region. -/
theorem compiled_loop_diverges {source : Program} {compiled : CompiledProgram}
    {free base returnPC pc : Nat} {stack : Region} {savedFP : Word w}
    {condition : Condition} {body : Stmt} {I : Locals w → DataMemory w → Prop}
    {locals : Locals w} {mem : DataMemory w}
    (hc : compile source = .ok compiled) (hfit : compiled.Fits w)
    (progress : LoopProgress source rho stack free condition body I) (hi : I locals mem)
    (hf : FrameState stack base locals savedFP returnPC mem s) (hpc : s.pc = pc)
    (hfree : free = stack.base+stack.size-(base+2+locals.length)) (hret : returnPC < modulus w)
    (hcode : CodeAt compiled.code pc
      (lower (fun id => (source.functions[id]?.map Function.frameSize).getD 0)
        (fun id => (compiled.functions[id]?.map FunctionLayout.entry).getD 0)
        compiled.exhaustion pc (.while condition body))) : WordRam.Diverges compiled.code rho s := by
  let J : State w registers → Prop := fun t => ∃ ls m,
    t.pc = pc ∧ FrameState stack base ls savedFP returnPC m t ∧ I ls m ∧ ls.length = locals.length
  apply target_diverges_of_chunks J _ ⟨locals,mem,hpc,hf,hi,rfl⟩
  intro t ht
  obtain ⟨ls,m,htpc,htframe,hinv,hlen⟩ := ht
  obtain ⟨htest,out,m',log,d,hout,hsep⟩ := progress ls m hinv
  obtain ⟨u,trace,hs,hupc,huframe,hproj,hbound⟩ := while_cycle hc hfit htest d hsep htframe
    (by simpa only [hlen] using hfree) hret (by rw [htpc]; exact hcode)
  exact ⟨_,u,trace,by omega,hs,out,m',hupc.trans htpc,huframe,hout,d.preserves_length.trans hlen⟩

/-- Bounded-space source divergence never exhausts its reserved physical stack;
this holds at every instruction, not merely at iteration boundaries. -/
theorem compiled_loop_stackBound {source : Program} {compiled : CompiledProgram}
    {free base returnPC pc : Nat} {stack : Region} {savedFP : Word w}
    {condition : Condition} {body : Stmt} {I : Locals w → DataMemory w → Prop}
    {locals : Locals w} {mem : DataMemory w}
    (hc : compile source = .ok compiled) (hfit : compiled.Fits w)
    (progress : LoopProgress source rho stack free condition body I) (hi : I locals mem)
    (hf : FrameState stack base locals savedFP returnPC mem s) (hpc : s.pc = pc)
    (hfree : free = stack.base+stack.size-(base+2+locals.length)) (hret : returnPC < modulus w)
    (hcode : CodeAt compiled.code pc
      (lower (fun id => (source.functions[id]?.map Function.frameSize).getD 0)
        (fun id => (compiled.functions[id]?.map FunctionLayout.entry).getD 0)
        compiled.exhaustion pc (.while condition body))) :
    ∀ fuel, ((WordRam.run compiled.code rho fuel s).state.regs sp).toNat ≤ stack.base+stack.size := by
  let J : State w registers → Prop := fun t => ∃ ls m,
    t.pc = pc ∧ FrameState stack base ls savedFP returnPC m t ∧ I ls m ∧ ls.length = locals.length
  apply target_chunks_stackBound J _ _ ⟨locals,mem,hpc,hf,hi,rfl⟩
  intro t ht
  obtain ⟨ls,m,htpc,htframe,hinv,hlen⟩ := ht
  obtain ⟨htest,out,m',log,d,hout,hsep⟩ := progress ls m hinv
  obtain ⟨u,trace,hs,hupc,huframe,hproj,hbound⟩ := while_cycle hc hfit htest d hsep htframe
    (by simpa only [hlen] using hfree) hret (by rw [htpc]; exact hcode)
  refine ⟨_,u,trace,by omega,hs,⟨out,m',hupc.trans htpc,huframe,hout,d.preserves_length.trans hlen⟩,?_⟩
  apply hbound.mono
  have hpeak := extraStack_le d
  have hupper := hf.frameUpper
  omega

end RamLang.Compiler
