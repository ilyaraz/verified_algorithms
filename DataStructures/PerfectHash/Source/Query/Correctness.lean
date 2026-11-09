import DataStructures.PerfectHash.Source.Query.SourceProof

namespace PerfectHash.Source.Query
open WordRam RamLang RamLang.Compiler

/-- A conservative constant includes all spills, two hash calls and final halt. -/
def cost : Nat := 237

/-- Maximum simultaneously allocated ordinary stack words, including headers. -/
def stackWords : Nat := 28

/-- Width, capacity and separation requirements of the alternative query.
Unlike the original query, this entry uses the ordinary source-language ABI. -/
structure Admissible (w : Nat) (retained stack : Region) : Prop where
  codeFit : 237 < modulus w
  stackFit : stack.Fits w
  capacity : stackWords ≤ stack.size
  separate : retained.Separated stack

/-- Two arguments contain descriptor base and key. Stack bounds use the shared
language ABI; all other registers and every stack word may initially be dirty. -/
structure Input (retained stack : Region) (key : Word w) (s : State w ABI.registers) : Prop where
  pc : s.pc = 0
  sp : s.regs ABI.sp = word w stack.base
  limit : s.regs ABI.limit = word w (stack.base+stack.size)
  base : s.regs (ABI.argument 0) = word w retained.base
  key : s.regs (ABI.argument 1) = key

/-- The compiled function and its only callee fit whenever the fixed code does. -/
theorem fits {w : Nat} (hw : 237 < modulus w) : compiled.Fits w := by
  change 237 < modulus w ∧ ∀ layout ∈ [FunctionLayout.mk 16 197 21,FunctionLayout.mk 213 24 7],
    layout.frameWords < modulus w
  refine ⟨hw,?_⟩
  intro layout hl
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hl
  rcases hl with rfl | rfl <;> dsimp <;> omega

/-- Placing a fresh stack immediately after a retained extent is feasible
whenever the explicitly enlarged reservation fits. Other separated placements
are equally valid, including a reused construction stack. -/
theorem admissible_after {w : Nat} (r : Region) (hw : 237 < modulus w)
    (hroom : r.base+r.size+28 < modulus w) : Admissible w r ⟨r.base+r.size,28⟩ :=
  ⟨hw,hroom,Nat.le_refl _,Or.inl (Nat.le_refl _)⟩

/-- Successful generated execution preserves application memory and the exact
membership answer, with safe arbitrary interrupted prefixes and a fixed stack
peak. There is no runtime stack-exhaustion outcome under Admissible. -/
theorem execution {w : Nat} {S : Finset (Word w)} {r stack : Region} {d : Table.Data w}
    (rho : RandomMemory w) (s : State w ABI.registers) (q : Word w)
    (v : Table.View S r s.mem d) (ha : Admissible w r stack) (hi : Input r stack q s) :
    ∃ work t trace, work ≤ cost ∧ WordRam.TerminatesIn compiled.code rho s work t trace ∧
      t.regs ABI.status = word w 1 ∧ t.regs ABI.result = word w (if q ∈ S then 1 else 0) ∧
      ApplicationMemory stack s.mem t.mem ∧
      (∀ fuel, (withStack stack (policy r)).AllowsTrace (WordRam.run compiled.code rho fuel s).trace) ∧
      StackBound compiled.code rho s work (stack.base+stackWords) := by
  have hcap : 28 ≤ stack.size := ha.capacity
  have hc := contract v q rho (free := stack.size-21) (by omega)
  have hc' := hc.consequence (post' := fun flow mem' trace => ∃ value,
      flow = .returned value ∧
        (value = word w (if q ∈ S then 1 else 0) ∧ mem' = s.mem ∧ (policy r).AllowsTrace trace) ∧
      Separated stack trace)
    (by
      rintro flow mem' trace ⟨hflow,hmem,hpolicy⟩
      refine ⟨_,hflow,⟨rfl,hmem,hpolicy⟩,?_⟩
      intro e he
      have hp := hpolicy e he
      cases e with
      | dataRead a value =>
        have hout := Region.not_contains_of_separated ha.separate hp
        simp [ABI.applicationEvent]
        unfold Region.Contains at hout
        omega
      | dataWrite a value => exact False.elim hp
      | randomRead a value => rfl) (Nat.le_refl _) (Nat.le_refl _)
  have hlocals : (entryValues s function.parameters.length).map some ++
      List.replicate function.locals.length none =
      [word w r.base,q].map some ++ List.replicate function.locals.length none := by
    change [some (s.regs (ABI.argument 0)),some (s.regs (ABI.argument 1))] ++ _ = _
    rw [hi.base,hi.key]
    rfl
  rw [←hlocals] at hc'
  obtain ⟨work,t,trace,value,mem',log,ht,hr,hs,hv,⟨rfl,rfl,hp⟩,hm,hlog,hpeak⟩ :=
    hc'.compiled compiles (fits ha.codeFit) (f := function) rfl hi.pc hi.sp hi.limit ha.stackFit (by
      change 21 ≤ stack.size; omega)
  have hpolicy : (withStack stack (policy r)).AllowsTrace trace := projected_policy (by rw [hlog]; exact hp)
  exact ⟨work,t,trace,ht,hr,hs,hv,hm,fun fuel => hr.prefix_policy hpolicy fuel,hpeak⟩

/-- Public alternative query output: stack writes are permitted, the retained
dictionary and every other application cell are preserved, and random memory
is never read. The original StaticSet.QueryOutput remains unchanged. -/
structure Output (S : Finset (Word w)) (r stack : Region) (q : Word w)
    (initial : DataMemory w) (result : RunResult w ABI.registers) : Prop where
  halted : result.reason = .halted
  time : result.steps ≤ cost
  status : result.state.regs ABI.status = word w 1
  answer : result.state.regs ABI.result = word w (if q ∈ S then 1 else 0)
  memory : ApplicationMemory stack initial result.state.mem
  accesses : (withStack stack (policy r)).AllowsTrace result.trace
  noRandomReads : result.randomReads = 0

/-- The fixed fuel bound yields the public result for every fixed random image. -/
theorem correct {w : Nat} {S : Finset (Word w)} {r stack : Region} {d : Table.Data w}
    (rho : RandomMemory w) (s : State w ABI.registers) (q : Word w)
    (v : Table.View S r s.mem d) (ha : Admissible w r stack) (hi : Input r stack q s) :
    Output S r stack q s.mem (WordRam.run compiled.code rho cost s) := by
  obtain ⟨work,t,trace,hw,hr,hs,hv,hm,hp,_⟩ := execution rho s q v ha hi
  have he : WordRam.run compiled.code rho cost s = ⟨t,work,trace,.halted⟩ := by
    have hstable := run_stable (p := compiled.code) (rho := rho) (s := s)
      (fuel := work) (by rw [hr.run_eq]; simp) (cost-work)
    simpa only [Nat.add_sub_of_le hw,hr.run_eq] using hstable
  have hpolicy := hp cost
  refine ⟨by rw [he],by simpa [he] using hw,by simpa [he] using hs,by simpa [he] using hv,
    by simpa [he] using hm,hpolicy,?_⟩
  have hn : (WordRam.run compiled.code rho cost s).trace.filterMap Access.randomAddress = [] := by
    apply List.filterMap_eq_nil_iff.mpr
    intro e hevent
    have hh := hpolicy e hevent
    cases e <;> simp_all [Access.randomAddress,AccessPolicy.Allows,withStack,policy]
  simp [RunResult.randomReads,RunResult.randomAddresses,hn]

/-- Public membership specification for the alternative ABI and stack effects.
The representation is exactly the construction-independent StaticSet interface. -/
def Spec : Prop :=
  ∀ (w : Nat) (S : Finset (Word w)) (r stack : Region) (s : State w ABI.registers),
    Table.representation.Holds S r s.mem → Admissible w r stack →
    ∀ (q : Word w), Input r stack q s → ∀ rho : RandomMemory w,
      Output S r stack q s.mem (WordRam.run compiled.code rho cost s)

/-- The new generated query implements the relaxed public specification. -/
theorem spec : Spec := by
  intro w S r stack s hrep ha q hi rho
  obtain ⟨d,hd⟩ := hrep
  exact correct rho s q hd ha hi

/-- Every subsequent query sees the same representation despite dirty stack
words left behind by ordinary function calls. -/
theorem representation_preserved {w : Nat} {S : Finset (Word w)} {r stack : Region} {d : Table.Data w}
    (rho : RandomMemory w) (s : State w ABI.registers) (q : Word w)
    (v : Table.View S r s.mem d) (ha : Admissible w r stack) (hi : Input r stack q s) :
    Table.View S r (WordRam.run compiled.code rho cost s).state.mem d := by
  apply v.frame
  intro a hinside
  exact ((correct rho s q v ha hi).memory a (Region.not_contains_of_separated ha.separate hinside)).symm

/-- Input, construction scratch, and former stack storage can be overwritten
arbitrarily before query. Only the retained representation must survive. -/
theorem after_overwrite {w : Nat} {S : Finset (Word w)} {r stack : Region} {d : Table.Data w}
    {mem : DataMemory w} (rho : RandomMemory w) (s : State w ABI.registers) (q : Word w)
    (v : Table.View S r mem d) (agree : AgreeOn r mem s.mem)
    (ha : Admissible w r stack) (hi : Input r stack q s) :
    Output S r stack q s.mem (WordRam.run compiled.code rho cost s) :=
  correct rho s q (v.frame agree) ha hi

end PerfectHash.Source.Query
