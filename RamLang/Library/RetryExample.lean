import RamLang.DSL.Automation
import RamLang.Library.Retry
import RamLang.Logic.Frame

namespace RamLang.Library.FirstNonzero
open WordRam Compiler Logic

/-- A bounded retry example accepts the first nonzero sample from explicitly
addressed random memory, returning zero when the attempt budget is exhausted. -/
def program : Program := ram_program first_nonzero {
  fn first_nonzero(n, address) {
    let sample;
    while (n != 0) {
      sample = random(address);
      address = address + 1;
      if (sample != 0) { return sample; }
      n = n - 1;
    }
    return 0;
  }
}

def function : Function := program.functions[0]'(by decide)

/-- One explicit sample, address advance, acceptance test, and budget decrement. -/
def attempt : Stmt :=
  .seq (.primitive (.random 2 (.local 1)))
    (.seq (.primitive (.binary 1 .add (.local 1) (.literal 1)))
      (.seq (.ite ⟨.ne,.local 2,.literal 0⟩ (.ret (.local 2)) .skip)
        (.primitive (.binary 0 .sub (.local 0) (.literal 1)))))

theorem body_eq : function.body = Retry.body 0 attempt := by rfl

/-- This example accesses only immutable random memory, never application RAM. -/
def policy : AccessPolicy w := ⟨fun _ => False,fun _ => False,fun _ => True⟩

/-- Remaining budget determines the next random address; the old sample local
may be uninitialized or contain an earlier rejected value. -/
def invariant (initial : DataMemory w) (start total remaining : Nat)
    (locals : Locals w) (mem : DataMemory w) : Prop :=
  ∃ last, locals = [some (word w remaining),some (word w (start+(total-remaining))),last] ∧ mem = initial

/-- A successful result was actually read from the reserved sample addresses. -/
def good (rho : RandomMemory w) (start total : Nat) (value : Word w) (_mem : DataMemory w) : Prop :=
  ∃ i, i < total ∧ rho (word w (start+i)) = value

/-- The attempt proof covers both acceptance and rejection. All paths read one
specified sample, cost at most twenty-three instructions, and allocate no frame. -/
theorem attempt_contract {w free : Nat} (rho : RandomMemory w) (initial : DataMemory w)
    (start total : Nat) (hfit : start+total < modulus w)
    (n : Nat) (locals : Locals w) (mem : DataMemory w) (hn : n+1 ≤ total)
    (hi : invariant initial start total (n+1) locals mem) :
    Contract program rho free attempt locals mem
      (fun flow mem' trace => Retry.randomAddresses trace = [word w (start+(total-(n+1)))] ∧
        policy.AllowsTrace trace ∧
        match flow with
        | .next out => invariant initial start total n out mem'
        | .returned value => value ≠ word w 0 ∧ good rho start total value mem'
        | .exhausted => False) 23 0 := by
  obtain ⟨last,rfl,hm⟩ := hi
  subst mem
  let address := start+(total-(n+1))
  let sample := rho (word w address)
  have hinc : word w address+word w 1 = word w (start+(total-n)) := by
    rw [WordRam.word_add]
    congr 1
    dsimp [address]
    omega
  have hsub : word w (n+1)-word w 1 = word w n := by
    rw [WordRam.word_sub (n+1) 1 (by omega) (by omega)]
    rfl
  let read : Evaluation program rho free (.primitive (.random 2 (.local 1)))
      [some (word w (n+1)),some (word w address),last] initial
      (.next [some (word w (n+1)),some (word w address),some sample]) initial
      [.randomRead (word w address) sample] := by ram_primitive
  let inc : Evaluation program rho free (.primitive (.binary 1 .add (.local 1) (.literal 1)))
      [some (word w (n+1)),some (word w address),some sample] initial
      (.next [some (word w (n+1)),some (word w (start+(total-n))),some sample]) initial [] :=
    .primitive (event := none) (by
      simp [Primitive.eval,Atom.eval,requireSome,writeLocal,Binary.eval,hinc,bind,pure,Except.bind,Except.pure])
  have hp : policy.AllowsTrace [.randomRead (word w address) sample] := by
    intro e he
    simp only [List.mem_singleton] at he
    subst e
    trivial
  by_cases hz : sample = word w 0
  · let test : Evaluation program rho free (.ite ⟨.ne,.local 2,.literal 0⟩ (.ret (.local 2)) .skip)
        [some (word w (n+1)),some (word w (start+(total-n))),some sample] initial
        (.next [some (word w (n+1)),some (word w (start+(total-n))),some sample]) initial [] :=
      .ifFalse (by simp [Condition.eval,Atom.eval,requireSome,Comparison.test,hz,bind,pure,Except.bind,Except.pure]) .skip
    let dec : Evaluation program rho free (.primitive (.binary 0 .sub (.local 0) (.literal 1)))
        [some (word w (n+1)),some (word w (start+(total-n))),some sample] initial
        (.next [some (word w n),some (word w (start+(total-n))),some sample]) initial [] :=
      .primitive (event := none) (by
        simp [Primitive.eval,Atom.eval,requireSome,writeLocal,Binary.eval,hsub,bind,pure,Except.bind,Except.pure])
    let d := Evaluation.sequence read (Evaluation.sequence inc (Evaluation.sequence test dec))
    exact Contract.ofEvaluation d ⟨rfl,hp,some sample,rfl,rfl⟩ (by change 22 ≤ 23; decide) (Nat.le_refl _)
  · let test : Evaluation program rho free (.ite ⟨.ne,.local 2,.literal 0⟩ (.ret (.local 2)) .skip)
        [some (word w (n+1)),some (word w (start+(total-n))),some sample] initial
        (.returned sample) initial [] :=
      .ifTrue (by simp [Condition.eval,Atom.eval,requireSome,Comparison.test,hz,bind,pure,Except.bind,Except.pure]) (.ret rfl)
    let d : Evaluation program rho free attempt
        [some (word w (n+1)),some (word w address),last] initial (.returned sample) initial
        [.randomRead (word w address) sample] :=
      .sequence read (.sequence inc (.sequenceStop test (by trivial)))
    exact Contract.ofEvaluation d ⟨rfl,hp,hz,total-(n+1),by omega,rfl⟩ (Nat.le_refl _) (Nat.le_refl _)

/-- Applying the generic retry contract gives the sample schedule, success or
budget failure, unchanged application RAM, and linear actual-instruction bounds. -/
theorem contract {w free : Nat} (rho : RandomMemory w) (initial : DataMemory w)
    (start total : Nat) (hfit : start+total < modulus w) :
    Contract program rho free function.body [some (word w total),some (word w start),none] initial
      (fun flow mem' trace => ∃ value used, flow = .returned value ∧ used ≤ total ∧
        (value = word w 0 → used = total) ∧ (value ≠ word w 0 → good rho start total value mem') ∧
        Retry.randomAddresses trace = Retry.addresses w start used ∧ policy.AllowsTrace trace ∧ mem' = initial)
      (28*total+12) 0 := by
  have h := Retry.contract (p := program) (rho := rho) (free := free) 0 attempt start total 23 0
    (fun n locals mem => n ≤ total ∧ invariant initial start total n locals mem)
    (good rho start total) policy
    (by rintro n locals mem ⟨hn,last,rfl,_⟩; exact ⟨rfl,by omega⟩)
    (by
      intro n locals mem hn hi
      apply (attempt_contract rho initial start total hfit n locals mem hn hi.2).consequence
      · intro flow mem' trace hpost
        refine ⟨hpost.1,hpost.2.1,?_⟩
        cases flow with
        | next out => exact ⟨by omega,hpost.2.2⟩
        | returned value => exact hpost.2.2
        | exhausted => exact hpost.2.2
      · exact Nat.le_refl _
      · exact Nat.le_refl _)
    [some (word w total),some (word w start),none] initial ⟨Nat.le_refl _,none,by simp,rfl⟩
  obtain ⟨flow,mem',trace,d,⟨value,used,hflow,hu,hzero,hgood,hr,hp⟩,hw,hpeak⟩ := h
  have hm : mem' = initial := by
    funext a
    exact d.frame a (fun v hv => hp (.dataWrite a v) hv)
  exact Contract.ofEvaluation d ⟨value,used,hflow,hu,hzero,hgood,hr,hp,hm⟩ hw hpeak

/-- The retry example has fixed code size and five-word frames. -/
def compiled : CompiledProgram :=
  match compile program with
  | .ok c => c
  | .error _ => ⟨#[],[],0⟩

theorem compiles : compile program = .ok compiled := by rfl

theorem fits {w : Nat} (hw : 61 < modulus w) : compiled.Fits w := by
  change 61 < modulus w ∧ ∀ layout ∈ [FunctionLayout.mk 16 45 5], layout.frameWords < modulus w
  refine ⟨hw,?_⟩
  intro layout h
  simp only [List.mem_singleton] at h
  subst layout
  change 5 < modulus w
  omega

/-- The compiled retry example always terminates successfully at the runtime
level. Its word result separately signals acceptance or budget failure, and
its full random-address trace is fresh with all sample and stack work charged. -/
theorem compiled_correct {w : Nat} (rho : RandomMemory w) (s : State w ABI.registers)
    (start total : Nat) (stack : Region) (hw : 61 < modulus w) (hfit : start+total < modulus w)
    (hpc : s.pc = 0) (hsp : s.regs ABI.sp = word w stack.base)
    (hlimit : s.regs ABI.limit = word w (stack.base+stack.size)) (hstack : stack.Fits w)
    (hspace : 5 ≤ stack.size) (hn : s.regs (ABI.argument 0) = word w total)
    (ha : s.regs (ABI.argument 1) = word w start) :
    ∃ work t trace value used, work ≤ 28*total+28 ∧ WordRam.TerminatesIn compiled.code rho s work t trace ∧
      t.regs ABI.status = word w 1 ∧ t.regs ABI.result = value ∧ used ≤ total ∧
      (value = word w 0 → used = total) ∧ (value ≠ word w 0 → good rho start total value s.mem) ∧
      ApplicationMemory stack s.mem t.mem ∧ Retry.randomAddresses trace = Retry.addresses w start used ∧
      (Retry.randomAddresses trace).Nodup ∧
      (∀ fuel, (withStack stack policy).AllowsTrace (WordRam.run compiled.code rho fuel s).trace) ∧
      StackBound compiled.code rho s work (stack.base+5) := by
  have hc := contract (free := stack.size-5) rho s.mem start total hfit
  have hc' := hc.consequence (post' := fun flow mem' trace => ∃ value,
      flow = .returned value ∧ (∃ used, used ≤ total ∧ (value = word w 0 → used = total) ∧
        (value ≠ word w 0 → good rho start total value mem') ∧
        Retry.randomAddresses trace = Retry.addresses w start used ∧ policy.AllowsTrace trace ∧ mem' = s.mem) ∧
      Separated stack trace)
    (by
      rintro flow mem' trace ⟨value,used,hflow,hu,hzero,hgood,hr,hp,hm⟩
      refine ⟨value,hflow,⟨used,hu,hzero,hgood,hr,hp,hm⟩,?_⟩
      intro e he
      have hh := hp e he
      cases e with
      | dataRead a v => exact False.elim hh
      | dataWrite a v => exact False.elim hh
      | randomRead a v => rfl) (Nat.le_refl _) (Nat.le_refl _)
  have he : (entryValues s function.parameters.length).map some ++ List.replicate function.locals.length none =
      [some (word w total),some (word w start),none] := by
    change [some (s.regs (ABI.argument 0)),some (s.regs (ABI.argument 1)),none] = _
    rw [hn,ha]
  rw [←he] at hc'
  obtain ⟨work,t,trace,value,mem',log,ht,hr,hstatus,hresult,⟨used,hu,hzero,hgood,hread,hpolicy,rfl⟩,hmem,hlog,hpeak⟩ :=
    hc'.compiled compiles (fits hw) (f := function) rfl hpc hsp hlimit hstack hspace
  have hsamples : Retry.randomAddresses trace = Retry.addresses w start used := by
    change trace.filterMap Access.randomAddress = _
    rw [←project_random_addresses stack trace,hlog]
    exact hread
  have hpolicy' : (withStack stack policy).AllowsTrace trace := projected_policy (by rw [hlog]; exact hpolicy)
  refine ⟨work,t,trace,value,used,?_,hr,hstatus,hresult,hu,hzero,hgood,hmem,hsamples,?_,
    fun fuel => hr.prefix_policy hpolicy' fuel,hpeak⟩
  · change work ≤ 12+2*2+(28*total+12) at ht
    omega
  · rw [hsamples]
    exact Retry.addresses_nodup (by omega)

end RamLang.Library.FirstNonzero
