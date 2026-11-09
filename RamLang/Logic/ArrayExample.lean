import RamLang.Logic.Loop
import RamLang.Logic.Frame

namespace RamLang.Logic.Fill
open WordRam Compiler

/-- Fill an array iteratively with an arbitrary word, using explicit memory
writes and word-valued pointer and length updates. -/
def iteration : Stmt :=
  .seq (.primitive (.store (.local 0) (.local 2)))
    (.seq (.primitive (.binary 0 .add (.local 0) (.literal 1)))
      (.primitive (.binary 1 .sub (.local 1) (.literal 1))))

/-- Continue while the remaining word count is nonzero. -/
def condition : Condition := ⟨.ne,.local 1,.literal 0⟩

/-- Three public parameters and no additional locals give a five-word frame. -/
def function : Function := ⟨"fill",["p","n","value"],[],
  .seq (.while condition iteration) (.ret (.literal 0))⟩

/-- The reusable source array-fill program has no hashing dependencies. -/
def program : Program := ⟨#[function],0⟩

/-- Mathematical memory after initializing a prefix of an array. -/
def filled (mem : DataMemory w) (base count : Nat) (value : Word w) : DataMemory w :=
  fun a => if base ≤ a.toNat ∧ a.toNat < base+count then value else mem a

/-- Initializing an empty prefix leaves every cell unchanged. -/
theorem filled_zero (mem : DataMemory w) (base : Nat) (value : Word w) :
    filled mem base 0 value = mem := by
  funext a
  simp only [filled,Nat.add_zero]
  split
  · omega
  · rfl

/-- One nonwrapping store extends the initialized prefix by one cell. -/
theorem filled_succ (mem : DataMemory w) (base count : Nat) (value : Word w)
    (hfit : base+count < modulus w) :
    update (filled mem base count value) (word w (base+count)) value = filled mem base (count+1) value := by
  funext a
  rw [update_word _ _ _ hfit]
  simp only [filled]
  split <;> split <;> (try split) <;> (first | rfl | omega)

/-- The fill routine may write only its array and has no data or random reads. -/
def policy (base count : Nat) : AccessPolicy w where
  read _ := False
  write a := (Region.mk base count).Contains a
  random _ := False

/-- The loop invariant relates a ghost remaining count to ordinary locals and
the precisely initialized memory prefix. -/
def invariant (initial : DataMemory w) (base count : Nat) (value : Word w)
    (remaining : Nat) (locals : Locals w) (mem : DataMemory w) : Prop :=
  ∃ done, done+remaining = count ∧ locals = [some (word w (base+done)),some (word w remaining),some value] ∧
    mem = filled initial base done value

/-- A single iteration preserves the prefix invariant, decreases the remaining
count, costs seventeen target instructions, and allocates no additional frame. -/
theorem iteration_contract {w free : Nat} (rho : RandomMemory w) (initial : DataMemory w)
    (base count : Nat) (value : Word w) (hfit : base+count < modulus w)
    (n : Nat) (locals : Locals w) (mem : DataMemory w)
    (hi : invariant initial base count value n locals mem) (htrue : condition.eval locals = .ok true) :
    Contract program rho free iteration locals mem
      (fun flow mem' trace => ∃ out m, flow = .next out ∧ m < n ∧
        invariant initial base count value m out mem' ∧ (policy base count).AllowsTrace trace) 17 0 := by
  obtain ⟨done,he,rfl,rfl⟩ := hi
  cases n with
  | zero => simp [condition,Condition.eval,Atom.eval,requireSome,Comparison.test,bind,pure,Except.bind,Except.pure] at htrue
  | succ n =>
    have hsub : word w (n+1)-word w 1 = word w n := by
      rw [WordRam.word_sub (n+1) 1 (by omega) (by omega)]
      rfl
    let m := filled initial base done value
    let m' := update m (word w (base+done)) value
    let store : Evaluation program rho free (.primitive (.store (.local 0) (.local 2)))
        [some (word w (base+done)),some (word w (n+1)),some value] m
        (.next [some (word w (base+done)),some (word w (n+1)),some value]) m'
        [.dataWrite (word w (base+done)) value] := .primitive (event := some _) rfl
    let inc : Evaluation program rho free (.primitive (.binary 0 .add (.local 0) (.literal 1)))
        [some (word w (base+done)),some (word w (n+1)),some value] m'
        (.next [some (word w (base+(done+1))),some (word w (n+1)),some value]) m' [] :=
      .primitive (event := none) (by simp [Primitive.eval,Atom.eval,requireSome,writeLocal,Binary.eval,
        WordRam.word_add,Nat.add_assoc,bind,pure,Except.bind,Except.pure])
    let dec : Evaluation program rho free (.primitive (.binary 1 .sub (.local 1) (.literal 1)))
        [some (word w (base+(done+1))),some (word w (n+1)),some value] m'
        (.next [some (word w (base+(done+1))),some (word w n),some value]) m' [] :=
      .primitive (event := none) (by simp [Primitive.eval,Atom.eval,requireSome,writeLocal,Binary.eval,
        hsub,bind,pure,Except.bind,Except.pure])
    let d := Evaluation.sequence store (Evaluation.sequence inc dec)
    refine .ofEvaluation d ⟨_,n,rfl,by omega,⟨done+1,by omega,rfl,?_⟩,?_⟩ (Nat.le_refl _) (Nat.le_refl _)
    · exact filled_succ initial base done value (by omega)
    · intro e hevent
      simp only [List.append_nil,List.mem_singleton] at hevent
      subst e
      change base ≤ (word w (base+done)).toNat ∧ (word w (base+done)).toNat < base+count
      rw [word_toNat_of_lt (by omega : base+done < modulus w)]
      omega

/-- The source loop rule proves total fill, its exact final array, preservation
outside that array, a linear time bound, and constant stack space. -/
theorem contract {w free : Nat} (rho : RandomMemory w) (initial : DataMemory w)
    (base count : Nat) (value : Word w) (hfit : base+count < modulus w) :
    Contract program rho free function.body [some (word w base),some (word w count),some value] initial
      (fun flow mem' trace => flow = .returned (word w 0) ∧ mem' = filled initial base count value ∧
        (policy base count).AllowsTrace trace) (22*count+12) 0 := by
  have loop := while_total (p := program) (rho := rho) (free := free) (condition := condition) (body := iteration)
    (invariant initial base count value) (policy base count) (fun n => 22*n+5) (fun _ => 17) 0
    (by
      intro n locals mem hi
      obtain ⟨done,_,rfl,_⟩ := hi
      exact ⟨!(word w n == word w 0),rfl⟩)
    (by intro n; change 3+2 ≤ 22*n+5; omega)
    (by intro n m hm; change 3+2+17+(22*m+5) ≤ 22*n+5; omega)
    (iteration_contract rho initial base count value hfit)
  have hinit : invariant initial base count value count
      [some (word w base),some (word w count),some value] initial :=
    ⟨0,Nat.zero_add _,by simp,by rw [filled_zero]⟩
  have hloop := loop count _ _ hinit
  have hloop' := hloop.consequence (post' := fun flow mem' trace => ∃ out, flow = .next out ∧
      ∃ k, invariant initial base count value k out mem' ∧ condition.eval out = .ok false ∧
        (policy base count).AllowsTrace trace)
    (by rintro _ _ _ ⟨out,k,hflow,hi,hf,hp⟩; exact ⟨out,hflow,k,hi,hf,hp⟩) (Nat.le_refl _) (Nat.le_refl _)
  have result := Contract.sequence (b := .ret (.literal 0)) (post := fun flow mem' trace => flow = .returned (word w 0) ∧
      mem' = filled initial base count value ∧ (policy base count).AllowsTrace trace)
    (middle := fun out mem' trace => ∃ k, invariant initial base count value k out mem' ∧
      condition.eval out = .ok false ∧ (policy base count).AllowsTrace trace)
    (work₂ := 7) (peak₂ := 0) hloop' (by
      intro out mem' prior hmid
      obtain ⟨k,hi,hfalse,hpolicy⟩ := hmid
      obtain ⟨done,he,rfl,rfl⟩ := hi
      have hz : word w k = word w 0 := by
        simpa [condition,Condition.eval,Atom.eval,requireSome,Comparison.test,
          bind,pure,Except.bind,Except.pure] using hfalse
      have hk : k = 0 := (word_eq_iff_of_lt (by omega) (by omega : 0 < modulus w)).mp hz
      have hd : done = count := by omega
      subst done
      exact Contract.ofEvaluation (Evaluation.ret (atom := .literal 0) rfl)
        ⟨rfl,rfl,by simpa using hpolicy⟩ (by simp [instructions,atom,epilogue]) (by simp [extraStack]))
  simpa [function,Nat.add_assoc] using result

/-- Every initialized array element contains the requested value. -/
theorem filled_array (mem : DataMemory w) (base count : Nat) (value : Word w)
    (hfit : base+count < modulus w) : ArrayAt (filled mem base count value) base (List.replicate count value) := by
  intro i
  have hi : i.val < count := by simpa using i.isLt
  simp only [filled,word_toNat_of_lt (by omega : base+i.val < modulus w)]
  rw [if_pos (by omega)]
  simp

/-- Filling the array preserves each cell outside its address interval. -/
theorem filled_outside (mem : DataMemory w) (base count : Nat) (value : Word w)
    (a : Addr w) (ha : ¬(Region.mk base count).Contains a) : filled mem base count value a = mem a :=
  if_neg ha

/-- The checker accepts the array routine with its three initialized parameters. -/
theorem checked : check program = .ok () := by rfl

/-- The linked array-fill program and its public resource metadata. -/
def compiled : CompiledProgram :=
  match compile program with
  | .ok c => c
  | .error _ => ⟨#[],[],0⟩

theorem compiles : compile program = .ok compiled := by rfl

/-- Fifty instructions and a five-word frame suffice at every input size. -/
theorem fits {w : Nat} (hw : 50 < modulus w) : compiled.Fits w := by
  change 50 < modulus w ∧ ∀ layout ∈ [FunctionLayout.mk 18 32 5], layout.frameWords < modulus w
  refine ⟨hw,?_⟩
  intro layout h
  simp only [List.mem_singleton] at h
  subst layout
  change 5 < modulus w
  omega

/-- A source array-write policy avoids the stack whenever the two supplied
regions are separated. No clean initial memory is required. -/
theorem separated_trace {w base count : Nat} {stack : Region} {trace : List (Access w)}
    (hsep : (Region.mk base count).Separated stack) (hp : (policy base count).AllowsTrace trace) :
    Separated stack trace := by
  intro e he
  have h := hp e he
  cases e with
  | dataRead a v => exact False.elim h
  | randomRead a v => exact False.elim h
  | dataWrite a v =>
    have hn := Region.not_contains_of_separated hsep h
    simp only [ABI.applicationEvent]
    simp
    unfold Region.Contains at hn
    omega

/-- The loop contract transfers to the generated program: at most 22n+30
instructions, a constant five-word stack, the filled array, and preservation of
all memory outside the array and stack. Every interrupted trace obeys the same
application-plus-stack access policy. -/
theorem compiled_correct {w : Nat} (rho : RandomMemory w) (s : State w ABI.registers)
    (base count : Nat) (value : Word w) (stack : Region)
    (hw : 50 < modulus w) (hfit : base+count < modulus w)
    (hpc : s.pc = 0) (hsp : s.regs ABI.sp = word w stack.base)
    (hlimit : s.regs ABI.limit = word w (stack.base+stack.size)) (hstack : stack.Fits w)
    (hspace : 5 ≤ stack.size) (hsep : (Region.mk base count).Separated stack)
    (hp : s.regs (ABI.argument 0) = word w base)
    (hn : s.regs (ABI.argument 1) = word w count)
    (hv : s.regs (ABI.argument 2) = value) :
    ∃ work t trace, work ≤ 22*count+30 ∧ WordRam.TerminatesIn compiled.code rho s work t trace ∧
      t.regs ABI.status = word w 1 ∧ t.regs ABI.result = word w 0 ∧
      ArrayAt t.mem base (List.replicate count value) ∧
      (∀ a, ¬(Region.mk base count).Contains a → ¬stack.Contains a → t.mem a = s.mem a) ∧
      (∀ fuel, (withStack stack (policy base count)).AllowsTrace (WordRam.run compiled.code rho fuel s).trace) ∧
      StackBound compiled.code rho s work (stack.base+5) := by
  have hc := contract (free := stack.size-5) rho s.mem base count value hfit
  have hc' := hc.consequence (post' := fun flow mem' trace => ∃ result,
      flow = .returned result ∧ (result = word w 0 ∧ mem' = filled s.mem base count value ∧
        (policy base count).AllowsTrace trace) ∧ Separated stack trace)
    (by rintro flow mem' trace ⟨hf,hm,hpolicy⟩
        exact ⟨word w 0,hf,⟨rfl,hm,hpolicy⟩,separated_trace hsep hpolicy⟩) (Nat.le_refl _) (Nat.le_refl _)
  have he : (entryValues s function.parameters.length).map some ++ List.replicate function.locals.length none =
      [some (word w base),some (word w count),some value] := by
    change [some (s.regs (ABI.argument 0)),some (s.regs (ABI.argument 1)),some (s.regs (ABI.argument 2))] = _
    rw [hp,hn,hv]
  rw [←he] at hc'
  obtain ⟨work,t,trace,result,mem',log,ht,hr,hstatus,hresult,⟨rfl,rfl,hpolicy⟩,hmem,hlog,hpeak⟩ :=
    hc'.compiled compiles (fits hw) (f := function) rfl hpc hsp hlimit hstack hspace
  have hpolicy' : (withStack stack (policy base count)).AllowsTrace trace := projected_policy (by rw [hlog]; exact hpolicy)
  refine ⟨work,t,trace,?_,hr,hstatus,hresult,?_,?_,fun fuel => hr.prefix_policy hpolicy' fuel,?_⟩
  · change work ≤ 12+2*3+(22*count+12) at ht
    omega
  · intro i
    have hi : i.val < count := by simpa using i.isLt
    have hin : (Region.mk base count).Contains (word w (base+i.val)) :=
      Region.contains_index hfit hi
    rw [hmem _ (Region.not_contains_of_separated hsep hin)]
    exact filled_array s.mem base count value hfit i
  · intro a ha hs
    rw [hmem a hs,filled_outside _ _ _ _ a ha]
  · exact hpeak

end RamLang.Logic.Fill
