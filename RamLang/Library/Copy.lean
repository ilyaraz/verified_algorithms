import RamLang.DSL.Automation
import RamLang.Library.Traversal
import RamLang.Logic.Frame

namespace RamLang.Library.Copy
open WordRam Compiler Logic

/-- Copy disjoint arrays with explicit loads and stores in readable source syntax. -/
def program : Program := ram_program copy {
  fn copy(dst, src, n) {
    let value;
    while (n != 0) {
      value = load(src);
      store(dst, value);
      dst = dst + 1;
      src = src + 1;
      n = n - 1;
    }
    return 0;
  }
}

/-- The sole checked function has three parameters and one local value slot. -/
def function : Function := program.functions[0]'(by decide)

/-- One visit loads a source word, writes it to the destination, and advances
both pointers while decrementing the remaining count. -/
def iteration : Stmt :=
  .seq (.primitive (.load 3 (.local 1)))
    (.seq (.primitive (.store (.local 0) (.local 3)))
      (.seq (.primitive (.binary 0 .add (.local 0) (.literal 1)))
        (.seq (.primitive (.binary 1 .add (.local 1) (.literal 1)))
          (.primitive (.binary 2 .sub (.local 2) (.literal 1))))))

/-- The DSL yields the generic traversal loop used in the proof. -/
theorem body_eq : function.body = .seq (Traversal.loop 2 iteration) (.ret (.literal 0)) := by rfl

/-- Mathematical copy of an initialized prefix, retaining all other memory. -/
def copied (initial : DataMemory w) (dst src count : Nat) : DataMemory w :=
  fun a => if dst ≤ a.toNat ∧ a.toNat < dst+count then initial (word w (src+(a.toNat-dst))) else initial a

/-- Copying zero words leaves memory unchanged. -/
theorem copied_zero (initial : DataMemory w) (dst src : Nat) : copied initial dst src 0 = initial := by
  funext a
  simp only [copied,Nat.add_zero]
  split
  · omega
  · rfl

/-- A nonwrapping destination store extends the copied prefix by one word. -/
theorem copied_succ (initial : DataMemory w) (dst src count : Nat) (hfit : dst+count < modulus w) :
    update (copied initial dst src count) (word w (dst+count)) (initial (word w (src+count))) =
      copied initial dst src (count+1) := by
  funext a
  rw [update_word _ _ _ hfit]
  simp only [copied]
  split
  · rename_i he
    rw [if_pos (by omega)]
    congr 2
    omega
  · split <;> split <;> (first | rfl | omega)

/-- Reads stay in the source array, writes in the destination, and no random
image is consulted. Source and destination separation is an explicit premise. -/
def policy (dst src count : Nat) : AccessPolicy w where
  read a := (Region.mk src count).Contains a
  write a := (Region.mk dst count).Contains a
  «random» _ := False

/-- The next source cell is unchanged by the already copied destination prefix. -/
theorem copied_read (initial : DataMemory w) (dst src count done : Nat)
    (hs : src+count < modulus w) (hsep : (Region.mk src count).Separated ⟨dst,count⟩) (hi : done < count) :
    copied initial dst src done (word w (src+done)) = initial (word w (src+done)) := by
  have hn := Region.not_contains_of_separated hsep (Region.contains_index hs hi)
  simp only [copied]
  apply if_neg
  change ¬(dst ≤ (word w (src+done)).toNat ∧ (word w (src+done)).toNat < dst+count) at hn
  intro he
  exact hn ⟨he.1,by omega⟩

/-- The invariant permits an arbitrary old value in the invocation-local slot;
its load overwrites that value before every use. -/
def invariant (initial : DataMemory w) (dst src count : Nat)
    (remaining : Nat) (locals : Locals w) (mem : DataMemory w) : Prop :=
  ∃ done last, done+remaining = count ∧
    locals = [some (word w (dst+done)),some (word w (src+done)),some (word w remaining),last] ∧
    mem = copied initial dst src done

/-- Each copy visit preserves the prefix invariant, costs twenty-eight target
instructions, and uses no additional stack beyond its fixed invocation frame. -/
theorem iteration_contract {w free : Nat} (rho : RandomMemory w) (initial : DataMemory w)
    (dst src count : Nat) (hd : dst+count < modulus w) (hs : src+count < modulus w)
    (hsep : (Region.mk src count).Separated ⟨dst,count⟩)
    (n : Nat) (locals : Locals w) (mem : DataMemory w)
    (hi : invariant initial dst src count (n+1) locals mem) :
    Contract program rho free iteration locals mem
      (fun flow mem' trace => ∃ out, flow = .next out ∧ invariant initial dst src count n out mem' ∧
        (policy dst src count).AllowsTrace trace) 28 0 := by
  obtain ⟨done,last,he,rfl,rfl⟩ := hi
  let m := copied initial dst src done
  let value := initial (word w (src+done))
  let m' := update m (word w (dst+done)) value
  have hread : m (word w (src+done)) = value := copied_read initial dst src count done hs hsep (by omega)
  have hsub : word w (n+1)-word w 1 = word w n := by
    rw [WordRam.word_sub (n+1) 1 (by omega) (by omega)]
    rfl
  let read : Evaluation program rho free (.primitive (.load 3 (.local 1)))
      [some (word w (dst+done)),some (word w (src+done)),some (word w (n+1)),last] m
      (.next [some (word w (dst+done)),some (word w (src+done)),some (word w (n+1)),some value]) m
      [.dataRead (word w (src+done)) value] := .primitive (event := some _) (by
        simp [Primitive.eval,Atom.eval,requireSome,writeLocal,hread,bind,pure,Except.bind,Except.pure])
  let write : Evaluation program rho free (.primitive (.store (.local 0) (.local 3)))
      [some (word w (dst+done)),some (word w (src+done)),some (word w (n+1)),some value] m
      (.next [some (word w (dst+done)),some (word w (src+done)),some (word w (n+1)),some value]) m'
      [.dataWrite (word w (dst+done)) value] := by
    apply Evaluation.primitive (event := some _)
    ram_simp
    rfl
  let incDst : Evaluation program rho free (.primitive (.binary 0 .add (.local 0) (.literal 1)))
      [some (word w (dst+done)),some (word w (src+done)),some (word w (n+1)),some value] m'
      (.next [some (word w (dst+(done+1))),some (word w (src+done)),some (word w (n+1)),some value]) m' [] :=
    .primitive (event := none) (by
      simp [Primitive.eval,Atom.eval,requireSome,writeLocal,Binary.eval,WordRam.word_add,Nat.add_assoc,
        bind,pure,Except.bind,Except.pure])
  let incSrc : Evaluation program rho free (.primitive (.binary 1 .add (.local 1) (.literal 1)))
      [some (word w (dst+(done+1))),some (word w (src+done)),some (word w (n+1)),some value] m'
      (.next [some (word w (dst+(done+1))),some (word w (src+(done+1))),some (word w (n+1)),some value]) m' [] :=
    .primitive (event := none) (by
      simp [Primitive.eval,Atom.eval,requireSome,writeLocal,Binary.eval,WordRam.word_add,Nat.add_assoc,
        bind,pure,Except.bind,Except.pure])
  let dec : Evaluation program rho free (.primitive (.binary 2 .sub (.local 2) (.literal 1)))
      [some (word w (dst+(done+1))),some (word w (src+(done+1))),some (word w (n+1)),some value] m'
      (.next [some (word w (dst+(done+1))),some (word w (src+(done+1))),some (word w n),some value]) m' [] :=
    .primitive (event := none) (by
      simp [Primitive.eval,Atom.eval,requireSome,writeLocal,Binary.eval,hsub,bind,pure,Except.bind,Except.pure])
  let d := Evaluation.sequence read (Evaluation.sequence write (Evaluation.sequence incDst (Evaluation.sequence incSrc dec)))
  refine Contract.ofEvaluation d ⟨_,rfl,⟨done+1,some value,by omega,rfl,?_⟩,?_⟩ (Nat.le_refl _) (Nat.le_refl _)
  · exact copied_succ initial dst src done (by omega)
  · intro e hevent
    simp only [List.append_nil,List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at hevent
    rcases hevent with rfl | rfl
    · exact Region.contains_index hs (by change done < count; omega)
    · exact Region.contains_index hd (by change done < count; omega)

/-- Generic traversal plus a return establishes copy correctness and a linear
instruction bound, without any target program counters in the source proof. -/
theorem contract {w free : Nat} (rho : RandomMemory w) (initial : DataMemory w)
    (dst src count : Nat) (hd : dst+count < modulus w) (hs : src+count < modulus w)
    (hsep : (Region.mk src count).Separated ⟨dst,count⟩) :
    Contract program rho free function.body
      [some (word w dst),some (word w src),some (word w count),none] initial
      (fun flow mem' trace => flow = .returned (word w 0) ∧ mem' = copied initial dst src count ∧
        (policy dst src count).AllowsTrace trace) (33*count+12) 0 := by
  have traversal := Traversal.contract (p := program) (rho := rho) (free := free) 2 iteration
    (invariant initial dst src count) (policy dst src count) 28 0
    (by rintro n locals mem ⟨done,last,he,rfl,_⟩; exact ⟨rfl,by omega⟩)
    (iteration_contract rho initial dst src count hd hs hsep)
  have hloop := traversal count [some (word w dst),some (word w src),some (word w count),none] initial
    ⟨0,none,Nat.zero_add _,by simp,by rw [copied_zero]⟩
  have h := Contract.sequence (b := .ret (.literal 0))
    (post := fun flow mem' trace => flow = .returned (word w 0) ∧ mem' = copied initial dst src count ∧
      (policy dst src count).AllowsTrace trace)
    (middle := fun out mem' trace => invariant initial dst src count 0 out mem' ∧ (policy dst src count).AllowsTrace trace)
    (work₂ := 7) (peak₂ := 0) hloop (by
      rintro out mem' prior ⟨⟨done,last,he,rfl,rfl⟩,hp⟩
      have hdone : done = count := by omega
      subst done
      exact Contract.ofEvaluation (Evaluation.ret (atom := .literal 0) rfl)
        ⟨rfl,rfl,by simpa using hp⟩ (by simp [instructions,atom,epilogue]) (by simp [extraStack]))
  rw [body_eq]
  simpa [Nat.add_assoc] using h

/-- The model initializes exactly the destination array with the original source words. -/
theorem copied_array (initial : DataMemory w) (dst src count : Nat) (hd : dst+count < modulus w) :
    ArrayAt (copied initial dst src count) dst ((List.range count).map (fun i => initial (word w (src+i)))) := by
  intro i
  have hi : i.val < count := by simpa using i.isLt
  simp only [copied,word_toNat_of_lt (by omega : dst+i.val < modulus w)]
  rw [if_pos (by omega)]
  simp

/-- The model preserves every ordinary memory cell outside the destination. -/
theorem copied_outside (initial : DataMemory w) (dst src count : Nat)
    (a : Addr w) (ha : ¬(Region.mk dst count).Contains a) : copied initial dst src count a = initial a :=
  if_neg ha

/-- The deterministic compiler emits sixty-one instructions and six-word frames. -/
def compiled : CompiledProgram :=
  match compile program with
  | .ok c => c
  | .error _ => ⟨#[],[],0⟩

theorem compiles : compile program = .ok compiled := by rfl

theorem fits {w : Nat} (hw : 61 < modulus w) : compiled.Fits w := by
  change 61 < modulus w ∧ ∀ layout ∈ [FunctionLayout.mk 18 43 6], layout.frameWords < modulus w
  refine ⟨hw,?_⟩
  intro layout h
  simp only [List.mem_singleton] at h
  subst layout
  change 6 < modulus w
  omega

/-- Source and destination access regions together avoid the compiler stack. -/
theorem separated_trace {w dst src count : Nat} {stack : Region} {trace : List (Access w)}
    (hd : (Region.mk dst count).Separated stack) (hs : (Region.mk src count).Separated stack)
    (hp : (policy dst src count).AllowsTrace trace) : Separated stack trace := by
  intro e he
  have h := hp e he
  cases e with
  | dataRead a v =>
    have hn := Region.not_contains_of_separated hs h
    simp only [ABI.applicationEvent]
    simp
    unfold Region.Contains at hn
    omega
  | dataWrite a v =>
    have hn := Region.not_contains_of_separated hd h
    simp only [ABI.applicationEvent]
    simp
    unfold Region.Contains at hn
    omega
  | randomRead a v => exact False.elim h

/-- The DSL copy routine uses at most 33n+30 actual instructions and six stack
words. Its physical output agrees with the full copy model outside the stack,
and every interrupted trace obeys the source/destination access contract. -/
theorem compiled_correct {w : Nat} (rho : RandomMemory w) (s : State w ABI.registers)
    (dst src count : Nat) (stack : Region) (hw : 61 < modulus w)
    (hd : dst+count < modulus w) (hs : src+count < modulus w)
    (hdisjoint : (Region.mk src count).Separated ⟨dst,count⟩)
    (hdstack : (Region.mk dst count).Separated stack) (hsstack : (Region.mk src count).Separated stack)
    (hpc : s.pc = 0) (hsp : s.regs ABI.sp = word w stack.base)
    (hlimit : s.regs ABI.limit = word w (stack.base+stack.size)) (hstack : stack.Fits w)
    (hspace : 6 ≤ stack.size) (hdarg : s.regs (ABI.argument 0) = word w dst)
    (hsarg : s.regs (ABI.argument 1) = word w src) (hnarg : s.regs (ABI.argument 2) = word w count) :
    ∃ work t trace, work ≤ 33*count+30 ∧ WordRam.TerminatesIn compiled.code rho s work t trace ∧
      t.regs ABI.status = word w 1 ∧ t.regs ABI.result = word w 0 ∧
      ApplicationMemory stack (copied s.mem dst src count) t.mem ∧
      (∀ fuel, (withStack stack (policy dst src count)).AllowsTrace (WordRam.run compiled.code rho fuel s).trace) ∧
      StackBound compiled.code rho s work (stack.base+6) := by
  have hc := contract (free := stack.size-6) rho s.mem dst src count hd hs hdisjoint
  have hc' := hc.consequence (post' := fun flow mem' trace => ∃ value, flow = .returned value ∧
      (value = word w 0 ∧ mem' = copied s.mem dst src count ∧ (policy dst src count).AllowsTrace trace) ∧
      Separated stack trace)
    (by rintro flow mem' trace ⟨hf,hm,hp⟩
        exact ⟨word w 0,hf,⟨rfl,hm,hp⟩,separated_trace hdstack hsstack hp⟩) (Nat.le_refl _) (Nat.le_refl _)
  have he : (entryValues s function.parameters.length).map some ++ List.replicate function.locals.length none =
      [some (word w dst),some (word w src),some (word w count),none] := by
    change [some (s.regs (ABI.argument 0)),some (s.regs (ABI.argument 1)),some (s.regs (ABI.argument 2)),none] = _
    rw [hdarg,hsarg,hnarg]
  rw [←he] at hc'
  obtain ⟨work,t,trace,value,mem',log,ht,hr,hstatus,hresult,⟨rfl,rfl,hpolicy⟩,hmem,hlog,hpeak⟩ :=
    hc'.compiled compiles (fits hw) (f := function) rfl hpc hsp hlimit hstack hspace
  have hpolicy' : (withStack stack (policy dst src count)).AllowsTrace trace := projected_policy (by rw [hlog]; exact hpolicy)
  refine ⟨work,t,trace,?_,hr,hstatus,hresult,hmem,fun fuel => hr.prefix_policy hpolicy' fuel,hpeak⟩
  change work ≤ 12+2*3+(33*count+12) at ht
  omega

end RamLang.Library.Copy
