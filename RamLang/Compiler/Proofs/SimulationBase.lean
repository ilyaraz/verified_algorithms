import RamLang.Compiler.Proofs.StackBounds

namespace RamLang.Compiler
open WordRam ABI

/-- Every referenced function uses one final linked entry and the emitted body. -/
def LinkedFunctions (source : Program) (code : WordRam.Program registers)
    (frames entries : FunctionId → Nat) (exhausted : Nat) : Prop :=
  ∀ id f, source.functions[id]? = some f → frames id = f.frameSize ∧
    CodeAt code (entries id) (prologue ++ lower frames entries exhausted (entries id+2) f.body)

/-- A continuing or returning fragment has continuing instructions only;
exhaustion includes the dedicated error halt in its charged instruction count. -/
def TargetRun (code : WordRam.Program registers) (rho : RandomMemory w) (flow : Flow w)
    (n : Nat) (s t : State w registers) (trace : List (Access w)) : Prop :=
  match flow with
  | .exhausted => WordRam.TerminatesIn code rho s n t trace
  | _ => WordRam.Steps code rho n s t trace

/-- Source control outcomes are represented by final PCs, restored registers,
or the dedicated error status. Application memory is related outside the stack. -/
def TargetPost (stack : Region) (base : Nat) (savedFP : Word w) (returnPC endPC : Nat)
    (flow : Flow w) (mem : DataMemory w) (t : State w registers) : Prop :=
  match flow with
  | .next locals => t.pc = endPC ∧ FrameState stack base locals savedFP returnPC mem t
  | .returned v => t.pc = returnPC ∧ t.regs fp = savedFP ∧ t.regs sp = word w base ∧
      t.regs result = v ∧ t.regs limit = word w (stack.base+stack.size) ∧ ApplicationMemory stack mem t.mem
  | .exhausted => t.regs status = word w 2 ∧ ApplicationMemory stack mem t.mem

structure Fragment (code : WordRam.Program registers) (rho : RandomMemory w)
    (stack : Region) (base top : Nat) (savedFP : Word w) (returnPC endPC : Nat)
    (flow : Flow w) (mem : DataMemory w) (observed : List (Access w))
    (n : Nat) (s t : State w registers) (trace : List (Access w)) : Prop where
  execution : TargetRun code rho flow n s t trace
  post : TargetPost stack base savedFP returnPC endPC flow mem t
  projection : projectTrace stack trace = observed
  policy : (framePolicy stack base top).AllowsTrace trace
  stackBound : StackBound code rho s n top

variable {w base top returnPC endPC n k : Nat} {stack : Region} {locals : Locals w}
  {savedFP : Word w} {mem mem' : DataMemory w} {s t u : State w registers}
  {code : WordRam.Program registers} {rho : RandomMemory w} {flow : Flow w}
  {trace log observed : List (Access w)}

theorem TargetRun.prepend (hs : WordRam.Steps code rho k s t log)
    (ht : TargetRun code rho flow n t u trace) : TargetRun code rho flow (k+n) s u (log++trace) := by
  cases flow with
  | next _ => exact hs.trans ht
  | returned _ => exact hs.trans ht
  | exhausted => exact hs.then_terminates ht

theorem TargetPost.changeEnd (h : TargetPost stack base savedFP returnPC endPC flow mem t)
    (hs : flow.stops) (other : Nat) : TargetPost stack base savedFP returnPC other flow mem t := by
  cases flow with
  | next _ => exact False.elim hs
  | returned _ => exact h
  | exhausted => exact h

/-- A final linked continuation whose first instruction exists fits every code-fit width. -/
theorem CodeAt.address_fits {instruction : Instr registers} {rest : Code}
    (h : CodeAt code pc (instruction::rest)) (hc : code.size < modulus w) : pc < modulus w := by
  have := (Array.getElem?_eq_some_iff.mp h.head).1
  omega

/-- A callee's body policy protects every ordinary word below its own frame. -/
theorem below_frame_preserved (hs : WordRam.Steps code rho n s t trace)
    (hp : (framePolicy stack base top).AllowsTrace trace)
    (ha : stack.Contains a) (hl : a.toNat < base) : t.mem a = s.mem a := by
  apply hs.frame_of_policy hp
  intro hwrite
  rcases hwrite with h | ⟨h,_⟩
  · exact h ha
  · omega

/-- Restored registers and preserved older words reconstruct the caller with
its live local values, even when the callee changed application memory. -/
theorem restore_caller (hf : FrameState stack base locals savedFP returnPC mem s)
    (hfp : t.regs fp = word w base) (hsp : t.regs sp = word w (base+2+locals.length))
    (hlimit : t.regs limit = word w (stack.base+stack.size))
    (happ : ApplicationMemory stack mem' t.mem)
    (hbelow : ∀ a : Addr w, stack.Contains a → a.toNat < base+2+locals.length → t.mem a = s.mem a) :
    FrameState stack base locals savedFP returnPC mem' t := by
  refine ⟨hf.stackFits,hf.baseLower,hf.frameUpper,hfp,hsp,hlimit,?_,?_,?_,happ⟩
  · intro i v hi
    have hb := (List.getElem?_eq_some_iff.mp hi).1
    rw [hbelow _ (hf.slotInside hb) (by
      simp only [slotAddress,word_toNat_of_lt (hf.frameFits.slot_lt hb)]; omega)]
    exact hf.localValues i v hi
  · have hb : base < modulus w := by have := hf.frameFits; unfold FrameFits at this; omega
    rw [hbelow _ (by simpa using hf.headerInside (i := 0) (by decide)) (by rw [word_toNat_of_lt hb]; omega)]
    exact hf.savedFrame
  · have hb : base+1 < modulus w := by have := hf.frameFits; unfold FrameFits at this; omega
    rw [hbelow _ (hf.headerInside (i := 1) (by decide)) (by rw [word_toNat_of_lt hb]; omega)]
    exact hf.savedLink

end RamLang.Compiler
