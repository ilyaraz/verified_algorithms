import WordRam.Assembly

/-! Fixed-size programs for clear/fill, copy, and read-only traversal. Every mode
has the same loop skeleton and exact instruction accounting. -/
namespace WordRam.Arrays

def source : Reg 4 := ⟨0, by decide⟩
def destination : Reg 4 := ⟨1, by decide⟩
def remaining : Reg 4 := ⟨2, by decide⟩
def value : Reg 4 := ⟨3, by decide⟩

inductive Mode where
  | fill | copy | visit
  deriving DecidableEq, Repr

inductive Label where
  | loop | done
  deriving DecidableEq, Repr

/-- Fill reads the value register; copy and visit load the source. Visit's second
instruction is a register move, so it performs no ordinary-memory writes. -/
def readInstruction : Mode → Instr 4
  | .fill => .mov value (.reg value)
  | .copy | .visit => .load value (.reg source)

def writeInstruction : Mode → Instr 4
  | .visit => .mov value (.reg value)
  | .fill | .copy => .store (.reg destination) (.reg value)

def assembly (mode : Mode) : List (Assembly.Item 4 Label) := [
  .label .loop,
  .instruction (.branch .eq (.reg remaining) (.imm 0) .done),
  .instruction (.emit (readInstruction mode)),
  .instruction (.emit (writeInstruction mode)),
  .instruction (.emit (.add source (.reg source) (.imm 1))),
  .instruction (.emit (.add destination (.reg destination) (.imm 1))),
  .instruction (.emit (.sub remaining (.reg remaining) (.imm 1))),
  .instruction (.jump .loop),
  .label .done,
  .instruction (.emit .halt)]

def program (mode : Mode) : Program 4 :=
  Assembly.assemble 0 (fun l => (Assembly.labelOffset l (assembly mode)).getD 0)
    (Assembly.instructions (assembly mode)).toArray

theorem compile_eq (mode : Mode) : Assembly.compile 0 (assembly mode) = some (program mode) := by
  cases mode <;> rfl

/-- Ghost one-iteration state and events, used only to specify the real code. -/
def nextValue (mode : Mode) (s : State w 4) : Word w :=
  match mode with
  | .fill => s.regs value
  | .copy | .visit => s.mem (s.regs source)

def nextMemory (mode : Mode) (s : State w 4) : DataMemory w :=
  match mode with
  | .visit => s.mem
  | .fill | .copy => update s.mem (s.regs destination) (nextValue mode s)

def next (mode : Mode) (s : State w 4) : State w 4 :=
  ⟨0, update (update (update (update s.regs value (nextValue mode s))
    source (s.regs source + word w 1)) destination (s.regs destination + word w 1))
    remaining (s.regs remaining - word w 1), nextMemory mode s⟩

def events (mode : Mode) (s : State w 4) : List (Access w) :=
  (match mode with
   | .fill => []
   | .copy | .visit => [.dataRead (s.regs source) (nextValue mode s)]) ++
  (match mode with
   | .visit => []
   | .fill | .copy => [.dataWrite (s.regs destination) (nextValue mode s)])

def finish (s : State w 4) : State w 4 := { s with pc := 7 }

variable {w : Nat} {s : State w 4} {rho : RandomMemory w}

/-- One actual loop iteration, including its back edge, costs seven instructions. -/
theorem iteration (mode : Mode) (hpc : s.pc = 0)
    (hn : s.regs remaining ≠ word w 0) :
    Steps (program mode) rho 7 s (next mode s) (events mode s) := by
  change s.regs (2 : Reg 4) ≠ word w 0 at hn
  apply steps_iff_run.mpr
  cases mode <;>
    simp [program, assembly, Assembly.assemble, Assembly.instructions, Assembly.labelOffset,
      Assembly.Instruction.resolve, Instr.relocate, readInstruction, writeInstruction,
      run, step, hpc, Comparison.test, Operand.eval, State.put, next, nextValue,
      nextMemory, events, remaining, source, destination, value, update, hn,
      RunResult.prepend, update_shadow]

/-- One branch plus the final halt, also for an empty array. -/
theorem exit (mode : Mode) (hpc : s.pc = 0) (hn : s.regs remaining = word w 0) :
    TerminatesIn (program mode) rho s 2 (finish s) [] := by
  change s.regs (2 : Reg 4) = word w 0 at hn
  apply terminatesIn_iff_run.mpr
  cases mode <;>
    simp [program, assembly, Assembly.assemble, Assembly.instructions, Assembly.labelOffset,
      Assembly.Instruction.resolve, Instr.relocate, readInstruction, writeInstruction,
      run, step, hpc, Comparison.test, Operand.eval, finish, hn, remaining,
      RunResult.prepend]

/-- The mathematical state reached after n iterations. It is not an interpreter
or an instruction: iteration proves its relation to seven authoritative steps. -/
def iterate (mode : Mode) : Nat → State w 4 → State w 4
  | 0, s => s
  | n+1, s => iterate mode n (next mode s)

def trace (mode : Mode) : Nat → State w 4 → List (Access w)
  | 0, _ => []
  | n+1, s => events mode s ++ trace mode n (next mode s)

@[simp] theorem next_source (mode : Mode) (s : State w 4) :
    (next mode s).regs source = s.regs source + word w 1 := by
  simp [next, update, source, destination, remaining, value]

@[simp] theorem next_destination (mode : Mode) (s : State w 4) :
    (next mode s).regs destination = s.regs destination + word w 1 := by
  simp [next, update, source, destination, remaining, value]

@[simp] theorem next_remaining (mode : Mode) (s : State w 4) :
    (next mode s).regs remaining = s.regs remaining - word w 1 := by
  simp [next, update, source, destination, remaining, value]

theorem count_down (hn : s.regs remaining = word w (n+1)) (hf : n+1 < modulus w) :
    (next mode s).regs remaining = word w n := by
  rw [next_remaining, hn]
  apply BitVec.eq_of_toNat_eq
  rw [sub_toNat, word_toNat_of_lt hf, word_toNat_of_lt (by omega : 1 < modulus w),
    word_toNat_of_lt (by omega : n < modulus w)]
  have : n + 1 + modulus w - 1 = n + modulus w := by omega
  rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]

theorem terminates (mode : Mode) (n : Nat) (hpc : s.pc = 0)
    (hn : s.regs remaining = word w n) (hf : n < modulus w) :
    TerminatesIn (program mode) rho s (7*n+2) (finish (iterate mode n s)) (trace mode n s) := by
  induction n generalizing s with
  | zero => simpa [iterate, trace] using exit mode hpc hn
  | succ n ih =>
    have hne : s.regs remaining ≠ word w 0 := by
      intro he
      have he' := congrArg BitVec.toNat (hn.symm.trans he)
      rw [word_toNat_of_lt hf] at he'
      simp at he'
    have hs := iteration mode hpc hne (rho := rho)
    obtain ⟨k, hk, ht, hh⟩ := ih (s := next mode s) rfl (count_down hn hf) (by omega)
    exact ⟨7+k, by omega, hs.trans ht, hh⟩

@[simp] theorem word_add_one (b : Nat) : word w b + word w 1 = word w (b+1) :=
  BitVec.ofNat_add_ofNat b 1

/-- Every location outside the destination interval retains its initial value,
even with dirty memory, overlapping sources, or arbitrary fill values. -/
theorem iterate_frame (mode : Mode) (n b : Nat) (hd : s.regs destination = word w b)
    (hf : b+n < modulus w) (ha : ¬ (Region.mk b n).Contains a) :
    (iterate mode n s).mem a = s.mem a := by
  induction n generalizing b s with
  | zero => rfl
  | succ n ih =>
    have ht : ¬ (Region.mk (b+1) n).Contains a := by
      unfold Region.Contains at *
      simp only at *
      omega
    have hn : (next mode s).regs destination = word w (b+1) := by simp [hd]
    rw [iterate, ih (b+1) hn (by omega) ht]
    have hne : a ≠ word w b := by
      intro he
      apply ha
      rw [he]
      exact Region.contains_index (r := ⟨b, n+1⟩) (i := 0) hf (by omega : 0 < n+1)
    cases mode <;> simp [next, nextMemory, hd, update, hne]

theorem fill_array (n b : Nat) (hd : s.regs destination = word w b)
    (hf : b+n < modulus w) :
    ArrayAt (iterate .fill n s).mem b (List.replicate n (s.regs value)) := by
  induction n generalizing b s with
  | zero => simp
  | succ n ih =>
    rw [List.replicate_succ, arrayAt_cons]
    have hn : (next .fill s).regs destination = word w (b+1) := by simp [hd]
    have hv : (next .fill s).regs value = s.regs value := by
      simp [next, nextValue, update, value, source, destination, remaining]
    constructor
    · change (iterate .fill n (next .fill s)).mem (word w b) = _
      rw [iterate_frame .fill n (b+1) hn (by omega)]
      · simp [next, nextMemory, nextValue, hd]
      · unfold Region.Contains
        rw [word_toNat_of_lt (by omega : b < modulus w)]
        simp only
        omega
    · simpa [iterate, hv] using ih (s := next .fill s) (b+1) hn (by omega)

theorem copy_array (xs : List (Word w)) (src dst : Nat)
    (hs : s.regs source = word w src) (hd : s.regs destination = word w dst)
    (hf : src+xs.length < modulus w) (hg : dst+xs.length < modulus w)
    (sep : (Region.mk src xs.length).Separated ⟨dst, xs.length⟩)
    (hm : ArrayAt s.mem src xs) :
    ArrayAt (iterate .copy xs.length s).mem dst xs := by
  induction xs generalizing s src dst with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨hx, ht⟩ := arrayAt_cons.mp hm
    have hn : (next .copy s).regs destination = word w (dst+1) := by simp [hd]
    have hs' : (next .copy s).regs source = word w (src+1) := by simp [hs]
    have hv : nextValue .copy s = x := by simpa [nextValue, hs] using hx
    have hsfit : src+1+xs.length < modulus w := by simp only [List.length_cons] at hf; omega
    have hdfit : dst+1+xs.length < modulus w := by simp only [List.length_cons] at hg; omega
    have hm' : ArrayAt (next .copy s).mem (src+1) xs := by
      change ArrayAt (update s.mem (s.regs destination) (nextValue .copy s)) _ _
      apply ht.update_outside hsfit
      rw [hd]
      unfold Region.Contains
      rw [word_toNat_of_lt (by simp only [List.length_cons] at hg; omega : dst < modulus w)]
      unfold Region.Separated at sep
      simp only [List.length_cons] at sep
      rcases sep with sep | sep <;> simp only at * <;> omega
    have sep' : (Region.mk (src+1) xs.length).Separated ⟨dst+1, xs.length⟩ := by
      unfold Region.Separated at *
      simp only [List.length_cons] at sep
      rcases sep with sep | sep
      · exact Or.inl (by simp only at *; omega)
      · exact Or.inr (by simp only at *; omega)
    apply arrayAt_cons.mpr
    constructor
    · change (iterate .copy xs.length (next .copy s)).mem (word w dst) = x
      rw [iterate_frame .copy xs.length (dst+1) hn hdfit]
      · simp [next, nextMemory, hv, hd]
      · unfold Region.Contains
        rw [word_toNat_of_lt (by simp only [List.length_cons] at hg; omega : dst < modulus w)]
        simp only
        omega
    · exact ih (s := next .copy s) (src+1) (dst+1) hs' hn hsfit hdfit sep' hm'

@[simp] theorem visit_memory (n : Nat) (s : State w 4) :
    (iterate .visit n s).mem = s.mem := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simpa [iterate, next, nextMemory] using ih (next .visit s)

/-- Every array access has a fitting, unwrapped address. The endpoint may be the
last representable word, but no iteration accesses it. -/
theorem trace_local (mode : Mode) (n src dst : Nat)
    (hs : s.regs source = word w src) (hd : s.regs destination = word w dst)
    (hf : src+n < modulus w) (hg : dst+n < modulus w) :
    AccessPolicy.AllowsTrace
      ⟨(Region.mk src n).Contains, (Region.mk dst n).Contains, fun _ => False⟩
      (trace mode n s) := by
  induction n generalizing s src dst with
  | zero => simp [trace, AccessPolicy.AllowsTrace]
  | succ n ih =>
    rw [trace, AccessPolicy.allowsTrace_append]
    constructor
    · have hrs : (Region.mk src (n+1)).Contains (s.regs source) := by
        rw [hs]; exact Region.contains_index (r := ⟨src, n+1⟩) (i := 0) hf (by omega : 0 < n+1)
      have hrd : (Region.mk dst (n+1)).Contains (s.regs destination) := by
        rw [hd]; exact Region.contains_index (r := ⟨dst, n+1⟩) (i := 0) hg (by omega : 0 < n+1)
      cases mode <;> simp [events, AccessPolicy.AllowsTrace, AccessPolicy.Allows, hrs, hrd]
    · have ht := ih (s := next mode s) (src+1) (dst+1)
        (by simp [hs]) (by simp [hd]) (by omega) (by omega)
      intro e he
      have he' := ht e he
      cases e <;> simp only [AccessPolicy.Allows, Region.Contains] at *
      all_goals omega

@[simp] theorem trace_random (mode : Mode) (n : Nat) (s : State w 4) :
    (trace mode n s).filterMap Access.randomAddress = [] := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih =>
    simp only [trace, List.filterMap_append, ih, List.append_nil]
    cases mode <;> rfl

@[simp] theorem visit_writes (n : Nat) (s : State w 4) :
    (trace .visit n s).filterMap Access.writeAddress = [] := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simp [trace, events, ih, Access.writeAddress]

end WordRam.Arrays
