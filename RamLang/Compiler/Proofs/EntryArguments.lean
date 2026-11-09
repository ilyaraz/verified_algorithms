import RamLang.Compiler.Proofs.Prefixes

namespace RamLang.Compiler
open WordRam ABI

/-- Copy an entry register directly into its prospective frame slot. -/
def entryCopy (i : Nat) : Code :=
  [.add address (.reg sp) (.imm (2+i)),.store (.reg address) (.reg (entryArgument i))]

def afterEntryCopy (i : Nat) (s : State w registers) : State w registers :=
  let a := s.regs sp + word w (2+i)
  { (s.put address a) with pc := s.pc+2,mem := update s.mem a (s.regs (entryArgument i)) }

def entryValues (s : State w registers) (arity : Nat) : List (Word w) :=
  (List.range arity).map (fun i => s.regs (entryArgument i))

variable {w i n current : Nat} {p : WordRam.Program registers} {rho : RandomMemory w}
  {s : State w registers} {stack : Region}

theorem entryArgument_ne_address (i : Nat) : entryArgument i ≠ address := by
  unfold entryArgument
  cases i with
  | zero => decide
  | succ i =>
    cases i with
    | zero => decide
    | succ i =>
      cases i with
      | zero => decide
      | succ i =>
        cases i with
        | zero => decide
        | succ i =>
          rw [Array.getElem?_eq_none]
          · decide
          · simp

theorem entryArgument_ne_control (i : Nat) :
    entryArgument i ≠ sp ∧ entryArgument i ≠ fp ∧ entryArgument i ≠ limit ∧
      entryArgument i ≠ left ∧ entryArgument i ≠ status := by
  unfold entryArgument
  cases i with
  | zero => decide
  | succ i =>
    cases i with
    | zero => decide
    | succ i =>
      cases i with
      | zero => decide
      | succ i =>
        cases i with
        | zero => decide
        | succ i =>
          rw [Array.getElem?_eq_none]
          · decide
          · simp

theorem entryCopy_steps (hc : CodeAt p s.pc (entryCopy i)) :
    WordRam.Steps p rho 2 s (afterEntryCopy i s)
      [.dataWrite (s.regs sp + word w (2+i)) (s.regs (entryArgument i))] := by
  let a := s.regs sp + word w (2+i)
  let t := s.put address a
  have h₁ : WordRam.Step p rho s t none := by
    unfold WordRam.Step WordRam.step
    rw [hc.head]
    rfl
  have h₂ : WordRam.Step p rho t (afterEntryCopy i s)
      (some (.dataWrite a (s.regs (entryArgument i)))) := by
    unfold WordRam.Step WordRam.step
    rw [show t.pc = s.pc+1 from rfl,hc.tail.head]
    simp only [Operand.eval,t,State.put,update_same,update_other _ _ _ _ (entryArgument_ne_address i)]
    rfl
  exact .cons h₁ (.cons h₂ (.refl _))

theorem entryArguments_succ (n : Nat) : entryArguments (n+1) = entryArguments n ++ entryCopy n := by
  simp [entryArguments,entryCopy,List.range_succ,List.flatMap_append]

theorem entryArguments_length (n : Nat) : (entryArguments n).length = 2*n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [entryArguments_succ,List.length_append,ih]; simp [entryCopy]; omega

theorem quiet_entryArguments (n : Nat) : Quiet (entryArguments n) := by
  induction n with
  | zero => simp [entryArguments,Quiet]
  | succ n ih =>
    rw [entryArguments_succ,quiet_append]
    exact ⟨ih,by simp [Quiet,entryCopy,straightInstruction,Instr.destination,Fin.ext_iff,address,sp]⟩

/-- Entry argument setup initializes only the parameter array; all remaining
locals can start dirty. The old entry-register values are read before clobbering. -/
theorem entryArguments_steps (hc : CodeAt p s.pc (entryArguments n))
    (hsp : s.regs sp = word w current) (hfit : stack.Fits w) (hbase : stack.base ≤ current)
    (hspace : current+2+n ≤ stack.base+stack.size) :
    ∃ t trace, WordRam.Steps p rho (2*n) s t trace ∧ t.pc = s.pc+2*n ∧
      (∀ r, r ≠ address → t.regs r = s.regs r) ∧
      ArrayAt t.mem (current+2) (entryValues s n) ∧
      ApplicationMemory stack s.mem t.mem ∧ projectTrace stack trace = [] ∧
      (framePolicy stack current (current+2+n)).AllowsTrace trace ∧
      (∀ a : Addr w, a.toNat < current+2 → t.mem a = s.mem a) := by
  induction n with
  | zero =>
    refine ⟨s,[],.refl _,by simp,by simp,?_,?_,rfl,?_,by simp⟩
    · simp [entryValues]
    · intro a ha; rfl
    · simp [AccessPolicy.AllowsTrace]
  | succ n ih =>
    rw [entryArguments_succ] at hc
    obtain ⟨t,trace,hs,hpc,hregs,harray,happ,hproj,hpol,hbelow⟩ := ih hc.prefix (by omega)
    have hcopy : CodeAt p t.pc (entryCopy n) := by rw [hpc]; simpa only [entryArguments_length] using hc.suffix
    have htsp : t.regs sp = word w current := (hregs sp (by decide)).trans hsp
    have hvalue : t.regs (entryArgument n) = s.regs (entryArgument n) := hregs _ (entryArgument_ne_address n)
    have haeq : t.regs sp+word w (2+n) = word w (current+2+n) := by rw [htsp,word_add]; congr 1; omega
    have hab : current+2+n < modulus w := by unfold Region.Fits at hfit; omega
    have hain : stack.Contains (word w (current+2+n)) := by
      unfold Region.Contains; rw [word_toNat_of_lt hab]; omega
    have hmem : (afterEntryCopy n t).mem = update t.mem (word w (current+2+n)) (s.regs (entryArgument n)) := by
      simp only [afterEntryCopy,haeq,hvalue]
    have hlog : [Access.dataWrite (t.regs sp+word w (2+n)) (t.regs (entryArgument n))] =
        [Access.dataWrite (word w (current+2+n)) (s.regs (entryArgument n))] := by rw [haeq,hvalue]
    refine ⟨afterEntryCopy n t,trace++[.dataWrite (word w (current+2+n)) (s.regs (entryArgument n))],?_,?_,?_,?_,?_,?_,?_,?_⟩
    · have hh := hs.trans (entryCopy_steps hcopy)
      rw [hlog] at hh
      simpa only [Nat.mul_add,Nat.mul_one] using hh
    · simp only [afterEntryCopy,hpc]; omega
    · intro r hr
      simp only [afterEntryCopy,State.put,update_other _ _ _ _ hr]
      exact hregs r hr
    · have heq : entryValues s (n+1) = entryValues s n ++ [s.regs (entryArgument n)] := by
        simp [entryValues,List.range_succ]
      rw [heq,hmem]
      have hlen : (entryValues s n).length = n := by simp [entryValues]
      have hh := harray.push (v := s.regs (entryArgument n)) (by
        rw [hlen]; unfold Region.Fits at hfit; omega)
      simpa only [hlen] using hh
    · intro a hout
      rw [hmem,update_other]
      · exact happ a hout
      · intro he; exact hout (he ▸ hain)
    · rw [project_append,hproj,project_stack_write hain]; rfl
    · apply (AccessPolicy.allowsTrace_append _).mpr
      refine ⟨framePolicy_mono (Nat.le_refl _) (by omega) hpol,?_⟩
      intro e hevent
      simp only [List.mem_singleton] at hevent
      subst e
      apply Or.inr
      rw [word_toNat_of_lt hab]
      omega
    · intro a ha
      rw [hmem,update_other]
      · exact hbelow a ha
      · intro he
        have hh := congrArg BitVec.toNat he
        rw [word_toNat_of_lt hab] at hh
        omega

end RamLang.Compiler
