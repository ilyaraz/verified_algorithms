import RamLang.Compiler.Proofs.Prefixes

namespace RamLang.Compiler.EntryRegisters
open WordRam ABI

/-- A reserved scratch register used only for parameter-cell addresses. -/
def addressRegister : Reg registers := ⟨10,by decide⟩

/-- A reserved register holding the prospective frame base before ABI setup. -/
def baseRegister : Reg registers := ⟨11,by decide⟩

/-- Copy an entry register directly into its prospective frame slot. -/
def entryCopy (argument : Nat → Reg registers) (i : Nat) : Code :=
  [.add addressRegister (.reg baseRegister) (.imm (2+i)),.store (.reg addressRegister) (.reg (argument i))]

def afterEntryCopy (argument : Nat → Reg registers) (i : Nat) (s : State w registers) : State w registers :=
  let a := s.regs baseRegister + word w (2+i)
  { (s.put addressRegister a) with pc := s.pc+2,mem := update s.mem a (s.regs (argument i)) }

def entryValues (argument : Nat → Reg registers) (s : State w registers) (arity : Nat) : List (Word w) :=
  (List.range arity).map (fun i => s.regs (argument i))

/-- Static register-to-frame copies, emitted in argument order. -/
def entryArguments (argument : Nat → Reg registers) (n : Nat) : Code :=
  (List.range n).flatMap (entryCopy argument)

variable {argument : Nat → Reg registers} {w i n current : Nat} {p : WordRam.Program registers} {rho : RandomMemory w}
  {s : State w registers} {stack : Region}

theorem entryCopy_steps (hc : CodeAt p s.pc (entryCopy argument i))
    (ha : argument i ≠ addressRegister) :
    WordRam.Steps p rho 2 s (afterEntryCopy argument i s)
      [.dataWrite (s.regs baseRegister + word w (2+i)) (s.regs (argument i))] := by
  let a := s.regs baseRegister + word w (2+i)
  let t := s.put addressRegister a
  have h₁ : WordRam.Step p rho s t none := by
    unfold WordRam.Step WordRam.step
    rw [hc.head]
    rfl
  have h₂ : WordRam.Step p rho t (afterEntryCopy argument i s)
      (some (.dataWrite a (s.regs (argument i)))) := by
    unfold WordRam.Step WordRam.step
    rw [show t.pc = s.pc+1 from rfl,hc.tail.head]
    simp only [Operand.eval,t,State.put,update_same,update_other _ _ _ _ ha]
    rfl
  exact .cons h₁ (.cons h₂ (.refl _))

theorem entryArguments_succ (argument : Nat → Reg registers) (n : Nat) : entryArguments argument (n+1) = entryArguments argument n ++ entryCopy argument n := by
  simp [entryArguments,entryCopy,List.range_succ,List.flatMap_append]

theorem entryArguments_length (argument : Nat → Reg registers) (n : Nat) : (entryArguments argument n).length = 2*n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [entryArguments_succ,List.length_append,ih]; simp [entryCopy]; omega

/-- Entry argument setup initializes only the parameter array; all remaining
locals can start dirty. The old entry-register values are read before clobbering. -/
theorem entryArguments_steps (hc : CodeAt p s.pc (entryArguments argument n))
    (hargs : ∀ i, i < n → argument i ≠ addressRegister)
    (hsp : s.regs baseRegister = word w current) (hfit : stack.Fits w) (hbase : stack.base ≤ current)
    (hspace : current+2+n ≤ stack.base+stack.size) :
    ∃ t trace, WordRam.Steps p rho (2*n) s t trace ∧ t.pc = s.pc+2*n ∧
      (∀ r, r ≠ addressRegister → t.regs r = s.regs r) ∧
      ArrayAt t.mem (current+2) (entryValues argument s n) ∧
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
    obtain ⟨t,trace,hs,hpc,hregs,harray,happ,hproj,hpol,hbelow⟩ := ih hc.prefix (fun i hi => hargs i (by omega)) (by omega)
    have hcopy : CodeAt p t.pc (entryCopy argument n) := by rw [hpc]; simpa only [entryArguments_length] using hc.suffix
    have htsp : t.regs baseRegister = word w current := (hregs baseRegister (by decide)).trans hsp
    have hvalue : t.regs (argument n) = s.regs (argument n) := hregs _ (hargs n (by omega))
    have haeq : t.regs baseRegister+word w (2+n) = word w (current+2+n) := by rw [htsp,word_add]; congr 1; omega
    have hab : current+2+n < modulus w := by unfold Region.Fits at hfit; omega
    have hain : stack.Contains (word w (current+2+n)) := by
      unfold Region.Contains; rw [word_toNat_of_lt hab]; omega
    have hmem : (afterEntryCopy argument n t).mem = update t.mem (word w (current+2+n)) (s.regs (argument n)) := by
      simp only [afterEntryCopy,haeq,hvalue]
    have hlog : [Access.dataWrite (t.regs baseRegister+word w (2+n)) (t.regs (argument n))] =
        [Access.dataWrite (word w (current+2+n)) (s.regs (argument n))] := by rw [haeq,hvalue]
    refine ⟨afterEntryCopy argument n t,trace++[.dataWrite (word w (current+2+n)) (s.regs (argument n))],?_,?_,?_,?_,?_,?_,?_,?_⟩
    · have hh := hs.trans (entryCopy_steps hcopy (hargs n (by omega)))
      rw [hlog] at hh
      simpa only [Nat.mul_add,Nat.mul_one] using hh
    · simp only [afterEntryCopy,hpc]; omega
    · intro r hr
      simp only [afterEntryCopy,State.put,update_other _ _ _ _ hr]
      exact hregs r hr
    · have heq : entryValues argument s (n+1) = entryValues argument s n ++ [s.regs (argument n)] := by
        simp [entryValues,List.range_succ]
      rw [heq,hmem]
      have hlen : (entryValues argument s n).length = n := by simp [entryValues]
      have hh := harray.push (v := s.regs (argument n)) (by
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

end RamLang.Compiler.EntryRegisters
