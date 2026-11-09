import RamLang.RegisterOnly.LeafProof

namespace RamLang.RegisterOnly
open WordRam Compiler

/-- An initialized parameter segment in the helper register interval. -/
def ValuesAt (regs : Registers w (capacity+2)) (base start : Nat) (values : List (Word w)) : Prop :=
  ∀ i value, values[i]? = some value → regs (slot capacity base (start+i)) = value

/-- Parameter values initialize source locals while untouched local slots remain
unconstrained, exactly as in the independent invocation semantics. -/
theorem ValuesAt.locals {capacity base extra : Nat} {regs : Registers w (capacity+2)} {values : List (Word w)}
    (h : ValuesAt regs base 0 values) : LocalsAt regs base (values.map some ++ List.replicate extra none) := by
  intro i v hi
  simp only [List.getElem?_append,List.length_map] at hi
  split at hi
  · simp only [List.getElem?_map] at hi
    cases hv : values[i]? with
    | none => simp [hv] at hi
    | some value =>
      simp [hv] at hi
      subst value
      simpa only [Nat.zero_add] using h i v hv
  · simp only [List.getElem?_replicate] at hi
    split at hi <;> cases hi

/-- Argument copying emits precisely one register move per source argument. -/
theorem argumentsFrom_length (capacity caller helper start : Nat) (args : List Atom) :
    (argumentsFrom capacity caller helper start args).length = args.length := by
  induction args generalizing start with
  | nil => rfl
  | cons a rest ih => simp [argumentsFrom,ih]

/-- Successful source argument evaluation preserves list length. -/
theorem arguments_values_length {args : List Atom} {locals : Locals w} {values : List (Word w)}
    (h : args.mapM (Atom.eval locals) = .ok values) : values.length = args.length := by
  induction args generalizing values with
  | nil => simp [List.mapM_nil,pure,Except.pure] at h; subst values; rfl
  | cons a rest ih =>
    cases ha : a.eval locals with
    | error e => simp [List.mapM_cons,ha,bind,Except.bind] at h
    | ok v =>
      cases hr : rest.mapM (Atom.eval locals) with
      | error e => simp [List.mapM_cons,ha,hr,bind,Except.bind] at h
      | ok vs =>
        simp [List.mapM_cons,ha,hr,bind,pure,Except.bind,Except.pure] at h
        subst values
        simpa using ih hr

/-- Copy arguments without any memory effects or caller-register changes. This
handles repeated/permuted arguments and preserves earlier copied parameters. -/
theorem arguments_steps {capacity helper slots start : Nat}
    {p : WordRam.Program (capacity+2)} {rho : RandomMemory w} {s : State w (capacity+2)}
    {locals : Locals w} {args : List Atom} {values : List (Word w)}
    (hc : CodeAt p s.pc (argumentsFrom capacity 0 helper start args))
    (hf : Fits capacity 0 locals.length) (hh : Fits capacity helper slots) (hsep : locals.length ≤ helper)
    (hroom : start+args.length ≤ slots) (hl : LocalsAt s.regs 0 locals)
    (he : args.mapM (Atom.eval locals) = .ok values) :
    ∃ t, WordRam.Steps p rho args.length s t [] ∧ t.pc = s.pc+args.length ∧
      LocalsAt t.regs 0 locals ∧ t.mem = s.mem ∧ ValuesAt t.regs helper start values ∧
      Preserves s.regs t.regs (helper+start) args.length := by
  induction args generalizing start values s with
  | nil =>
    simp [List.mapM_nil,pure,Except.pure] at he
    subst values
    refine ⟨s,.refl _,by simp,hl,rfl,?_,fun _ _ => rfl⟩
    intro i v hi
    simp at hi
  | cons a rest ih =>
    cases ha : a.eval locals with
    | error e => simp [List.mapM_cons,ha,bind,Except.bind] at he
    | ok v =>
      cases hr : rest.mapM (Atom.eval locals) with
      | error e => simp [List.mapM_cons,ha,hr,bind,Except.bind] at he
      | ok vs =>
        simp [List.mapM_cons,ha,hr,bind,pure,Except.bind,Except.pure] at he
        subst values
        have hstart : start < slots := by simp only [List.length_cons] at hroom; omega
        let t := s.put (slot capacity helper start) v
        have hs : WordRam.Step p rho s t none := by
          unfold WordRam.Step WordRam.step
          rw [hc.head]
          simp only [atom_value hl ha]
          rfl
        have htlocals : LocalsAt t.regs 0 locals := hl.frame (by
          intro i hi
          apply update_other
          exact slot_disjoint hf hh (by omega) hi hstart)
        have hctail : CodeAt p t.pc (argumentsFrom capacity 0 helper (start+1) rest) := hc.tail
        obtain ⟨u,hsteps,hupc,hulocals,humem,huvalues,huframe⟩ := ih hctail
          (by simp only [List.length_cons] at hroom; omega) htlocals hr
        have htailfit : Fits capacity (helper+(start+1)) rest.length := by
          unfold Fits at *
          simp only [List.length_cons] at hroom
          omega
        have hheadOutside : Outside capacity (helper+(start+1)) rest.length (slot capacity helper start) := by
          intro i hi h
          have hval := congrArg Fin.val h
          rw [slot_val hh hstart,slot_val htailfit hi] at hval
          omega
        refine ⟨u,WordRam.Steps.cons hs hsteps,?_,hulocals,humem,?_,?_⟩
        · dsimp [t,State.put] at hupc
          simp only [List.length_cons]
          omega
        · intro i value hvalue
          cases i with
          | zero =>
            simp only [List.getElem?_cons_zero,Option.some.injEq] at hvalue
            subst value
            change u.regs (slot capacity helper start) = v
            rw [huframe _ hheadOutside]
            exact update_same _ _ _
          | succ i =>
            have hh := huvalues i value (by simpa using hvalue)
            simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh
        · intro r hout
          have hout' : Outside capacity (helper+(start+1)) rest.length r := by
            intro i hi heq
            apply hout (i+1) (by simp only [List.length_cons]; omega)
            rw [heq]
            simp [slot_shift,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]
          rw [huframe r hout']
          apply update_other
          have ho := hout 0 (by simp only [List.length_cons]; omega)
          simpa [slot_shift] using ho

end RamLang.RegisterOnly
