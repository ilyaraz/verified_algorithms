import WordRam.Assembly

namespace WordRam

/-- A continuing instruction may be embedded while each halt is replaced by a
caller continuation. This relation preserves all charged pre-halt work. -/
def BodyEmbedded (p q : Program R) (base : Nat) : Prop :=
  ∀ pc i, p[pc]? = some i → i ≠ .halt → q[base+pc]? = some (i.relocate base)

/-- Finite fetch checking suffices to certify an embedding into surrounding code. -/
theorem BodyEmbedded.of_check (p q : Program R) (base : Nat)
    (h : ∀ pc : Fin p.size, ∀ i ∈ p[pc.val]?,
      i ≠ .halt → q[base+pc.val]? = some (i.relocate base)) : BodyEmbedded p q base := by
  intro pc i hi hn
  obtain ⟨hb,_⟩ := Array.getElem?_eq_some_iff.mp hi
  exact h ⟨pc,hb⟩ i hi hn

variable {w R : Nat} {p q : Program R} {rho : RandomMemory w}
  {s t : State w R} {base : Nat} {r : Reg R}

theorem Step.relocate_body (h : Step p rho s t event) (he : BodyEmbedded p q base) :
    Step q rho (s.relocate base) (t.relocate base) event := by
  unfold Step step at h ⊢
  cases hi : p[s.pc]? with
  | none => simp [hi] at h
  | some i =>
    have hn : i ≠ .halt := by intro hh; simp [hi,hh] at h
    rw [show (s.relocate base).pc = base+s.pc from rfl, he _ _ hi hn]
    cases i <;> simp only [hi, StepResult.next.injEq] at h
    all_goals try { cases h }
    all_goals rcases h with ⟨rfl,rfl⟩
    all_goals simp [Instr.relocate, State.relocate, State.put, Nat.add_assoc]
    split <;> rfl

theorem Steps.relocate_body (h : Steps p rho k s t log) (he : BodyEmbedded p q base) :
    Steps q rho k (s.relocate base) (t.relocate base) log := by
  induction h with
  | refl => exact .refl _
  | cons hs ht ih => exact .cons (hs.relocate_body he) ih

/-- The only register possibly changed by an instruction. -/
def Instr.destination : Instr R → Option (Reg R)
  | .mov r _ | .add r _ _ | .sub r _ _ | .mul r _ _ | .mod r _ _
  | .shr r _ _ | .load r _ | .rload r _ => some r
  | _ => none

theorem Step.register_frame (h : Step p rho s t event)
    (hr : ∀ (pc : Nat) (i : Instr R), p[pc]? = some i → i.destination ≠ some r) : t.regs r = s.regs r := by
  unfold Step step at h
  cases hi : p[s.pc]? with
  | none => simp [hi] at h
  | some i =>
    have hn := hr _ _ hi
    cases i <;> simp only [hi,StepResult.next.injEq] at h
    all_goals try { cases h }
    all_goals rcases h with ⟨rfl,rfl⟩
    all_goals simp_all [Instr.destination,State.put,update,Ne.symm]

theorem Steps.register_frame (h : Steps p rho k s t log)
    (hr : ∀ (pc : Nat) (i : Instr R), p[pc]? = some i → i.destination ≠ some r) : t.regs r = s.regs r := by
  induction h with
  | refl => rfl
  | cons hs ht ih => exact ih.trans (hs.register_frame hr)

theorem TerminatesIn.register_frame (h : TerminatesIn p rho s k t log)
    (hr : ∀ (pc : Nat) (i : Instr R), p[pc]? = some i → i.destination ≠ some r) : t.regs r = s.regs r :=
  h.choose_spec.2.1.register_frame hr

/-- Compose a continuing block with a terminating continuation, charging its halt. -/
theorem Steps.then_terminates (h : Steps p rho k s t log)
    (ht : TerminatesIn p rho t l u tail) : TerminatesIn p rho s (k+l) u (log++tail) := by
  obtain ⟨n,hl,hs,hh⟩ := ht
  exact ⟨k+n,by omega,h.trans hs,hh⟩

end WordRam
