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

theorem Step.relocate_body (h : Step p rho s t event) (he : BodyEmbedded p q base)
    (hc : p.PCRelocatable := by decide) :
    Step q rho (s.relocate base) (t.relocate base) event := by
  unfold Step step at h ⊢
  cases hi : p[s.pc]? with
  | none => simp [hi] at h
  | some i =>
    have hn : i ≠ .halt := by intro hh; simp [hi,hh] at h
    rw [show (s.relocate base).pc = base+s.pc from rfl, he _ _ hi hn]
    have hsafe := hc.fetch hi
    cases i <;> simp only [Instr.pcRelocatable, Bool.false_eq_true] at hsafe
    all_goals try contradiction
    all_goals simp only [hi, StepResult.next.injEq] at h
    all_goals try { cases h }
    all_goals rcases h with ⟨rfl,rfl⟩
    all_goals simp [Instr.relocate, State.relocate, State.put, Nat.add_assoc]
    split <;> rfl

theorem Steps.relocate_body (h : Steps p rho k s t log) (he : BodyEmbedded p q base)
    (hc : p.PCRelocatable := by decide) :
    Steps q rho k (s.relocate base) (t.relocate base) log := by
  induction h with
  | refl => exact .refl _
  | cons hs ht ih => exact .cons (hs.relocate_body he hc) ih

/-- The only register possibly changed by an instruction. -/
def Instr.destination : Instr R → Option (Reg R)
  | .mov r _ | .add r _ _ | .sub r _ _ | .mul r _ _ | .mod r _ _
  | .shr r _ _ | .load r _ | .rload r _ | .call r _ => some r
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

/-- A caller replaces every callee halt by a jump to the named continuation. -/
def HaltsTo (p q : Program R) (base continuation : Nat) : Prop :=
  ∀ pc, p[pc]? = some .halt → q[base+pc]? = some (.jump continuation)

theorem HaltsTo.of_check (p q : Program R) (base continuation : Nat)
    (h : ∀ pc : Fin p.size, p[pc.val]? = some .halt →
      q[base+pc.val]? = some (.jump continuation)) : HaltsTo p q base continuation := by
  intro pc hp
  obtain ⟨hb,_⟩ := Array.getElem?_eq_some_iff.mp hp
  exact h ⟨pc,hb⟩ hp

theorem halt_fetch (h : step p rho s = .halt) : p[s.pc]? = some .halt := by
  unfold step at h
  cases hi : p[s.pc]? with
  | none => simp [hi] at h
  | some i => cases i <;> simp_all

/-- Inlining a terminating callee charges the replacement jump exactly as its
standalone halt and returns the same registers, ordinary memory, and trace. -/
theorem TerminatesIn.call (h : TerminatesIn p rho s k t log)
    (he : BodyEmbedded p q base) (hh : HaltsTo p q base continuation)
    (hc : p.PCRelocatable := by decide) :
    Steps q rho k (s.relocate base) {t with pc := continuation} log := by
  obtain ⟨n,hk,hs,ht⟩ := h
  have hf := hh t.pc (halt_fetch ht)
  have hj : Step q rho (t.relocate base) {t with pc := continuation} none := by
    unfold Step step
    rw [show (t.relocate base).pc = base+t.pc from rfl,hf]
    rfl
  have hend : Steps q rho 1 (t.relocate base) {t with pc := continuation} [] :=
    .cons hj (.refl _)
  simpa [hk] using (hs.relocate_body he hc).trans hend

/-- A finite register-preservation check, reusable for each inlined routine. -/
theorem register_preserved_of_check (p : Program R) (r : Reg R)
    (h : ∀ pc : Fin p.size, p[pc.val].destination ≠ some r) :
    ∀ (pc : Nat) (i : Instr R), p[pc]? = some i → i.destination ≠ some r := by
  intro pc i hi
  obtain ⟨hb,he⟩ := Array.getElem?_eq_some_iff.mp hi
  simpa [he] using h ⟨pc,hb⟩

end WordRam
