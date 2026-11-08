import DataStructures.PerfectHash.Total.RootFallback

namespace PerfectHash.Total
open WordRam Bounded Construction.Registers Bounded.Registers

set_option maxRecDepth 50000
set_option maxHeartbeats 20000000

variable {w : Nat} {xs : List (Word w)} {l : Layout} {a : Word w} {b : Fin (rootSlots xs)} {s t : State w 64}

theorem child_setup_fallback (h : ChildSetup xs l a b s) (pc : Nat) (chosen : Word w) :
    ChildSetup xs l a b (fallbackState s pc chosen) := by
  have hg : Globals xs l (fallbackState s pc chosen).regs := by
    apply h.core.globals.frame
    intro r hh
    have hc : ∀ r : Reg 64, globalRegister r = true → r ≠ status ∧ r ≠ seed ∧ r ≠ fallbackMode := by decide
    obtain ⟨h1,h2,h3⟩ := hc r hh
    exact fallback_register s pc chosen r h1 h2 h3
  refine ⟨⟨hg,?_,?_,?_,?_,h.core.chain⟩,h.partial,?_,?_,?_,?_,h.storedShift,h.storedTable⟩
  all_goals rw [fallback_register s pc chosen _ (by decide) (by decide) (by decide)]
  · exact h.core.table
  · exact h.core.slots
  · exact h.core.shift
  · exact h.core.head
  · exact h.index
  · exact h.directory
  · exact h.endPointer
  · exact h.count

theorem child_setup_pc (h : ChildSetup xs l a b s) (pc : Nat) : ChildSetup xs l a b {s with pc := pc} :=
  ⟨⟨h.core.globals,h.core.table,h.core.slots,h.core.shift,h.core.head,h.core.chain⟩,
    h.partial,h.index,h.directory,h.endPointer,h.count,h.storedShift,h.storedTable⟩

/-- A rejected child trial has the same locality obligation as a successful one;
only its own allocated slots may have changed. -/
theorem child_setup_frame (ha : Admissible w xs.length l) (h : ChildSetup xs l a b s)
    (hc : ChildState xs l a b t) (hr : ∀ r, childStable r → t.regs r = s.regs r)
    (hf : ChildFrame xs l a b s.mem t.mem) : ChildSetup xs l a b t := by
  refine ⟨hc,h.partial.child_frame ha (by omega) hf,?_,?_,?_,?_,?_,?_⟩
  · rw [hr bucketIndex (by decide)]; exact h.index
  · rw [hr directoryCursor (by decide)]; exact h.directory
  · rw [hr tableEnd (by decide)]; exact h.endPointer
  · rw [hr childCount (by decide)]; exact h.count
  · rw [hf _ (Region.not_contains_of_separated (Packed.directory_table_separated _ _ b b)
      (Region.contains_index (directory_fit ha b) (by decide : 2 < 4)))]
    exact h.storedShift
  · rw [hf _ (Region.not_contains_of_separated (Packed.directory_table_separated _ _ b b)
      (Region.contains_index (directory_fit ha b) (by decide : 3 < 4)))]
    exact h.storedTable

structure ChildEnumeration (xs : List (Word w)) (l : Layout) (a : Word w)
    (b : Fin (rootSlots xs)) (i : Nat) (s : State w 64) : Prop where
  setup : ChildSetup xs l a b s
  pc : s.pc = Bounded.location .childTrial
  seed : s.regs Construction.Registers.seed = candidate w i
  trials : s.regs trialsLeft = word w 0
  stage : s.regs Bounded.Registers.stage = word w 1
  mode : s.regs fallbackMode = word w 1

theorem child_enumeration_contract (ha : Admissible w xs.length l) (rho : RandomMemory w) :
    SearchStepContract Total.program rho (candidate w) (childAccepted xs a b)
      (10*childCapacity xs a b+17*bucketCount xs a b+20) (policy w xs.length l)
      (ChildEnumeration xs l a b) (fun chosen t => ChildStagePost xs l a b (some chosen) t) := by
  constructor
  intro i s h
  have hone : word w 1 ≠ word w 0 := by
    have hf := ha.arithmetic.linearSizes
    intro he
    have := (word_eq_iff_of_lt (by omega : 1 < modulus w) (by omega : 0 < modulus w)).mp he
    omega
  obtain ⟨k,t,log,ht,hk,hpc,hcore,hstatus,hslots,hregs,hframe,hpol,hrandom⟩ :=
    child_trial ha h.setup.partial.accepted h.setup.core h.pc rho
  have hreg (r : Reg 64) (hr : 27 ≤ r.val) := hregs r (Or.inr (Or.inr (Or.inr (Or.inr hr))))
  have hsetup := child_setup_frame ha h.setup hcore (fun r hr => hreg r hr.1) hframe
  have hseed : t.regs seed = candidate w i := (hregs seed (Or.inl rfl)).trans h.seed
  have htrials : t.regs trialsLeft = word w 0 := (hreg trialsLeft (by decide)).trans h.trials
  have hstage : t.regs stage = word w 1 := (hreg stage (by decide)).trans h.stage
  have hmode : t.regs fallbackMode = word w 1 := (hreg fallbackMode (by decide)).trans h.mode
  rw [h.seed] at hstatus hslots
  cases hy : childAccepted xs a b (candidate w i)
  · have hn : t.regs status = word w 0 := by simpa [hy] using hstatus
    let v : State w 64 := {t with pc := Bounded.location .childChoose}
    have hnxt := child_next v rho rfl htrials hmode hstage hone
    have he : v.regs seed+word w 2 = candidate w (i+1) := by rw [show v.regs seed = candidate w i from hseed,candidate_next]
    rw [he] at hnxt
    have ht' := ((lift_steps ht).trans (lift_steps (child_no t rho hpc hn))).trans hnxt
    refine ⟨k+1+8,fallbackState v 188 (candidate w (i+1)),log,by simpa using ht',by omega,hpol,hrandom,?_⟩
    simp only [hy,Bool.false_eq_true,↓reduceIte]
    refine ⟨child_setup_fallback (child_setup_pc hsetup _) _ _,rfl,?_,?_,?_,?_⟩
    · simp [fallbackState,update,seed,fallbackMode]
    · rw [fallback_register v _ _ trialsLeft (by decide) (by decide) (by decide)]; exact htrials
    · rw [fallback_register v _ _ stage (by decide) (by decide) (by decide)]; exact hstage
    · simp [fallbackState,update]
  · refine ⟨k,t,log,lift_steps ht,by omega,hpol,hrandom,?_⟩
    simp only [hy,↓reduceIte,ChildStagePost]
    exact ⟨hsetup,hpc,by simpa [hy] using hstatus,hseed,trivial,hslots hy⟩

theorem child_fallback (ha : Admissible w xs.length l) (rho : RandomMemory w)
    (h : ChildSetup xs l a b s) (hp : s.pc = Bounded.location .childChoose)
    (hn : s.regs trialsLeft = word w 0) (hm : s.regs fallbackMode = word w 0)
    (hs : s.regs stage = word w 1) (hf : fallbackChoice (childAccepted xs a b) = some chosen) :
    ∃ k t log, Steps Total.program rho k s t log ∧
      k ≤ (10*childCapacity xs a b+17*bucketCount xs a b+30)*seedCount w ∧
      ChildStagePost xs l a b (some chosen) t ∧ (policy w xs.length l).AllowsTrace log ∧
      log.filterMap Access.randomAddress = [] := by
  have hone : word w 1 ≠ word w 0 := by
    have hh := ha.arithmetic.linearSizes
    intro he
    have := (word_eq_iff_of_lt (by omega : 1 < modulus w) (by omega : 0 < modulus w)).mp he
    omega
  let u := fallbackState s 188 (word w 1)
  have hu : ChildEnumeration xs l a b 0 u := by
    refine ⟨child_setup_fallback h _ _,rfl,?_,?_,?_,?_⟩
    · simp [u,fallbackState,update,seed,fallbackMode,candidate]
    · rw [fallback_register s _ _ trialsLeft (by decide) (by decide) (by decide)]; exact hn
    · rw [fallback_register s _ _ stage (by decide) (by decide) (by decide)]; exact hs
    · simp [u,fallbackState,update]
  obtain ⟨k,t,log,ht,hk,hpol,hr,hpost⟩ := (child_enumeration_contract (b := b) ha rho).run hu (seedCount w)
  have hfound : ChildStagePost xs l a b (some chosen) t := by
    simpa only [Nat.zero_add,show FiniteProbability.Retry.find (childAccepted xs a b) (seedCount w)
      (fun i => candidate w i.val) = some chosen from hf] using hpost
  refine ⟨8+k,t,log,by simpa using (child_first s rho hp hn hm hs hone).trans ht,?_,hfound,hpol,hr⟩
  have hpos := seed_count_pos w
  nlinarith

end PerfectHash.Total
