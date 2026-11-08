import DataStructures.PerfectHash.Total.Blocks
import DataStructures.PerfectHash.Total.Selection
import WordRam.DeterministicSearch

namespace PerfectHash.Total
open WordRam Bounded Construction.Registers Bounded.Registers

set_option maxRecDepth 50000
set_option maxHeartbeats 20000000

variable {w : Nat} {xs : List (Word w)} {l : Layout} {s : State w 64}

theorem fallback_register (s : State w 64) (pc : Nat) (a : Word w) (r : Reg 64)
    (hs : r ≠ status) (ha : r ≠ seed) (hm : r ≠ fallbackMode) :
    (fallbackState s pc a).regs r = s.regs r := by simp [fallbackState,update,hs,ha,hm]

theorem root_state_fallback (h : RootState xs l s) (pc : Nat) (a : Word w) :
    RootState xs l (fallbackState s pc a) := by
  refine ⟨h.globals.frame ?_,?_,h.array⟩
  · intro r hr
    have hc : ∀ r : Reg 64, globalRegister r = true → r ≠ status ∧ r ≠ seed ∧ r ≠ fallbackMode := by decide
    obtain ⟨hs,ha,hm⟩ := hc r hr
    exact fallback_register s pc a r hs ha hm
  · rw [fallback_register s pc a shift (by decide) (by decide) (by decide)]
    exact h.shift

/-- The deterministic loop's ghost index describes the multiplier in register 5;
it is not an extra RAM input or an allocated enumeration array. -/
structure RootEnumeration (xs : List (Word w)) (l : Layout) (i : Nat) (s : State w 64) : Prop where
  core : RootState xs l s
  pc : s.pc = Bounded.location .rootTrial
  seed : s.regs Construction.Registers.seed = candidate w i
  trials : s.regs trialsLeft = word w 0
  stage : s.regs Bounded.Registers.stage = word w 0
  mode : s.regs fallbackMode = word w 1

theorem root_enumeration_contract (ha : Admissible w xs.length l) (rho : RandomMemory w) :
    SearchStepContract Total.program rho (candidate w) (rootAccepted xs)
      (20*rootSlots xs+25*(values xs).length+20) (policy w xs.length l)
      (RootEnumeration xs l) (fun a t => RootFound xs l t.regs a t) := by
  constructor
  intro i s h
  have hone : word w 1 ≠ word w 0 := by
    have hf := ha.arithmetic.linearSizes
    intro he
    have := (word_eq_iff_of_lt (by omega : 1 < modulus w) (by omega : 0 < modulus w)).mp he
    omega
  obtain ⟨k,t,log,ht,hk,hpc,hcore,hstatus,hgroup,hregs,hpol,hrandom⟩ := root_trial ha h.core h.pc rho
  have hseed : t.regs seed = candidate w i := (hregs seed (Or.inl rfl)).trans h.seed
  have htrials : t.regs trialsLeft = word w 0 := (hregs trialsLeft (by right; right; decide)).trans h.trials
  have hstage : t.regs stage = word w 0 := (hregs stage (by right; right; decide)).trans h.stage
  have hmode : t.regs fallbackMode = word w 1 := (hregs fallbackMode (by right; right; decide)).trans h.mode
  rw [h.seed] at hstatus hgroup
  cases hy : rootAccepted xs (candidate w i)
  · have hn : t.regs status ≠ word w 1 := by
      simpa [hstatus,hy] using Ne.symm hone
    let v : State w 64 := {t with pc := Bounded.location .rootChoose}
    have hnxt := root_next v rho rfl htrials hmode hstage hone
    have he : v.regs seed+word w 2 = candidate w (i+1) := by rw [show v.regs seed = candidate w i from hseed,candidate_next]
    rw [he] at hnxt
    have ht' := ((lift_steps ht).trans (lift_steps (root_no t rho hpc hn))).trans hnxt
    refine ⟨k+2+7,fallbackState v 93 (candidate w (i+1)),log,by simpa using ht',by omega,hpol,hrandom,?_⟩
    simp only [hy,Bool.false_eq_true,↓reduceIte]
    refine ⟨root_state_fallback (s := v) ⟨hcore.globals,hcore.shift,hcore.array⟩ _ _,rfl,?_,?_,?_,?_⟩
    · simp [fallbackState,update,seed,fallbackMode]
    · rw [fallback_register v _ _ trialsLeft (by decide) (by decide) (by decide)]; exact htrials
    · rw [fallback_register v _ _ stage (by decide) (by decide) (by decide)]; exact hstage
    · simp [fallbackState,update]
  · have hy' : t.regs status = word w 1 := by simpa [hy] using hstatus
    refine ⟨k+1,{t with pc := Bounded.location .rootAccepted},log,
      by simpa using (lift_steps ht).trans (lift_steps (root_yes t rho hpc hy')),by omega,hpol,hrandom,?_⟩
    simp only [hy,↓reduceIte]
    exact ⟨⟨hcore.globals,hcore.shift,hcore.array⟩,rfl,hseed,hy,hgroup hy,by intros; rfl⟩

/-- Exhaustion enters the verified enumeration, with no further random reads.
The cost includes entry and every rejected deterministic trial. -/
theorem root_fallback (ha : Admissible w xs.length l) (rho : RandomMemory w)
    (h : RootSearchState xs l rs c 0 s) (hm : s.regs fallbackMode = word w 0)
    (hs : s.regs stage = word w 0) (hf : fallbackChoice (rootAccepted xs) = some a) :
    ∃ k t log, Steps Total.program rho k s t log ∧
      k ≤ (20*rootSlots xs+25*(values xs).length+30)*seedCount w ∧
      RootFound xs l t.regs a t ∧ (policy w xs.length l).AllowsTrace log ∧
      log.filterMap Access.randomAddress = [] := by
  let u := fallbackState s 93 (word w 1)
  have hu : RootEnumeration xs l 0 u := by
    refine ⟨root_state_fallback h.core _ _,rfl,?_,?_,?_,?_⟩
    · simp [u,fallbackState,update,seed,fallbackMode,candidate]
    · rw [fallback_register s _ _ trialsLeft (by decide) (by decide) (by decide)]; exact h.trials
    · rw [fallback_register s _ _ stage (by decide) (by decide) (by decide)]; exact hs
    · simp [u,fallbackState,update]
  obtain ⟨k,t,log,ht,hk,hpol,hr,hpost⟩ := (root_enumeration_contract ha rho).run hu (seedCount w)
  have hfound : RootFound xs l t.regs a t := by
    simpa only [Nat.zero_add,show FiniteProbability.Retry.find (rootAccepted xs) (seedCount w)
      (fun i => candidate w i.val) = some a from hf] using hpost
  refine ⟨7+k,t,log,by simpa using (root_first s rho h.pc h.trials hm hs).trans ht,?_,hfound,hpol,hr⟩
  have hp := seed_count_pos w
  nlinarith

end PerfectHash.Total
