import DataStructures.PerfectHash.Bounded.RootTrial
import WordRam.BoundedRetry

namespace PerfectHash.Bounded
open WordRam Construction.Registers Registers

set_option maxRecDepth 50000
set_option maxHeartbeats 20000000

def sampleAt (rho : RandomMemory w) (c : Nat) : Word w :=
  Hashing.MultiplyShift.sample (rho (word w c))

structure RootSearchState (xs : List (Word w)) (l : Layout) (rs : WordRam.Registers w 64)
    (c n : Nat) (s : State w 64) : Prop where
  core : RootState xs l s
  pc : s.pc = location .rootChoose
  trials : s.regs trialsLeft = word w n
  cursor : s.regs randomCursor = word w c
  lower : l.randomBase ≤ c
  upper : c+n ≤ l.randomBase+randomCapacity w xs.length
  registers : ∀ r : Reg 64, 34 ≤ r.val → s.regs r = rs r

structure RootFound (xs : List (Word w)) (l : Layout) (rs : WordRam.Registers w 64)
    (a : Word w) (s : State w 64) : Prop where
  core : RootState xs l s
  pc : s.pc = location .rootAccepted
  seed : s.regs Construction.Registers.seed = a
  accepted : rootAccepted xs a = true
  grouped : Construction.Grouped (rootHash xs a) (l.outputBase+4) l.scratchBase (values xs).reverse s.mem
  registers : ∀ r : Reg 64, 34 ≤ r.val → s.regs r = rs r

variable {w : Nat} {xs : List (Word w)} {l : Layout} {s : State w 64}

theorem sampled_register (rho : RandomMemory w) (s : State w 64) (pc : Nat) (r : Reg 64)
    (ht : r ≠ temp) (hs : r ≠ seed) (hc : r ≠ randomCursor) (hn : r ≠ trialsLeft) :
    (sampled rho s pc).regs r = s.regs r := by simp [sampled,update,ht,hs,hc,hn]

theorem RootState.sampled (h : RootState xs l s) (rho : RandomMemory w) (pc : Nat) :
    RootState xs l (sampled rho s pc) := by
  refine ⟨h.globals.frame ?_,?_,h.array⟩
  · intro r hr
    have hc : ∀ r : Reg 64, globalRegister r = true →
        r ≠ temp ∧ r ≠ seed ∧ r ≠ randomCursor ∧ r ≠ trialsLeft := by decide
    obtain ⟨ht,hs,hc,hn⟩ := hc r hr
    exact sampled_register rho s pc r ht hs hc hn
  · rw [sampled_register rho s pc Construction.Registers.shift (by decide) (by decide) (by decide) (by decide)]
    exact h.shift

theorem sample_policy (ha : Admissible w xs.length l) (hc : s.regs randomCursor = word w c)
    (hl : l.randomBase ≤ c) (hu : c < l.randomBase+randomCapacity w xs.length) :
    (policy w xs.length l).AllowsTrace (sampleTrace rho s) := by
  have hf := ha.random
  change l.randomBase+randomCapacity w xs.length < modulus w at hf
  intro e he
  simp only [sampleTrace,List.mem_singleton] at he
  subst e
  change (l.random w xs.length).Contains (s.regs randomCursor)
  simp only [hc,Layout.random,Region.Contains,word_toNat_of_lt (by omega : c < modulus w)]
  omega

theorem root_retry_contract (ha : Admissible w xs.length l) (rho : RandomMemory w)
    (rs : WordRam.Registers w 64) :
    RetryStepContract program rho (sampleAt rho) (rootAccepted xs)
      (20*rootSlots xs+25*(values xs).length+20) (policy w xs.length l)
      (RootSearchState xs l rs) (RootFound xs l rs) := by
  constructor
  intro c n s h
  have hf := ha.random
  change l.randomBase+randomCapacity w xs.length < modulus w at hf
  have hnfit : n+1 < modulus w := by have := h.upper; omega
  have hone : 1 < modulus w := by omega
  have hn : s.regs trialsLeft ≠ word w 0 := by
    rw [h.trials]
    intro he
    have := (word_eq_iff_of_lt hnfit (by omega : 0 < modulus w)).mp he
    omega
  let v := sampled rho s (location .rootTrial)
  have hc : s.regs (33 : Reg 64) = word w c := h.cursor
  have hvseed : v.regs seed = sampleAt rho c := by
    simp [v,sampled,update,trialsLeft,randomCursor,seed,hc,sampleAt]
  have hvcount : v.regs trialsLeft = word w n := by
    simp only [v,sampled,update_same,h.trials]
    rw [word_sub (n+1) 1 hone (by omega)]
    simp
  have hvcursor : v.regs randomCursor = word w (c+1) := by
    simp [v,sampled,update,trialsLeft,randomCursor,hc,word_add]
  have hvreg (r : Reg 64) (hr : 34 ≤ r.val) : v.regs r = rs r := by
    rw [sampled_register rho s _ r (by intro he; subst r; simp [temp] at hr)
      (by intro he; subst r; simp [seed] at hr)
      (by intro he; subst r; simp [randomCursor] at hr)
      (by intro he; subst r; simp [trialsLeft] at hr)]
    exact h.registers r hr
  obtain ⟨k,t,log,ht,hk,hpc,hcore,hstatus,hgroup,hregs,hpolicy,hrandom⟩ :=
    root_trial ha (h.core.sampled rho _) (s := v) rfl rho
  rw [hvseed] at hstatus hgroup
  have hprefix := (root_sample s rho h.pc hn).trans ht
  have hprefixPolicy : (policy w xs.length l).AllowsTrace (sampleTrace rho s++log) :=
    (AccessPolicy.allowsTrace_append _).mpr
      ⟨sample_policy ha h.cursor h.lower (by have := h.upper; omega),hpolicy⟩
  have hprefixRandom : (sampleTrace rho s++log).filterMap Access.randomAddress = [word w c] := by
    simp [List.filterMap_append,hrandom,sampleTrace,Access.randomAddress,h.cursor]
  have htreg (r : Reg 64) (hr : 34 ≤ r.val) : t.regs r = rs r :=
    (hregs r (Or.inr (Or.inr (by omega)))).trans (hvreg r hr)
  cases hy : rootAccepted xs (sampleAt rho c)
  · have hno : t.regs status ≠ word w 1 := by
      rw [hstatus,hy]
      simp only [Bool.toNat_false]
      intro he
      have := (word_eq_iff_of_lt (by omega : 0 < modulus w) hone).mp he
      omega
    refine ⟨7+k+2,{t with pc := location .rootChoose},sampleTrace rho s++log,
      by simpa using hprefix.trans (root_no t rho hpc hno),by omega,hprefixPolicy,hprefixRandom,?_⟩
    simp only [hy,Bool.false_eq_true,↓reduceIte]
    refine ⟨⟨hcore.globals,hcore.shift,hcore.array⟩,rfl,?_,?_,by have := h.lower; omega,by have := h.upper; omega,htreg⟩
    · exact (hregs trialsLeft (Or.inr (Or.inr (by decide)))).trans hvcount
    · exact (hregs randomCursor (Or.inr (Or.inr (by decide)))).trans hvcursor
  · have hyes : t.regs status = word w 1 := by simpa [hy] using hstatus
    refine ⟨7+k+1,{t with pc := location .rootAccepted},sampleTrace rho s++log,
      by simpa using hprefix.trans (root_yes t rho hpc hyes),by omega,hprefixPolicy,hprefixRandom,?_⟩
    simp only [hy,↓reduceIte]
    exact ⟨⟨hcore.globals,hcore.shift,hcore.array⟩,rfl,(hregs seed (Or.inl rfl)).trans hvseed,hy,hgroup hy,htreg⟩

/-- End-to-end root retries expose precisely the prefix tested by the abstract
finite search. Exhaustion returns at the budget guard for the caller to handle. -/
theorem root_search (ha : Admissible w xs.length l) (rho : RandomMemory w)
    (h : RootSearchState xs l rs c n s) :
    ∃ k t log, Steps program rho k s t log ∧
      k ≤ (20*rootSlots xs+25*(values xs).length+20) *
        FiniteProbability.Retry.attempts (rootAccepted xs) n (fun i => sampleAt rho (c+i.val)) ∧
      (policy w xs.length l).AllowsTrace log ∧
      log.filterMap Access.randomAddress = consecutiveAddresses w c
        (FiniteProbability.Retry.attempts (rootAccepted xs) n (fun i => sampleAt rho (c+i.val))) ∧
      match FiniteProbability.Retry.find (rootAccepted xs) n (fun i => sampleAt rho (c+i.val)) with
      | none => RootSearchState xs l rs (c+n) 0 t
      | some a => RootFound xs l rs a t := by
  obtain ⟨k,t,log,ht,hk,hp,hr,hpost⟩ := (root_retry_contract ha rho rs).run h
  refine ⟨k,t,log,ht,hk,hp,hr,?_⟩
  cases he : FiniteProbability.Retry.find (rootAccepted xs) n (fun i => sampleAt rho (c+i.val)) <;>
    simpa only [he] using hpost

theorem RootReady.search_state (ha : Admissible w xs.length l) (h : RootReady xs l s) :
    RootSearchState xs l s.regs (l.randomBase+1) w s := by
  refine ⟨⟨h.globals,h.shift,h.array⟩,h.pc,h.trials,h.cursor,by omega,?_,by intros; rfl⟩
  have hh : w ≤ w*(bucketCapacity xs.length+1) := by
    exact Nat.le_mul_of_pos_right w (by omega)
  unfold randomCapacity
  omega

end PerfectHash.Bounded
