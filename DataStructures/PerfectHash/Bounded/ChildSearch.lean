import DataStructures.PerfectHash.Bounded.ChildTrial
import DataStructures.PerfectHash.Bounded.RootSearch

namespace PerfectHash.Bounded
open WordRam Construction.Registers Registers

set_option maxRecDepth 50000
set_option maxHeartbeats 20000000

def ChildFrame (xs : List (Word w)) (l : Layout) (a : Word w) (b : Fin (rootSlots xs))
    (mem mem' : DataMemory w) : Prop :=
  ∀ addr, ¬ (Region.mk (Packed.table l.outputBase (childCapacity xs a) b) (2*childCapacity xs a b)).Contains addr →
    mem' addr = mem addr

/-- Allocation and outer-loop registers excluded from sampler temporaries. -/
def childStable (r : Reg 64) : Prop := 27 ≤ r.val ∧ r ≠ trialsLeft ∧ r ≠ randomCursor

instance childStableDecidable (r : Reg 64) : Decidable (childStable r) :=
  inferInstanceAs (Decidable (27 ≤ r.val ∧ r ≠ trialsLeft ∧ r ≠ randomCursor))

structure ChildSearchState (xs : List (Word w)) (l : Layout) (a : Word w) (b : Fin (rootSlots xs))
    (rs : WordRam.Registers w 64) (mem : DataMemory w) (c n : Nat) (s : State w 64) : Prop where
  core : ChildState xs l a b s
  pc : s.pc = location .childChoose
  trials : s.regs trialsLeft = word w n
  cursor : s.regs randomCursor = word w c
  lower : l.randomBase ≤ c
  upper : c+n ≤ l.randomBase+randomCapacity w xs.length
  registers : ∀ r : Reg 64, childStable r → s.regs r = rs r
  frame : ChildFrame xs l a b mem s.mem

structure ChildFound (xs : List (Word w)) (l : Layout) (a : Word w) (b : Fin (rootSlots xs))
    (rs : WordRam.Registers w 64) (mem : DataMemory w) (chosen : Word w) (s : State w 64) : Prop where
  core : ChildState xs l a b s
  pc : s.pc = location .childResult
  status : s.regs Construction.Registers.status = word w 1
  seed : s.regs Construction.Registers.seed = chosen
  accepted : childAccepted xs a b chosen = true
  slots : Construction.SlotsAt (childHash w (bucketCount xs a b) chosen) (childCapacity xs a b)
    (Packed.table l.outputBase (childCapacity xs a) b) (bucketKeys xs a b).reverse s.mem
  registers : ∀ r : Reg 64, childStable r → s.regs r = rs r
  frame : ChildFrame xs l a b mem s.mem

variable {w : Nat} {xs : List (Word w)} {l : Layout} {a : Word w} {b : Fin (rootSlots xs)} {s : State w 64}

theorem ChildState.sampled (h : ChildState xs l a b s) (rho : RandomMemory w) (pc : Nat) :
    ChildState xs l a b (sampled rho s pc) := by
  refine ⟨h.globals.frame ?_,?_,?_,?_,?_,h.chain⟩
  · intro r hr
    have hc : ∀ r : Reg 64, globalRegister r = true →
        r ≠ temp ∧ r ≠ seed ∧ r ≠ randomCursor ∧ r ≠ trialsLeft := by decide
    obtain ⟨ht,hs,hc,hn⟩ := hc r hr
    exact sampled_register rho s pc r ht hs hc hn
  · rw [sampled_register rho s pc Construction.Registers.table (by decide) (by decide) (by decide) (by decide)]
    exact h.table
  · rw [sampled_register rho s pc Construction.Registers.slots (by decide) (by decide) (by decide) (by decide)]
    exact h.slots
  · rw [sampled_register rho s pc Construction.Registers.shift (by decide) (by decide) (by decide) (by decide)]
    exact h.shift
  · rw [sampled_register rho s pc rootHead (by decide) (by decide) (by decide) (by decide)]
    exact h.head

theorem child_retry_contract (ha : Admissible w xs.length l) (hy : rootAccepted xs a = true)
    (rho : RandomMemory w) (rs : WordRam.Registers w 64) (mem : DataMemory w) :
    RetryStepContract program rho (sampleAt rho) (childAccepted xs a b)
      (10*childCapacity xs a b+17*bucketCount xs a b+20) (policy w xs.length l)
      (ChildSearchState xs l a b rs mem) (ChildFound xs l a b rs mem) := by
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
  let v := sampled rho s (location .childTrial)
  have hc : s.regs (33 : Reg 64) = word w c := h.cursor
  have hvseed : v.regs seed = sampleAt rho c := by
    simp [v,sampled,update,trialsLeft,randomCursor,seed,hc,sampleAt]
  have hvcount : v.regs trialsLeft = word w n := by
    simp only [v,sampled,update_same,h.trials]
    rw [word_sub (n+1) 1 hone (by omega)]
    simp
  have hvcursor : v.regs randomCursor = word w (c+1) := by
    simp [v,sampled,update,trialsLeft,randomCursor,hc,word_add]
  have hvreg (r : Reg 64) (hr : childStable r) : v.regs r = rs r := by
    rw [sampled_register rho s _ r (by intro he; subst r; simp [temp,childStable] at hr)
      (by intro he; subst r; simp [seed,childStable] at hr) hr.2.2 hr.2.1]
    exact h.registers r hr
  obtain ⟨k,t,log,ht,hk,hpc,hcore,hstatus,hslots,hregs,hframe,hpolicy,hrandom⟩ :=
    child_trial ha hy (h.core.sampled rho _) (s := v) rfl rho
  rw [hvseed] at hstatus hslots
  have hprefix := (child_sample s rho h.pc hn).trans ht
  have hprefixPolicy : (policy w xs.length l).AllowsTrace (sampleTrace rho s++log) :=
    (AccessPolicy.allowsTrace_append _).mpr
      ⟨sample_policy ha h.cursor h.lower (by have := h.upper; omega),hpolicy⟩
  have hprefixRandom : (sampleTrace rho s++log).filterMap Access.randomAddress = [word w c] := by
    simp [hrandom,sampleTrace,Access.randomAddress,h.cursor]
  have htreg (r : Reg 64) (hr : childStable r) : t.regs r = rs r :=
    (hregs r (Or.inr (Or.inr (Or.inr (Or.inr hr.1))))).trans (hvreg r hr)
  have htframe : ChildFrame xs l a b mem t.mem := fun addr hh =>
    (hframe addr hh).trans (h.frame addr hh)
  cases hg : childAccepted xs a b (sampleAt rho c)
  · have hno : t.regs status = word w 0 := by simpa [hg] using hstatus
    refine ⟨8+k+1,{t with pc := location .childChoose},sampleTrace rho s++log,
      by simpa using hprefix.trans (child_no t rho hpc hno),by omega,hprefixPolicy,hprefixRandom,?_⟩
    simp only [Bool.false_eq_true,↓reduceIte]
    refine ⟨⟨hcore.globals,hcore.table,hcore.slots,hcore.shift,hcore.head,hcore.chain⟩,rfl,?_,?_,
      by have := h.lower; omega,by have := h.upper; omega,htreg,htframe⟩
    · exact (hregs trialsLeft (Or.inr (Or.inr (Or.inr (Or.inr (by decide)))))).trans hvcount
    · exact (hregs randomCursor (Or.inr (Or.inr (Or.inr (Or.inr (by decide)))))).trans hvcursor
  · have hyes : t.regs status = word w 1 := by simpa [hg] using hstatus
    refine ⟨8+k,t,sampleTrace rho s++log,hprefix,by omega,hprefixPolicy,hprefixRandom,?_⟩
    simp only [↓reduceIte]
    exact ⟨hcore,hpc,hyes,(hregs seed (Or.inl rfl)).trans hvseed,hg,hslots hg,htreg,htframe⟩

/-- A direct bucket cannot collide and therefore needs no random read. -/
theorem child_direct_accepted (ha : Admissible w xs.length l) (hb : bucketCount xs a b ≤ 1) (chosen : Word w) :
    childAccepted xs a b chosen = true := by
  unfold childAccepted
  rw [Construction.childAccepted_iff _ _ _ (by simp)]
  simp only [List.append_nil,List.map_reverse,List.nodup_reverse]
  have hl : (bucketKeys xs a b).length ≤ 1 := by rw [bucket_length]; exact hb
  have hl' : ((bucketKeys xs a b).map (childHash w (bucketCount xs a b) chosen)).length ≤ 1 := by
    simpa using hl
  generalize he : (bucketKeys xs a b).map (childHash w (bucketCount xs a b) chosen) = ys at hl' ⊢
  cases ys with
  | nil => simp
  | cons x ys =>
    have hy : ys = [] := List.length_eq_zero.mp (by simp only [List.length_cons] at hl'; omega)
    simp [hy]

end PerfectHash.Bounded
