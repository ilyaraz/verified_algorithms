import DataStructures.PerfectHash.Bounded.ChildCompletion

namespace PerfectHash.Bounded
open WordRam Construction.Registers Registers

set_option maxRecDepth 50000
set_option maxHeartbeats 20000000

def childRandomBase (l : Layout) (w j : Nat) : Nat := l.randomBase+1+w*(j+1)

def childSamples (xs : List (Word w)) (l : Layout) (b : Fin (rootSlots xs)) (rho : RandomMemory w) : Fin w → Word w :=
  fun i => sampleAt rho (childRandomBase l w b.val+i.val)

def childChoice (xs : List (Word w)) (l : Layout) (a : Word w) (b : Fin (rootSlots xs)) (rho : RandomMemory w) : Option (Word w) :=
  if bucketCount xs a b ≤ 1 then some (word w 1)
  else FiniteProbability.Retry.find (childAccepted xs a b) w (childSamples xs l b rho)

def childAttempts (xs : List (Word w)) (l : Layout) (a : Word w) (b : Fin (rootSlots xs)) (rho : RandomMemory w) : Nat :=
  if bucketCount xs a b ≤ 1 then 1
  else FiniteProbability.Retry.attempts (childAccepted xs a b) w (childSamples xs l b rho)

def childReads (xs : List (Word w)) (l : Layout) (a : Word w) (b : Fin (rootSlots xs)) (rho : RandomMemory w) : Nat :=
  if bucketCount xs a b ≤ 1 then 0
  else FiniteProbability.Retry.attempts (childAccepted xs a b) w (childSamples xs l b rho)

def ChildStagePost (xs : List (Word w)) (l : Layout) (a : Word w) (b : Fin (rootSlots xs))
    (choice : Option (Word w)) (s : State w 64) : Prop :=
  ChildSetup xs l a b s ∧ match choice with
  | none => s.pc = location .childChoose ∧ s.regs trialsLeft = word w 0 ∧
      s.regs stage = word w 1 ∧ s.regs fallbackMode = word w 0
  | some chosen => s.pc = location .childResult ∧ s.regs status = word w 1 ∧ s.regs seed = chosen ∧
      childAccepted xs a b chosen = true ∧
      Construction.SlotsAt (childHash w (bucketCount xs a b) chosen) (childCapacity xs a b)
        (Packed.table l.outputBase (childCapacity xs a) b) (bucketKeys xs a b).reverse s.mem

variable {w : Nat} {xs : List (Word w)} {l : Layout} {a : Word w} {b : Fin (rootSlots xs)} {s : State w 64}

theorem ChildSearchState.setup (h : ChildSearchState xs l a b s.regs s.mem c n t)
    (ha : Admissible w xs.length l) (hs : ChildSetup xs l a b s) : ChildSetup xs l a b t := by
  refine ⟨h.core,hs.partial.child_frame ha (by omega) h.frame,?_,?_,?_,?_,?_,?_⟩
  · rw [h.registers bucketIndex (by decide)]; exact hs.index
  · rw [h.registers directoryCursor (by decide)]; exact hs.directory
  · rw [h.registers tableEnd (by decide)]; exact hs.endPointer
  · rw [h.registers childCount (by decide)]; exact hs.count
  · rw [h.frame _ (Region.not_contains_of_separated (Packed.directory_table_separated _ _ b b)
      (Region.contains_index (directory_fit ha b) (by decide : 2 < 4)))]
    exact hs.storedShift
  · rw [h.frame _ (Region.not_contains_of_separated (Packed.directory_table_separated _ _ b b)
      (Region.contains_index (directory_fit ha b) (by decide : 3 < 4)))]
    exact hs.storedTable

theorem child_random_block (b : Fin (rootSlots xs)) :
    childRandomBase l w b.val+w ≤ l.randomBase+randomCapacity w xs.length := by
  have hd := values_length_le xs
  have hm := root_slots_bound xs
  have hb := b.isLt
  have hi : b.val+2 ≤ bucketCapacity xs.length+1 := by unfold bucketCapacity; omega
  have hh := Nat.mul_le_mul_left w hi
  unfold childRandomBase randomCapacity
  nlinarith

theorem allocated_search_state (h : ChildSetup xs l a b s) :
    ChildSearchState xs l a b (allocatedState s (location .childChoose)).regs s.mem
      (childRandomBase l w b.val) w (allocatedState s (location .childChoose)) := by
  have hi : s.regs (39 : Reg 64) = word w b.val := h.index
  have hw : s.regs (61 : Reg 64) = word w w := h.core.globals.saved.width
  have hr : s.regs (60 : Reg 64) = word w l.randomBase := h.core.globals.saved.random
  refine ⟨(h.allocated _).core,rfl,?_,?_,?_,child_random_block b,by intros; rfl,by intro addr hh; rfl⟩
  · simp [allocatedState,update,trialsLeft,temp,randomCursor,stage,fallbackMode,machineWidth,hw]
  · simp [allocatedState,update,randomCursor,stage,fallbackMode,randomBase,bucketIndex,machineWidth,
      hr,hi,hw,word_add,word_mul,childRandomBase,Nat.mul_comm,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc]
  · unfold childRandomBase; omega

/-- A complete bounded child search, with a deterministic direct path for zero
or one key. On exhaustion the budget guard is the explicit continuation point. -/
theorem child_stage (ha : Admissible w xs.length l) (h : ChildSetup xs l a b s)
    (hp : s.pc = location .allocated) (rho : RandomMemory w) :
    ∃ k t log, Steps program rho k s t log ∧
      k ≤ 9+(10*childCapacity xs a b+17*bucketCount xs a b+20)*childAttempts xs l a b rho ∧
      (policy w xs.length l).AllowsTrace log ∧
      log.filterMap Access.randomAddress = consecutiveAddresses w (childRandomBase l w b.val) (childReads xs l a b rho) ∧
      ChildStagePost xs l a b (childChoice xs l a b rho) t := by
  have hfit := bucket_fit ha h.partial.accepted b
  have hone : 1 < modulus w := by have := ha.arithmetic.linearSizes; omega
  by_cases hd : bucketCount xs a b ≤ 1
  · let v := allocatedState s (location .directChild)
    let u := directState v
    have hv := h.allocated (location .directChild)
    have hu := hv.direct
    have hpre := (allocated_direct s rho hp (by rw [h.count,word_toNat_of_lt hfit.1,word_toNat_of_lt hone]; exact hd)).trans
      (direct_child v rho rfl)
    obtain ⟨k,t,log,ht,hk,hpc,hcore,hstatus,hslots,hregs,hframe,hpol,hrandom⟩ :=
      child_trial ha h.partial.accepted (s := u) hu.core rfl rho
    have hseed : u.regs seed = word w 1 := by simp [u,directState,update]
    have hg := child_direct_accepted ha hd (word w 1)
    have hfound : ChildFound xs l a b v.regs v.mem (word w 1) t := by
      refine ⟨hcore,hpc,?_,?_,hg,?_,?_,hframe⟩
      · simpa [hseed,hg] using hstatus
      · exact (hregs seed (Or.inl rfl)).trans hseed
      · simpa [hseed] using hslots (by simpa [hseed] using hg)
      · intro r hr
        rw [hregs r (Or.inr (Or.inr (Or.inr (Or.inr hr.1))))]
        have hn : r ≠ seed := by intro he; subst r; simp [childStable,seed] at hr
        simp [u,directState,update,hn]
    refine ⟨9+k,t,log,by simpa using hpre.trans ht,?_,hpol,?_,?_⟩
    · simp only [childAttempts,hd,↓reduceIte,Nat.mul_one]; omega
    · simpa [childReads,hd,consecutiveAddresses] using hrandom
    · simp only [childChoice,hd,↓reduceIte,ChildStagePost]
      exact ⟨hfound.setup ha hv,hfound.pc,hfound.status,hfound.seed,hfound.accepted,hfound.slots⟩
  · let v := allocatedState s (location .childChoose)
    have hv := h.allocated (location .childChoose)
    have hpre := allocated_hashed s rho hp (by rw [h.count,word_toNat_of_lt hfit.1,word_toNat_of_lt hone]; omega)
    obtain ⟨k,t,log,ht,hk,hpol,hrandom,hpost⟩ :=
      (child_retry_contract (b := b) ha h.partial.accepted rho v.regs v.mem).run (allocated_search_state h)
    refine ⟨8+k,t,log,by simpa using hpre.trans ht,?_,hpol,?_,?_⟩
    · simpa only [childAttempts,hd,↓reduceIte,childSamples] using (show 8+k ≤
        9+(10*childCapacity xs a b+17*bucketCount xs a b+20)*
          FiniteProbability.Retry.attempts (childAccepted xs a b) w
            (fun i => sampleAt rho (childRandomBase l w b.val+i.val)) by omega)
    · simpa only [childReads,hd,↓reduceIte,childSamples] using hrandom
    · simp only [childChoice,hd,↓reduceIte,ChildStagePost]
      cases he : FiniteProbability.Retry.find (childAccepted xs a b) w (childSamples xs l b rho) with
      | none =>
        unfold childSamples at he
        have hs : ChildSearchState xs l a b v.regs v.mem (childRandomBase l w b.val+w) 0 t := by
          simpa only [he] using hpost
        refine ⟨hs.setup ha hv,hs.pc,hs.trials,?_,?_⟩
        · rw [hs.registers stage (by decide)]
          simp [v,allocatedState,update,stage,fallbackMode]
        · rw [hs.registers fallbackMode (by decide)]
          simp [v,allocatedState,update]
      | some chosen =>
        unfold childSamples at he
        have hs : ChildFound xs l a b v.regs v.mem chosen t := by simpa only [he] using hpost
        exact ⟨hs.setup ha hv,hs.pc,hs.status,hs.seed,hs.accepted,hs.slots⟩

end PerfectHash.Bounded
