import DataStructures.PerfectHash.Construction.AllocationBlocks

namespace PerfectHash.Construction.Allocation
open WordRam Registers

/-- Direct children store the full width as their zero-bit hash shift. -/
def childShift (w b : Nat) : Nat :=
  if b ≤ 1 then w else w-Hashing.PowerOfTwo.computeBits (2*b*b)

structure Prepared (b : Nat) (s t : State w 64) : Prop where
  pc : t.pc = 14
  slots : t.regs Registers.slots = word w (Sizes.childSlots b)
  shift : t.regs Registers.shift = word w (childShift w b)
  count : t.regs childCount = word w b
  head : t.regs rootHead = s.mem (s.regs address+word w 1)
  address : t.regs Registers.address = s.regs Registers.address
  table : t.regs Registers.table = s.regs Registers.table
  memory : t.mem = s.mem

set_option maxRecDepth 20000
set_option maxHeartbeats 3000000

macro "allocation_regs" : tactic => `(tactic|
  simp [initialized,loaded,rounded,update,address,temp,rootHead,width,childCount,slots,
    size,shift,roundTarget,table,tableEnd, *])

variable {w b : Nat} {s : State w 64}

theorem prepare (rho : RandomMemory w) (hp : s.pc = 0)
    (hc : s.mem (s.regs address) = word w b) (hw : s.regs width = word w w)
    (hb : b < modulus w) (hq : Sizes.childSlots b < modulus w)
    (hwidth : w < modulus w) (hone : 1 < modulus w) :
    ∃ k t, Steps program rho k s t (loadTrace s) ∧
      k ≤ 4*Hashing.PowerOfTwo.bits (2*b*b)+11 ∧ Prepared b s t := by
  have hc' : s.mem (s.regs (12 : Reg 64)) = word w b := hc
  have hw' : s.regs (4 : Reg 64) = word w w := hw
  by_cases hd : b ≤ 1
  · have ht := direct s rho hp (by rw [hc,word_toNat_of_lt hb,word_toNat_of_lt hone]; exact hd)
    refine ⟨6,loaded s 14,ht,by omega,rfl,?_,?_,?_,?_,?_,?_,rfl⟩
    all_goals simp [loaded,update,slots,shift,childCount,temp,rootHead,address,width,table,
      Sizes.childSlots,childShift,hd,hc',hw']
  · have hq' : Hashing.PowerOfTwo.size (2*b*b) < modulus w := by
      simpa [Sizes.childSlots,hd,Hashing.PowerOfTwo.computeSize_eq] using hq
    have htarg : 2*b*b < modulus w := lt_of_le_of_lt (Hashing.PowerOfTwo.covers _) hq'
    have hbits : Hashing.PowerOfTwo.bits (2*b*b) ≤ w :=
      Hashing.PowerOfTwo.least (Nat.le_of_lt htarg)
    have hs := hashed s rho hp (by rw [hc,word_toNat_of_lt hb,word_toNat_of_lt hone]; omega)
    let u : State w 64 := {initialized s with pc := 0}
    have htarget : u.regs roundTarget = word w (2*b*b) := by
      have he : u.regs roundTarget = s.mem (s.regs address)*s.mem (s.regs address)*word w 2 := by
        simp [u,initialized,update,size,roundTarget]
      rw [he,hc,word_mul,word_mul]
      congr 1
      ring
    have hsize : u.regs size = word w (2^0) := by simp [u,initialized,update]
    have hshift : u.regs shift = word w (w-0) := by
      simpa [u,initialized,loaded,update,shift,size,roundTarget,slots,rootHead,temp,childCount] using hw
    obtain ⟨v,hv,post⟩ := Round.round_many rho (2*b*b) 0 (Hashing.PowerOfTwo.bits (2*b*b))
      (s := u) rfl htarget hsize hshift (by simp) hbits hq' hwidth
    have he := hv.relocate_body round_embedded
    have hu : u.relocate 9 = initialized s := rfl
    rw [hu] at he
    have hpc : (v.relocate 9).pc = 13 := by simp [State.relocate,post.pc]
    have he' := (hs.trans he).trans (rounded_next (v.relocate 9) rho hpc)
    refine ⟨9+(4*Hashing.PowerOfTwo.bits (2*b*b)+1)+1,rounded (v.relocate 9),
      by simpa using he',by omega,rfl,?_,?_,?_,?_,?_,?_,?_⟩
    · change v.regs size = _
      rw [post.size]
      simp [Sizes.childSlots,hd,Hashing.PowerOfTwo.computeSize_eq]
    · change update v.regs slots (v.regs size) shift = _
      rw [update_other _ _ _ _ (by decide : shift ≠ slots),post.shift]
      simp [childShift,hd,Hashing.PowerOfTwo.computeBits_eq]
    · change update v.regs slots (v.regs size) childCount = _
      rw [update_other _ _ _ _ (by decide : childCount ≠ slots),
        post.registers childCount (by decide) (by decide)]
      simp [u,initialized,loaded,update,childCount,slots,shift,rootHead,temp,roundTarget,size,hc]
    · change update v.regs slots (v.regs size) rootHead = _
      rw [update_other _ _ _ _ (by decide : rootHead ≠ slots),
        post.registers rootHead (by decide) (by decide)]
      simp [u,initialized,loaded,update,childCount,slots,shift,rootHead,temp,roundTarget,size]
    · change update v.regs slots (v.regs size) address = _
      rw [update_other _ _ _ _ (by decide : address ≠ slots),
        post.registers address (by decide) (by decide)]
      simp [u,initialized,loaded,update,childCount,slots,shift,rootHead,temp,roundTarget,size,address]
    · change update v.regs slots (v.regs size) table = _
      rw [update_other _ _ _ _ (by decide : table ≠ slots),
        post.registers table (by decide) (by decide)]
      simp [u,initialized,loaded,update,childCount,slots,shift,rootHead,temp,roundTarget,size,table]
    · exact post.memory

structure Output (b : Nat) (s t : State w 64) : Prop where
  pc : t.pc = 20
  slots : t.regs Registers.slots = word w (Sizes.childSlots b)
  shift : t.regs Registers.shift = word w (childShift w b)
  count : t.regs childCount = word w b
  head : t.regs rootHead = s.mem (s.regs address+word w 1)
  address : t.regs Registers.address = s.regs Registers.address
  table : t.regs Registers.table = s.regs Registers.table
  endPointer : t.regs tableEnd = s.regs Registers.table+word w (2*Sizes.childSlots b)
  memory : t.mem = update (update s.mem (s.regs Registers.address+word w 3) (s.regs Registers.table))
    (s.regs Registers.address+word w 2) (word w (childShift w b))

theorem finished_output (h : Prepared b s t) : Output b s (finished t) := by
  refine ⟨rfl,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa [finished,update,slots,temp,tableEnd] using h.slots
  · simpa [finished,update,shift,temp,tableEnd] using h.shift
  · simpa [finished,update,childCount,temp,tableEnd] using h.count
  · simpa [finished,update,rootHead,temp,tableEnd] using h.head
  · simpa [finished,update,address,temp,tableEnd] using h.address
  · simpa [finished,update,table,temp,tableEnd] using h.table
  · change update (update t.regs tableEnd (t.regs table+t.regs slots*word w 2))
        temp (t.regs address+word w 2) tableEnd = _
    rw [update_other _ _ _ _ (by decide : tableEnd ≠ temp),update_same,h.slots,h.table,word_mul,Nat.mul_comm]
  · change finalMemory t = _
    rw [finalMemory,h.memory,h.address,h.table,h.shift]

def policy (dir : Nat) : AccessPolicy w :=
  ⟨(Region.mk dir 4).Contains,(Region.mk dir 4).Contains,fun _ => False⟩

theorem prepare_policy (hf : (Region.mk dir 4).Fits w) (ha : s.regs address = word w dir) :
    (policy dir).AllowsTrace (loadTrace s) := by
  have h0 := Region.contains_index hf (by decide : 0 < 4)
  have h1 := Region.contains_index hf (by decide : 1 < 4)
  simp only [loadTrace,ha,word_add,AccessPolicy.AllowsTrace,List.mem_cons,List.not_mem_nil,or_false]
  intro e he
  rcases he with rfl | rfl
  · exact h0
  · exact h1

theorem finish_policy (h : Prepared b s t) (hf : (Region.mk dir 4).Fits w)
    (ha : s.regs address = word w dir) : (policy dir).AllowsTrace (finishTrace t) := by
  have h2 := Region.contains_index hf (by decide : 2 < 4)
  have h3 := Region.contains_index hf (by decide : 3 < 4)
  simp only [finishTrace,h.address,ha,word_add,AccessPolicy.AllowsTrace,List.mem_cons,List.not_mem_nil,or_false]
  intro e he
  rcases he with rfl | rfl
  · exact h3
  · exact h2

/-- The complete allocation routine reads the stored root count and performs
its size arithmetic on the RAM. Only two directory metadata cells are written. -/
theorem total (rho : RandomMemory w) (hp : s.pc = 0)
    (hc : s.mem (s.regs address) = word w b) (hw : s.regs width = word w w)
    (hb : b < modulus w) (hq : Sizes.childSlots b < modulus w)
    (hwidth : w < modulus w) (hone : 1 < modulus w)
    (hf : (Region.mk dir 4).Fits w) (ha : s.regs address = word w dir) :
    ∃ k t log, TerminatesIn program rho s k t log ∧
      k ≤ 4*Hashing.PowerOfTwo.bits (2*b*b)+18 ∧ Output b s t ∧ (policy dir).AllowsTrace log := by
  obtain ⟨k,u,hs,hk,hu⟩ := prepare rho hp hc hw hb hq hwidth hone
  exact ⟨k+7,finished u,loadTrace s++finishTrace u,hs.then_terminates (finish_next u rho hu.pc),
    by omega,finished_output hu,(AccessPolicy.allowsTrace_append _).mpr
      ⟨prepare_policy hf ha,finish_policy hu hf ha⟩⟩

/-- Accepted-root energy supplies the arithmetic fit needed by the local routine;
no global quadratic-size assumption has been introduced. -/
theorem accepted_fit (hash : Word w → Fin m) (xs : List (Word w)) (b : Fin m)
    (he : Buckets.energy hash xs ≤ 6*xs.length) (hf : 64*(xs.length+1) < modulus w) :
    Buckets.count hash xs b < modulus w ∧
    2*(Buckets.count hash xs b)^2 < modulus w ∧
    Sizes.childSlots (Buckets.count hash xs b) < modulus w := by
  have hc := Buckets.count_le hash xs b
  exact ⟨by omega,Sizes.child_fit hash xs he hf b⟩

end PerfectHash.Construction.Allocation
