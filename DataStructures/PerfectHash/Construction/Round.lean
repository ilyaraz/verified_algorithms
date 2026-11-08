import DataStructures.PerfectHash.Construction.Clear

namespace PerfectHash.Construction.Round
open WordRam Registers

/-- Reusable power-of-two rounding loop. The caller initializes size to one and
shift to the machine width; all arithmetic is proved to fit before execution. -/
def program : Program 64 := #[
  .branch .le (.reg roundTarget) (.reg size) 4,
  .add size (.reg size) (.reg size),
  .sub shift (.reg shift) (.imm 1),
  .jump 0, .halt]

def roundNext (s : State w 64) : State w 64 :=
  ⟨0,update (update s.regs size (s.regs size+s.regs size)) shift (s.regs shift-word w 1),s.mem⟩

macro "round_reduce" : tactic => `(tactic|
  simp [program,run,step,Comparison.test,Operand.eval,State.put,update,RunResult.prepend,
    roundTarget,size,shift, *])

theorem round_iteration (s : State w 64) (rho : RandomMemory w) (hp : s.pc = 0)
    (hn : (s.regs size).toNat < (s.regs roundTarget).toNat) :
    Steps program rho 4 s (roundNext s) [] := by
  change (s.regs (31 : Reg 64)).toNat < (s.regs (30 : Reg 64)).toNat at hn
  have hn' := Nat.not_le.mpr hn
  apply steps_iff_run.mpr
  unfold roundNext
  round_reduce

theorem round_exit (s : State w 64) (rho : RandomMemory w) (hp : s.pc = 0)
    (hn : (s.regs roundTarget).toNat ≤ (s.regs size).toNat) :
    Steps program rho 1 s {s with pc := 4} [] := by
  change (s.regs (30 : Reg 64)).toNat ≤ (s.regs (31 : Reg 64)).toNat at hn
  apply steps_iff_run.mpr
  round_reduce

open Hashing.PowerOfTwo

structure RoundPost (N w : Nat) (s t : State w 64) : Prop where
  pc : t.pc = 4
  size : t.regs Registers.size = word w (Hashing.PowerOfTwo.size N)
  shift : t.regs Registers.shift = word w (w-bits N)
  memory : t.mem = s.mem
  registers : ∀ r, r ≠ Registers.size → r ≠ Registers.shift → t.regs r = s.regs r

/-- The doubling loop stops at the least power of two covering N. Both the
roundTargeter and the full shift amount are representable at each iteration. -/
theorem round_many (rho : RandomMemory w) (N k r : Nat) {s : State w 64}
    (hp : s.pc = 0) (hn : s.regs roundTarget = word w N)
    (hs : s.regs Registers.size = word w (2^k))
    (ht : s.regs Registers.shift = word w (w-k))
    (hr : k+r = bits N) (hb : bits N ≤ w)
    (hm : Hashing.PowerOfTwo.size N < modulus w) (hw : w < modulus w) :
    ∃ t, Steps program rho (4*r+1) s t [] ∧ RoundPost N w s t := by
  have hk : k ≤ bits N := by omega
  have hkfit : 2^k < modulus w := lt_of_le_of_lt
    (Nat.pow_le_pow_right (n := 2) (by decide) hk) hm
  have hN : N < modulus w := lt_of_le_of_lt (covers N) hm
  have h1 : 1 < modulus w := lt_of_le_of_lt (positive N) hm
  induction r generalizing s k with
  | zero =>
    have hk : k = bits N := by omega
    refine ⟨{s with pc := 4}, round_exit s rho hp ?_, ?_⟩
    · rw [hn,hs,word_toNat_of_lt hN,word_toNat_of_lt hkfit,hk]
      exact covers N
    · refine ⟨rfl,?_,?_,rfl,by intros; rfl⟩
      · simpa [hk,Hashing.PowerOfTwo.size] using hs
      · simpa [hk] using ht
  | succ r ih =>
    have hlt : 2^k < N := by
      by_contra h
      have hh := least (Nat.le_of_not_gt h)
      omega
    have hh : (s.regs Registers.size).toNat < (s.regs roundTarget).toNat := by
      rw [hs,hn,word_toNat_of_lt hkfit,word_toNat_of_lt hN]
      exact hlt
    have hn' : (roundNext s).regs roundTarget = word w N := by
      simpa [roundNext,update,roundTarget,Registers.size,Registers.shift] using hn
    have hs' : (roundNext s).regs Registers.size = word w (2^(k+1)) := by
      have he : (roundNext s).regs Registers.size = s.regs Registers.size+s.regs Registers.size := by
        simp [roundNext,update,Registers.size,Registers.shift]
      rw [he,hs,word_add]
      congr 1
      simp [Nat.pow_succ,Nat.mul_two]
    have ht' : (roundNext s).regs Registers.shift = word w (w-(k+1)) := by
      simp only [roundNext,update_same]
      rw [ht,word_sub _ _ h1 (by omega)]
      congr 1
    obtain ⟨t,hsteps,hpost⟩ := ih (k+1) rfl hn' hs' ht' (by omega) (by omega)
      (lt_of_le_of_lt (Nat.pow_le_pow_right (n := 2) (by decide) (by omega : k+1 ≤ bits N)) hm)
    refine ⟨t,?_,hpost.pc,hpost.size,hpost.shift,hpost.memory,?_⟩
    · simpa [Nat.mul_add,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using (round_iteration s rho hp hh).trans hsteps
    · intro j hj hk
      rw [hpost.registers j hj hk]
      simp [roundNext,update,hj,hk]


end PerfectHash.Construction.Round
