import Algorithms.Dedup.Blocks

namespace Dedup.Blocks
open WordRam Registers
open Hashing.PowerOfTwo

structure RoundPost (N w : Nat) (s t : State w 64) : Prop where
  pc : t.pc = 9
  size : t.regs Registers.size = word w (Hashing.PowerOfTwo.size N)
  shift : t.regs Registers.shift = word w (w-bits N)
  memory : t.mem = s.mem
  registers : ∀ r, r ≠ Registers.size → r ≠ Registers.shift → t.regs r = s.regs r

/-- The doubling loop stops at the least power of two covering N. Both the
counter and the full shift amount are representable at each iteration. -/
theorem round_many (rho : RandomMemory w) (N k r : Nat) {s : State w 64}
    (hp : s.pc = 5) (hn : s.regs count = word w N)
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
    refine ⟨{s with pc := 9}, round_exit s rho hp ?_, ?_⟩
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
    have hh : (s.regs Registers.size).toNat < (s.regs count).toNat := by
      rw [hs,hn,word_toNat_of_lt hkfit,word_toNat_of_lt hN]
      exact hlt
    have hn' : (roundNext s).regs count = word w N := by
      simpa [roundNext,update,count,Registers.size,Registers.shift] using hn
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

theorem bits_le_input (N : Nat) : bits N ≤ N := least (Nat.le_of_lt Nat.lt_two_pow_self)

end Dedup.Blocks
