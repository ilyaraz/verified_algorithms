import DataStructures.PerfectHash.Construction.Registers
import DataStructures.PerfectHash.Construction.Energy
import Hashing.MultiplyShift

namespace PerfectHash.Construction.Enumeration
open WordRam Registers Hashing.MultiplyShift

/-- The enumeration control loop uses wrap back to one as its end marker. It
never attempts to store the modulus or allocate an array of candidate seeds.
The retry driver uses this same finite sequence of odd-word candidates. -/
def program : Program 64 := #[
  .mov seed (.imm 1),
  .add seed (.reg seed) (.imm 2),
  .branch .eq (.reg seed) (.imm 1) 4,
  .jump 1,.halt]

def next (s : State w 64) : State w 64 :=
  ⟨1,update s.regs seed (s.regs seed+word w 2),s.mem⟩

macro "enumeration_reduce" : tactic => `(tactic|
  simp [program,run,step,Comparison.test,Operand.eval,State.put,update,
    RunResult.prepend,seed, *])

theorem iteration (s : State w 64) (rho : RandomMemory w) (hp : s.pc = 1)
    (hn : s.regs seed+word w 2 ≠ word w 1) : Steps program rho 3 s (next s) [] := by
  change s.regs (5 : Reg 64)+word w 2 ≠ word w 1 at hn
  apply steps_iff_run.mpr
  unfold next
  enumeration_reduce

theorem last (s : State w 64) (rho : RandomMemory w) (hp : s.pc = 1)
    (hn : s.regs seed+word w 2 = word w 1) :
    TerminatesIn program rho s 3 ⟨4,update s.regs seed (word w 1),s.mem⟩ [] := by
  change s.regs (5 : Reg 64)+word w 2 = word w 1 at hn
  apply terminatesIn_iff_run.mpr
  enumeration_reduce

theorem candidate_ne_first (hi : 0 < i) (hb : i < 2^w) : candidate w i ≠ first w := by
  intro he
  have ht := congrArg BitVec.toNat he
  rw [candidate_before_wrap hb] at ht
  have hp : 1 < modulus (w+1) := by have := Nat.two_pow_pos w; simp only [modulus,Nat.pow_succ]; omega
  rw [first,word_toNat_of_lt hp] at ht
  omega

/-- Any remaining suffix of the odd-seed cycle terminates exactly at wrap. -/
theorem cycle (rho : RandomMemory (w+1)) (n i : Nat) (s : State (w+1) 64)
    (hp : s.pc = 1) (hs : s.regs seed = candidate w i)
    (hi : i < 2^w) (hn : i+n = 2^w) :
    TerminatesIn program rho s (3*n) ⟨4,update s.regs seed (first w),s.mem⟩ [] := by
  induction n generalizing i s with
  | zero => omega
  | succ n ih =>
    have ha : s.regs seed+word (w+1) 2 = candidate w (i+1) := by
      rw [hs,candidate_succ]
      rfl
    by_cases hz : n = 0
    · subst n
      have he : i+1 = 2^w := by omega
      have hh : s.regs seed+word (w+1) 2 = word (w+1) 1 := by rw [ha,he,candidate_wrap]; rfl
      exact last s rho hp hh
    · have hnext : i+1 < 2^w := by omega
      have hne : s.regs seed+word (w+1) 2 ≠ word (w+1) 1 := by
        rw [ha]
        exact candidate_ne_first (by omega) hnext
      have ht := ih (i+1) (next s) rfl (by simp [next,ha]) hnext (by omega)
      have hh := (iteration s rho hp hne).then_terminates ht
      simpa [next,update_shadow,Nat.mul_add,Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using hh

/-- Concrete instruction prefixes visit every encoded family seed, exactly in
numeric odd-word order, before the wrap test ends the enumeration. -/
theorem visits (rho : RandomMemory (w+1)) (rs : Registers (w+1) 64) (mem : DataMemory (w+1))
    (i : Nat) (hi : i < 2^w) :
    Steps program rho (3*i) ⟨1,update rs seed (first w),mem⟩
      ⟨1,update rs seed (candidate w i),mem⟩ [] := by
  induction i with
  | zero => exact .refl _
  | succ i ih =>
    have hp := ih (by omega)
    have hne : candidate w i+word (w+1) 2 ≠ word (w+1) 1 := by
      change advance (candidate w i) ≠ first w
      rw [← candidate_succ]
      exact candidate_ne_first (by omega) hi
    have hs := iteration (⟨1,update rs seed (candidate w i),mem⟩ : State (w+1) 64) rho rfl
      (by simpa using hne)
    have hh := hp.trans hs
    simpa [next,update_shadow,candidate_succ,advance,Nat.mul_add,Nat.add_assoc] using hh

/-- Every seed in the collision-bounded family appears at a charged RAM prefix. -/
theorem covers (rho : RandomMemory (w+1)) (rs : Registers (w+1) 64) (mem : DataMemory (w+1))
    (a : Seed w) :
    Steps program rho (3*a.val) ⟨1,update rs seed (first w),mem⟩
      ⟨1,update rs seed (encode a),mem⟩ [] := visits rho rs mem a.val a.isLt

/-- The standalone enumeration loop visits the entire finite family and halts
without any random reads or ordinary-memory effects. -/
theorem total (rho : RandomMemory (w+1)) (rs : Registers (w+1) 64) (mem : DataMemory (w+1)) :
    TerminatesIn program rho (.initial rs mem) (1+3*2^w)
      ⟨4,update rs seed (first w),mem⟩ [] := by
  have hs : Steps program rho 1 (.initial rs mem) ⟨1,update rs seed (first w),mem⟩ [] := by
    apply steps_iff_run.mpr
    simp [program,run,step,State.initial,State.put,Operand.eval,RunResult.prepend,first]
  have ht := cycle rho (2^w) 0 ⟨1,update rs seed (first w),mem⟩ rfl (by simp [candidate_zero])
    (Nat.two_pow_pos w) (by simp)
  simpa [update_shadow] using hs.then_terminates ht

end PerfectHash.Construction.Enumeration
