import Hashing.Source.MultiplyShift
import Hashing.PowerOfTwo

namespace Hashing.Source.Rounding
open WordRam RamLang RamLang.Compiler RamLang.Logic

/-- Round by charged word doubling, returning the bucket count and storing its
multiply-shift parameter in one explicitly supplied ordinary-memory cell. -/
def program : RamLang.Program := ram_program round {
  fn round(target, width, shiftCell) {
    let size = 1;
    while (size < target) {
      size = size + size;
      width = width - 1;
    }
    store(shiftCell, width);
    return size;
  }
}

/-- Three arguments and one local give a six-word frame. -/
def function : RamLang.Function := program.functions[0]'(by decide)

/-- The doubling loop has two word operations and a comparison. -/
def loop : Stmt := .while ⟨.lt,.local 3,.local 0⟩
  (.seq (.primitive (.binary 3 .add (.local 3) (.local 3)))
    (.primitive (.binary 1 .sub (.local 1) (.literal 1))))

/-- A fitting rounded capacity needs strictly fewer bits than the word width. -/
theorem bits_lt_width {w n : Nat} (hf : PowerOfTwo.size n < modulus w) : PowerOfTwo.bits n < w := by
  by_contra hn
  have hp := Nat.pow_le_pow_right (n := 2) (by decide) (Nat.le_of_not_gt hn)
  change 2^(PowerOfTwo.bits n) < 2^w at hf
  omega

/-- A loop state records the current power and the corresponding decreasing
shift. These are ghost parameters; the program computes both ordinary words. -/
def locals (w n i : Nat) (cell : Word w) : Locals w :=
  [some (word w n),some (word w (w-i)),some cell,some (word w (2^i))]

/-- Source invariant proof for every remaining doubling step. It charges
nineteen instructions per iteration and six for the final condition. -/
theorem loop_contract {w free : Nat} (p : RamLang.Program) (rho : RandomMemory w)
    (mem : DataMemory w) (n : Nat) (cell : Word w) (hf : PowerOfTwo.size n < modulus w)
    (remaining i : Nat) (hi : i+remaining = PowerOfTwo.bits n) :
    Contract p rho free loop (locals w n i cell) mem
      (fun flow mem' trace => flow = .next (locals w n (PowerOfTwo.bits n) cell) ∧
        mem' = mem ∧ trace = []) (19*remaining+6) 0 := by
  have hpower : 2^(PowerOfTwo.bits n) < modulus w := hf
  have hb := bits_lt_width hf
  have hn : n < modulus w := Nat.lt_of_le_of_lt (PowerOfTwo.covers n) hf
  have hw : w < modulus w := Nat.lt_two_pow_self
  have hone : 1 < modulus w := by
    have hp := PowerOfTwo.positive n
    omega
  induction remaining generalizing i with
  | zero =>
    have he : i = PowerOfTwo.bits n := by omega
    subst i
    let d : Evaluation p rho free loop (locals w n (PowerOfTwo.bits n) cell) mem
        (.next (locals w n (PowerOfTwo.bits n) cell)) mem [] :=
      .whileFalse (by
        have hcover := PowerOfTwo.covers n
        simp [Condition.eval,Atom.eval,requireSome,Comparison.test,locals,
          bind,pure,Except.bind,Except.pure,word_toNat_of_lt hpower,word_toNat_of_lt hn,
          PowerOfTwo.size] at hcover ⊢
        omega)
    exact Contract.ofEvaluation d ⟨rfl,rfl,rfl⟩ (by change 6 ≤ 6; decide) (Nat.le_refl _)
  | succ remaining ih =>
    have hil : i < PowerOfTwo.bits n := by omega
    have hp : 2^i < modulus w := Nat.lt_of_le_of_lt
      (Nat.pow_le_pow_right (n := 2) (by decide) (Nat.le_of_lt hil)) hf
    have hsmall : 2^i < n := by
      by_contra h
      have hleast := PowerOfTwo.least (Nat.le_of_not_gt h)
      omega
    have htest : (Condition.mk .lt (.local 3) (.local 0)).eval (locals w n i cell) = .ok true := by
      simp [Condition.eval,Atom.eval,requireSome,Comparison.test,locals,
        bind,pure,Except.bind,Except.pure,word_toNat_of_lt hp,word_toNat_of_lt hn,hsmall]
    have hadd : word w (2^i)+word w (2^i) = word w (2^(i+1)) := by
      rw [WordRam.word_add,Nat.pow_succ]
      congr 1
      omega
    have hsub : word w (w-i)-word w 1 = word w (w-(i+1)) := by
      rw [WordRam.word_sub _ _ hone (by omega),Nat.sub_sub]
    let step : Evaluation p rho free
        (.seq (.primitive (.binary 3 .add (.local 3) (.local 3)))
          (.primitive (.binary 1 .sub (.local 1) (.literal 1))))
        (locals w n i cell) mem (.next (locals w n (i+1) cell)) mem [] :=
      .sequence (.primitive (locals' := [some (word w n),some (word w (w-i)),some cell,some (word w (2^(i+1)))])
        (mem' := mem) (event := none) (by
        simp [Primitive.eval,Atom.eval,requireSome,writeLocal,Binary.eval,locals,hadd,
          bind,pure,Except.bind,Except.pure] <;> rfl))
        (.primitive (event := none) (by
          simp [Primitive.eval,Atom.eval,requireSome,writeLocal,Binary.eval,locals,hsub,
            bind,pure,Except.bind,Except.pure]))
    obtain ⟨flow,mem',trace,d,⟨rfl,rfl,rfl⟩,ht,hs⟩ := ih (i+1) (by omega)
    refine Contract.ofEvaluation (.whileContinue htest step d) ⟨rfl,rfl,rfl⟩ ?_ ?_
    · change 6+13+instructions d ≤ 19*(remaining+1)+6
      omega
    · change max 0 (extraStack d) ≤ 0
      omega

/-- Complete rounding computes the existing mathematical ceiling power of two,
initializes the requested shift cell, and touches no other application address. -/
theorem contract {w free : Nat} (p : RamLang.Program) (rho : RandomMemory w)
    (mem : DataMemory w) (n : Nat) (cell : Word w) (hf : PowerOfTwo.size n < modulus w) :
    Contract p rho free function.body
      ([word w n,word w w,cell].map some ++ List.replicate function.locals.length none) mem
      (fun flow mem' trace => flow = .returned (word w (PowerOfTwo.size n)) ∧
        mem' = update mem cell (word w (w-PowerOfTwo.bits n)) ∧
        trace = [.dataWrite cell (word w (w-PowerOfTwo.bits n))])
      (19*PowerOfTwo.bits n+22) 0 := by
  obtain ⟨flow,mem',trace,d,⟨hflow,hmem,htrace⟩,ht,hs⟩ := loop_contract (free := free) p rho mem n cell hf
    (PowerOfTwo.bits n) 0 (by simp)
  subst flow
  subst mem'
  subst trace
  let init : Evaluation p rho free (.primitive (.move 3 (.literal 1)))
      ([word w n,word w w,cell].map some ++ List.replicate function.locals.length none) mem
      (.next (locals w n 0 cell)) mem [] := .primitive (event := none) rfl
  let finish : Evaluation p rho free (.seq (.primitive (.store (.local 2) (.local 1))) (.ret (.local 3)))
      (locals w n (PowerOfTwo.bits n) cell) mem (.returned (word w (PowerOfTwo.size n)))
      (update mem cell (word w (w-PowerOfTwo.bits n)))
      [.dataWrite cell (word w (w-PowerOfTwo.bits n))] :=
    .sequence (.primitive (event := some _) rfl) (.ret rfl)
  refine Contract.ofEvaluation (.sequence init (.sequence d finish)) ⟨rfl,rfl,rfl⟩ ?_ ?_
  · change 3+(instructions d+13) ≤ 19*PowerOfTwo.bits n+22
    omega
  · change max 0 (max (extraStack d) 0) ≤ 0
    omega

end Hashing.Source.Rounding
