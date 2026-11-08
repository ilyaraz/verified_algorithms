import Algorithms.Dedup.Correctness
import Algorithms.Dedup.Bounds
import Hashing.MultiplyShiftProbability

namespace Dedup
open WordRam
open Hashing.PowerOfTwo Hashing.MultiplyShift
open FiniteProbability
noncomputable section
open scoped Classical

/-- A single random-memory coordinate has the uniform word mean. -/
theorem mean_cell (a : Addr w) (f : Word w → ℝ) :
    mean (fun rho : RandomMemory w => f (rho a)) = mean f := by
  letI : DecidableEq Unit := Classical.decEq _
  have hh := RandomBlocks.mean_coordinates (fun _ : Unit => a)
    (Function.injective_of_subsingleton _) (fun values => f (values ()))
  have he := mean_equiv (Equiv.funUnique Unit (Word w)) f
  exact hh.trans he

/-- The raw-to-odd transformation transfers the comparison bound without a bias
factor. Every occurrence is included, regardless of multiplicity. -/
theorem expected_raw_comparisons (xs : List (Word w)) (l : Layout)
    (ha : Admissible w xs.length l) :
    mean (fun raw : Word w => (comparisons (parameters ha raw).hash xs [] : ℝ)) ≤ 3*xs.length := by
  cases w with
  | zero => have := ha.positive; omega
  | succ w =>
    letI : Nonempty (Seed w) := ⟨⟨0,Nat.two_pow_pos w⟩⟩
    let f := family w (bits xs.length) ha.bucket_bits
    have hm : 0 < 2^bits xs.length := positive xs.length
    have hb := expected_comparisons_linear f (collision_bound w (bits xs.length) ha.bucket_bits)
      hm xs (covers xs.length)
    have he (raw : Word (w+1)) : comparisons (parameters ha raw).hash xs [] =
        comparisons (f.eval (rawIndex raw)) xs [] := by
      have hh := comparisons_injective (fun i : Fin (2^bits xs.length) => i.val)
        Fin.val_injective (f.eval (rawIndex raw)) xs []
      simpa [parameters,f,family,sample_eq_encode] using hh
    rw [mean_congr (fun raw => congrArg (fun n : Nat => (n : ℝ)) (he raw))]
    rw [mean_rawSeed (fun a => (comparisons (f.eval a) xs [] : ℝ))]
    exact hb

/-- Expected executed instructions to successful completion, including rounding,
clearing, the random load, all duplicate searches, all stores, and the halt. -/
theorem expected_instructions (xs : List (Word w)) (l : Layout)
    (ha : Admissible w xs.length l) {s : State w 64} (hp : s.pc = 0)
    (hin : Input w xs.length l s.regs) (arr : ArrayAt s.mem l.input xs) :
    expectedSteps program (fuel xs.length) s ≤ 67*(xs.length+1) := by
  change mean (fun rho : RandomMemory w => ((run program rho (fuel xs.length) s).steps : ℝ)) ≤ _
  have hbound : mean (fun rho : RandomMemory w => ((run program rho (fuel xs.length) s).steps : ℝ)) ≤
      mean (fun rho : RandomMemory w => (40 : ℝ)*(xs.length+1)+
        9*(comparisons (parameters ha (rho (word w l.random))).hash xs [] : ℝ)) := by
    apply mean_mono
    intro rho
    exact_mod_cast (run_correct xs l ha rho hp hin arr).2.1
  rw [mean_add,mean_const,mean_mul] at hbound
  rw [mean_cell (word w l.random) (fun raw => (comparisons (parameters ha raw).hash xs [] : ℝ))] at hbound
  have hcomp := expected_raw_comparisons xs l ha
  nlinarith

end
end Dedup
