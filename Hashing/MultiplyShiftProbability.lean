import Hashing.MultiplyShift
import Hashing.Family
import WordRam.Random

namespace Hashing.MultiplyShift
open WordRam

/-- Raw words are the product of an odd-seed index and the discarded low bit. -/
def rawEquiv (w : Nat) : Word (w+1) ≃ Seed w × Fin 2 where
  toFun r := (rawIndex r, ⟨r.toNat%2, Nat.mod_lt _ (by decide)⟩)
  invFun p := word (w+1) (2*p.1.val+p.2.val)
  left_inv r := by
    apply BitVec.eq_of_toNat_eq
    have hd := Nat.mod_add_div r.toNat 2
    simp only [rawIndex]
    rw [show 2*(r.toNat/2)+r.toNat%2 = r.toNat by omega, word_toNat_of_lt r.isLt]
  right_inv p := by
    have hp : p.1.val < 2^w := p.1.isLt
    have hb := p.2.isLt
    have hf : 2*p.1.val+p.2.val < modulus (w+1) := by
      simp only [modulus, Nat.pow_succ]
      omega
    apply Prod.ext
    · apply Fin.ext
      simp [rawIndex, word_toNat_of_lt hf]
      omega
    · apply Fin.ext
      simp [word_toNat_of_lt hf, Nat.mod_eq_of_lt hb]

/-- Each encoded seed has precisely the two raw preimages differing in bit zero. -/
def rawFiberEquiv (a : Seed w) : {r : Word (w+1) // rawIndex r = a} ≃ Fin 2 where
  toFun r := ((rawEquiv w) r.val).2
  invFun b := ⟨(rawEquiv w).symm (a,b), by
    have h := congrArg Prod.fst ((rawEquiv w).apply_symm_apply (a,b))
    exact h⟩
  left_inv r := by
    apply Subtype.ext
    apply (rawEquiv w).injective
    simp only [Equiv.apply_symm_apply]
    apply Prod.ext
    · exact r.property.symm
    · rfl
  right_inv b := by simp

@[simp] theorem raw_fiber_card (a : Seed w) :
    Nat.card {r : Word (w+1) // rawIndex r = a} = 2 := by
  rw [Nat.card_congr (rawFiberEquiv a), Nat.card_fin]

/-- Raw sampling realizes the uniform seed PMF exactly, including width one. -/
theorem raw_seed_probability (a : Seed w) :
    ((PMF.uniformOfFintype (Word (w+1))).toOuterMeasure {r | rawIndex r = a}).toReal =
      (1 : ℝ) / 2^w := by
  classical
  rw [PMF.toOuterMeasure_uniformOfFintype_apply]
  have hc : Fintype.card {r : Word (w+1) // rawIndex r = a} = 2 := by
    rw [← Nat.card_eq_fintype_card, raw_fiber_card]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, Set.coe_setOf, hc, card_word, modulus, Nat.pow_succ]
  push_cast
  have hp : (0 : ℝ) < 2^w := by positivity
  field_simp

/-- A random-memory coordinate supplies exactly the raw-word PMF used above. -/
theorem cell_seed_probability (address : Addr (w+1)) (a : Seed w) :
    probability (fun rho => rawIndex (rho address) = a) = (1 : ℝ)/2^w := by
  classical
  let lo := (rawEquiv w).symm (a, ⟨0, by decide⟩)
  let hi := (rawEquiv w).symm (a, ⟨1, by decide⟩)
  have hlo : lo ≠ hi := by
    intro he
    have := (rawEquiv w).symm.injective he
    have := congrArg (fun p : Seed w × Fin 2 => p.2.val) this
    simp at this
  have he : ∀ rho : RandomMemory (w+1), rawIndex (rho address) = a ↔
      rho address = lo ∨ rho address = hi := by
    intro rho
    constructor
    · intro ha
      have hf := ((rawEquiv w) (rho address)).2.isLt
      have hb : ((rawEquiv w) (rho address)).2.val = 0 ∨
          ((rawEquiv w) (rho address)).2.val = 1 := by omega
      rcases hb with hb | hb
      · left
        apply (rawEquiv w).injective
        simp only [lo, Equiv.apply_symm_apply]
        exact Prod.ext ha (Fin.ext hb)
      · right
        apply (rawEquiv w).injective
        simp only [hi, Equiv.apply_symm_apply]
        exact Prod.ext ha (Fin.ext hb)
    · intro hh
      rcases hh with hh | hh <;> rw [hh]
      all_goals exact congrArg Prod.fst ((rawEquiv w).apply_symm_apply _)
  rw [probability_congr he]
  -- The disjoint union law is proved directly from the finite PMF used by RAM.
  rw [probability_eq_pmf, randomMemoryLaw]
  rw [PMF.toOuterMeasure_uniformOfFintype_apply]
  simp only [ENNReal.toReal_div, ENNReal.toReal_natCast, Set.coe_setOf]
  have hc : Fintype.card {rho : RandomMemory (w+1) // rho address = lo ∨ rho address = hi} =
      eventCount (fun rho => rho address = lo) + eventCount (fun rho => rho address = hi) := by
    simp only [eventCount, ← Nat.card_eq_fintype_card]
    simpa only [← Nat.card_eq_fintype_card] using
      Fintype.card_subtype_or_disjoint (fun rho : RandomMemory (w+1) => rho address = lo)
        (fun rho => rho address = hi)
        (fun p hp hq rho hr => hlo ((hp rho hr).symm.trans (hq rho hr)))
  rw [hc, Nat.cast_add, add_div]
  change probability (fun rho => rho address = lo) + probability (fun rho => rho address = hi) = _
  rw [probability_cell, probability_cell]
  simp only [modulus, Nat.pow_succ]
  push_cast
  have hp : (0 : ℝ) < 2^w := by positivity
  field_simp
  ring

theorem cell_sample_probability (address : Addr (w+1)) (a : Seed w) :
    probability (fun rho => sample (rho address) = encode a) = (1 : ℝ)/2^w := by
  rw [probability_congr (fun rho => by
    rw [sample_eq_encode, encode_injective.eq_iff])]
  exact cell_seed_probability address a

end Hashing.MultiplyShift
