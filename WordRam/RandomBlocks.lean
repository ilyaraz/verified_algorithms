import WordRam.Random
import WordRam.Regions
import Probability.Finite

/-! Transfer finite block coordinates to independent uniform laws. History may
be any function of earlier coordinates; no assumption of unequal sampled values
is made. The complete immutable random memory is sampled just once. -/
namespace WordRam.RandomBlocks
noncomputable section
open scoped Classical

variable {w : Nat} {I J : Type*} [Fintype I] [Fintype J]

def cells (addresses : I → Addr w) : Finset (Addr w) := Finset.univ.image addresses

/-- All selected coordinates and the untouched complement determine a unique
complete memory image. This is a mathematical bijection, never a runtime sampler. -/
def coordinatesEquiv (addresses : I → Addr w) (hinj : Function.Injective addresses) :
    RandomMemory w ≃ ((I → Word w) × ({a : Addr w // a ∉ cells addresses} → Word w)) where
  toFun rho := (fun i => rho (addresses i), fun a => rho a.val)
  invFun p a := if h : ∃ i, addresses i = a then p.1 (Classical.choose h)
    else p.2 ⟨a, by simpa [cells] using h⟩
  left_inv rho := by
    funext a
    dsimp only
    split
    · rename_i h
      rw [Classical.choose_spec h]
    · rfl
  right_inv p := by
    apply Prod.ext
    · funext i
      dsimp only
      split
      · rename_i h
        rw [hinj (Classical.choose_spec h)]
      · rename_i h
        exact False.elim (h ⟨i, rfl⟩)
    · funext a
      dsimp only
      split
      · rename_i h
        exact False.elim (a.property (by simpa [cells] using h))
      · rfl

/-- Any observation of distinct coordinates has exactly the uniform tuple law. -/
theorem mean_coordinates (addresses : I → Addr w) (hinj : Function.Injective addresses)
    (f : (I → Word w) → ℝ) :
    FiniteProbability.mean (fun rho : RandomMemory w => f (fun i => rho (addresses i))) =
      FiniteProbability.mean f := by
  have h := FiniteProbability.mean_equiv (coordinatesEquiv addresses hinj) (fun p => f p.1)
  rw [FiniteProbability.mean_prod] at h
  simpa only [coordinatesEquiv, Equiv.coe_fn_mk, FiniteProbability.mean_const] using h

theorem probability_eq_finite (event : RandomMemory w → Prop) :
    WordRam.probability event = FiniteProbability.probability event := by
  rw [FiniteProbability.probability_card]
  simp [WordRam.probability, eventCount, Nat.card_eq_fintype_card]

theorem probability_coordinates (addresses : I → Addr w) (hinj : Function.Injective addresses)
    (event : (I → Word w) → Prop) :
    WordRam.probability (fun rho => event (fun i => rho (addresses i))) =
      FiniteProbability.probability event := by
  rw [probability_eq_finite]
  simpa only [FiniteProbability.probability] using
    mean_coordinates addresses hinj (fun values => if event values then (1 : ℝ) else 0)

omit [Fintype I] [Fintype J] in
/-- A disjoint union of two injective address families is still injective. -/
theorem sum_injective (left : I → Addr w) (right : J → Addr w)
    (hl : Function.Injective left) (hr : Function.Injective right)
    (hd : ∀ i j, left i ≠ right j) : Function.Injective (Sum.elim left right) := by
  intro a b he
  cases a <;> cases b
  · exact congrArg Sum.inl (hl he)
  · exact False.elim (hd _ _ he)
  · exact False.elim (hd _ _ he.symm)
  · exact congrArg Sum.inr (hr he)

/-- An arbitrary function of the past and a disjoint next block has the product
law. This covers history-dependent bucket contents, table sizes, and predicates. -/
theorem mean_disjoint (left : I → Addr w) (right : J → Addr w)
    (hl : Function.Injective left) (hr : Function.Injective right)
    (hd : ∀ i j, left i ≠ right j) (f : (I → Word w) → (J → Word w) → ℝ) :
    FiniteProbability.mean (fun rho : RandomMemory w =>
      f (fun i => rho (left i)) (fun j => rho (right j))) =
      FiniteProbability.mean (fun past => FiniteProbability.mean (fun next => f past next)) := by
  letI : DecidableEq (I ⊕ J) := Classical.decEq _
  have h := mean_coordinates (Sum.elim left right) (sum_injective left right hl hr hd)
    (fun values => f (fun i => values (.inl i)) (fun j => values (.inr j)))
  have he := FiniteProbability.mean_equiv (Equiv.sumArrowEquivProdArrow I J (Word w))
    (fun p => f p.1 p.2)
  rw [FiniteProbability.mean_prod] at he
  exact h.trans he

/-- Conditional cost bounds valid for every earlier observation transfer to the
one complete random-memory average without assuming a fixed construction history. -/
theorem mean_disjoint_le (left : I → Addr w) (right : J → Addr w)
    (hl : Function.Injective left) (hr : Function.Injective right)
    (hd : ∀ i j, left i ≠ right j) (f : (I → Word w) → (J → Word w) → ℝ)
    (budget : (I → Word w) → ℝ)
    (hb : ∀ past, FiniteProbability.mean (fun next => f past next) ≤ budget past) :
    FiniteProbability.mean (fun rho : RandomMemory w =>
      f (fun i => rho (left i)) (fun j => rho (right j))) ≤
      FiniteProbability.mean budget := by
  rw [mean_disjoint left right hl hr hd]
  exact FiniteProbability.mean_mono hb

end

/-- A fitting block has distinct word addresses; no arithmetic endpoint wraps. -/
def address (w base : Nat) (i : Fin n) : Addr w := word w (base+i.val)

theorem address_injective (hf : base+n < modulus w) :
    Function.Injective (address w base (n := n)) := by
  intro i j he
  have he' := congrArg BitVec.toNat he
  simp only [address, word_toNat_of_lt (by have := i.isLt; omega : base+i.val < modulus w),
    word_toNat_of_lt (by have := j.isLt; omega : base+j.val < modulus w)] at he'
  apply Fin.ext
  omega

theorem address_contains (hf : (Region.mk base n).Fits w) (i : Fin n) :
    (Region.mk base n).Contains (address w base i) := Region.contains_index hf i.isLt

theorem address_disjoint (hf : (Region.mk base n).Fits w)
    (hg : (Region.mk other m).Fits w)
    (hs : (Region.mk base n).Separated ⟨other, m⟩) (i : Fin n) (j : Fin m) :
    address w base i ≠ address w other j := by
  intro he
  have h := Region.not_contains_of_separated hs (address_contains hf i)
  exact h (he ▸ address_contains hg j)

/-- The frozen block discipline leaves cell base for deduplication, then puts
root and child stages in adjacent blocks of width w. -/
def stageBase (base w stage : Nat) : Nat := base + 1 + w*stage

theorem stages_separated (h : i < j) :
    (Region.mk (stageBase base w i) w).Separated ⟨stageBase base w j, w⟩ := by
  left
  dsimp [stageBase]
  have hmul := Nat.mul_le_mul_left w (show i+1 ≤ j by omega)
  simp only [Nat.mul_add, Nat.mul_one] at hmul
  omega

theorem dedup_separated :
    (Region.mk base 1).Separated ⟨stageBase base w stage, w⟩ := by
  left
  dsimp [stageBase]
  omega

theorem stage_fits (hf : base+1+w*count < modulus w) (hi : stage < count) :
    (Region.mk (stageBase base w stage) w).Fits w := by
  have hmul := Nat.mul_le_mul_left w (show stage+1 ≤ count by omega)
  simp only [Nat.mul_add, Nat.mul_one] at hmul
  dsimp [Region.Fits, stageBase]
  omega

theorem dedup_fits (hf : base+1+w*count < modulus w) :
    (Region.mk base 1).Fits w := by
  dsimp [Region.Fits]
  omega

end WordRam.RandomBlocks
