import WordRam.Properties
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-! The uniform law of a complete, immutable random memory. Probability is kept
out of the executable machine modules. Real-valued event probabilities below
are proved to agree with the finite PMF. -/
namespace WordRam

noncomputable section
open scoped Classical BigOperators ENNReal

def wordEquivFin (w : Nat) : Word w ≃ Fin (modulus w) where
  toFun := BitVec.toFin
  invFun := BitVec.ofFin
  left_inv _ := rfl
  right_inv _ := rfl

instance wordFintype (w : Nat) : Fintype (Word w) :=
  Fintype.ofEquiv (Fin (modulus w)) (wordEquivFin w).symm

@[simp] theorem card_word (w : Nat) : Fintype.card (Word w) = modulus w :=
  (Fintype.card_congr (wordEquivFin w)).trans (Fintype.card_fin _)

@[simp] theorem card_randomMemory (w : Nat) :
    Fintype.card (RandomMemory w) = modulus w ^ modulus w := by
  simp only [RandomMemory, Addr, Fintype.card_fun, card_word]

/-- All `2^w` cells are sampled independently and uniformly, once. -/
def randomMemoryLaw (w : Nat) : PMF (RandomMemory w) :=
  PMF.uniformOfFintype (RandomMemory w)

def runLaw (p : Program R) (fuel : Nat) (s : State w R) : PMF (RunResult w R) :=
  (randomMemoryLaw w).map (fun rho => run p rho fuel s)

theorem randomMemoryLaw_apply (rho : RandomMemory w) :
    randomMemoryLaw w rho = ((modulus w ^ modulus w : Nat) : ℝ≥0∞)⁻¹ := by
  simp [randomMemoryLaw, PMF.uniformOfFintype_apply]

def eventCount (E : RandomMemory w → Prop) : Nat := Fintype.card {rho // E rho}

/-- Real notation for exact finite-uniform probabilities. -/
def probability (E : RandomMemory w → Prop) : ℝ :=
  (eventCount E : ℝ) / Fintype.card (RandomMemory w)

theorem probability_eq_pmf (E : RandomMemory w → Prop) :
    probability E = ((randomMemoryLaw w).toOuterMeasure {rho | E rho}).toReal := by
  rw [randomMemoryLaw, PMF.toOuterMeasure_uniformOfFintype_apply]
  simp [probability, eventCount, ENNReal.toReal_div]

def runProbability (p : Program R) (fuel : Nat) (s : State w R)
    (E : RunResult w R → Prop) : ℝ := probability (fun rho => E (run p rho fuel s))

theorem runProbability_eq_pmf (p : Program R) (fuel : Nat) (s : State w R)
    (E : RunResult w R → Prop) :
    runProbability p fuel s E = ((runLaw p fuel s).toOuterMeasure {r | E r}).toReal := by
  rw [runLaw, PMF.toOuterMeasure_map_apply]
  exact probability_eq_pmf _

theorem probability_nonneg (E : RandomMemory w → Prop) : 0 ≤ probability E := by
  exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem probability_le_one (E : RandomMemory w → Prop) : probability E ≤ 1 := by
  have hc := Fintype.card_subtype_le E
  have hp : (0 : ℝ) < Fintype.card (RandomMemory w) := by exact_mod_cast Fintype.card_pos
  exact (div_le_one hp).mpr (by exact_mod_cast hc)

@[simp] theorem probability_true : probability (w := w) (fun _ => True) = 1 := by
  simp [probability, eventCount]

@[simp] theorem probability_false : probability (w := w) (fun _ => False) = 0 := by
  simp [probability, eventCount]

theorem probability_congr {E F : RandomMemory w → Prop} (h : ∀ rho, E rho ↔ F rho) :
    probability E = probability F := by
  have he : E = F := funext (fun rho => propext (h rho))
  rw [he]

/-- A finite partial table; values outside `cells` do not constrain the memory. -/
def Matches (cells : Finset (Addr w)) (values rho : RandomMemory w) : Prop :=
  ∀ a ∈ cells, rho a = values a

/-- Extensions of a partial table are in bijection with assignments to its complement. -/
def extensionsEquiv (cells : Finset (Addr w)) (values : RandomMemory w) :
    {rho // Matches cells values rho} ≃ ({a // a ∉ cells} → Word w) where
  toFun rho a := rho.val a.val
  invFun f := ⟨fun a => if h : a ∈ cells then values a else f ⟨a, h⟩, by
    intro a ha
    simp [ha]⟩
  left_inv rho := by
    apply Subtype.ext
    funext a
    dsimp only
    by_cases ha : a ∈ cells
    · simpa [ha] using (rho.property a ha).symm
    · simp [ha]
  right_inv f := by
    funext a
    simp [a.property]

theorem count_matches (cells : Finset (Addr w)) (values : RandomMemory w) :
    eventCount (Matches cells values) = modulus w ^ (modulus w - cells.card) := by
  unfold eventCount
  rw [Fintype.card_congr (extensionsEquiv cells values), Fintype.card_fun,
    Fintype.card_subtype_compl]
  simp

theorem probability_matches (cells : Finset (Addr w)) (values : RandomMemory w) :
    probability (Matches cells values) = ((modulus w : ℝ) ^ cells.card)⁻¹ := by
  have hle : cells.card ≤ modulus w := by simpa using cells.card_le_univ
  have hpos : (0 : ℝ) < modulus w := by exact_mod_cast Nat.two_pow_pos w
  rw [probability, count_matches, card_randomMemory]
  push_cast
  have he : modulus w = (modulus w - cells.card) + cells.card := by omega
  conv_lhs => arg 2; rw [he, pow_add]
  field_simp

theorem probability_matches_pos (cells : Finset (Addr w)) (values : RandomMemory w) :
    0 < probability (Matches cells values) := by
  rw [probability_matches]
  positivity

theorem probability_cell (a : Addr w) (x : Word w) :
    probability (fun rho => rho a = x) = (modulus w : ℝ)⁻¹ := by
  calc
    _ = probability (Matches {a} (fun _ => x)) := probability_congr (by
      intro rho
      simp [Matches])
    _ = _ := by simpa using probability_matches {a} (fun _ => x)

/-- Extend assignments at named cells to a total table; injectivity makes this
agree with every requested value. The default outside the image is irrelevant. -/
def assignedValues (addresses : Fin k → Addr w) (values : Fin k → Word w) : RandomMemory w :=
  fun a => if h : ∃ i, addresses i = a then values (Classical.choose h) else 0

theorem assignedValues_apply (addresses : Fin k → Addr w)
    (hinj : Function.Injective addresses) (values : Fin k → Word w) (i : Fin k) :
    assignedValues addresses values (addresses i) = values i := by
  unfold assignedValues
  split
  · rename_i h
    rw [hinj (Classical.choose_spec h)]
  · rename_i h
    exact False.elim (h ⟨i, rfl⟩)

/-- Full finite independence, for any injective list of addresses. -/
theorem probability_distinct_cells (addresses : Fin k → Addr w)
    (hinj : Function.Injective addresses) (values : Fin k → Word w) :
    probability (fun rho => ∀ i, rho (addresses i) = values i) =
      ((modulus w : ℝ) ^ k)⁻¹ := by
  let cells := Finset.univ.image addresses
  have he : ∀ rho, (∀ i, rho (addresses i) = values i) ↔
      Matches cells (assignedValues addresses values) rho := by
    intro rho
    constructor
    · intro hh a ha
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
      rw [assignedValues_apply addresses hinj]
      exact hh i
    · intro hh i
      have h := hh (addresses i) (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
      simpa [assignedValues_apply addresses hinj] using h
  rw [probability_congr he, probability_matches]
  have hc : cells.card = k := by
    simp [cells, Finset.card_image_of_injective _ hinj]
  rw [hc]

theorem probability_two_cells (a b : Addr w) (hab : a ≠ b) (x y : Word w) :
    probability (fun rho => rho a = x ∧ rho b = y) = ((modulus w : ℝ)^2)⁻¹ := by
  have he : ∀ rho, (rho a = x ∧ rho b = y) ↔
      Matches {a, b} (update (fun _ => y) a x) rho := by
    intro rho
    simp [Matches, update, Ne.symm hab]
  rw [probability_congr he, probability_matches]
  simp [hab]

/-- The two observations of one cell have the diagonal law. -/
theorem probability_repeated_cell (a : Addr w) (x y : Word w) :
    probability (fun rho => rho a = x ∧ rho a = y) =
      if x = y then (modulus w : ℝ)⁻¹ else 0 := by
  by_cases h : x = y
  · subst y
    simpa using probability_cell a x
  · rw [if_neg h]
    calc
      _ = probability (w := w) (fun _ => False) := probability_congr (by
        intro rho
        simp only [iff_false]
        rintro ⟨hx, hy⟩
        exact h (hx.symm.trans hy))
      _ = 0 := probability_false

def conditionalProbability (E H : RandomMemory w → Prop) : ℝ :=
  probability (fun rho => E rho ∧ H rho) / probability H

/-- A fresh cell remains uniform after a specified partial table is observed. -/
theorem conditional_fresh_cell (cells : Finset (Addr w)) (values : RandomMemory w)
    (a : Addr w) (ha : a ∉ cells) (x : Word w) :
    conditionalProbability (fun rho => rho a = x) (Matches cells values) =
      (modulus w : ℝ)⁻¹ := by
  have he : ∀ rho, (rho a = x ∧ Matches cells values rho) ↔
      Matches (insert a cells) (update values a x) rho := by
    intro rho
    simp only [Matches, Finset.mem_insert, forall_eq_or_imp, update_same]
    constructor
    · rintro ⟨hx, hh⟩
      refine ⟨hx, fun b hb => ?_⟩
      have hba : b ≠ a := by rintro rfl; exact ha hb
      simpa [update, hba] using hh b hb
    · rintro ⟨hx, hh⟩
      refine ⟨hx, fun b hb => ?_⟩
      have hba : b ≠ a := by rintro rfl; exact ha hb
      simpa [update, hba] using hh b hb
  rw [conditionalProbability, probability_congr he, probability_matches, probability_matches]
  rw [Finset.card_insert_of_notMem ha, pow_succ]
  have hpos : (0 : ℝ) < modulus w := by exact_mod_cast Nat.two_pow_pos w
  field_simp

/-- Expected executed instructions of a bounded run, including incomplete runs. -/
def expectedSteps (p : Program R) (fuel : Nat) (s : State w R) : ℝ :=
  (∑ rho : RandomMemory w, ((run p rho fuel s).steps : ℝ)) /
    Fintype.card (RandomMemory w)

theorem expectedSteps_le (p : Program R) (fuel : Nat) (s : State w R) :
    expectedSteps p fuel s ≤ fuel := by
  have hp : (0 : ℝ) < Fintype.card (RandomMemory w) := by exact_mod_cast Fintype.card_pos
  apply (div_le_iff₀ hp).mpr
  calc
    _ ≤ ∑ _rho : RandomMemory w, (fuel : ℝ) := Finset.sum_le_sum (by
      intro rho _
      exact_mod_cast run_steps_le p rho fuel s)
    _ = _ := by simp [mul_comm]

end
end WordRam
