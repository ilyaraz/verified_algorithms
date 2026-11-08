import DataStructures.PerfectHash.Build.Model

namespace PerfectHash.Build
open Buckets Sizes FiniteProbability
open scoped Classical
noncomputable section

variable {Key Seed : Type} {m : Nat} {xs : List Key}

def Model.rootBudget (_model : Model Key Seed m xs) : Nat := xs.length+m+1

def Model.childBudget (model : Model Key Seed m xs) (a : Seed) (b : Fin m) : Nat :=
  childSlots (count (model.root.eval a) xs b)+count (model.root.eval a) xs b+1

def Model.rootWork (model : Model Key Seed m xs) (samples : Fin model.attempts → Seed) : Nat :=
  FiniteSearch.searchWork (rootAccept model.root xs) model.enumeration model.rootBudget model.attempts samples

def Model.childWork (model : Model Key Seed m xs) (a : Seed) (b : Fin m)
    (samples : Fin model.attempts → Seed) : Nat :=
  if (model.childKeys a b).length ≤ 1 then model.childBudget a b
  else FiniteSearch.searchWork (childAccept (model.child a b) (model.childKeys a b))
    model.enumeration (model.childBudget a b) model.attempts samples

/-- Charged abstract work includes every tested seed and each direct child.
The root-dependent child costs remain inside the same observation. -/
def Model.work (model : Model Key Seed m xs)
    (samples : (Fin model.attempts → Seed) × (Fin m → Fin model.attempts → Seed)) : Nat :=
  model.rootWork samples.1 + match model.rootSearch samples.1 with
    | none => 0
    | some a => ∑ b : Fin m, model.childWork a b (samples.2 b)

variable [DecidableEq Key] [Fintype Seed] [Nonempty Seed]

theorem model_child_rejection (model : Model Key Seed m xs) (hyp : Hypotheses model)
    {a : Seed} (ha : rootAccept model.root xs a = true) (b : Fin m) :
    Retry.rejection (childAccept (model.child a b) (model.childKeys a b)) ≤ 1/2 := by
  have hp : 0 < Hashing.PowerOfTwo.computeSize
      (2*(count (model.root.eval a) xs b)*(count (model.root.eval a) xs b)) := by
    rw [Hashing.PowerOfTwo.computeSize_eq]
    exact Hashing.PowerOfTwo.positive _
  have hcover : 2*(model.childKeys a b).length^2 ≤ Hashing.PowerOfTwo.computeSize
      (2*(count (model.root.eval a) xs b)*(count (model.root.eval a) xs b)) := by
    rw [Hashing.PowerOfTwo.computeSize_eq]
    convert Hashing.PowerOfTwo.covers (2*(count (model.root.eval a) xs b)^2) using 1 <;>
      simp only [Model.childKeys,count] <;> congr 1 <;> ring
  exact child_rejection (model.child a b) (hyp.child_collision a ha b) hp
    (model.childKeys a b) (nodup _ _ _ hyp.distinct) hcover

/-- The w-attempt, 2^(w-1)-candidate search bound applies to actual tested trials. -/
theorem expected_search_word (accept : Seed → Bool) (hq : Retry.rejection accept ≤ 1/2)
    (enumeration : List Seed) (r B : Nat) (hen : enumeration.length = 2^(r-1)) :
    mean (fun samples : Fin r → Seed => (FiniteSearch.searchWork accept enumeration B r samples : ℝ)) ≤ 3*B := by
  apply le_trans _ (FiniteSearch.expected_work_word accept hq B r)
  apply mean_mono
  intro samples
  have hh := FiniteSearch.searchWork_le accept enumeration B r samples
  rw [hen] at hh
  exact_mod_cast hh

theorem expected_root_work (model : Model Key Seed m xs) (hyp : Hypotheses model) :
    mean (fun samples => (model.rootWork samples : ℝ)) ≤ 3*model.rootBudget :=
  expected_search_word _
    (root_rejection model.root hyp.root_collision hyp.buckets_pos xs hyp.distinct hyp.buckets_cover)
    _ _ _ hyp.enumeration_length

theorem expected_child_work (model : Model Key Seed m xs) (hyp : Hypotheses model)
    {a : Seed} (ha : rootAccept model.root xs a = true) (b : Fin m) :
    mean (fun samples => (model.childWork a b samples : ℝ)) ≤ 3*model.childBudget a b := by
  by_cases hb : (model.childKeys a b).length ≤ 1
  · simp only [Model.childWork,hb,↓reduceIte,mean_const]
    have hh := Nat.cast_nonneg (model.childBudget a b) (α := ℝ)
    linarith
  · simp only [Model.childWork,hb,↓reduceIte]
    exact expected_search_word _ (model_child_rejection model hyp ha b) _ _ _ hyp.enumeration_length

theorem expected_children_work (model : Model Key Seed m xs) (hyp : Hypotheses model)
    {a : Seed} (ha : rootAccept model.root xs a = true) :
    mean (fun samples : Fin m → Fin model.attempts → Seed =>
      ((∑ b : Fin m, model.childWork a b (samples b)) : ℝ)) ≤ 3*(27*xs.length+2) := by
  have he : ∀ samples : Fin m → Fin model.attempts → Seed,
      ((∑ b : Fin m, model.childWork a b (samples b)) : ℝ) =
        ∑ b : Fin m, (model.childWork a b (samples b) : ℝ) := by intro samples; push_cast; rfl
  rw [mean_congr he,mean_sum]
  have hb : (∑ b : Fin m, mean (fun samples : Fin m → Fin model.attempts → Seed =>
      (model.childWork a b (samples b) : ℝ))) ≤ ∑ b : Fin m, (3 : ℝ)*model.childBudget a b := by
    apply Finset.sum_le_sum
    intro b _
    rw [mean_apply b (fun samples => (model.childWork a b samples : ℝ))]
    exact expected_child_work model hyp ha b
  have hs := child_work_linear (model.root.eval a) xs (accepted_energy model ha) hyp.buckets_bound
  have hs' : (∑ b : Fin m, (model.childBudget a b : ℝ)) ≤ 27*xs.length+2 := by
    exact_mod_cast hs
  rw [← Finset.mul_sum] at hb
  linarith

/-- Conditional child budgets are averaged after the root block, keeping each
child's own size. This theorem concerns abstract trial work, not RAM instructions. -/
theorem expected_work (model : Model Key Seed m xs) (hyp : Hypotheses model) :
    mean (fun samples => (model.work samples : ℝ)) ≤ 90*(xs.length+1) := by
  rw [mean_prod]
  have he : ∀ roots : Fin model.attempts → Seed,
      mean (fun children : Fin m → Fin model.attempts → Seed => (model.work (roots,children) : ℝ)) ≤
        (model.rootWork roots : ℝ)+3*(27*xs.length+2) := by
    intro roots
    obtain ⟨a,ha,hgood⟩ := root_search_total model hyp roots
    simp only [Model.work,ha,Nat.cast_add]
    rw [mean_add,mean_const]
    simpa only [Nat.cast_sum] using add_le_add_left (expected_children_work model hyp hgood)
      (model.rootWork roots : ℝ)
  have hh := mean_mono he
  rw [mean_add,mean_const] at hh
  have hr := expected_root_work model hyp
  have hm : (m : ℝ) ≤ 2*(xs.length+1) := by exact_mod_cast hyp.buckets_bound
  simp only [Model.rootBudget,Nat.cast_add,Nat.cast_one] at hr
  nlinarith

theorem search_work_worst (accept : Seed → Bool) (enumeration : List Seed) (B r : Nat)
    (samples : Fin r → Seed) :
    FiniteSearch.searchWork accept enumeration B r samples ≤ B*(r+enumeration.length) :=
  (FiniteSearch.searchWork_le _ _ _ _ _).trans (FiniteSearch.work_le _ _ _ _ _)

theorem work_worst (model : Model Key Seed m xs) (hyp : Hypotheses model)
    (samples : (Fin model.attempts → Seed) × (Fin m → Fin model.attempts → Seed)) :
    model.work samples ≤ (30*xs.length+5)*(model.attempts+model.enumeration.length) := by
  obtain ⟨a,ha,hgood⟩ := root_search_total model hyp samples.1
  have hr := search_work_worst (rootAccept model.root xs) model.enumeration model.rootBudget model.attempts samples.1
  have hen : 0 < model.enumeration.length := by rw [hyp.enumeration_length]; positivity
  have hc (b : Fin m) : model.childWork a b (samples.2 b) ≤
      model.childBudget a b*(model.attempts+model.enumeration.length) := by
    unfold Model.childWork
    split
    · exact Nat.le_mul_of_pos_right _ (by omega)
    · exact search_work_worst _ _ _ _ _
  have hsum := Finset.sum_le_sum (fun b (_ : b ∈ (Finset.univ : Finset (Fin m))) => hc b)
  rw [← Finset.sum_mul] at hsum
  have hs := child_work_linear (model.root.eval a) xs (accepted_energy model hgood) hyp.buckets_bound
  have htotal : model.rootBudget+(∑ b : Fin m, model.childBudget a b) ≤ 30*xs.length+5 := by
    have hm := hyp.buckets_bound
    change xs.length+m+1+(∑ b : Fin m, _) ≤ _
    change (∑ b : Fin m, model.childBudget a b) ≤ 27*xs.length+2 at hs
    omega
  unfold Model.work
  rw [ha]
  have hmul := Nat.mul_le_mul_right (model.attempts+model.enumeration.length) htotal
  change model.rootWork samples.1 ≤ _ at hr
  nlinarith

end
end PerfectHash.Build
