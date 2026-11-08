import Hashing.Family
import Hashing.PowerOfTwo
import Probability.Finite
import Mathlib.Data.List.Nodup

/-! FKS bucket counting is independent of physical memory and machine execution.
The key list is distinct when applying collision probabilities. -/
namespace PerfectHash.Buckets

variable {Key : Type*} {m : Nat}

/-- Preserve input order within one mathematical bucket. -/
def keys (hash : Key → Fin m) (xs : List Key) (b : Fin m) : List Key :=
  xs.filter (fun x => hash x == b)

def count (hash : Key → Fin m) (xs : List Key) (b : Fin m) : Nat := (keys hash xs b).length

def energy (hash : Key → Fin m) (xs : List Key) : Nat := ∑ b : Fin m, (count hash xs b)^2

/-- Count each unordered pair of input positions once, against its later suffix. -/
def pairs (hash : Key → Fin m) : List Key → Nat
  | [] => 0
  | x::xs => count hash xs (hash x)+pairs hash xs

@[simp] theorem mem_keys (hash : Key → Fin m) (xs : List Key) (b : Fin m) (x : Key) :
    x ∈ keys hash xs b ↔ x ∈ xs ∧ hash x = b := by simp [keys]

@[simp] theorem count_nil (hash : Key → Fin m) (b : Fin m) : count hash [] b = 0 := rfl

@[simp] theorem count_cons (hash : Key → Fin m) (x : Key) (xs : List Key) (b : Fin m) :
    count hash (x::xs) b = count hash xs b + if hash x = b then 1 else 0 := by
  by_cases h : hash x = b <;> simp [count,keys,h]

theorem count_le (hash : Key → Fin m) (xs : List Key) (b : Fin m) :
    count hash xs b ≤ xs.length := List.length_filter_le _ _

theorem nodup (hash : Key → Fin m) (xs : List Key) (b : Fin m) (hx : xs.Nodup) :
    (keys hash xs b).Nodup := hx.filter _

/-- Buckets partition all input occurrences, including when some buckets are empty. -/
theorem sum_count (hash : Key → Fin m) (xs : List Key) :
    (∑ b : Fin m, count hash xs b) = xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [count_cons,Finset.sum_add_distrib,ih]

@[simp] theorem energy_nil (hash : Key → Fin m) : energy hash [] = 0 := by simp [energy]

theorem energy_cons (hash : Key → Fin m) (x : Key) (xs : List Key) :
    energy hash (x::xs) = energy hash xs+2*count hash xs (hash x)+1 := by
  have he (b : Fin m) : (count hash (x::xs) b)^2 =
      (count hash xs b)^2 + if hash x = b then 2*count hash xs b+1 else 0 := by
    by_cases h : hash x = b <;> simp [count_cons,h] <;> ring
  simp only [energy,he,Finset.sum_add_distrib]
  simp [Finset.sum_ite_eq',Nat.add_assoc]

/-- The energy is the number of diagonal pairs plus twice the unordered collisions. -/
theorem energy_identity (hash : Key → Fin m) (xs : List Key) :
    energy hash xs = xs.length+2*pairs hash xs := by
  induction xs with
  | nil => simp [pairs]
  | cons x xs ih => rw [energy_cons,ih]; simp only [pairs,List.length_cons]; omega

theorem count_square_le_energy (hash : Key → Fin m) (xs : List Key) (b : Fin m) :
    (count hash xs b)^2 ≤ energy hash xs := by
  unfold energy
  exact Finset.single_le_sum (f := fun b => (count hash xs b)^2) (fun _ _ => Nat.zero_le _) (Finset.mem_univ b)

/-- A bucket is collision free precisely when its hash is injective on the input list. -/
theorem pairs_zero_iff [DecidableEq Key] (hash : Key → Fin m) (xs : List Key) (hx : xs.Nodup) :
    pairs hash xs = 0 ↔ Set.InjOn hash {x | x ∈ xs} := by
  induction xs with
  | nil => simp [pairs,Set.InjOn]
  | cons x xs ih =>
    obtain ⟨hn,ht⟩ := List.nodup_cons.mp hx
    rw [pairs,Nat.add_eq_zero,ih ht]
    constructor
    · rintro ⟨hc,hi⟩ a ha b hb he
      simp only [Set.mem_setOf_eq,List.mem_cons] at ha hb
      have hnone : ∀ y ∈ xs, hash y ≠ hash x := by
        intro y hy heq
        have hm : y ∈ keys hash xs (hash x) := (mem_keys hash xs (hash x) y).mpr ⟨hy,heq⟩
        have hz : keys hash xs (hash x) = [] := List.length_eq_zero_iff.mp hc
        simpa [hz] using hm
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · rfl
      · exact False.elim (hnone b hb he.symm)
      · exact False.elim (hnone a ha he)
      · exact hi ha hb he
    · intro hi
      constructor
      · apply List.length_eq_zero_iff.mpr
        apply List.eq_nil_iff_forall_not_mem.mpr
        intro y hy
        obtain ⟨hy,he⟩ := (mem_keys hash xs (hash x) y).mp hy
        have heq := hi (by simp [hy] : y ∈ {z | z ∈ x::xs}) (by simp) he
        exact hn (heq ▸ hy)
      · intro a ha b hb he
        exact hi (by simp_all) (by simp_all) he

noncomputable section
open FiniteProbability
open scoped Classical
variable {Key Seed : Type} [DecidableEq Key] [Fintype Seed] [Nonempty Seed]

/-- A key distinct from every suffix key has no diagonal self-collision term. -/
theorem expected_count (family : Hashing.Family Key Seed m) (hc : Hashing.CollisionBound family c)
    (hm : 0 < m) (x : Key) (xs : List Key) (hx : x ∉ xs) :
    mean (fun a => (count (family.eval a) xs (family.eval a x) : ℝ)) ≤ (c : ℝ)/m*xs.length := by
  induction xs with
  | nil => simp
  | cons y xs ih =>
    have hn : y ≠ x := by simp only [List.mem_cons,not_or] at hx; exact Ne.symm hx.1
    have ht : x ∉ xs := fun h => hx (by simp [h])
    have he (a : Seed) : (count (family.eval a) (y::xs) (family.eval a x) : ℝ) =
        (count (family.eval a) xs (family.eval a x) : ℝ) +
        if family.eval a y = family.eval a x then 1 else 0 := by
      rw [count_cons,Nat.cast_add]
      split <;> simp
    rw [mean_congr he,mean_add,mean_indicator,probability_pmf]
    have hp := hc.probability hm hn
    unfold Hashing.uniformLaw at hp
    have hh := ih ht
    simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
    nlinarith

/-- The elementary expectation bound suffices for both root and child acceptance;
the exact diagonal identity is proved separately above. -/
theorem expected_pairs (family : Hashing.Family Key Seed m) (hc : Hashing.CollisionBound family c)
    (hm : 0 < m) (xs : List Key) (hx : xs.Nodup) :
    mean (fun a => (pairs (family.eval a) xs : ℝ)) ≤ (c : ℝ)/m*xs.length*(xs.length-1)/2 := by
  induction xs with
  | nil => simp [pairs]
  | cons x xs ih =>
    obtain ⟨hn,ht⟩ := List.nodup_cons.mp hx
    have hh := expected_count family hc hm x xs hn
    have hi := ih ht
    have he (a : Seed) : (pairs (family.eval a) (x::xs) : ℝ) =
        (count (family.eval a) xs (family.eval a x) : ℝ)+(pairs (family.eval a) xs : ℝ) := by
      simp [pairs]
    rw [mean_congr he,mean_add]
    have hp : (0 : ℝ) ≤ c/m := by positivity
    simp only [List.length_cons,Nat.cast_add,Nat.cast_one]
    nlinarith

theorem expected_energy (family : Hashing.Family Key Seed m) (hc : Hashing.CollisionBound family c)
    (hm : 0 < m) (xs : List Key) (hx : xs.Nodup) :
    mean (fun a => (energy (family.eval a) xs : ℝ)) ≤ xs.length+(c : ℝ)/m*xs.length*(xs.length-1) := by
  have he (a : Seed) : (energy (family.eval a) xs : ℝ) =
      (xs.length : ℝ)+2*(pairs (family.eval a) xs : ℝ) := by rw [energy_identity]; push_cast; rfl
  rw [mean_congr he,mean_add,mean_const,mean_mul]
  have hh := expected_pairs family hc hm xs hx
  linarith

end
end PerfectHash.Buckets
