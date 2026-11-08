import DataStructures.PerfectHash.Acceptance
import WordRam.Regions

namespace PerfectHash.Construction
open WordRam Buckets

variable {Key : Type*} {m : Nat}

@[simp] theorem count_append (hash : Key → Fin m) (xs ys : List Key) (b : Fin m) :
    count hash (xs++ys) b = count hash xs b+count hash ys b := by
  simp [count,keys,List.filter_append]

theorem energy_append_right (hash : Key → Fin m) (xs ys : List Key) :
    energy hash ys ≤ energy hash (xs++ys) := by
  apply Finset.sum_le_sum
  intro b _
  rw [count_append]
  exact Nat.pow_le_pow_left (Nat.le_add_left _ _) 2

theorem energy_perm (hash : Key → Fin m) (h : xs.Perm ys) :
    energy hash xs = energy hash ys := by
  unfold energy count keys
  congr 1
  funext b
  rw [(h.filter _).length_eq]

/-- A root trial maintains a remaining energy allowance. The increment is
checked before subtraction; no quadratic energy is ever held in a word. -/
def groupAccepted (hash : Key → Fin m) (budget : Nat) (seen : List Key) : List Key → Bool
  | [] => true
  | x::xs => if 2*count hash seen (hash x)+1 ≤ budget then
      groupAccepted hash (budget-(2*count hash seen (hash x)+1)) (x::seen) xs
    else false

/-- Early rejection agrees exactly with the full mathematical root predicate. -/
theorem groupAccepted_iff (hash : Key → Fin m) (budget : Nat) (seen rest : List Key) :
    groupAccepted hash budget seen rest = true ↔
      energy hash (rest.reverse++seen) ≤ energy hash seen+budget := by
  induction rest generalizing seen budget with
  | nil => simp [groupAccepted]
  | cons x xs ih =>
    have he : energy hash ((x::xs).reverse++seen) = energy hash (xs.reverse++(x::seen)) := by
      simp [List.reverse_cons,List.append_assoc]
    rw [he,groupAccepted]
    split
    · rename_i hh
      rw [ih,energy_cons]
      omega
    · rename_i hh
      have hm := energy_append_right hash xs.reverse (x::seen)
      rw [energy_cons] at hm
      simp only [Bool.false_eq_true, false_iff]
      omega

/-- A safe increment uses only the linear input bound, even for a rejected root. -/
theorem energy_increment_fit {w d : Nat} (hash : Key → Fin m) (seen : List Key)
    (x : Key) (hn : seen.length < d) (hf : 64*(d+1) < modulus w) :
    2*count hash seen (hash x)+1 < modulus w := by
  have hc := count_le hash seen (hash x)
  omega

theorem energy_budget_fit {w d budget : Nat} (hb : budget ≤ 6*d)
    (hf : 64*(d+1) < modulus w) : budget < modulus w := by omega

/-- The word comparison and subtraction implement the natural capped update. -/
theorem energy_word_update {w c budget : Nat} (hc : 2*c+1 < modulus w)
    (hb : budget < modulus w) :
    ((word w budget).toNat < (word w c*word w 2+word w 1).toNat ↔ budget < 2*c+1) ∧
    (2*c+1 ≤ budget → word w budget-(word w c*word w 2+word w 1) = word w (budget-(2*c+1))) := by
  rw [word_mul,word_add,Nat.mul_comm c 2,word_toNat_of_lt hc,word_toNat_of_lt hb]
  exact ⟨Iff.rfl,fun h => word_sub _ _ hc h⟩

end PerfectHash.Construction
