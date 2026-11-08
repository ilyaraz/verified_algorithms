import DataStructures.PerfectHash.Acceptance

namespace PerfectHash.Sizes
open Hashing.PowerOfTwo Buckets

/-- Empty buckets have no slots; singleton buckets use one direct slot; all other
buckets round twice their squared cardinality to a power of two. -/
def childSlots (b : Nat) : Nat :=
  if b ≤ 1 then b else computeSize (2*b*b)

def headerWords : Nat := 4

def directoryWords : Nat := 4

def slotWords : Nat := 2

/-- Retained words include the header, every directory entry, occupancy, and keys. -/
def retained (hash : Key → Fin m) (xs : List Key) : Nat :=
  headerWords+directoryWords*m+slotWords*∑ b : Fin m, childSlots (count hash xs b)

@[simp] theorem childSlots_zero : childSlots 0 = 0 := rfl
@[simp] theorem childSlots_one : childSlots 1 = 1 := rfl

theorem childSlots_many (hb : 2 ≤ b) : childSlots b = size (2*b^2) := by
  simp only [childSlots,show ¬ b ≤ 1 by omega,↓reduceIte,computeSize_eq]
  congr 1
  ring

theorem childSlots_le (b : Nat) : childSlots b ≤ 4*b^2 := by
  by_cases hb : b ≤ 1
  · interval_cases b <;> decide
  · rw [childSlots_many (by omega)]
    have hb0 : 0 < b := by omega
    have hp : 0 < 2*b^2 := by positivity
    have ht := less_than_twice hp
    omega

theorem childSlots_covers (hb : 2 ≤ b) : 2*b^2 ≤ childSlots b := by
  rw [childSlots_many hb]
  exact covers _

theorem total_slots (hash : Key → Fin m) (xs : List Key)
    (ha : energy hash xs ≤ 6*xs.length) :
    (∑ b : Fin m, childSlots (count hash xs b)) ≤ 24*xs.length := by
  have hh := Finset.sum_le_sum (fun b (_ : b ∈ (Finset.univ : Finset (Fin m))) => childSlots_le (count hash xs b))
  rw [← Finset.mul_sum] at hh
  change _ ≤ 4*energy hash xs at hh
  omega

theorem retained_linear (hash : Key → Fin m) (xs : List Key)
    (ha : energy hash xs ≤ 6*xs.length) (hm : m ≤ 2*(xs.length+1)) :
    retained hash xs ≤ 64*(xs.length+1) := by
  have hs := total_slots hash xs ha
  unfold retained headerWords directoryWords slotWords
  omega

/-- The sum of each child's own clearing/insertion budget is linear after root
acceptance. Charging every child by the largest child's size is unnecessary. -/
theorem child_work_linear (hash : Key → Fin m) (xs : List Key)
    (ha : energy hash xs ≤ 6*xs.length) (hm : m ≤ 2*(xs.length+1)) :
    (∑ b : Fin m, (childSlots (count hash xs b)+count hash xs b+1)) ≤ 27*xs.length+2 := by
  have hs := total_slots hash xs ha
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
    smul_eq_mul,mul_one,sum_count]
  omega

/-- Each accepted bucket's square and rounded allocation are bounded by the root
energy, so their word fit follows from a linear capacity assumption. -/
theorem child_fit (hash : Key → Fin m) (xs : List Key)
    (ha : energy hash xs ≤ 6*xs.length) (hf : 64*(xs.length+1) < 2^w) (b : Fin m) :
    2*(count hash xs b)^2 < 2^w ∧ childSlots (count hash xs b) < 2^w := by
  have he := count_square_le_energy hash xs b
  have hs := childSlots_le (count hash xs b)
  constructor <;> omega

theorem child_bits_fit (hash : Key → Fin m) (xs : List Key)
    (ha : energy hash xs ≤ 6*xs.length) (hf : 64*(xs.length+1) < 2^w) (b : Fin m) :
    bits (2*(count hash xs b)^2) ≤ w :=
  least (Nat.le_of_lt (child_fit hash xs ha hf b).1)

end PerfectHash.Sizes
