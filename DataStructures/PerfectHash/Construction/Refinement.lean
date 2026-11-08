import DataStructures.PerfectHash.Construction.RootInitialization
import DataStructures.PerfectHash.Construction.ChildInitialization
import DataStructures.PerfectHash.Construction.Allocation
import DataStructures.PerfectHash.Construction.Enumeration

namespace PerfectHash.Construction
open WordRam Buckets

/-- The overflow-safe root guard implements exactly M5's root acceptance event. -/
theorem root_acceptance (family : Hashing.Family Key Seed m) (xs : List Key) (a : Seed) :
    groupAccepted (family.eval a) (6*xs.length) [] xs = rootAccept family xs a := by
  apply Bool.eq_iff_iff.mpr
  rw [groupAccepted_iff]
  simp only [energy_nil,Nat.zero_add,List.append_nil,rootAccept,decide_eq_true_eq]
  rw [energy_perm _ (List.reverse_perm xs),energy_identity]

/-- The occupied-slot test agrees with the mathematical collision-free child
predicate. The distinctness hypothesis comes from the separate deduplication pass. -/
theorem child_acceptance [DecidableEq Key] (family : Hashing.Family Key Seed m)
    (xs : List Key) (hx : xs.Nodup) (a : Seed) :
    childAccepted (fun x => (family.eval a x).val) [] xs = childAccept family xs a := by
  apply Bool.eq_iff_iff.mpr
  rw [childAccepted_iff _ _ _ (by simp)]
  simp only [List.append_nil,List.map_reverse,List.nodup_reverse,childAccept,decide_eq_true_eq]
  rw [List.nodup_map_iff_inj_on hx,pairs_zero_iff _ _ hx]
  constructor
  · intro hi x hx y hy he
    exact hi x hx y hy (congrArg Fin.val he)
  · intro hi x hx y hy he
    exact hi hx hy (Fin.ext he)

/-- Concrete trial costs refine their own abstract budgets, including the last
rejected probe and the halt instruction. -/
theorem root_cost (h : k ≤ 20*m+25*d+9) : k ≤ 40*(d+m+1) := by omega

theorem child_cost (h : k ≤ 10*q+17*b+7) : k ≤ 20*(q+b+1) := by omega

theorem allocation_bits (b : Nat) : Hashing.PowerOfTwo.bits (2*b*b) ≤ Sizes.childSlots b := by
  by_cases hb : b ≤ 1
  · rw [← Hashing.PowerOfTwo.computeBits_eq]
    interval_cases b <;> decide
  · have hc : Hashing.PowerOfTwo.bits (2*b*b) ≤ 2*b*b :=
      Hashing.PowerOfTwo.least (Nat.le_of_lt Nat.lt_two_pow_self)
    have hs : 2*b*b ≤ Sizes.childSlots b := by
      simpa [Sizes.childSlots,hb,Hashing.PowerOfTwo.computeSize_eq] using
        Hashing.PowerOfTwo.covers (2*b*b)
    omega

theorem allocation_cost (h : k ≤ 4*Hashing.PowerOfTwo.bits (2*b*b)+18) :
    k ≤ 22*(Sizes.childSlots b+b+1) := by have := allocation_bits b; omega

end PerfectHash.Construction
