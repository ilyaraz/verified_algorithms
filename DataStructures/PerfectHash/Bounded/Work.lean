import DataStructures.PerfectHash.Bounded.ChildStage

namespace PerfectHash.Bounded
open WordRam

def childWork (xs : List (Word w)) (l : Layout) (a : Word w) (b : Fin (rootSlots xs)) (rho : RandomMemory w) : Nat :=
  4*Hashing.PowerOfTwo.bits (2*bucketCount xs a b*bucketCount xs a b)+38+
    (10*childCapacity xs a b+17*bucketCount xs a b+20)*childAttempts xs l a b rho

/-- A suffix sum charges each child by its own allocation and stopping time.
The final six instructions include the outer-loop exit and successful halt. -/
def remainingWork (xs : List (Word w)) (l : Layout) (a : Word w) (rho : RandomMemory w) (j : Nat) : Nat :=
  6+∑ b : Fin (rootSlots xs), if j ≤ b.val then childWork xs l a b rho else 0

theorem remainingWork_end (xs : List (Word w)) (l : Layout) (a : Word w) (rho : RandomMemory w) :
    remainingWork xs l a rho (rootSlots xs) = 6 := by
  simp [remainingWork,show ∀ b : Fin (rootSlots xs), ¬ rootSlots xs ≤ b.val from fun b => Nat.not_le.mpr b.isLt]

theorem remainingWork_next (xs : List (Word w)) (l : Layout) (a : Word w) (rho : RandomMemory w)
    (b : Fin (rootSlots xs)) :
    remainingWork xs l a rho b.val = childWork xs l a b rho+remainingWork xs l a rho (b.val+1) := by
  have he (c : Fin (rootSlots xs)) :
      (if b.val ≤ c.val then childWork xs l a c rho else 0) =
      (if c = b then childWork xs l a c rho else 0)+
      (if b.val+1 ≤ c.val then childWork xs l a c rho else 0) := by
    by_cases hc : c = b
    · subst c; simp
    · have hn : c.val ≠ b.val := fun hh => hc (Fin.ext hh)
      by_cases hl : b.val ≤ c.val <;> simp [hc,hl,show (b.val+1 ≤ c.val ↔ b.val ≤ c.val) by omega]
  simp only [remainingWork,he,Finset.sum_add_distrib]
  simp [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

theorem remainingWork_ge (xs : List (Word w)) (l : Layout) (a : Word w) (rho : RandomMemory w) (j : Nat) :
    6 ≤ remainingWork xs l a rho j := by unfold remainingWork; omega

theorem child_attempts_le (hw : 1 ≤ w) (xs : List (Word w)) (l : Layout) (a : Word w)
    (b : Fin (rootSlots xs)) (rho : RandomMemory w) : childAttempts xs l a b rho ≤ w := by
  unfold childAttempts
  split
  · exact hw
  · exact FiniteProbability.Retry.attempts_le _ _ _

theorem child_work_le (hw : 1 ≤ w) (xs : List (Word w)) (l : Layout) (a : Word w)
    (b : Fin (rootSlots xs)) (rho : RandomMemory w) :
    childWork xs l a b rho ≤ 42*(w+1)*(childCapacity xs a b+bucketCount xs a b+1) := by
  have hb := Construction.allocation_bits (bucketCount xs a b)
  have hat := child_attempts_le hw xs l a b rho
  have hh := Nat.mul_le_mul_left (10*childCapacity xs a b+17*bucketCount xs a b+20) hat
  change Hashing.PowerOfTwo.bits (2*bucketCount xs a b*bucketCount xs a b) ≤ childCapacity xs a b at hb
  unfold childWork
  nlinarith

theorem remaining_work_le (ha : Admissible w xs.length l) (hy : rootAccepted xs a = true)
    (rho : RandomMemory w) (j : Nat) :
    remainingWork xs l a rho j ≤ 6+42*(w+1)*(27*(values xs).length+2) := by
  have hs := Sizes.child_work_linear (rootHash xs a) (rootKeys xs) (accepted_energy hy)
    (by simpa [rootKeys] using root_slots_bound xs)
  change (∑ b : Fin (rootSlots xs), (childCapacity xs a b+bucketCount xs a b+1)) ≤ _ at hs
  simp only [rootKeys,List.length_reverse] at hs
  have hh : (∑ b : Fin (rootSlots xs), if j ≤ b.val then childWork xs l a b rho else 0) ≤
      ∑ b : Fin (rootSlots xs), 42*(w+1)*(childCapacity xs a b+bucketCount xs a b+1) := by
    apply Finset.sum_le_sum
    intro b _
    split
    · exact child_work_le ha.arithmetic.positiveWidth xs l a b rho
    · exact Nat.zero_le _
  rw [← Finset.mul_sum] at hh
  have hm := Nat.mul_le_mul_left (42*(w+1)) hs
  unfold remainingWork
  omega

end PerfectHash.Bounded
