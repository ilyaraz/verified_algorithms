import DataStructures.PerfectHash.Total.RootStage
import DataStructures.PerfectHash.Total.ChildStage

namespace PerfectHash.Total
open WordRam Bounded

def childWork (xs : List (Word w)) (l : Layout) (a : Word w) (b : Fin (rootSlots xs)) (rho : RandomMemory w) : Nat :=
  4*Hashing.PowerOfTwo.bits (2*bucketCount xs a b*bucketCount xs a b)+38+
    childTrialWork xs l a b rho

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


/-- The exact remaining random-read count; deterministic fallback contributes
zero and each direct child also contributes zero. -/
def remainingReads (xs : List (Word w)) (l : Layout) (a : Word w) (rho : RandomMemory w) (j : Nat) : Nat :=
  ∑ b : Fin (rootSlots xs), if j ≤ b.val then Bounded.childReads xs l a b rho else 0

theorem remainingReads_end (xs : List (Word w)) (l : Layout) (a : Word w) (rho : RandomMemory w) :
    remainingReads xs l a rho (rootSlots xs) = 0 := by
  simp [remainingReads,show ∀ b : Fin (rootSlots xs), ¬ rootSlots xs ≤ b.val from fun b => Nat.not_le.mpr b.isLt]

theorem remainingReads_next (xs : List (Word w)) (l : Layout) (a : Word w) (rho : RandomMemory w)
    (b : Fin (rootSlots xs)) :
    remainingReads xs l a rho b.val = Bounded.childReads xs l a b rho+remainingReads xs l a rho (b.val+1) := by
  have he (c : Fin (rootSlots xs)) :
      (if b.val ≤ c.val then Bounded.childReads xs l a c rho else 0) =
      (if c = b then Bounded.childReads xs l a c rho else 0)+
      (if b.val+1 ≤ c.val then Bounded.childReads xs l a c rho else 0) := by
    by_cases hc : c = b
    · subst c; simp
    · have hn : c.val ≠ b.val := fun hh => hc (Fin.ext hh)
      by_cases hl : b.val ≤ c.val <;> simp [hc,hl,show (b.val+1 ≤ c.val ↔ b.val ≤ c.val) by omega]
  simp only [remainingReads,he,Finset.sum_add_distrib]
  simp [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

end PerfectHash.Total
