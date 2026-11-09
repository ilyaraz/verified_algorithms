import DataStructures.PerfectHash.Source.Regions
import DataStructures.PerfectHash.Bounded.Representation

namespace PerfectHash.Source.Children
open WordRam RamLang RamLang.Compiler RamLang.Logic PerfectHash.Bounded

/-- Source orchestration of child allocation, search and completion. -/
def function : RamLang.Function := Source.Bounded.source.functions[11]'(by decide)

/-- The retry loop is the third lowered statement, after table initialization. -/
def loop : Stmt := match function.body with | .seq _ (.seq _ (.seq body _)) => body | _ => .skip

/-- One allocated child, including its ordinary search call and metadata write. -/
def iteration : Stmt := match loop with | .while _ body => body | _ => .skip

/-- Shared search interface for bounded and total orchestration. Choices and
costs are ghost descriptions of the source execution proved by body, never
runtime arguments or computational advice. -/
structure SearchSpec (p : RamLang.Program) (rho : RandomMemory w) (xs : List (Word w))
    (l : Layout) (root : Word w) (f : RamLang.Function)
    (choice : Fin (rootSlots xs) → Option (Word w)) (cost : Fin (rootSlots xs) → Nat) : Prop where
  lookup : p.functions[10]? = some f
  parameters : f.parameters.length = 7
  frame : f.frameSize ≤ 14
  nonzero : ∀ b seed, choice b = some seed → seed ≠ word w 0
  body : ∀ free mem b, 26 ≤ free → Dedup.ChainAt mem l.scratchBase (bucketChain xs root b) →
    Contract p rho free f.body
      ([word w l.scratchBase,word w (Dedup.firstIndex (bucketChain xs root b)),
        word w (Packed.table l.outputBase (childCapacity xs root) b),word w (childCapacity xs root b),
        word w (Source.Allocation.shift w (bucketCount xs root b)),word w (childRandomBase l w b.val),word w w].map some ++
        List.replicate f.locals.length none) mem
      (fun flow mem' log => flow = .returned ((choice b).getD (word w 0)) ∧
        (∀ seed, choice b = some seed → childAccepted xs root b seed = true ∧
          Construction.SlotsAt (childHash w (bucketCount xs root b) seed) (childCapacity xs root b)
            (Packed.table l.outputBase (childCapacity xs root) b) (bucketKeys xs root b).reverse mem') ∧
        (Source.Search.Child.policy l.scratchBase (values xs).length
          (Packed.table l.outputBase (childCapacity xs root) b) (childCapacity xs root b)
          (childRandomBase l w b.val) w).AllowsTrace log ∧
        (RamLang.Library.Retry.randomAddresses log).Sublist (consecutiveAddresses w (childRandomBase l w b.val) w))
      (cost b) 26

/-- Source shifts are exactly the established child-shift model. -/
theorem shift_eq (w n : Nat) : Source.Allocation.shift w n = Construction.Allocation.childShift w n := by
  simp [Source.Allocation.shift,Construction.Allocation.childShift,Hashing.PowerOfTwo.computeBits_eq]

/-- Allocation and search allowances add per child; outer control and all
argument-transfer instructions receive an additional fixed charge. -/
def work (xs : List (Word w)) (a : Word w) (cost : Fin (rootSlots xs) → Nat) (b : Fin (rootSlots xs)) : Nat :=
  Source.Allocation.work (bucketCount xs a b)+cost b+200

/-- A suffix budget includes every child still possible and the final return. -/
def remainingWork (xs : List (Word w)) (a : Word w) (cost : Fin (rootSlots xs) → Nat) (j : Nat) : Nat :=
  12+∑ b : Fin (rootSlots xs), if j ≤ b.val then work xs a cost b else 0

/-- No child remains when the directory cursor reaches its endpoint. -/
theorem remaining_end (xs : List (Word w)) (a : Word w) (cost : Fin (rootSlots xs) → Nat) :
    remainingWork xs a cost (rootSlots xs) = 12 := by
  simp [remainingWork,show ∀ b : Fin (rootSlots xs), ¬ rootSlots xs ≤ b.val from fun b => Nat.not_le.mpr b.isLt]

/-- The suffix budget splits at the next child, independently of its outcome. -/
theorem remaining_next (xs : List (Word w)) (a : Word w) (cost : Fin (rootSlots xs) → Nat)
    (b : Fin (rootSlots xs)) : remainingWork xs a cost b.val = work xs a cost b+remainingWork xs a cost (b.val+1) := by
  have he (c : Fin (rootSlots xs)) :
      (if b.val ≤ c.val then work xs a cost c else 0) =
      (if c = b then work xs a cost c else 0)+(if b.val+1 ≤ c.val then work xs a cost c else 0) := by
    by_cases hc : c = b
    · subst c; simp
    · have hn : c.val ≠ b.val := fun hh => hc (Fin.ext hh)
      by_cases hl : b.val ≤ c.val <;> simp [hc,hl,show (b.val+1 ≤ c.val ↔ b.val ≤ c.val) by omega]
  simp only [remainingWork,he,Finset.sum_add_distrib]
  simp [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm]

/-- The final return allowance is present in every suffix. -/
theorem remaining_ge (xs : List (Word w)) (a : Word w) (cost : Fin (rootSlots xs) → Nat) (j : Nat) :
    12 ≤ remainingWork xs a cost j := by unfold remainingWork; omega

end PerfectHash.Source.Children
