import DataStructures.PerfectHash.Source.Regions
import DataStructures.PerfectHash.Bounded.Correctness

namespace PerfectHash.Source
open WordRam RamLang RamLang.Compiler RamLang.Logic PerfectHash.Bounded

/-- Source root-search interface shared by capped and fallback constructors.
The chosen seed and cost are proved execution descriptions, not inputs. -/
structure RootSpec (p : RamLang.Program) (rho : RandomMemory w) (xs : List (Word w)) (l : Layout)
    (f : RamLang.Function) (choice : Option (Word w)) (cost : Nat) : Prop where
  lookup : p.functions[9]? = some f
  parameters : f.parameters.length = 8
  frame : f.frameSize ≤ 14
  nonzero : ∀ seed, choice = some seed → seed ≠ word w 0
  body : ∀ free mem, 34 ≤ free → ArrayAt mem ((dedupLayout l).compact xs.length).base (values xs) →
    Contract p rho free f.body
      ([word w ((dedupLayout l).compact xs.length).base,word w (values xs).length,
        word w (l.outputBase+4),word w l.scratchBase,word w (rootSlots xs),
        word w (w-Hashing.PowerOfTwo.bits (values xs).length),word w (l.randomBase+1),word w w].map some ++
        List.replicate f.locals.length none) mem
      (fun flow mem' log => flow = .returned (choice.getD (word w 0)) ∧
        (∀ seed, choice = some seed → rootAccepted xs seed = true ∧
          Construction.Grouped (rootHash xs seed) (l.outputBase+4) l.scratchBase (values xs).reverse mem') ∧
        (Source.policy w xs.length l).AllowsTrace log ∧
        (RamLang.Library.Retry.randomAddresses log).Sublist (consecutiveAddresses w (l.randomBase+1) w)) cost 34

end PerfectHash.Source
