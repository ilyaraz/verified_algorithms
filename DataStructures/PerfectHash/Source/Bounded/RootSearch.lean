import DataStructures.PerfectHash.Source.RootSpec

namespace PerfectHash.Source.Bounded
open WordRam RamLang RamLang.Compiler RamLang.Logic PerfectHash.Bounded
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000

/-- Root search charges only the trials actually reached in the capped block. -/
def rootWork (xs : List (Word w)) (l : Layout) (rho : RandomMemory w) : Nat :=
  (300*((values xs).length+rootSlots xs+1)+155)*rootAttempts xs l rho+12

/-- First successful root seed agrees with the existing mathematical model. -/
theorem root_choice_eq (xs : List (Word w)) (l : Layout) (rho : RandomMemory w) :
    RamLang.Library.Search.choice (Source.Search.Root.sample rho)
      (Source.Search.Root.accept (rootHash xs) (values xs)) (l.randomBase+1) w = rootChoice xs l rho := by
  rw [Source.Search.choice_eq]
  have he : Source.Search.Root.accept (rootHash xs) (values xs) = rootAccepted xs := funext (Source.Search.root_accept xs)
  rw [he]
  rfl

/-- Bounded source root search initializes exactly the established grouping
model and uses a prefix of its dedicated fresh random block. -/
theorem root_search_spec {w : Nat} (p : RamLang.Program) (rho : RandomMemory w)
    (xs : List (Word w)) (l : Layout) (ha : Admissible w xs.length l)
    (hsample : p.functions[3]? = some Hashing.Source.Sampling.function)
    (hroot : p.functions[6]? = some Source.Root.function)
    (hfill : p.functions[2]? = some RamLang.Logic.Fill.function)
    (hsearch : p.functions[9]? = some Source.Search.Root.function) :
    RootSpec p rho xs l Source.Search.Root.function (rootChoice xs l rho) (rootWork xs l rho) := by
  refine ⟨hsearch,rfl,by decide,?_,?_⟩
  · intro seed he
    apply Source.Search.choice_ne_zero (by have := ha.arithmetic.positiveWidth; omega)
    rw [root_choice_eq]
    exact he
  · intro free mem hfree hinput
    let ctx := rootContext xs l ha
    have hlinear : 64*((values xs).length+1) < modulus w := by
      have hh := ha.arithmetic.linearSizes
      have hd := values_length_le xs
      omega
    have hrandom : (Region.mk (l.randomBase+1) w).Fits w := by
      have hf := ha.random
      change l.randomBase+randomCapacity w xs.length < modulus w at hf
      have hh : w ≤ w*(bucketCapacity xs.length+1) := Nat.le_mul_of_pos_right _ (by omega)
      change l.randomBase+1+w < modulus w
      unfold randomCapacity at hf
      omega
    have hc := Source.Search.Root.contract (free := free) p rho mem (rootHash xs)
      (word w (w-Hashing.PowerOfTwo.bits (values xs).length)) (values xs) hsample hroot hfill hfree
      ctx.space hlinear hinput (root_evaluator ha) ctx.input_fit ctx.input_directory ctx.input_nodes hrandom
    apply hc.consequence
    · rintro flow mem' log ⟨hf,hgroup,_,hp,hr⟩
      refine ⟨by simpa only [root_choice_eq] using hf,?_,?_,?_⟩
      · intro seed he
        refine ⟨FiniteProbability.Retry.find_sound _ _ _ he,hgroup seed ?_⟩
        rw [root_choice_eq]
        exact he
      · intro e he
        have hh := hp e he
        cases e with
        | randomRead addr value =>
          change (Region.mk (l.randomBase+1) w).Contains addr at hh
          change l.randomBase ≤ addr.toNat ∧ addr.toNat < l.randomBase+randomCapacity w xs.length
          simp only [Region.Contains] at hh
          have hm : w ≤ w*(bucketCapacity xs.length+1) := Nat.le_mul_of_pos_right _ (by omega)
          unfold randomCapacity
          omega
        | dataRead addr value =>
          apply Source.root_policy xs l (log := [.dataRead addr value])
          · intro e he
            simp only [List.mem_singleton] at he
            subst e
            exact hh
          · simp
        | dataWrite addr value =>
          apply Source.root_policy xs l (log := [.dataWrite addr value])
          · intro e he
            simp only [List.mem_singleton] at he
            subst e
            exact hh
          · simp
      · rw [hr,Source.Search.addresses_eq]
        exact consecutiveAddresses_sublist w _ (RamLang.Library.Search.attempts_le _ _ _ _)
    · rw [Source.Search.attempts_eq]
      have he : Source.Search.Root.accept (rootHash xs) (values xs) = rootAccepted xs := funext (Source.Search.root_accept xs)
      rw [he]
      exact Nat.le_refl _
    · exact Nat.le_refl _

end PerfectHash.Source.Bounded
