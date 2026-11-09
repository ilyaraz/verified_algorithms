import DataStructures.PerfectHash.Source.RootSpec
import DataStructures.PerfectHash.Source.Total.Search
import DataStructures.PerfectHash.Source.Total.Model
import DataStructures.PerfectHash.Total.RootStage

namespace PerfectHash.Source.Total
open WordRam RamLang RamLang.Compiler RamLang.Logic PerfectHash.Bounded
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000

/-- A scaled pure stopping-time majorant covers every source trial and its control flow. -/
def rootWork (xs : List (Word w)) (l : Layout) (rho : RandomMemory w) : Nat :=
  100*PerfectHash.Total.rootWork xs l rho+100

/-- Total source root search initializes exactly the established grouping
model and uses a prefix of its dedicated fresh random block. -/
theorem root_search_spec {w : Nat} (p : RamLang.Program) (rho : RandomMemory w)
    (xs : List (Word w)) (l : Layout) (ha : Admissible w xs.length l)
    (hsample : p.functions[3]? = some Hashing.Source.Sampling.function)
    (hroot : p.functions[6]? = some Source.Root.function)
    (hfill : p.functions[2]? = some RamLang.Logic.Fill.function)
    (hsearch : p.functions[9]? = some rootFunction) :
    RootSpec p rho xs l rootFunction (some (PerfectHash.Total.rootSeed xs l rho)) (rootWork xs l rho) := by
  refine ⟨hsearch,rfl,by decide,?_,?_⟩
  · intro seed he
    cases he
    exact selection_nonzero (by have := ha.arithmetic.positiveWidth; omega) rho _ _
      (PerfectHash.Total.root_fallback_total ha)
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
    obtain ⟨fallback,hfallback,_⟩ := PerfectHash.Total.root_fallback_total ha
    have he : Source.Search.Root.accept (rootHash xs) (values xs) = rootAccepted xs :=
      funext (Source.Search.root_accept xs)
    have hf : RamLang.Library.Search.choice (PerfectHash.Total.candidate w)
        (Source.Search.Root.accept (rootHash xs) (values xs)) 0 (PerfectHash.Total.seedCount w) = some fallback := by
      rw [he,fallback_eq]; exact hfallback
    have hselection : (RamLang.Library.Search.choice (Source.Search.Root.sample rho)
        (Source.Search.Root.accept (rootHash xs) (values xs)) (l.randomBase+1) w).getD fallback =
        PerfectHash.Total.rootSeed xs l rho := by
      rw [he]; exact selection_eq rho _ _ _ hfallback
    have hc := Source.Search.Root.total_contract (free := free) p rho mem (rootHash xs)
      (word w (w-Hashing.PowerOfTwo.bits (values xs).length)) (values xs) hsample hroot hfill hfree
      ctx.space hlinear hinput (root_evaluator ha) ctx.input_fit ctx.input_directory ctx.input_nodes hrandom fallback hf
    apply hc.consequence
    · rintro flow mem' log ⟨hf,hgroup,_,hp,hr⟩
      refine ⟨by simpa only [hselection,Option.getD_some] using hf,?_,?_,?_⟩
      · intro seed hs
        cases hs
        exact ⟨PerfectHash.Total.root_seed_accepted ha rho,by simpa only [hselection] using hgroup⟩
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
    · rw [he]
      have hbudget : 300*((values xs).length+rootSlots xs+1)+155 ≤ 100*PerfectHash.Total.rootBudget xs := by
        unfold PerfectHash.Total.rootBudget
        omega
      have hmul := Nat.mul_le_mul_right
        (RamLang.Library.Search.attempts (Source.Search.Root.sample rho) (rootAccepted xs) (l.randomBase+1) w +
          if (RamLang.Library.Search.choice (Source.Search.Root.sample rho) (rootAccepted xs) (l.randomBase+1) w).isNone
            then PerfectHash.Total.seedCount w else 0) hbudget
      conv at hmul => rhs; rw [Nat.mul_assoc,trial_work_eq]
      exact (Nat.add_le_add_right hmul 40).trans (Nat.add_le_add_left (by decide : 40 ≤ 100) _)
    · exact Nat.le_refl _

end PerfectHash.Source.Total
