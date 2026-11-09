import DataStructures.PerfectHash.Source.Children.Spec

namespace PerfectHash.Source.Bounded
open WordRam RamLang RamLang.Compiler RamLang.Logic PerfectHash.Bounded
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000

/-- The bounded child majorant charges each reached trial and direct children. -/
def searchWork (xs : List (Word w)) (l : Layout) (a : Word w)
    (rho : RandomMemory w) (b : Fin (rootSlots xs)) : Nat :=
  500*(childCapacity xs a b+bucketCount xs a b+1)*childAttempts xs l a b rho+60

/-- Source and existing models use the same consecutive candidate sequence. -/
theorem child_choice_eq (xs : List (Word w)) (l : Layout) (a : Word w)
    (rho : RandomMemory w) (b : Fin (rootSlots xs)) (hb : ¬ bucketCount xs a b ≤ 1) :
    RamLang.Library.Search.choice (Source.Search.Root.sample rho)
      (Source.Search.Child.accept (childHash w (bucketCount xs a b)) (bucketChain xs a b))
      (childRandomBase l w b.val) w = childChoice xs l a b rho := by
  rw [Source.Search.choice_eq,Source.Search.child_accept]
  simp only [childChoice,hb,↓reduceIte]
  rfl

/-- The bounded source search instantiates the common orchestration interface
for every admissible root and every dirty current-child table. -/
theorem child_search_spec {w : Nat} (p : RamLang.Program) (rho : RandomMemory w)
    (xs : List (Word w)) (l : Layout) (a : Word w) (ha : Admissible w xs.length l)
    (hy : rootAccepted xs a = true)
    (hsample : p.functions[3]? = some Hashing.Source.Sampling.function)
    (hchild : p.functions[7]? = some Source.Child.function)
    (hfill : p.functions[2]? = some RamLang.Logic.Fill.function)
    (hsearch : p.functions[10]? = some Source.Search.Child.function) :
    Source.Children.SearchSpec p rho xs l a Source.Search.Child.function
      (fun b => childChoice xs l a b rho) (searchWork xs l a rho) := by
  have hone : 1 < modulus w := by have := ha.arithmetic.linearSizes; omega
  have hnonzero : word w 1 ≠ word w 0 := by
    intro he
    have := (word_eq_iff_of_lt hone (by omega : 0 < modulus w)).mp he
    omega
  refine ⟨hsearch,rfl,by decide,?_,?_⟩
  · intro b seed he
    by_cases hb : bucketCount xs a b ≤ 1
    · simp only [childChoice,hb,↓reduceIte,Option.some.injEq] at he
      subst seed
      exact hnonzero
    · apply Source.Search.choice_ne_zero (by have := ha.arithmetic.positiveWidth; omega)
      rw [child_choice_eq xs l a rho b hb]
      exact he
  · intro free mem b hfree hchain
    let ctx := childContext ha hy b
    have hfit := bucket_fit ha hy b
    have hhash (seed key : Word w) :
        unsignedShiftRight (seed*key) (word w (Source.Allocation.shift w (bucketCount xs a b))) =
          word w (childHash w (bucketCount xs a b) seed key) := by
      rw [Source.Children.shift_eq]
      unfold childHash
      simp only [word,BitVec.ofNat_toNat,BitVec.setWidth_eq]
    by_cases hb : bucketCount xs a b ≤ 1
    · have hchoice : childChoice xs l a b rho = some (word w 1) := by simp [childChoice,hb]
      have hcost : 200*((bucketChain xs a b).length+2)+60 ≤ searchWork xs l a rho b := by
        simp only [searchWork,childAttempts,hb,↓reduceIte,Nat.mul_one,bucket_chain_length]
        omega
      by_cases hz : bucketCount xs a b = 0
      · have hq : childCapacity xs a b = 0 := by simp [childCapacity,Sizes.childSlots,hb,hz]
        have hc := Source.Search.Child.empty_contract (free := free) p rho mem (word w l.scratchBase)
          (word w (Dedup.firstIndex (bucketChain xs a b)))
          (word w (Packed.table l.outputBase (childCapacity xs a) b))
          (word w (Source.Allocation.shift w (bucketCount xs a b))) (word w (childRandomBase l w b.val)) (word w w)
        rw [hq]
        apply hc.consequence
        · rintro flow mem' log ⟨rfl,rfl,rfl⟩
          refine ⟨by simp [hchoice],?_,by simp [AccessPolicy.AllowsTrace],by simp [RamLang.Library.Retry.randomAddresses]⟩
          intro seed hs
          rw [hchoice] at hs
          cases hs
          exact ⟨child_direct_accepted ha hb _,⟨by intro i hi; omega,by intro i hi; omega⟩⟩
        · omega
        · omega
      · have hb1 : bucketCount xs a b = 1 := by omega
        have hq : childCapacity xs a b = 1 := by simp [childCapacity,Sizes.childSlots,hb,hb1]
        have hc := Source.Search.Child.singleton_contract (free := free) p rho mem
          (childHash w (bucketCount xs a b) (word w 1))
          (word w (Source.Allocation.shift w (bucketCount xs a b))) (word w (childRandomBase l w b.val)) (word w w)
          (bucketChain xs a b) hchild hfill hfree hchain (bucket_indices b)
          (fun key => by rw [child_hash_direct ha.arithmetic.widthValue hb]; omega) (hhash _)
          ctx.node_fit (by simpa only [hq] using ctx.table_fit) (by simpa only [hq] using ctx.separated)
          (child_direct_accepted ha hb _)
        rw [hq]
        apply hc.consequence
        · rintro flow mem' log ⟨rfl,hslots,hchain',hp,hr⟩
          refine ⟨by simp [hchoice],?_,?_,?_⟩
          · intro seed hs
            rw [hchoice] at hs
            cases hs
            exact ⟨child_direct_accepted ha hb _,hslots⟩
          · intro e he
            have hh := hp e he
            cases e <;> first | exact hh | exact False.elim hh
          · rw [hr]; simp
        · exact hcost
        · exact Nat.le_refl _
    · have hq : 1 < childCapacity xs a b := by
        have hl := Sizes.childSlots_covers (b := bucketCount xs a b) (by omega)
        change 1 < Sizes.childSlots (bucketCount xs a b)
        nlinarith
      have hrandom : (Region.mk (childRandomBase l w b.val) w).Fits w := by
        have hh := child_random_block (l := l) (w := w) (xs := xs) b
        have hf : l.randomBase+randomCapacity w xs.length < modulus w := ha.random
        exact lt_of_le_of_lt hh hf
      have hc := Source.Search.Child.contract (free := free) p rho mem
        (childHash w (bucketCount xs a b)) (word w (Source.Allocation.shift w (bucketCount xs a b)))
        (bucketChain xs a b) hsample hchild hfill hfree hchain (bucket_indices b)
        (fun seed key => child_hash_range ha.arithmetic.widthValue hfit.2 (by omega) seed key)
        hhash ctx.node_fit ctx.table_fit ctx.separated hq hrandom
      apply hc.consequence
      · rintro flow mem' log ⟨hf,hslots,hchain',hp,hr⟩
        refine ⟨by simpa only [child_choice_eq xs l a rho b hb] using hf,?_,hp,?_⟩
        · intro seed hs
          refine ⟨?_,hslots seed (by rw [child_choice_eq xs l a rho b hb]; exact hs)⟩
          apply FiniteProbability.Retry.find_sound
          simpa only [childChoice,hb,↓reduceIte] using hs
        · rw [hr,Source.Search.addresses_eq]
          exact consecutiveAddresses_sublist w _ (RamLang.Library.Search.attempts_le _ _ _ _)
      · rw [Source.Search.attempts_eq,Source.Search.child_accept]
        simp only [searchWork,childAttempts,hb,↓reduceIte,bucket_chain_length]
        change (200*(childCapacity xs a b+bucketCount xs a b+1)+155)*
          FiniteProbability.Retry.attempts (childAccepted xs a b) w (childSamples xs l b rho)+30 ≤ _
        nlinarith
      · exact Nat.le_refl _

end PerfectHash.Source.Bounded
