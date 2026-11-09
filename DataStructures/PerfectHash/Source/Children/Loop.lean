import DataStructures.PerfectHash.Source.Children.Iteration

namespace PerfectHash.Source.Children
open WordRam RamLang RamLang.Compiler RamLang.Logic PerfectHash.Bounded
set_option maxRecDepth 65536
set_option maxHeartbeats 5000000

/-- A loop either exposes a real failed search or reaches the complete packed
table. An all-success search specification excludes the failure alternative. -/
def Post (xs : List (Word w)) (l : Layout) (a : Word w)
    (choice : Fin (rootSlots xs) → Option (Word w)) (j : Nat) (flow : Flow w) (mem : DataMemory w) : Prop :=
  (∃ b, j ≤ b.val ∧ choice b = none ∧ flow = .returned (word w 0)) ∨
  (∃ saved, flow = .next (locals xs l a (rootSlots xs) 0 saved) ∧ Partial xs l a (rootSlots xs) mem)

/-- The entire child loop preserves completed siblings and follows disjoint
random blocks. Its suffix sum charges every reached allocation, rejected trial,
call, branch and return, and its extra live stack is at most forty words. -/
theorem loop_contract {w free : Nat} {p : RamLang.Program} {rho : RandomMemory w}
    {xs : List (Word w)} {l : Layout} {a : Word w} {f : RamLang.Function}
    {choice : Fin (rootSlots xs) → Option (Word w)} {cost : Fin (rootSlots xs) → Nat}
    (ha : Admissible w xs.length l) (spec : SearchSpec p rho xs l a f choice cost)
    (hround : p.functions[1]? = some Hashing.Source.Rounding.function)
    (hallocate : p.functions[8]? = some Source.Allocation.function)
    (hfree : 40 ≤ free) (j r : Nat) (hlen : j+r = rootSlots xs) (mem : DataMemory w)
    (hpartial : Partial xs l a j mem) (old : Scratch w) :
    Contract p rho free loop (locals xs l a j r old) mem
      (fun flow mem' log => Post xs l a choice j flow mem' ∧ (Source.policy w xs.length l).AllowsTrace log ∧
        (RamLang.Library.Retry.randomAddresses log).Sublist (consecutiveAddresses w (childRandomBase l w j) (w*r)))
      (remainingWork xs a cost j) 40 := by
  induction r generalizing j mem old with
  | zero =>
    have hj : j = rootSlots xs := by omega
    subst j
    refine Contract.ofEvaluation (.whileFalse (by rfl)) ⟨Or.inr ⟨old,rfl,hpartial⟩,?_,?_⟩ ?_ (by simp [extraStack])
    · simp [AccessPolicy.AllowsTrace]
    · simp [RamLang.Library.Retry.randomAddresses]
    · rw [remaining_end]
      exact (by decide : 5 ≤ 12)
  | succ r ih =>
    have hj : j < rootSlots xs := by omega
    let b : Fin (rootSlots xs) := ⟨j,hj⟩
    have hf : r+1 < modulus w := by
      have hm := root_slots_bound xs
      have hd := values_length_le xs
      have hl := ha.arithmetic.linearSizes
      omega
    have hne : word w (r+1) ≠ word w 0 := by
      intro he
      have hh := (word_eq_iff_of_lt hf (by omega : 0 < modulus w)).mp he
      omega
    have htest : (Condition.mk .ne (.local 2) (.literal 0)).eval (locals xs l a j (r+1) old) = .ok true := by
      unfold locals
      search_test
    have hc := iteration_contract ha spec hround hallocate hfree b mem hpartial old
    have hc' : Contract p rho free iteration (locals xs l a j (r+1) old) mem
        (fun flow mem' log => (Source.policy w xs.length l).AllowsTrace log ∧
          (RamLang.Library.Retry.randomAddresses log).Sublist (consecutiveAddresses w (childRandomBase l w j) w) ∧
          match choice b with
          | none => flow = .returned (word w 0)
          | some _ => ∃ saved, flow = .next (locals xs l a (j+1) r saved) ∧ Partial xs l a (j+1) mem')
        (work xs a cost b-5) 40 := by
      have hr : rootSlots xs-j = r+1 := by omega
      have hr' : rootSlots xs-(j+1) = r := by omega
      simpa only [b,hr,hr'] using hc
    obtain ⟨flow,mem₁,log₁,d₁,⟨hp₁,hr₁,hq₁⟩,ht₁,hs₁⟩ := hc'
    have hwork : 5 ≤ work xs a cost b := by unfold work; omega
    have hremaining := remaining_next xs a cost b
    have hremainingMin := remaining_ge xs a cost (j+1)
    have hseq : consecutiveAddresses w (childRandomBase l w j) (w*(r+1)) =
        consecutiveAddresses w (childRandomBase l w j) w ++
          consecutiveAddresses w (childRandomBase l w (j+1)) (w*r) := by
      rw [show w*(r+1) = w+w*r by ring,consecutiveAddresses_append]
      congr 2
      unfold childRandomBase
      ring
    cases he : choice b with
    | none =>
      simp only [he] at hq₁
      subst flow
      refine Contract.ofEvaluation (.whileStop htest d₁ (by trivial)) ⟨Or.inl ⟨b,Nat.le_refl _,he,rfl⟩,hp₁,?_⟩ ?_ (by simpa [extraStack] using hs₁)
      · rw [hseq]
        exact hr₁.trans (List.sublist_append_left _ _)
      · change 4+instructions d₁ ≤ _
        change remainingWork xs a cost j = work xs a cost b+remainingWork xs a cost (j+1) at hremaining
        omega
    | some seed =>
      simp only [he] at hq₁
      obtain ⟨saved,rfl,hpart⟩ := hq₁
      obtain ⟨flow,mem₂,log₂,d₂,⟨hq₂,hp₂,hr₂⟩,ht₂,hs₂⟩ := ih (j+1) (by omega) mem₁ hpart saved
      refine Contract.ofEvaluation (.whileContinue htest d₁ d₂) ⟨?_,?_,?_⟩ ?_ ?_
      · rcases hq₂ with ⟨c,hc,hec,hf⟩ | hd
        · exact Or.inl ⟨c,by omega,hec,hf⟩
        · exact Or.inr hd
      · exact (AccessPolicy.allowsTrace_append _).mpr ⟨hp₁,hp₂⟩
      · rw [RamLang.Library.Retry.randomAddresses_append,hseq]
        exact hr₁.append hr₂
      · change 5+instructions d₁+instructions d₂ ≤ _
        change remainingWork xs a cost j = work xs a cost b+remainingWork xs a cost (j+1) at hremaining
        omega
      · exact Nat.max_le.mpr ⟨hs₁,hs₂⟩

/-- A successful child sequence yields the existing retained representation;
ordinary bounded failure identifies a genuinely exhausted child search. -/
theorem contract {w free : Nat} {p : RamLang.Program} {rho : RandomMemory w}
    {xs : List (Word w)} {l : Layout} {a : Word w} {f : RamLang.Function}
    {choice : Fin (rootSlots xs) → Option (Word w)} {cost : Fin (rootSlots xs) → Nat}
    (ha : Admissible w xs.length l) (spec : SearchSpec p rho xs l a f choice cost)
    (hround : p.functions[1]? = some Hashing.Source.Rounding.function)
    (hallocate : p.functions[8]? = some Source.Allocation.function)
    (hfree : 40 ≤ free) (mem : DataMemory w) (hpartial : Partial xs l a 0 mem) :
    Contract p rho free function.body
      ([word w (l.outputBase+4),word w l.scratchBase,word w (rootSlots xs),
        word w (childRandomBase l w 0),word w w].map some ++ List.replicate function.locals.length none) mem
      (fun flow mem' log =>
        ((flow = .returned (word w 0) ∧ ∃ b, choice b = none) ∨
          (flow = .returned (word w (l.outputBase+Packed.words (childCapacity xs a))) ∧
            Partial xs l a (rootSlots xs) mem')) ∧ (Source.policy w xs.length l).AllowsTrace log ∧
        (RamLang.Library.Retry.randomAddresses log).Sublist
          (consecutiveAddresses w (childRandomBase l w 0) (w*rootSlots xs)))
      (remainingWork xs a cost 0+30) 40 := by
  let saved : Scratch w := ![some (word w 4*word w (rootSlots xs)),none,none,none,none,none,none,none,none,none]
  have hc := loop_contract ha spec hround hallocate hfree 0 (rootSlots xs) (by omega) mem hpartial saved
  have hlocals : locals xs l a 0 (rootSlots xs) saved =
      [some (word w (l.outputBase+4)),some (word w l.scratchBase),some (word w (rootSlots xs)),
        some (word w (childRandomBase l w 0)),some (word w w),
        some (word w (l.outputBase+4)+word w 4*word w (rootSlots xs)),
        some (word w 4*word w (rootSlots xs)),none,none,none,none,none,none,none,none,none] := by
    simp [locals,saved,cursor_start,WordRam.word_add,WordRam.word_mul]
  rw [hlocals] at hc
  obtain ⟨flow,mem',log,d,⟨hq,hp,hr⟩,ht,hs⟩ := hc
  rcases hq with ⟨b,_,he,rfl⟩ | ⟨old,rfl,hpart⟩
  · refine ⟨_,_,_,by ram_derive (search_test),?_,?_,?_⟩
    · exact ⟨Or.inl ⟨rfl,b,he⟩,hp,hr⟩
    · ram_cost
      omega
    · ram_cost
      exact hs
  · refine ⟨_,_,_,by ram_derive (search_test),?_,?_,?_⟩
    · refine ⟨Or.inr ⟨?_,hpart⟩,by simpa using hp,by simpa using hr⟩
      simp [cursor_end]
    · ram_cost
      omega
    · ram_cost
      exact hs

end PerfectHash.Source.Children
