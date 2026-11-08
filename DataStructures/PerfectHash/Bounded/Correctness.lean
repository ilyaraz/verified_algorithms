import DataStructures.PerfectHash.Bounded.OuterLoop

namespace PerfectHash.Bounded
open WordRam Construction.Registers Registers

set_option maxRecDepth 50000
set_option maxHeartbeats 20000000

def rootSamples (xs : List (Word w)) (l : Layout) (rho : RandomMemory w) : Fin w → Word w :=
  fun i => sampleAt rho (l.randomBase+1+i.val)

def rootChoice (xs : List (Word w)) (l : Layout) (rho : RandomMemory w) : Option (Word w) :=
  FiniteProbability.Retry.find (rootAccepted xs) w (rootSamples xs l rho)

def rootAttempts (xs : List (Word w)) (l : Layout) (rho : RandomMemory w) : Nat :=
  FiniteProbability.Retry.attempts (rootAccepted xs) w (rootSamples xs l rho)

def tailWork (xs : List (Word w)) (l : Layout) (rho : RandomMemory w) : Nat :=
  match rootChoice xs l rho with
  | none => 3
  | some a => 11+remainingWork xs l a rho 0

/-- A pointwise bound on executed instructions. Comparisons and every retry's
stopping rule are retained for the later average-cost proof. -/
def constructionWork (xs : List (Word w)) (l : Layout) (ha : Admissible w xs.length l) (rho : RandomMemory w) : Nat :=
  9+40*(xs.length+1)+9*Dedup.comparisons
    (Dedup.parameters (dedup_admissible ha) (rho (word w l.randomBase))).hash xs []+
    (4*Hashing.PowerOfTwo.bits (values xs).length+17)+
    (20*rootSlots xs+25*(values xs).length+20)*rootAttempts xs l rho+tailWork xs l rho

def randomSpan (w : Nat) (xs : List (Word w)) : Nat := 1+w*(rootSlots xs+1)

theorem random_schedule (xs : List (Word w)) (l : Layout) :
    consecutiveAddresses w l.randomBase (randomSpan w xs) =
      [word w l.randomBase] ++ consecutiveAddresses w (l.randomBase+1) w ++
        consecutiveAddresses w (childRandomBase l w 0) (w*rootSlots xs) := by
  unfold randomSpan
  rw [show 1+w*(rootSlots xs+1) = (1+w)+w*rootSlots xs by ring,
    consecutiveAddresses_append,consecutiveAddresses_append]
  simp [consecutiveAddresses,childRandomBase,Nat.add_assoc]

variable {w : Nat} {xs : List (Word w)} {l : Layout} {s : State w 64}

/-- Every admissible repeated-input execution reaches its own success or budget
halt. A successful result supplies the already verified all-word query view. -/
theorem total (ha : Admissible w xs.length l) (rho : RandomMemory w) (hp : s.pc = 0)
    (hin : BuildInput w xs.length l s.regs) (harr : ArrayAt s.mem l.inputBase xs) :
    ∃ k t log, TerminatesIn program rho s k t log ∧ k ≤ constructionWork xs l ha rho ∧
      (t.regs status = word w 0 ∨ ∃ a, Built xs l a t) ∧ (policy w xs.length l).AllowsTrace log ∧
      (log.filterMap Access.randomAddress).Sublist (consecutiveAddresses w l.randomBase (randomSpan w xs)) := by
  obtain ⟨kd,u,ld,htd,hkd,hd,hpold,hrd⟩ := deduplicate xs l ha rho hp hin harr
  obtain ⟨v,hti,hready,hmem⟩ := initialize_root ha hd rho
  obtain ⟨kr,t,lr,htr,hkr,hpolr,hrr,hpost⟩ := root_search ha rho (hready.search_state ha)
  have hpref := (htd.trans hti).trans htr
  have hpolpref : (policy w xs.length l).AllowsTrace (ld++lr) :=
    (AccessPolicy.allowsTrace_append _).mpr ⟨hpold,hpolr⟩
  have hrsub : (lr.filterMap Access.randomAddress).Sublist (consecutiveAddresses w (l.randomBase+1) w) := by
    rw [hrr]
    exact consecutiveAddresses_sublist w _ (FiniteProbability.Retry.attempts_le _ _ _)
  have hprefsub : ((ld++lr).filterMap Access.randomAddress).Sublist
      ([word w l.randomBase]++consecutiveAddresses w (l.randomBase+1) w) := by
    rw [List.filterMap_append,hrd]
    exact (List.Sublist.refl _).append hrsub
  have hprefcost : kd+(4*Hashing.PowerOfTwo.bits (values xs).length+17)+kr ≤
      9+40*(xs.length+1)+9*Dedup.comparisons
        (Dedup.parameters (dedup_admissible ha) (rho (word w l.randomBase))).hash xs []+
        (4*Hashing.PowerOfTwo.bits (values xs).length+17)+
        (20*rootSlots xs+25*(values xs).length+20)*rootAttempts xs l rho := by
    change kr ≤ (20*rootSlots xs+25*(values xs).length+20)*rootAttempts xs l rho at hkr
    omega
  cases he : rootChoice xs l rho with
  | none =>
    have he' : FiniteProbability.Retry.find (rootAccepted xs) w
        (fun i => sampleAt rho (l.randomBase+1+i.val)) = none := he
    have hs : RootSearchState xs l v.regs (l.randomBase+1+w) 0 t := by simpa only [he'] using hpost
    have hf := (root_budget t rho hs.pc hs.trials).then_terminates (failed {t with pc := location .failed} rho rfl)
    refine ⟨kd+(4*Hashing.PowerOfTwo.bits (values xs).length+17)+kr+3,
      ⟨230,update t.regs status (word w 0),t.mem⟩,ld++lr,
      by simpa using hpref.then_terminates hf,?_,Or.inl (by simp [update]),hpolpref,?_⟩
    · simpa only [constructionWork,tailWork,he] using Nat.add_le_add_right hprefcost 3
    · rw [random_schedule]
      exact hprefsub.trans (List.sublist_append_left _ _)
  | some a =>
    have he' : FiniteProbability.Retry.find (rootAccepted xs) w
        (fun i => sampleAt rho (l.randomBase+1+i.val)) = some a := he
    have hs : RootFound xs l v.regs a t := by simpa only [he'] using hpost
    have hhead := root_header t rho hs.pc
    obtain ⟨ko,z,lo,hto,hko,hout,hpolo,hro⟩ := outer_loop ha rho (hs.outer ha) (by omega : 0+rootSlots xs = rootSlots xs)
    refine ⟨kd+(4*Hashing.PowerOfTwo.bits (values xs).length+17)+kr+11+ko,z,
      (ld++lr)++headerTrace t++lo,by simpa using (hpref.trans hhead).then_terminates hto,?_,?_,?_,?_⟩
    · simp only [constructionWork,tailWork,he]
      omega
    · exact hout.elim Or.inl (fun hh => Or.inr ⟨a,hh⟩)
    · exact (AccessPolicy.allowsTrace_append _).mpr ⟨
        (AccessPolicy.allowsTrace_append _).mpr ⟨hpolpref,root_header_policy ha hs.core.globals⟩,hpolo⟩
    · simp only [List.filterMap_append,headerTrace,List.filterMap_cons,Access.randomAddress,
        List.filterMap_nil,List.append_nil]
      rw [random_schedule]
      simpa only [List.filterMap_append] using hprefsub.append hro

end PerfectHash.Bounded
