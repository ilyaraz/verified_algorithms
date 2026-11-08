import DataStructures.PerfectHash.Total.ChildFallback
import DataStructures.PerfectHash.Total.Acceptance

namespace PerfectHash.Total
open WordRam Bounded Construction.Registers Bounded.Registers FiniteProbability

set_option maxRecDepth 50000
set_option maxHeartbeats 20000000

def childRawSamples (l : Layout) (w j : Nat) (rho : RandomMemory w) : Fin w → Word w :=
  fun i => rho (word w (childRandomBase l w j+i.val))

def childSeed (xs : List (Word w)) (l : Layout) (a : Word w) (b : Fin (rootSlots xs)) (rho : RandomMemory w) : Word w :=
  if bucketCount xs a b ≤ 1 then word w 1
  else selected (childAccepted xs a b) (childRawSamples l w b.val rho)

def childBudget (xs : List (Word w)) (a : Word w) (b : Fin (rootSlots xs)) : Nat :=
  10*childCapacity xs a b+17*bucketCount xs a b+30

def childTrialWork (xs : List (Word w)) (l : Layout) (a : Word w) (b : Fin (rootSlots xs)) (rho : RandomMemory w) : Nat :=
  if bucketCount xs a b ≤ 1 then childBudget xs a b
  else trialWork (childAccepted xs a b) (childBudget xs a b) (childRawSamples l w b.val rho)

variable {w : Nat} {xs : List (Word w)} {l : Layout} {a : Word w} {b : Fin (rootSlots xs)} {s : State w 64}

theorem child_seed_accepted (ha : Admissible w xs.length l) (hr : rootAccepted xs a = true)
    (b : Fin (rootSlots xs)) (rho : RandomMemory w) : childAccepted xs a b (childSeed xs l a b rho) = true := by
  unfold childSeed
  split
  · exact child_direct_accepted ha ‹_› _
  · exact (search_total _ _ (child_fallback_total ha hr b)).2

/-- Direct children need no sample; larger children fall back to exhaustive
search on exhaustion. Successful siblings and current metadata are preserved. -/
theorem child_stage (ha : Admissible w xs.length l) (rho : RandomMemory w)
    (h : ChildSetup xs l a b s) (hp : s.pc = Bounded.location .allocated) :
    ∃ k t log, Steps Total.program rho k s t log ∧ k ≤ 9+childTrialWork xs l a b rho ∧
      ChildStagePost xs l a b (some (childSeed xs l a b rho)) t ∧ (policy w xs.length l).AllowsTrace log ∧
      log.filterMap Access.randomAddress = consecutiveAddresses w (childRandomBase l w b.val) (childReads xs l a b rho) := by
  obtain ⟨k,t,log,ht,hk,hpol,hr,hpost⟩ := Bounded.child_stage ha h hp rho
  cases he : childChoice xs l a b rho with
  | some chosen =>
    have hseed : childSeed xs l a b rho = chosen := by
      by_cases hd : bucketCount xs a b ≤ 1
      · simpa only [childChoice,childSeed,hd,↓reduceIte,Option.some.injEq] using he
      · simp only [childSeed,hd,↓reduceIte]
        apply selected_random
        simpa only [childChoice,hd,↓reduceIte] using he
    refine ⟨k,t,log,lift_steps ht,?_,?_,hpol,hr⟩
    · by_cases hd : bucketCount xs a b ≤ 1
      · simp only [childTrialWork,childAttempts,hd,↓reduceIte,Nat.mul_one] at hk ⊢
        unfold childBudget
        omega
      · have hfind : Retry.find (childAccepted xs a b) w (childSamples xs l b rho) = some chosen := by
          simpa only [childChoice,hd,↓reduceIte] using he
        have hw := trial_work_random (childAccepted xs a b) (childBudget xs a b) (childRawSamples l w b.val rho) hfind
        simp only [childTrialWork,hd,↓reduceIte,hw]
        simp only [childAttempts,hd,↓reduceIte] at hk
        unfold childBudget
        change k ≤ 9+(10*childCapacity xs a b+17*bucketCount xs a b+30)*Retry.attempts (childAccepted xs a b) w (childSamples xs l b rho)
        nlinarith
    · simpa only [he,hseed] using hpost
  | none =>
    have hd : ¬ bucketCount xs a b ≤ 1 := by
      intro hh
      simp [childChoice,hh] at he
    have hfind : Retry.find (childAccepted xs a b) w (childSamples xs l b rho) = none := by
      simpa only [childChoice,hd,↓reduceIte] using he
    have hv : ChildSetup xs l a b t ∧ t.pc = Bounded.location .childChoose ∧ t.regs trialsLeft = word w 0 ∧
        t.regs stage = word w 1 ∧ t.regs fallbackMode = word w 0 := by simpa [ChildStagePost,he] using hpost
    obtain ⟨chosen,hchoice,hgood⟩ := child_fallback_total ha h.partial.accepted b
    obtain ⟨kf,u,lf,htf,hkf,hfound,hpolf,hrf⟩ := child_fallback ha rho hv.1 hv.2.1 hv.2.2.1 hv.2.2.2.2 hv.2.2.2.1 hchoice
    have hseed : childSeed xs l a b rho = chosen := by
      simp only [childSeed,hd,↓reduceIte]
      exact selected_fallback _ _ hfind hchoice
    have hw := trial_work_fallback (childAccepted xs a b) (childBudget xs a b) (childRawSamples l w b.val rho) hfind
    refine ⟨k+kf,u,log++lf,(lift_steps ht).trans htf,?_,?_,
      (AccessPolicy.allowsTrace_append _).mpr ⟨hpol,hpolf⟩,?_⟩
    · simp only [childTrialWork,hd,↓reduceIte,hw]
      simp only [childAttempts,hd,↓reduceIte] at hk
      unfold childBudget
      change k+kf ≤ 9+(10*childCapacity xs a b+17*bucketCount xs a b+30)*
        (Retry.attempts (childAccepted xs a b) w (childSamples xs l b rho)+seedCount w)
      nlinarith
    · simpa only [hseed] using hfound
    · simp only [List.filterMap_append,hr,hrf,List.append_nil]

end PerfectHash.Total
