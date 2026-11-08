import DataStructures.PerfectHash.Total.RootFallback
import DataStructures.PerfectHash.Total.Acceptance

namespace PerfectHash.Total
open WordRam Bounded Construction.Registers Bounded.Registers FiniteProbability

set_option maxRecDepth 50000
set_option maxHeartbeats 20000000

def rootRawSamples (l : Layout) (rho : RandomMemory w) : Fin w → Word w :=
  fun i => rho (word w (l.randomBase+1+i.val))

def rootSeed (xs : List (Word w)) (l : Layout) (rho : RandomMemory w) : Word w :=
  selected (rootAccepted xs) (rootRawSamples l rho)

def rootBudget (xs : List (Word w)) : Nat := 20*rootSlots xs+25*(values xs).length+30

def rootWork (xs : List (Word w)) (l : Layout) (rho : RandomMemory w) : Nat :=
  trialWork (rootAccepted xs) (rootBudget xs) (rootRawSamples l rho)

variable {w : Nat} {xs : List (Word w)} {l : Layout} {s : State w 64}

theorem root_seed_accepted (ha : Admissible w xs.length l) (rho : RandomMemory w) :
    rootAccepted xs (rootSeed xs l rho) = true :=
  (search_total _ _ (root_fallback_total ha)).2

/-- Root random retries followed by complete enumeration. The chosen seed and
pointwise work are functions of the root block alone, for conditional averaging. -/
theorem root_stage (ha : Admissible w xs.length l) (rho : RandomMemory w) (h : RootReady xs l s) :
    ∃ k t log, Steps Total.program rho k s t log ∧ k ≤ rootWork xs l rho ∧
      RootFound xs l t.regs (rootSeed xs l rho) t ∧ (policy w xs.length l).AllowsTrace log ∧
      log.filterMap Access.randomAddress = consecutiveAddresses w (l.randomBase+1) (rootAttempts xs l rho) := by
  obtain ⟨k,t,log,ht,hk,hpol,hr,hpost⟩ := root_search ha rho (h.search_state ha)
  change k ≤ (20*rootSlots xs+25*(values xs).length+20)*rootAttempts xs l rho at hk
  change log.filterMap Access.randomAddress = consecutiveAddresses w (l.randomBase+1) (rootAttempts xs l rho) at hr
  cases he : rootChoice xs l rho with
  | some a =>
    have he' : Retry.find (rootAccepted xs) w (fun i => sampleAt rho (l.randomBase+1+i.val)) = some a := he
    have hf : RootFound xs l s.regs a t := by simpa only [he'] using hpost
    have hseed : rootSeed xs l rho = a := selected_random _ _ he
    have hw : rootWork xs l rho = rootBudget xs*rootAttempts xs l rho := trial_work_random _ _ _ he
    refine ⟨k,t,log,lift_steps ht,?_,?_,hpol,hr⟩
    · rw [hw]; unfold rootBudget; nlinarith
    · rw [hseed]
      exact ⟨hf.core,hf.pc,hf.seed,hf.accepted,hf.grouped,by intros; rfl⟩
  | none =>
    have hf : RootSearchState xs l s.regs (l.randomBase+1+w) 0 t := by
      simpa only [show Retry.find (rootAccepted xs) w (fun i => sampleAt rho (l.randomBase+1+i.val)) = none from he] using hpost
    have hm : t.regs fallbackMode = word w 0 := (hf.registers fallbackMode (by decide)).trans h.fallback
    have hs : t.regs stage = word w 0 := (hf.registers stage (by decide)).trans h.stage
    obtain ⟨a,hchoice,hgood⟩ := root_fallback_total ha
    obtain ⟨kf,u,lf,htf,hkf,hfound,hpolf,hrf⟩ := root_fallback ha rho hf hm hs hchoice
    have hseed : rootSeed xs l rho = a := selected_fallback _ _ he hchoice
    have hw : rootWork xs l rho = rootBudget xs*(rootAttempts xs l rho+seedCount w) := trial_work_fallback _ _ _ he
    refine ⟨k+kf,u,log++lf,(lift_steps ht).trans htf,?_,?_,
      (AccessPolicy.allowsTrace_append _).mpr ⟨hpol,hpolf⟩,?_⟩
    · rw [hw]; unfold rootBudget; nlinarith
    · simpa only [hseed] using hfound
    · simp only [List.filterMap_append,hr,hrf,List.append_nil]

end PerfectHash.Total
