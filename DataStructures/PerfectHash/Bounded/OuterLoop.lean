import DataStructures.PerfectHash.Bounded.Work
import DataStructures.PerfectHash.Bounded.Representation

namespace PerfectHash.Bounded
open WordRam Construction.Registers Registers

set_option maxRecDepth 50000
set_option maxHeartbeats 20000000

/-- Successful bounded construction returns the exact retained descriptor and
the distinct count computed by the executed deduplication pass. -/
structure Built (xs : List (Word w)) (l : Layout) (a : Word w) (s : State w 64) : Prop where
  status : s.regs Construction.Registers.status = word w 1
  base : s.regs Construction.Registers.input = word w l.outputBase
  extent : s.regs count = word w (Packed.words (childCapacity xs a))
  distinct : s.regs directory = word w (StaticSet.distinctCount xs)
  accepted : rootAccepted xs a = true
  representation : Table.representation.Holds xs.toFinset (Packed.region l.outputBase (childCapacity xs a)) s.mem

variable {w : Nat} {xs : List (Word w)} {l : Layout} {a : Word w} {s : State w 64}

theorem outer_finish (ha : Admissible w xs.length l) (h : OuterState xs l a (rootSlots xs) s)
    (rho : RandomMemory w) :
    ∃ t, TerminatesIn program rho s 6 t [] ∧ Built xs l a t := by
  have he : s.regs bucketIndex = s.regs buckets := h.index.trans h.globals.buckets.symm
  let v : State w 64 := {s with pc := location .finish}
  have ht := (child_done s rho h.pc he).then_terminates (finish v rho rfl)
  have h0 : s.regs (56 : Reg 64) = word w l.outputBase := h.globals.saved.output
  have h1 : s.regs (42 : Reg 64) = word w (l.outputBase+Packed.words (childCapacity xs a)) := by
    simpa only [tableCursor,cursor_end] using h.table
  have h2 : s.regs (37 : Reg 64) = word w (StaticSet.distinctCount xs) := by
    simpa only [Registers.distinctCount,values_length] using h.globals.distinct
  refine ⟨finished v,by simpa using ht,?_,?_,?_,?_,h.partial.accepted,h.partial.representation ha⟩
  · simp [v,finished,update,status,Construction.Registers.input,count,directory]
  · simp [v,finished,update,status,Construction.Registers.input,count,directory,outputBase,h0]
  · simp only [v,finished,update,status,Construction.Registers.input,count,directory,tableCursor,outputBase,
      Fin.isValue,Fin.reduceFinMk,↓reduceIte,h0,h1]
    have hf := ha.ordinary.output
    change l.outputBase+64*(xs.length+1) < modulus w at hf
    rw [word_sub _ _ (by omega) (by omega),Nat.add_sub_cancel_left]
    simp
  · simp [v,finished,update,status,Construction.Registers.input,count,directory,Registers.distinctCount,h2]

theorem child_success_policy (ha : Admissible w xs.length l) (h : ChildSetup xs l a b s) :
    (policy w xs.length l).AllowsTrace [.dataWrite (s.regs directoryCursor+word w 1) (s.regs seed)] := by
  apply allocation_policy ha b
  intro e he
  simp only [List.mem_singleton] at he
  subst e
  change (Region.mk (Packed.directory l.outputBase b) 4).Contains (s.regs directoryCursor+word w 1)
  rw [h.directory,word_add]
  exact Region.contains_index (directory_fit ha b) (by decide : 1 < 4)

theorem child_reads_le (xs : List (Word w)) (l : Layout) (a : Word w)
    (b : Fin (rootSlots xs)) (rho : RandomMemory w) : childReads xs l a b rho ≤ w := by
  unfold childReads
  split
  · omega
  · exact FiniteProbability.Retry.attempts_le _ _ _

/-- The complete bounded child loop. Exhaustion is a real failure halt; success
establishes the retained query representation. Each exposed random address is
a subsequence of its reserved consecutive block, so no address is reused. -/
theorem outer_loop (ha : Admissible w xs.length l) (rho : RandomMemory w)
    (h : OuterState xs l a j s) (hlen : j+r = rootSlots xs) :
    ∃ k t log, TerminatesIn program rho s k t log ∧ k ≤ remainingWork xs l a rho j ∧
      (t.regs status = word w 0 ∨ Built xs l a t) ∧ (policy w xs.length l).AllowsTrace log ∧
      (log.filterMap Access.randomAddress).Sublist
        (consecutiveAddresses w (childRandomBase l w j) (w*r)) := by
  induction r generalizing j s with
  | zero =>
    have hj : j = rootSlots xs := by omega
    subst j
    obtain ⟨t,ht,hb⟩ := outer_finish ha h rho
    exact ⟨6,t,[],ht,by rw [remainingWork_end],Or.inr hb,by simp [AccessPolicy.AllowsTrace],by simp⟩
  | succ r ih =>
    have hj : j < rootSlots xs := by omega
    let b : Fin (rootSlots xs) := ⟨j,hj⟩
    obtain ⟨ka,u,la,hta,hka,hpa,hsetup,hpola,hra⟩ := allocate_child (b := b) ha h rho
    obtain ⟨kc,v,lc,htc,hkc,hpolc,hrc,hpost⟩ := child_stage ha hsetup hpa rho
    have hpref := hta.trans htc
    have hpolpref := (AccessPolicy.allowsTrace_append _).mpr ⟨hpola,hpolc⟩
    have hrprefix : ((la++lc).filterMap Access.randomAddress).Sublist
        (consecutiveAddresses w (childRandomBase l w j) w) := by
      simp only [List.filterMap_append,hra,List.nil_append,hrc]
      exact consecutiveAddresses_sublist w _ (child_reads_le xs l a b rho)
    have hcost : ka+kc+7 ≤ childWork xs l a b rho := by unfold childWork; omega
    have hrem := remainingWork_next xs l a rho b
    have hmin := remainingWork_ge xs l a rho (j+1)
    have hseq : consecutiveAddresses w (childRandomBase l w j) (w*(r+1)) =
        consecutiveAddresses w (childRandomBase l w j) w ++
          consecutiveAddresses w (childRandomBase l w (j+1)) (w*r) := by
      rw [show w*(r+1) = w+w*r by ring,consecutiveAddresses_append]
      congr 2
      unfold childRandomBase
      ring
    cases he : childChoice xs l a b rho with
    | none =>
      have hv : ChildSetup xs l a b v ∧ v.pc = location .childChoose ∧ v.regs trialsLeft = word w 0 ∧
          v.regs stage = word w 1 ∧ v.regs fallbackMode = word w 0 := by simpa [ChildStagePost,he] using hpost
      have hfail := (child_budget v rho hv.2.1 hv.2.2.1).then_terminates
        (failed {v with pc := location .failed} rho rfl)
      refine ⟨ka+kc+3,⟨230,update v.regs status (word w 0),v.mem⟩,la++lc,
        by simpa using hpref.then_terminates hfail,?_,Or.inl (by simp [update]),hpolpref,?_⟩
      · change remainingWork xs l a rho j = _ at hrem
        omega
      · rw [hseq]
        exact hrprefix.trans (List.sublist_append_left _ _)
    | some chosen =>
      have hv : ChildSetup xs l a b v ∧ v.pc = location .childResult ∧ v.regs status = word w 1 ∧
          v.regs seed = chosen ∧ childAccepted xs a b chosen = true ∧
          Construction.SlotsAt (childHash w (bucketCount xs a b) chosen) (childCapacity xs a b)
            (Packed.table l.outputBase (childCapacity xs a) b) (bucketKeys xs a b).reverse v.mem := by
        simpa [ChildStagePost,he] using hpost
      have hc : CompleteChild xs l a b (v.regs seed) (childSuccess v).mem :=
        hv.1.completed ha (by simpa [hv.2.2.2.1] using hv.2.2.2.2.1) (by simpa [hv.2.2.2.1] using hv.2.2.2.2.2)
      have houter := hv.1.outer ha hc
      have hone : 1 < modulus w := by have := ha.arithmetic.linearSizes; omega
      have hn : v.regs status ≠ word w 0 := by
        rw [hv.2.2.1]
        intro he
        have hh := (word_eq_iff_of_lt hone (by omega : 0 < modulus w)).mp he
        omega
      have hsuccess := child_yes v rho hv.2.1 hn
      obtain ⟨kr,t,lr,htr,hkr,htpost,hpolr,hrr⟩ := ih houter (by change j+1+r = _; omega)
      refine ⟨ka+kc+7+kr,t,(la++lc)++[.dataWrite (v.regs directoryCursor+word w 1) (v.regs seed)]++lr,
        (hpref.trans hsuccess).then_terminates htr,?_,htpost,?_,?_⟩
      · change remainingWork xs l a rho j = _ at hrem
        omega
      · exact (AccessPolicy.allowsTrace_append _).mpr ⟨
          (AccessPolicy.allowsTrace_append _).mpr ⟨hpolpref,child_success_policy ha hv.1⟩,hpolr⟩
      · simp only [List.filterMap_append,List.filterMap_cons,Access.randomAddress,List.filterMap_nil,List.append_nil]
        rw [hseq]
        simpa only [List.filterMap_append] using hrprefix.append hrr

end PerfectHash.Bounded
