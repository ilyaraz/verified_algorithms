import DataStructures.PerfectHash.Construction.RootRound

namespace PerfectHash.Construction.Root
open WordRam Registers

structure LoopPost (ctx : Context w m N) (hash : Word w → Fin m)
    (seen rest : List (Word w)) (t : State w 64) : Prop where
  status : t.regs Registers.status = word w
    (groupAccepted hash (6*N-Buckets.energy hash seen) seen rest).toNat
  pc : t.pc = if groupAccepted hash (6*N-Buckets.energy hash seen) seen rest then 36 else 38
  grouped : groupAccepted hash (6*N-Buckets.energy hash seen) seen rest = true →
    Grouped hash ctx.directoryBase ctx.nodeBase (rest.reverse++seen) t.mem

variable {w m N : Nat} {ctx : Context w m N} {hash : Word w → Fin m}
  {seen rest : List (Word w)} {s : State w 64}

/-- Every root seed reaches a truthful status, with linear actual instruction
cost even when its bucket energy exceeds the cap and it is rejected early. -/
theorem loop_total (h : LoopState ctx hash seen rest s) (rho : RandomMemory w) :
    ∃ k t log, TerminatesIn program rho s k t log ∧ k ≤ 25*rest.length+3 ∧
      LoopPost ctx hash seen rest t ∧ (policy ctx).AllowsTrace log := by
  induction rest generalizing seen s with
  | nil =>
    refine ⟨3,⟨36,update s.regs status (word w 1),s.mem⟩,[],
      exhausted s rho h.pc h.remaining,by simp,?_,by simp [AccessPolicy.AllowsTrace]⟩
    refine ⟨by simp [groupAccepted],rfl,?_⟩
    intro _
    simpa using h.grouped
  | cons x rest ih =>
    by_cases hb : 2*Buckets.count hash seen (hash x)+1 ≤ 6*N-Buckets.energy hash seen
    · have he : groupAccepted hash (6*N-Buckets.energy hash seen) seen (x::rest) =
          groupAccepted hash (6*N-Buckets.energy hash (x::seen)) (x::seen) rest := by
        rw [groupAccepted,if_pos hb,Buckets.energy_cons]
        congr 1
        omega
      obtain ⟨k,t,log,ht,hk,hpost,hpolicy⟩ := ih (round_invariant h hb)
      refine ⟨25+k,t,roundTrace s++log,(round_steps h rho hb).then_terminates ht,?_,?_,
        (AccessPolicy.allowsTrace_append _).mpr ⟨round_policy h,hpolicy⟩⟩
      · simp only [List.length_cons]
        omega
      · refine ⟨?_,?_,?_⟩
        · rw [he]; exact hpost.status
        · rw [he]; exact hpost.pc
        · rw [he]
          intro hh
          simpa [List.reverse_cons,List.append_assoc] using hpost.grouped hh
    · have he : groupAccepted hash (6*N-Buckets.energy hash seen) seen (x::rest) = false := by
        simp [groupAccepted,hb]
      have hn : s.regs remaining ≠ word w 0 := by
        rw [h.remaining]
        intro heq
        have hf := ctx.arithmetic
        have hl := h.length
        have ht := congrArg BitVec.toNat heq
        rw [word_toNat_of_lt (by simp only [List.length_cons] at *; omega),word_toNat_of_lt (by omega)] at ht
        simp at ht
      have hc : ((probe s).regs budget).toNat < ((probe s).regs increment).toNat := by
        rw [h.probe_budget,h.probe_increment,
          word_toNat_of_lt (energy_budget_fit (Nat.sub_le _ _) ctx.arithmetic),
          word_toNat_of_lt (energy_increment_fit hash seen x
            (by have := h.length; simp at *; omega) ctx.arithmetic)]
        omega
      have hs := (probe_next s rho h.pc hn).trans (reject (probe s) rho rfl hc)
      have ht := hs.then_terminates (rejected {probe s with pc := 37} rho rfl)
      refine ⟨12,⟨38,update (probe s).regs status (word w 0),s.mem⟩,probeTrace s,
        by simpa using ht,by simp; omega,?_,probe_policy h⟩
      exact ⟨by simp [he],by simp [he],by simp [he]⟩

end PerfectHash.Construction.Root
