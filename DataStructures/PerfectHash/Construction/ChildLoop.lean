import DataStructures.PerfectHash.Construction.ChildRound

namespace PerfectHash.Construction.Child
open WordRam Registers

structure LoopPost (ctx : Context w N q) (hash : Word w → Nat)
    (seen : List (Word w)) (rest : List (Word w × Nat)) (t : State w 64) : Prop where
  status : t.regs Registers.status = word w (childAccepted hash seen (rest.map Prod.fst)).toNat
  pc : t.pc = if childAccepted hash seen (rest.map Prod.fst) then 26 else 28
  slots : childAccepted hash seen (rest.map Prod.fst) = true →
    SlotsAt hash q ctx.tableBase ((rest.map Prod.fst).reverse++seen) t.mem

variable {w N q : Nat} {ctx : Context w N q} {hash : Word w → Nat}
  {seen : List (Word w)} {rest : List (Word w × Nat)} {s : State w 64}

/-- A child trial visits each linked node at most once, including when its first
collision rejects the seed. No sibling table is touched by either outcome. -/
theorem loop_total (h : LoopState ctx hash seen rest s) (rho : RandomMemory w) :
    ∃ k t log, TerminatesIn program rho s k t log ∧ k ≤ 17*rest.length+3 ∧
      LoopPost ctx hash seen rest t ∧ (policy ctx).AllowsTrace log := by
  induction rest generalizing seen s with
  | nil =>
    refine ⟨3,⟨26,update s.regs status (word w 1),s.mem⟩,[],
      exhausted s rho h.pc h.cursor,by simp,?_,by simp [AccessPolicy.AllowsTrace]⟩
    refine ⟨by simp [childAccepted],rfl,?_⟩
    intro _
    simpa using h.slots
  | cons p rest ih =>
    obtain ⟨x,i⟩ := p
    by_cases hf : hash x ∈ seen.map hash
    · have he : childAccepted hash seen (((x,i)::rest).map Prod.fst) = false := by
        simp [childAccepted,hf]
      have hn : (probe s).regs flag ≠ word w 0 := fun heq => h.flag_zero.mp heq hf
      have hs := (probe_next s rho h.pc h.cursor_nonzero).trans (reject (probe s) rho rfl hn)
      have ht := hs.then_terminates (rejected {probe s with pc := 27} rho rfl)
      refine ⟨13,⟨28,update (probe s).regs status (word w 0),s.mem⟩,probeTrace s,
        by simpa using ht,by simp; omega,?_,probe_policy h⟩
      exact ⟨by simp [childAccepted,hf],by simp [childAccepted,hf],by simp [childAccepted,hf]⟩
    · have he : childAccepted hash seen (((x,i)::rest).map Prod.fst) =
          childAccepted hash (x::seen) (rest.map Prod.fst) := by simp [childAccepted,hf]
      obtain ⟨k,t,log,ht,hk,hpost,hpolicy⟩ := ih (round_invariant h hf)
      refine ⟨17+k,t,roundTrace s++log,(round_steps h rho hf).then_terminates ht,?_,?_,
        (AccessPolicy.allowsTrace_append _).mpr ⟨round_policy h,hpolicy⟩⟩
      · simp only [List.length_cons]
        omega
      · refine ⟨?_,?_,?_⟩
        · rw [he]; exact hpost.status
        · rw [he]; exact hpost.pc
        · rw [he]
          intro hh
          simpa [List.reverse_cons,List.append_assoc] using hpost.slots hh

end PerfectHash.Construction.Child
