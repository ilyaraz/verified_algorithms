import DataStructures.PerfectHash.Construction.RootLoop

namespace PerfectHash.Construction.Root
open WordRam Registers

structure Input (ctx : Context w m N) (hash : Word w → Fin m) (xs : List (Word w))
    (s : State w 64) : Prop where
  pc : s.pc = 0
  input : s.regs Registers.input = word w ctx.inputBase
  count : s.regs Registers.count = word w N
  directory : s.regs Registers.directory = word w ctx.directoryBase
  nodes : s.regs Registers.nodes = word w ctx.nodeBase
  buckets : s.regs Registers.buckets = word w m
  evaluator : ∀ x, unsignedShiftRight (s.regs seed*x) (s.regs shift) = word w (hash x).val
  length : xs.length = N
  array : ArrayAt s.mem ctx.inputBase xs

def clearStart (s : State w 64) : State w 64 := {initial s with pc := 0}

def cleared (s : State w 64) (m : Nat) : State w 64 :=
  {Clear.clearMany (4*m) (clearStart s) with pc := 10}

variable {w m N : Nat} {ctx : Context w m N} {hash : Word w → Fin m}
  {xs : List (Word w)} {s : State w 64}

theorem clear_start (h : Input ctx hash xs s) :
    (clearStart s).regs clearCursor = word w ctx.directoryBase ∧
    (clearStart s).regs clearRemaining = word w (4*m) := by
  simp [clearStart,initial,update,clearCursor,clearRemaining]
  exact ⟨h.directory,by rw [h.buckets,word_mul,Nat.mul_comm]⟩

theorem cleared_register (s : State w 64) (m : Nat) (r : Reg 64)
    (hc : r ≠ clearCursor) (hr : r ≠ clearRemaining) :
    (cleared s m).regs r = (initial s).regs r :=
  Clear.clear_many_register (4*m) (clearStart s) r hc hr

theorem initialized (h : Input ctx hash xs s) (rho : RandomMemory w) :
    Steps program rho (20*m+6) s (cleared s m) (Clear.clearTrace (4*m) (clearStart s)) := by
  have hf := ctx.space.directory
  simp only [Region.Fits] at hf
  have hs := Clear.clear_many rho (4*m) (s := clearStart s) rfl (clear_start h).2 (by omega)
  have he := hs.relocate_body clear_embedded
  have hh : (clearStart s).relocate 5 = initial s := rfl
  rw [hh] at he
  have ht := (entry s rho h.pc).trans he
  convert ht using 1 <;> first | rfl | omega

theorem initialized_invariant (h : Input ctx hash xs s) :
    LoopState ctx hash [] xs (cleared s m) := by
  have hg := clear_start h
  have hf := ctx.space.directory
  have reg (r : Reg 64) (hc : r ≠ clearCursor) (hr : r ≠ clearRemaining) :=
    cleared_register s m r hc hr
  have ha : AgreeOn ⟨ctx.inputBase,N⟩ s.mem (cleared s m).mem := by
    intro a ha
    symm
    exact Clear.clear_frame (4*m) ctx.directoryBase hg.1 hf
      (Region.not_contains_of_separated ctx.input_directory ha)
  have harr := h.array.congr (by simpa [h.length] using ctx.input_fit) (by simpa [h.length] using ha)
  have hgroup : Grouped hash ctx.directoryBase ctx.nodeBase [] (cleared s m).mem :=
    Grouped.empty (Clear.clear_array (4*m) ctx.directoryBase hg.1 hf)
  refine ⟨rfl,?_,?_,?_,?_,?_,?_,?_,by simpa using h.length,by simp,harr,hgroup⟩
  · rw [reg Registers.input (by decide) (by decide)]
    simpa [initial,update,Registers.input,remaining,distinct,budget,clearCursor,clearRemaining] using h.input
  · rw [reg remaining (by decide) (by decide)]
    simpa [initial,update,remaining,distinct,budget,clearCursor,clearRemaining,h.length] using h.count
  · rw [reg distinct (by decide) (by decide)]
    simp [initial,update,distinct,budget,clearCursor,clearRemaining]
  · rw [reg directory (by decide) (by decide)]
    simpa [initial,update,directory,remaining,distinct,budget,clearCursor,clearRemaining] using h.directory
  · rw [reg nodes (by decide) (by decide)]
    simpa [initial,update,nodes,remaining,distinct,budget,clearCursor,clearRemaining] using h.nodes
  · intro x
    rw [reg seed (by decide) (by decide),reg shift (by decide) (by decide)]
    simpa [initial,update,seed,shift,remaining,distinct,budget,clearCursor,clearRemaining] using h.evaluator x
  · rw [reg budget (by decide) (by decide)]
    simp only [initial,update,budget,remaining,distinct,clearCursor,clearRemaining,Fin.reduceFinMk,
      Fin.isValue,↓reduceIte,Buckets.energy_nil,Nat.sub_zero]
    change s.regs count*word w 6 = _
    rw [h.count,word_mul,Nat.mul_comm]

theorem initialization_policy (h : Input ctx hash xs s) :
    (policy ctx).AllowsTrace (Clear.clearTrace (4*m) (clearStart s)) := by
  have hp := Clear.clear_trace (4*m) ctx.directoryBase (clear_start h).1 ctx.space.directory
  intro e he
  have hh := hp e he
  cases e <;> simp_all [AccessPolicy.Allows,policy]

/-- Full root-trial contract, including charged dirty-directory initialization. -/
theorem total (h : Input ctx hash xs s) (rho : RandomMemory w) :
    ∃ k t log, TerminatesIn program rho s k t log ∧ k ≤ 20*m+25*N+9 ∧
      LoopPost ctx hash [] xs t ∧ (policy ctx).AllowsTrace log := by
  obtain ⟨k,t,log,ht,hk,hpost,hpolicy⟩ := loop_total (initialized_invariant h) rho
  refine ⟨20*m+6+k,t,Clear.clearTrace (4*m) (clearStart s)++log,
    (initialized h rho).then_terminates ht,?_,hpost,
    (AccessPolicy.allowsTrace_append _).mpr ⟨initialization_policy h,hpolicy⟩⟩
  rw [h.length] at hk
  omega

/-- The returned flag agrees with root acceptance, independently of seed quality. -/
theorem status_correct (post : LoopPost ctx hash [] xs t) :
    t.regs status = word w (decide (Buckets.energy hash xs ≤ 6*N)).toNat := by
  have he : groupAccepted hash (6*N-Buckets.energy hash []) [] xs =
      decide (Buckets.energy hash xs ≤ 6*N) := by
    apply Bool.eq_iff_iff.mpr
    rw [groupAccepted_iff]
    simp only [Buckets.energy_nil,Nat.sub_zero,Nat.zero_add,List.append_nil,decide_eq_true_eq]
    rw [energy_perm hash (List.reverse_perm xs)]
  rw [post.status,he]

end PerfectHash.Construction.Root
