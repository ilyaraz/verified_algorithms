import DataStructures.PerfectHash.Construction.ChildLoop

namespace PerfectHash.Construction.Child
open WordRam Registers

structure Input (ctx : Context w N q) (hash : Word w → Nat) (chain : List (Word w × Nat))
    (s : State w 64) : Prop where
  pc : s.pc = 0
  nodes : s.regs Registers.nodes = word w ctx.nodeBase
  table : s.regs Registers.table = word w ctx.tableBase
  slots : s.regs Registers.slots = word w q
  head : s.regs rootHead = word w (Dedup.firstIndex chain)
  evaluator : ∀ x, unsignedShiftRight (s.regs seed*x) (s.regs shift) = word w (hash x)
  range : ∀ p ∈ chain, hash p.1 < q
  indices : ∀ p ∈ chain, 0 < p.2 ∧ p.2 ≤ N
  chain_at : Dedup.ChainAt s.mem ctx.nodeBase chain

def clearStart (s : State w 64) : State w 64 := {initial s with pc := 0}

def cleared (s : State w 64) (q : Nat) : State w 64 :=
  {Clear.clearMany (2*q) (clearStart s) with pc := 7}

def prepared (s : State w 64) (q : Nat) : State w 64 := startLoop (cleared s q)

variable {w N q : Nat} {ctx : Context w N q} {hash : Word w → Nat}
  {chain : List (Word w × Nat)} {s : State w 64}

theorem clear_start (h : Input ctx hash chain s) :
    (clearStart s).regs clearCursor = word w ctx.tableBase ∧
    (clearStart s).regs clearRemaining = word w (2*q) := by
  simp [clearStart,initial,update,clearCursor,clearRemaining]
  exact ⟨h.table,by rw [h.slots,word_mul,Nat.mul_comm]⟩

theorem cleared_register (s : State w 64) (q : Nat) (r : Reg 64)
    (hc : r ≠ clearCursor) (hr : r ≠ clearRemaining) :
    (cleared s q).regs r = (initial s).regs r :=
  Clear.clear_many_register (2*q) (clearStart s) r hc hr

theorem initialized (h : Input ctx hash chain s) (rho : RandomMemory w) :
    Steps program rho (10*q+4) s (prepared s q) (Clear.clearTrace (2*q) (clearStart s)) := by
  have hf := ctx.table_fit
  simp only [Region.Fits] at hf
  have hs := Clear.clear_many rho (2*q) (s := clearStart s) rfl (clear_start h).2 (by omega)
  have he := hs.relocate_body clear_embedded
  have hh : (clearStart s).relocate 2 = initial s := rfl
  rw [hh] at he
  have ht := ((entry s rho h.pc).trans he).trans (start_loop (cleared s q) rho rfl)
  convert ht using 1 <;> (try rfl) <;> (try simp only [List.nil_append,List.append_nil]) <;> omega

theorem initialized_invariant (h : Input ctx hash chain s) :
    LoopState ctx hash [] chain (prepared s q) := by
  have hg := clear_start h
  have reg (r : Reg 64) (hc : r ≠ clearCursor) (hr : r ≠ clearRemaining) :=
    cleared_register s q r hc hr
  have ha : AgreeOn ⟨ctx.nodeBase,2*N⟩ s.mem (prepared s q).mem := by
    intro a ha
    symm
    exact Clear.clear_frame (2*q) ctx.tableBase hg.1 ctx.table_fit
      (Region.not_contains_of_separated ctx.separated ha)
  have hslots : SlotsAt hash q ctx.tableBase [] (prepared s q).mem :=
    SlotsAt.empty (Clear.clear_array (2*q) ctx.tableBase hg.1 ctx.table_fit)
  refine ⟨rfl,?_,?_,?_,?_,h.range,h.indices,h.chain_at.frame h.indices ctx.node_fit ha,hslots,by simp⟩
  · change update (cleared s q).regs cursor ((cleared s q).regs rootHead) nodes = _
    rw [update_other _ _ _ _ (by decide : nodes ≠ cursor),reg nodes (by decide) (by decide)]
    simpa [initial,update,nodes,clearCursor,clearRemaining] using h.nodes
  · change update (cleared s q).regs cursor ((cleared s q).regs rootHead) table = _
    rw [update_other _ _ _ _ (by decide : table ≠ cursor),reg table (by decide) (by decide)]
    simpa [initial,update,table,clearCursor,clearRemaining] using h.table
  · change update (cleared s q).regs cursor ((cleared s q).regs rootHead) cursor = _
    rw [update_same,reg rootHead (by decide) (by decide)]
    simpa [initial,update,rootHead,clearCursor,clearRemaining] using h.head
  · intro x
    change unsignedShiftRight
      (update (cleared s q).regs cursor ((cleared s q).regs rootHead) seed*x)
      (update (cleared s q).regs cursor ((cleared s q).regs rootHead) shift) = _
    rw [update_other _ _ _ _ (by decide : seed ≠ cursor),update_other _ _ _ _ (by decide : shift ≠ cursor),
      reg seed (by decide) (by decide),reg shift (by decide) (by decide)]
    simpa [initial,update,seed,shift,clearCursor,clearRemaining] using h.evaluator x

theorem initialization_policy (h : Input ctx hash chain s) :
    (policy ctx).AllowsTrace (Clear.clearTrace (2*q) (clearStart s)) := by
  have hp := Clear.clear_trace (2*q) ctx.tableBase (clear_start h).1 ctx.table_fit
  intro e he
  have hh := hp e he
  cases e <;> simp_all [AccessPolicy.Allows,policy]

/-- Complete deterministic child-trial bound, charging initialization even on a
bad seed. The returned slot view is claimed only on a successful status. -/
theorem total (h : Input ctx hash chain s) (rho : RandomMemory w) :
    ∃ k t log, TerminatesIn program rho s k t log ∧ k ≤ 10*q+17*chain.length+7 ∧
      LoopPost ctx hash [] chain t ∧ (policy ctx).AllowsTrace log := by
  obtain ⟨k,t,log,ht,hk,hpost,hpolicy⟩ := loop_total (initialized_invariant h) rho
  refine ⟨10*q+4+k,t,Clear.clearTrace (2*q) (clearStart s)++log,
    (initialized h rho).then_terminates ht,by omega,hpost,
    (AccessPolicy.allowsTrace_append _).mpr ⟨initialization_policy h,hpolicy⟩⟩

end PerfectHash.Construction.Child
