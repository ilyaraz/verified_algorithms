import DataStructures.PerfectHash.Construction.ChildBlocks
import DataStructures.PerfectHash.Construction.Slots
import Algorithms.Dedup.Representation

namespace PerfectHash.Construction.Child
open WordRam Registers

structure Context (w N q : Nat) where
  nodeBase : Nat
  tableBase : Nat
  node_fit : (Region.mk nodeBase (2*N)).Fits w
  table_fit : (Region.mk tableBase (2*q)).Fits w
  separated : (Region.mk nodeBase (2*N)).Separated ⟨tableBase,2*q⟩
  one_lt : 1 < modulus w

/-- A child trial consumes exactly its linked bucket, without scanning other
buckets. The slot view is valid after every successful insertion. -/
structure LoopState (ctx : Context w N q) (hash : Word w → Nat)
    (seen : List (Word w)) (rest : List (Word w × Nat)) (s : State w 64) : Prop where
  pc : s.pc = 8
  nodes : s.regs Registers.nodes = word w ctx.nodeBase
  table : s.regs Registers.table = word w ctx.tableBase
  cursor : s.regs Registers.cursor = word w (Dedup.firstIndex rest)
  evaluator : ∀ x, unsignedShiftRight (s.regs seed*x) (s.regs shift) = word w (hash x)
  range : ∀ p ∈ rest, hash p.1 < q
  indices : ∀ p ∈ rest, 0 < p.2 ∧ p.2 ≤ N
  chain : Dedup.ChainAt s.mem ctx.nodeBase rest
  slots : SlotsAt hash q ctx.tableBase seen s.mem
  positions : (seen.map hash).Nodup

variable {w N q : Nat} {ctx : Context w N q} {hash : Word w → Nat}
  {seen : List (Word w)} {rest : List (Word w × Nat)} {x : Word w} {i : Nat} {s : State w 64}

macro "child_regs" : tactic => `(tactic|
  simp [probe,inserted,insertedMemory,update,Registers.input,count,directory,nodes,width,seed,
    shift,budget,remaining,distinct,key,Registers.hash,address,oldCount,oldHead,increment,node,
    temp,status,clearCursor,clearRemaining,buckets,table,slots,cursor,slot,flag,rootHead, *])

theorem LoopState.node_address (h : LoopState ctx hash seen ((x,i)::rest) s) :
    nodeAddress s = word w (Dedup.nodeAddress ctx.nodeBase i) := by
  have hi := h.indices (x,i) (by simp)
  unfold nodeAddress Dedup.nodeAddress
  rw [h.nodes,h.cursor]
  change word w ctx.nodeBase+(word w i-word w 1)*word w 2 = _
  rw [word_sub _ _ ctx.one_lt hi.1,word_mul,word_add,Nat.mul_comm]

theorem LoopState.key_value (h : LoopState ctx hash seen ((x,i)::rest) s) :
    s.mem (nodeAddress s) = x := by rw [h.node_address]; exact h.chain.1

theorem LoopState.slot_address (h : LoopState ctx hash seen ((x,i)::rest) s) :
    slotAddress s = word w (ctx.tableBase+2*hash x) := by
  unfold slotAddress hashed
  rw [h.table,h.key_value,h.evaluator,word_mul,word_add,Nat.mul_comm]

theorem LoopState.cursor_nonzero (h : LoopState ctx hash seen ((x,i)::rest) s) :
    s.regs Registers.cursor ≠ word w 0 := by
  have hi := h.indices (x,i) (by simp)
  have hf := ctx.node_fit
  simp only [Region.Fits] at hf
  rw [h.cursor]
  change word w i ≠ word w 0
  intro he
  have ht := (word_eq_iff_of_lt (by omega : i < modulus w) (by have := ctx.one_lt; omega)).mp he
  omega

theorem LoopState.flag_zero (h : LoopState ctx hash seen ((x,i)::rest) s) :
    (probe s).regs Registers.flag = word w 0 ↔ hash x ∉ seen.map hash := by
  change s.mem (slotAddress s) = word w 0 ↔ _
  rw [h.slot_address]
  exact h.slots.empty_iff ctx.one_lt (h.range (x,i) (by simp))

def roundNext (s : State w 64) : State w 64 := inserted {probe s with pc := 19}

def roundTrace (s : State w 64) : List (Access w) := probeTrace s++insertedTrace {probe s with pc := 19}

theorem round_steps (h : LoopState ctx hash seen ((x,i)::rest) s) (rho : RandomMemory w)
    (hf : hash x ∉ seen.map hash) : Steps program rho 17 s (roundNext s) (roundTrace s) := by
  have hs := probe_next s rho h.pc h.cursor_nonzero
  have ht := accept (probe s) rho rfl (h.flag_zero.mpr hf)
  have hu := insert_next {probe s with pc := 19} rho rfl
  simpa [roundNext,roundTrace,List.append_assoc] using (hs.trans ht).trans hu

theorem round_memory (h : LoopState ctx hash seen ((x,i)::rest) s) :
    (roundNext s).mem = slotMemory ctx.tableBase (hash x) x s.mem := by
  unfold roundNext inserted insertedMemory probe
  simp only [update,flag,slot,Registers.hash,key,node,Fin.reduceFinMk,Fin.isValue,↓reduceIte]
  change update (update s.mem (slotAddress s) (word w 1))
    (slotAddress s+word w 1) (s.mem (nodeAddress s)) = _
  rw [h.key_value,h.slot_address,word_add]
  rfl

theorem round_frame (h : LoopState ctx hash seen ((x,i)::rest) s) (a : Addr w)
    (ha : ¬ (Region.mk ctx.tableBase (2*q)).Contains a) : (roundNext s).mem a = s.mem a := by
  rw [round_memory h]
  exact slotMemory_frame ctx.table_fit (h.range (x,i) (by simp)) a ha

theorem round_registers (s : State w 64) :
    (roundNext s).regs nodes = s.regs nodes ∧
    (roundNext s).regs table = s.regs table ∧
    (roundNext s).regs seed = s.regs seed ∧
    (roundNext s).regs shift = s.regs shift ∧
    (roundNext s).regs cursor = (roundNext s).mem (nodeAddress s+word w 1) := by
  unfold roundNext
  child_regs

theorem round_invariant (h : LoopState ctx hash seen ((x,i)::rest) s)
    (hf : hash x ∉ seen.map hash) : LoopState ctx hash (x::seen) rest (roundNext s) := by
  obtain ⟨hn,ht,hs,hsh,hc⟩ := round_registers s
  have hi := h.indices (x,i) (by simp)
  have hframe : AgreeOn ⟨ctx.nodeBase,2*N⟩ s.mem (roundNext s).mem := by
    intro a ha
    exact (round_frame h a (Region.not_contains_of_separated ctx.separated ha)).symm
  refine ⟨rfl,hn.trans h.nodes,ht.trans h.table,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [hc,h.node_address,word_add]
    have hn := (Dedup.node_contains ctx.node_fit hi.1 hi.2).2
    rw [← hframe _ hn]
    exact h.chain.2.1
  · intro y
    rw [hs,hsh,h.evaluator]
  · intro p hp
    exact h.range p (by simp [hp])
  · intro p hp
    exact h.indices p (by simp [hp])
  · exact h.chain.2.2.frame (fun p hp => h.indices p (by simp [hp])) ctx.node_fit hframe
  · rw [round_memory h]
    exact h.slots.insert ctx.table_fit (h.range (x,i) (by simp))
  · exact List.nodup_cons.mpr ⟨hf,h.positions⟩

/-- Reads may visit the bucket's node region, but writes visit only the current
child table. Disjoint successful siblings are preserved on every branch. -/
def policy (ctx : Context w N q) : AccessPolicy w :=
  ⟨fun a => (Region.mk ctx.nodeBase (2*N)).Contains a ∨ (Region.mk ctx.tableBase (2*q)).Contains a,
    (Region.mk ctx.tableBase (2*q)).Contains,fun _ => False⟩

theorem probe_policy (h : LoopState ctx hash seen ((x,i)::rest) s) :
    (policy ctx).AllowsTrace (probeTrace s) := by
  have hi := h.indices (x,i) (by simp)
  have hn := (Dedup.node_contains ctx.node_fit hi.1 hi.2).1
  have ht := Region.contains_index ctx.table_fit (by have hx : hash x < q := h.range (x,i) (by simp); omega : 2*hash x < 2*q)
  simp only [probeTrace,h.node_address,h.slot_address,AccessPolicy.AllowsTrace,List.mem_cons,
    List.not_mem_nil,or_false]
  intro e he
  rcases he with rfl | rfl
  · exact Or.inl hn
  · exact Or.inr ht

theorem round_policy (h : LoopState ctx hash seen ((x,i)::rest) s) :
    (policy ctx).AllowsTrace (roundTrace s) := by
  rw [roundTrace,AccessPolicy.allowsTrace_append]
  refine ⟨probe_policy h,?_⟩
  have hi := h.indices (x,i) (by simp)
  have hn := (Dedup.node_contains ctx.node_fit hi.1 hi.2).2
  have ht0 := Region.contains_index ctx.table_fit (by have hx : hash x < q := h.range (x,i) (by simp); omega : 2*hash x < 2*q)
  have ht1 := Region.contains_index ctx.table_fit (by have hx : hash x < q := h.range (x,i) (by simp); omega : 2*hash x+1 < 2*q)
  have hs : (probe s).regs slot = slotAddress s := by child_regs
  have hd : (probe s).regs node = nodeAddress s := by child_regs
  simp only [insertedTrace,hs,hd,h.node_address,h.slot_address,word_add,AccessPolicy.AllowsTrace,
    List.mem_cons,List.not_mem_nil,or_false]
  intro e he
  rcases he with rfl | rfl | rfl
  · exact ht0
  · simpa [Nat.add_assoc] using ht1
  · exact Or.inl hn

end PerfectHash.Construction.Child
