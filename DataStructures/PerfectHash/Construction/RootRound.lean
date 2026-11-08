import DataStructures.PerfectHash.Construction.RootBlocks
import DataStructures.PerfectHash.Construction.Grouping

namespace PerfectHash.Construction.Root
open WordRam Registers

/-- Fixed trial regions and arithmetic assumptions. The input array and nodes
are separate, so grouping never overwrites an unread key. -/
structure Context (w m N : Nat) where
  inputBase : Nat
  directoryBase : Nat
  nodeBase : Nat
  space : GroupSpace w m N directoryBase nodeBase
  input_fit : (Region.mk inputBase N).Fits w
  input_directory : (Region.mk inputBase N).Separated ⟨directoryBase,4*m⟩
  input_nodes : (Region.mk inputBase N).Separated ⟨nodeBase,2*N⟩
  arithmetic : 64*(N+1) < modulus w

/-- Simulation at the grouping loop head. The ghost list records nodes already
inserted in reverse order; the machine discovers all counts by executing stores. -/
structure LoopState (ctx : Context w m N) (hash : Word w → Fin m)
    (seen rest : List (Word w)) (s : State w 64) : Prop where
  pc : s.pc = 10
  input : s.regs Registers.input = word w (ctx.inputBase+seen.length)
  remaining : s.regs Registers.remaining = word w rest.length
  distinct : s.regs Registers.distinct = word w seen.length
  directory : s.regs Registers.directory = word w ctx.directoryBase
  nodes : s.regs Registers.nodes = word w ctx.nodeBase
  evaluator : ∀ x, unsignedShiftRight (s.regs seed*x) (s.regs shift) = word w (hash x).val
  budget : s.regs Registers.budget = word w (6*N-Buckets.energy hash seen)
  length : seen.length+rest.length = N
  energy : Buckets.energy hash seen ≤ 6*N
  array : ArrayAt s.mem (ctx.inputBase+seen.length) rest
  grouped : Grouped hash ctx.directoryBase ctx.nodeBase seen s.mem

variable {w m N : Nat} {ctx : Context w m N} {hash : Word w → Fin m}
  {seen rest : List (Word w)} {s : State w 64} {x : Word w}

macro "root_regs" : tactic => `(tactic|
  simp [probe,hashed,bucketAddress,inserted,insertedMemory,newNode,
    update,Registers.input,count,directory,nodes,width,seed,shift,budget,remaining,
    distinct,key,Registers.hash,address,oldCount,oldHead,increment,node,temp,status,
    clearCursor,clearRemaining,buckets, *])

theorem LoopState.key (h : LoopState ctx hash seen (x::rest) s) :
    s.mem (s.regs Registers.input) = x := by
  rw [h.input]
  exact (arrayAt_cons.mp h.array).1

theorem LoopState.hash_value (h : LoopState ctx hash seen (x::rest) s) :
    hashed s = word w (hash x).val := by unfold hashed; rw [h.key,h.evaluator]

theorem LoopState.address (h : LoopState ctx hash seen (x::rest) s) :
    bucketAddress s = word w (ctx.directoryBase+4*(hash x).val) := by
  unfold bucketAddress
  rw [h.directory,h.hash_value,word_mul,word_add,Nat.mul_comm]

theorem LoopState.probe_count (h : LoopState ctx hash seen (x::rest) s) :
    s.mem (bucketAddress s) = word w (Buckets.count hash seen (hash x)) := by
  rw [h.address]
  exact h.grouped.counts _

theorem LoopState.probe_budget (h : LoopState ctx hash seen (x::rest) s) :
    (probe s).regs Registers.budget = word w (6*N-Buckets.energy hash seen) := by
  simpa [probe,update,increment,oldCount,Registers.address,Registers.hash,Registers.key,Registers.budget] using h.budget

theorem LoopState.probe_increment (h : LoopState ctx hash seen (x::rest) s) :
    (probe s).regs increment = word w (2*Buckets.count hash seen (hash x)+1) := by
  simp only [probe,update_same,h.probe_count,word_mul,word_add,Nat.mul_comm]

def roundNext (s : State w 64) : State w 64 := inserted {probe s with pc := 20}

def roundTrace (s : State w 64) : List (Access w) :=
  probeTrace s++insertedTrace {probe s with pc := 20}

theorem round_steps (h : LoopState ctx hash seen (x::rest) s) (rho : RandomMemory w)
    (hb : 2*Buckets.count hash seen (hash x)+1 ≤ 6*N-Buckets.energy hash seen) :
    Steps program rho 25 s (roundNext s) (roundTrace s) := by
  have hn : s.regs remaining ≠ word w 0 := by
    rw [h.remaining]
    intro he
    have ht := congrArg BitVec.toNat he
    rw [word_toNat_of_lt (by have := ctx.arithmetic; have := h.length; simp at *; omega),
      word_toNat_of_lt (by have := ctx.arithmetic; omega)] at ht
    simp at ht
  have hc : ((probe s).regs increment).toNat ≤ ((probe s).regs budget).toNat := by
    rw [h.probe_increment,h.probe_budget,
      word_toNat_of_lt (energy_increment_fit hash seen x (by have := h.length; simp at *; omega) ctx.arithmetic),
      word_toNat_of_lt (energy_budget_fit (Nat.sub_le _ _) ctx.arithmetic)]
    exact hb
  have hs := probe_next s rho h.pc hn
  have ht := accept (probe s) rho rfl hc
  have hu := insert_next {probe s with pc := 20} rho rfl
  simpa [roundNext,roundTrace,List.append_assoc] using (hs.trans ht).trans hu

/-- The machine's stores coincide with the natural-address grouping update. -/
theorem round_memory (h : LoopState ctx hash seen (x::rest) s) :
    (roundNext s).mem = groupMemory ctx.directoryBase ctx.nodeBase seen.length (hash x).val
      (Buckets.count hash seen (hash x)) x
      (word w (Dedup.firstIndex (Dedup.chain (fun y => (hash y).val) seen (hash x).val))) s.mem := by
  have hh : s.mem (bucketAddress s+word w 1) =
      word w (Dedup.firstIndex (Dedup.chain (fun y => (hash y).val) seen (hash x).val)) := by
    rw [h.address,word_add]
    exact h.grouped.heads _
  simp only [roundNext,inserted,insertedMemory,newNode,probe]
  simp only [update,Registers.input,count,directory,nodes,width,seed,shift,budget,remaining,
    distinct,key,Registers.hash,address,oldCount,oldHead,increment,node,temp,status,
    clearCursor,clearRemaining,buckets,Fin.reduceFinMk,Fin.isValue,↓reduceIte]
  change update (update (update (update s.mem
    (s.regs nodes+s.regs distinct*word w 2) (s.mem (s.regs Registers.input)))
    (s.regs nodes+s.regs distinct*word w 2+word w 1) (s.mem (bucketAddress s+word w 1)))
    (bucketAddress s+word w 1) (s.regs distinct+word w 1))
    (bucketAddress s) (s.mem (bucketAddress s)+word w 1) = _
  rw [h.nodes,h.distinct,h.key,h.probe_count,hh,h.address]
  simp only [word_mul,word_add,Nat.mul_comm,groupMemory]

/-- Register effects are independent of directory contents and address values. -/
theorem round_registers (s : State w 64) :
    (roundNext s).regs Registers.input = s.regs Registers.input+word w 1 ∧
    (roundNext s).regs remaining = s.regs remaining-word w 1 ∧
    (roundNext s).regs distinct = s.regs distinct+word w 1 ∧
    (roundNext s).regs directory = s.regs directory ∧
    (roundNext s).regs nodes = s.regs nodes ∧
    (roundNext s).regs seed = s.regs seed ∧
    (roundNext s).regs shift = s.regs shift ∧
    (roundNext s).regs budget = (probe s).regs budget-(probe s).regs increment := by
  unfold roundNext
  root_regs

theorem round_frame (h : LoopState ctx hash seen (x::rest) s) (a : Addr w)
    (hd : ¬ (Region.mk ctx.directoryBase (4*m)).Contains a)
    (hn : ¬ (Region.mk ctx.nodeBase (2*N)).Contains a) :
    (roundNext s).mem a = s.mem a := by
  rw [round_memory h]
  exact groupMemory_frame ctx.space (by have := h.length; simp at *; omega)
    (hash x).isLt _ _ _ _ hd hn

theorem round_invariant (h : LoopState ctx hash seen (x::rest) s)
    (hb : 2*Buckets.count hash seen (hash x)+1 ≤ 6*N-Buckets.energy hash seen) :
    LoopState ctx hash (x::seen) rest (roundNext s) := by
  obtain ⟨hi,hr,hd,hdir,hn,hs,hsh,hbgt⟩ := round_registers s
  have hf := ctx.arithmetic
  have hl := h.length
  have he := h.energy
  have hinc := energy_increment_fit hash seen x (by simp at hl; omega) hf
  refine ⟨rfl,?_,?_,?_,hdir.trans h.directory,hn.trans h.nodes,?_,?_,?_,?_,?_,?_⟩
  · rw [hi,h.input,word_add]
    simp [Nat.add_assoc]
  · rw [hr,h.remaining,word_sub _ _ (by omega) (by simp)]
    simp
  · rw [hd,h.distinct,word_add]
    rfl
  · intro y
    rw [hs,hsh,h.evaluator]
  · rw [hbgt,h.probe_budget,h.probe_increment,word_sub _ _ hinc hb,Buckets.energy_cons]
    congr 1
    omega
  · simp only [List.length_cons] at hl ⊢
    omega
  · rw [Buckets.energy_cons]
    omega
  · have ha := (arrayAt_cons.mp h.array).2
    have hh : ctx.inputBase+seen.length+1 = ctx.inputBase+(x::seen).length := by simp [Nat.add_assoc]
    rw [hh] at ha
    refine ha.congr ?_ ?_
    · have hf := ctx.input_fit
      simp only [Region.Fits,List.length_cons] at *
      omega
    · intro a ha
      symm
      have hc : (Region.mk ctx.inputBase N).Contains a := by
        simp only [Region.Contains,List.length_cons] at *
        omega
      exact round_frame h a (Region.not_contains_of_separated ctx.input_directory hc)
        (Region.not_contains_of_separated ctx.input_nodes hc)
  · rw [round_memory h]
    exact h.grouped.insert ctx.space (by simp at hl; omega)

/-- Both the read-only probe and the committing stores stay inside the trial's
linear regions. This bound also applies to prefixes stopped before rejection. -/
def policy (ctx : Context w m N) : AccessPolicy w :=
  ⟨fun a => (Region.mk ctx.inputBase N).Contains a ∨
      (Region.mk ctx.directoryBase (4*m)).Contains a ∨ (Region.mk ctx.nodeBase (2*N)).Contains a,
    fun a => (Region.mk ctx.directoryBase (4*m)).Contains a ∨ (Region.mk ctx.nodeBase (2*N)).Contains a,
    fun _ => False⟩

theorem probe_policy (h : LoopState ctx hash seen (x::rest) s) :
    (policy ctx).AllowsTrace (probeTrace s) := by
  have hl : seen.length < N := by have := h.length; simp at *; omega
  have hi := Region.contains_index ctx.input_fit hl
  have hb := Region.contains_index ctx.space.directory
    (by have := (hash x).isLt; omega : 4*(hash x).val < 4*m)
  simp only [probeTrace,AccessPolicy.AllowsTrace,List.mem_cons,List.not_mem_nil,or_false]
  intro e he
  rcases he with rfl | rfl
  · exact Or.inl (h.input ▸ hi)
  · exact Or.inr (Or.inl (h.address ▸ hb))

theorem round_policy (h : LoopState ctx hash seen (x::rest) s) :
    (policy ctx).AllowsTrace (roundTrace s) := by
  rw [roundTrace,AccessPolicy.allowsTrace_append]
  refine ⟨probe_policy h,?_⟩
  have hl : seen.length < N := by have := h.length; simp at *; omega
  have hn0 := Region.contains_index ctx.space.nodes_fit (by omega : 2*seen.length < 2*N)
  have hn1 := Region.contains_index ctx.space.nodes_fit (by omega : 2*seen.length+1 < 2*N)
  have hd0 := Region.contains_index ctx.space.directory
    (by have := (hash x).isLt; omega : 4*(hash x).val < 4*m)
  have hd1 := Region.contains_index ctx.space.directory
    (by have := (hash x).isLt; omega : 4*(hash x).val+1 < 4*m)
  have heNode : newNode {probe s with pc := 20} = word w (ctx.nodeBase+2*seen.length) := by
    simp only [newNode,probe]
    have hh : (probe s).regs nodes = s.regs nodes ∧ (probe s).regs distinct = s.regs distinct := by root_regs
    change s.regs nodes+s.regs distinct*word w 2 = _
    rw [h.nodes,h.distinct,word_mul,word_add,Nat.mul_comm seen.length 2]
  have heAddr : (probe s).regs address = bucketAddress s := by
    simp [probe,update,address,increment,oldCount]
  simp only [insertedTrace,heNode,heAddr,h.address,word_add,AccessPolicy.AllowsTrace,
    List.mem_cons,List.not_mem_nil,or_false]
  intro e he
  rcases he with rfl | rfl | rfl | rfl | rfl
  · exact Or.inr (Or.inl (by simpa [Nat.add_assoc] using hd1))
  · exact Or.inr hn0
  · exact Or.inr (by simpa [Nat.add_assoc] using hn1)
  · exact Or.inl (by simpa [Nat.add_assoc] using hd1)
  · exact Or.inl hd0

end PerfectHash.Construction.Root
