import Algorithms.Dedup.Search
import Algorithms.Dedup.Insertion

namespace Dedup
open WordRam Registers Blocks

/-- Mathematical description of the two actual arithmetic instructions used for
hashing; it supplies no advice or additional operation to the RAM program. -/
structure HashParameters (w N : Nat) where
  seed : Word w
  shift : Word w
  slots : Nat
  hash : Word w → Nat
  range : ∀ x, hash x < slots
  capacity : slots ≤ 2*(N+1)
  realizes : ∀ x, unsignedShiftRight (seed*x) shift = word w (hash x)

structure LoopRegisters (N : Nat) (l : Layout) (h : HashParameters w N)
    (d remainingCount : Nat) (s : State w 64) : Prop where
  input : s.regs Registers.input = word w (l.input+(N-remainingCount))
  remaining : s.regs Registers.remaining = word w remainingCount
  distinct : s.regs Registers.distinct = word w d
  heads : s.regs Registers.heads = word w l.scratch
  nodes : s.regs Registers.nodes = word w (l.nodes N).base
  compact : s.regs Registers.compact = word w (l.compact N).base
  seed : s.regs Registers.seed = h.seed
  shift : s.regs Registers.shift = h.shift

structure LoopInvariant (N : Nat) (l : Layout) (h : HashParameters w N)
    (seen rest : List (Word w)) (s : State w 64) : Prop
    extends LoopRegisters N l h seen.length rest.length s where
  pc : s.pc = 25
  space : seen.length+rest.length ≤ N
  array : ArrayAt s.mem (l.input+(N-rest.length)) rest
  representation : Representation w N l h.slots h.hash seen s.mem

/-- Ordinary accesses during the input loop are confined to the input and the
reserved scratch region, with stores confined to scratch. -/
def loopPolicy (l : Layout) (N : Nat) : AccessPolicy w :=
  ⟨fun a => (l.inputRegion N).Contains a ∨ (l.workspace N).Contains a,
    (l.workspace N).Contains, fun _ => False⟩

structure LoopPost (N : Nat) (l : Layout) (h : HashParameters w N)
    (seen rest : List (Word w)) (s t : State w 64) : Prop where
  representation : Representation w N l h.slots h.hash (collect rest seen) t.mem
  base : t.regs Registers.input = word w (l.compact N).base
  count : t.regs Registers.count = word w (collect rest seen).length
  frame : ∀ a, ¬ (l.workspace N).Contains a → t.mem a = s.mem a

variable {w N : Nat} {l : Layout} {h : HashParameters w N}
  {seen rest : List (Word w)} {x : Word w} {s : State w 64}

theorem LoopInvariant.input_loaded (inv : LoopInvariant N l h seen (x::rest) s) :
    s.mem (s.regs Registers.input) = x := by
  rw [inv.input]
  exact (arrayAt_cons.mp inv.array).1

theorem LoopInvariant.head_address (inv : LoopInvariant N l h seen (x::rest) s) :
    inputHead s = word w (l.scratch+h.hash x) := by
  unfold inputHead inputHash
  rw [inv.input_loaded,inv.seed,inv.shift,h.realizes,inv.heads,word_add]

theorem LoopInvariant.head_loaded (inv : LoopInvariant N l h seen (x::rest) s) :
    s.mem (inputHead s) = word w (firstIndex (chain h.hash seen (h.hash x))) := by
  rw [inv.head_address]
  exact inv.representation.head _ (h.range x)

/-- All data needed after search is preserved even though the chain cursor and
its temporary registers are overwritten on every comparison. -/
structure SearchPost (N : Nat) (l : Layout) (h : HashParameters w N)
    (seen : List (Word w)) (x : Word w) (s t : State w 64) : Prop where
  memory : t.mem = s.mem
  pc : t.pc = if x ∈ seen then 41 else 44
  registers : ∀ r, r ≠ Registers.hash → r ≠ key → r ≠ headAddress → r ≠ oldHead →
    r ≠ cursor → r ≠ pointer → r ≠ loaded → t.regs r = s.regs r
  key : t.regs Registers.key = x
  headAddress : t.regs Registers.headAddress = word w (l.scratch+h.hash x)
  oldHead : t.regs Registers.oldHead = word w (firstIndex (chain h.hash seen (h.hash x)))

theorem search_input (rho : RandomMemory w) (ha : Admissible w N l)
    (inv : LoopInvariant N l h seen (x::rest) s) :
    ∃ k t log, Steps program rho k s t log ∧
      k ≤ 8+9*scanComparisons x (bucket h.hash seen x) ∧
      SearchPost N l h seen x s t ∧ (loopPolicy l N).AllowsTrace log := by
  have hs := ha.workspace
  simp only [Layout.workspace,workspaceCapacity,Region.Fits] at hs
  have hr : (x::rest).length < modulus w := by have := inv.space; omega
  have hne : s.regs remaining ≠ word w 0 := by
    rw [inv.remaining]
    intro he
    have ht := congrArg BitVec.toNat he
    rw [word_toNat_of_lt hr,word_toNat_of_lt (by have := ha.two_lt; omega : 0 < modulus w)] at ht
    simp at ht
  have hk : (inputNext s).regs key = x := by
    simpa [inputNext,update,key,Registers.hash,headAddress,oldHead,cursor] using inv.input_loaded
  have hn : (inputNext s).regs nodes = word w (l.nodes N).base := by
    simpa [inputNext,update,key,Registers.hash,headAddress,oldHead,cursor,nodes] using inv.nodes
  have hc : (inputNext s).regs cursor = word w (firstIndex (chain h.hash seen (h.hash x))) := by
    simpa [inputNext] using inv.head_loaded
  obtain ⟨k,t,log,ht,hcost,hpc,hframe,htrace⟩ := scan_total rho rfl hk hn hc
    (inv.representation.chains _ (h.range x)) (fun _ hp => chain_index hp)
    (show (Region.mk (l.nodes N).base (2*seen.length)).Fits w from by
      have := inv.space
      simp only [Region.Fits,Layout.nodes]
      omega) (by have := ha.two_lt; omega)
  refine ⟨7+k,t,_,(input_next s rho inv.pc hne).trans ht,?_,?_,?_⟩
  · simp only [chain_keys] at hcost
    change k ≤ 9*scanComparisons x (bucket h.hash seen x)+1 at hcost
    omega
  · refine ⟨hframe.1,?_,?_,?_,?_,?_⟩
    · simpa [chain_keys,bucket] using hpc
    · intro r hh hk hhA ho hc hp hl
      rw [hframe.2 r hc hp hl]
      simp [inputNext,update,hh,hk,hhA,ho,hc]
    · rw [hframe.2 key (by decide) (by decide) (by decide), hk]
    · rw [hframe.2 headAddress (by decide) (by decide) (by decide)]
      simpa [inputNext,update,headAddress,oldHead,cursor] using inv.head_address
    · rw [hframe.2 oldHead (by decide) (by decide) (by decide)]
      simpa [inputNext,update,oldHead,cursor] using inv.head_loaded
  · rw [AccessPolicy.allowsTrace_append]
    constructor
    · simp only [AccessPolicy.AllowsTrace,List.mem_cons,List.not_mem_nil,or_false]
      intro e he
      rcases he with rfl | rfl
      · apply Or.inl
        rw [inv.input]
        apply Region.contains_index (r := l.inputRegion N) ha.input
        have := inv.space
        simp only [List.length_cons] at *
        change N-(rest.length+1) < N
        omega
      · apply Or.inr
        rw [inv.head_address]
        apply Region.contains_index (r := l.workspace N) ha.workspace
        have := h.range x
        have := h.capacity
        change h.hash x < 6*(N+1)
        omega
    · intro e he
      have hh := htrace e he
      cases e <;> simp only [AccessPolicy.Allows,loopPolicy] at *
      · apply Or.inr
        simp only [Region.Contains,Layout.workspace,Layout.nodes,workspaceCapacity] at *
        have := inv.space
        omega

theorem SearchPost.core {t : State w 64} (post : SearchPost N l h seen x s t)
    (r : Reg 64) (hr : r ∈ [Registers.input,remaining,distinct,heads,nodes,compact,seed,shift]) :
    t.regs r = s.regs r := by
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    apply post.registers <;> decide

theorem SearchPost.loopRegisters {t : State w 64} (post : SearchPost N l h seen x s t)
    (inv : LoopRegisters N l h d k s) : LoopRegisters N l h d k t := by
  constructor
  all_goals rw [post.core _ (by simp)]
  exact inv.input
  exact inv.remaining
  exact inv.distinct
  exact inv.heads
  exact inv.nodes
  exact inv.compact
  exact inv.seed
  exact inv.shift

theorem LoopRegisters.continue {d k : Nat} (regs : LoopRegisters N l h d (k+1) s)
    (ha : Admissible w N l) (hk : k+1 ≤ N) :
    LoopRegisters N l h d k (foundNext s) := by
  have hn : (foundNext s).regs Registers.input = s.regs Registers.input+word w 1 := by
    simp [foundNext,update,Registers.input,Registers.remaining]
  have hr : (foundNext s).regs Registers.remaining = s.regs Registers.remaining-word w 1 := by
    simp [foundNext,update]
  constructor
  · rw [hn,regs.input,word_add]
    congr 1
    omega
  · rw [hr,regs.remaining,word_sub _ _ (by have := ha.two_lt; omega) (by omega)]
    simp
  · simpa [foundNext,update,Registers.input,Registers.remaining,Registers.distinct] using regs.distinct
  · simpa [foundNext,update,Registers.input,Registers.remaining,Registers.heads] using regs.heads
  · simpa [foundNext,update,Registers.input,Registers.remaining,Registers.nodes] using regs.nodes
  · simpa [foundNext,update,Registers.input,Registers.remaining,Registers.compact] using regs.compact
  · simpa [foundNext,update,Registers.input,Registers.remaining,Registers.seed] using regs.seed
  · simpa [foundNext,update,Registers.input,Registers.remaining,Registers.shift] using regs.shift

theorem continue_invariant {t : State w 64} {keys : List (Word w)}
    (ha : Admissible w N l) (space : keys.length+rest.length ≤ N) (hk : rest.length+1 ≤ N)
    (regs : LoopRegisters N l h keys.length (rest.length+1) t)
    (rep : Representation w N l h.slots h.hash keys t.mem)
    (arr : ArrayAt t.mem (l.input+(N-(rest.length+1))) (x::rest)) :
    LoopInvariant N l h keys rest (foundNext t) := by
  refine ⟨regs.continue ha hk,rfl,space,?_,rep⟩
  have ht := (arrayAt_cons.mp arr).2
  have he : l.input+(N-(rest.length+1))+1 = l.input+(N-rest.length) := by omega
  simpa [he] using ht

theorem missing_memory {t : State w 64} (inv : LoopInvariant N l h seen (x::rest) s)
    (post : SearchPost N l h seen x s t) :
    missingMemory t = insertMemory l N seen.length (h.hash x) x
      (word w (firstIndex (chain h.hash seen (h.hash x)))) s.mem := by
  have regs := post.loopRegisters inv.toLoopRegisters
  have hn : missingNode t = word w ((l.nodes N).base+2*seen.length) := by
    unfold missingNode
    rw [regs.distinct,regs.nodes,word_mul,word_add]
    congr 1
    omega
  have hc : missingCompact t = word w ((l.compact N).base+seen.length) := by
    unfold missingCompact
    rw [regs.compact,regs.distinct,word_add]
  unfold missingMemory insertMemory
  rw [hn,hc,word_add,post.key,post.oldHead,post.headAddress,regs.distinct,word_add,post.memory]

theorem missing_registers {t : State w 64} (post : SearchPost N l h seen x s t)
    (inv : LoopRegisters N l h seen.length k s) :
    LoopRegisters N l h (seen.length+1) k (missingNext t) := by
  have regs := post.loopRegisters inv
  constructor
  · simpa [missingNext,update,Registers.input,newNode,compactPointer,distinct] using regs.input
  · simpa [missingNext,update,remaining,newNode,compactPointer,distinct] using regs.remaining
  · simp only [missingNext,update_same,regs.distinct,word_add]
  · simpa [missingNext,update,heads,newNode,compactPointer,distinct] using regs.heads
  · simpa [missingNext,update,nodes,newNode,compactPointer,distinct] using regs.nodes
  · simpa [missingNext,update,compact,newNode,compactPointer,distinct] using regs.compact
  · simpa [missingNext,update,seed,newNode,compactPointer,distinct] using regs.seed
  · simpa [missingNext,update,shift,newNode,compactPointer,distinct] using regs.shift

theorem LoopInvariant.array_frame {mem : DataMemory w}
    (inv : LoopInvariant N l h seen rest s) (ha : Admissible w N l)
    (frame : ∀ a, ¬ (l.workspace N).Contains a → mem a = s.mem a) :
    ArrayAt mem (l.input+(N-rest.length)) rest := by
  intro i
  rw [frame]
  · exact inv.array i
  · apply Region.not_contains_of_separated ha.separated
    have he : l.input+(N-rest.length)+i.val = l.input+((N-rest.length)+i.val) := by omega
    rw [he]
    apply Region.contains_index ha.input
    have := inv.space
    have := i.isLt
    change N-rest.length+i.val < N
    omega

theorem missing_trace {t : State w 64} (ha : Admissible w N l)
    (inv : LoopInvariant N l h seen (x::rest) s) (post : SearchPost N l h seen x s t) :
    (loopPolicy l N).AllowsTrace (missingTrace t) := by
  have regs := post.loopRegisters inv.toLoopRegisters
  have hn : missingNode t = word w ((l.nodes N).base+2*seen.length) := by
    unfold missingNode
    rw [regs.distinct,regs.nodes,word_mul,word_add]
    congr 1
    omega
  have hc : missingCompact t = word w ((l.compact N).base+seen.length) := by
    unfold missingCompact
    rw [regs.compact,regs.distinct,word_add]
  unfold missingTrace
  rw [hn,hc,word_add,post.headAddress]
  intro e he
  simp only [List.mem_cons,List.not_mem_nil,or_false] at he
  have hd := inv.space
  simp only [List.length_cons] at hd
  rcases he with rfl | rfl | rfl | rfl
  all_goals
    change (l.workspace N).Contains _
    try simp only [Layout.nodes,Layout.compact]
  · have he : l.scratch+2*(N+1)+2*seen.length = l.scratch+(2*(N+1)+2*seen.length) := by omega
    rw [he]
    exact Region.contains_index ha.workspace (by change _ < 6*(N+1); omega)
  · have he : l.scratch+2*(N+1)+2*seen.length+1 = l.scratch+(2*(N+1)+2*seen.length+1) := by omega
    rw [he]
    exact Region.contains_index ha.workspace (by change _ < 6*(N+1); omega)
  · have he : l.scratch+2*(N+1)+2*N+seen.length = l.scratch+(2*(N+1)+2*N+seen.length) := by omega
    rw [he]
    exact Region.contains_index ha.workspace (by change _ < 6*(N+1); omega)
  · exact Region.contains_index ha.workspace (by
      have := h.range x
      have := h.capacity
      change _ < 6*(N+1)
      omega)

/-- One occurrence searches its chain, inserts exactly when absent, and advances
the input pointer. The ten-store-block instructions are charged on every input
in this upper bound, so duplicate-heavy inputs need no separate analysis. -/
theorem loop_iteration (rho : RandomMemory w) (ha : Admissible w N l)
    (inv : LoopInvariant N l h seen (x::rest) s) :
    ∃ k t log, Steps program rho k s t log ∧
      k ≤ 21+9*scanComparisons x (bucket h.hash seen x) ∧
      LoopInvariant N l h (insert x seen) rest t ∧ (loopPolicy l N).AllowsTrace log := by
  obtain ⟨k,t,log,hsteps,hcost,post,htrace⟩ := search_input rho ha inv
  have hs := inv.space
  simp only [List.length_cons] at hs
  by_cases hx : x ∈ seen
  · have hp : t.pc = 41 := by simpa [hx] using post.pc
    have hi : LoopInvariant N l h seen rest (foundNext t) := continue_invariant ha (by omega)
      (by omega) (post.loopRegisters inv.toLoopRegisters)
      (by rw [post.memory]; exact inv.representation) (by rw [post.memory]; exact inv.array)
    refine ⟨k+3,foundNext t,log,?_,by omega,?_,htrace⟩
    · simpa using hsteps.trans (found_next t rho hp)
    · simpa [insert,hx] using hi
  · have hp : t.pc = 44 := by simpa [hx] using post.pc
    have hm := missing_memory inv post
    have hd : seen.length < N := by omega
    have hb : h.hash x < 2*(N+1) := (h.range x).trans_le h.capacity
    have frame : ∀ a, ¬ (l.workspace N).Contains a → (missingNext t).mem a = s.mem a := by
      intro a haa
      change missingMemory t a = s.mem a
      rw [hm]
      exact insertMemory_frame ha hd hb haa
    have rep : Representation w N l h.slots h.hash (x::seen) (missingNext t).mem := by
      change Representation _ _ _ _ _ _ (missingMemory t)
      rw [hm]
      exact inv.representation.insertMemory ha h.capacity (h.range x) hx hd
    have hi := continue_invariant ha (by simp only [List.length_cons]; omega :
        (x::seen).length+rest.length ≤ N) (by omega)
      (missing_registers post inv.toLoopRegisters) rep (inv.array_frame ha frame)
    have hsuffix := (missing_next t rho hp).trans (found_next (missingNext t) rho rfl)
    refine ⟨k+13,foundNext (missingNext t),log++missingTrace t,?_,by omega,?_,?_⟩
    · simpa using hsteps.trans hsuffix
    · simpa [insert,hx] using hi
    · exact (AccessPolicy.allowsTrace_append _).mpr ⟨htrace,missing_trace ha inv post⟩

/-- Totality and actual instruction accounting for the complete occurrence loop.
The seed-independent comparison model is the only input-dependent term. -/
theorem loop_total (rho : RandomMemory w) (ha : Admissible w N l)
    (inv : LoopInvariant N l h seen rest s) :
    ∃ k t log, TerminatesIn program rho s k t log ∧
      k ≤ 21*rest.length+9*comparisons h.hash rest seen+4 ∧
      LoopPost N l h seen rest s t ∧ (loopPolicy l N).AllowsTrace log := by
  induction rest generalizing seen s with
  | nil =>
    refine ⟨4,finish s,[],input_exit s rho inv.pc inv.remaining,by simp [comparisons],?_,?_⟩
    · refine ⟨inv.representation,?_,?_,by intros; rfl⟩
      · simpa [finish,update,Registers.input,count] using inv.compact
      · simpa [finish,update,collect] using inv.distinct
    · simp [AccessPolicy.AllowsTrace]
  | cons x rest ih =>
    obtain ⟨a,u,la,hstep,hbound,hinv,htrace⟩ := loop_iteration rho ha inv
    obtain ⟨b,t,lb,hterm,hcost,hpost,htrace'⟩ := ih hinv
    obtain ⟨b',hb',hsteps,hhalt⟩ := hterm
    have hc : a+b = a+b'+1 := by omega
    have hfull := hstep.trans hsteps
    have policy := (AccessPolicy.allowsTrace_append _).mpr ⟨htrace,htrace'⟩
    refine ⟨a+b,t,la++lb,⟨a+b',hc,hfull,hhalt⟩,?_,?_,policy⟩
    · simp only [List.length_cons,comparisons]
      omega
    · refine ⟨hpost.representation,hpost.base,hpost.count,?_⟩
      intro addr had
      exact hfull.frame_of_policy policy had

end Dedup
