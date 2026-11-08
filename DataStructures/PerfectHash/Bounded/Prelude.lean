import DataStructures.PerfectHash.Bounded.MachineCode
import DataStructures.PerfectHash.Admissibility

namespace PerfectHash.Bounded
open WordRam Construction.Registers Registers

set_option maxRecDepth 50000
set_option maxHeartbeats 20000000

/-- The independent deduplication pass uses only its smaller part of the public
scratch reservation and the first addressed random word. -/
def dedupLayout (l : Layout) : Dedup.Layout := ⟨l.inputBase,l.scratchBase,l.randomBase⟩

theorem dedup_admissible (h : Admissible w N l) : Dedup.Admissible w N (dedupLayout l) := by
  have hs := h.ordinary.scratch
  have hsep := h.ordinary.input_scratch
  have hr := h.random
  simp only [Layout.scratch,workspaceCapacity,Region.Fits] at hs
  simp only [Layout.input,Layout.scratch,workspaceCapacity,Region.Separated] at hsep
  simp only [RandomFit,Layout.random,randomCapacity,Region.Fits] at hr
  refine ⟨h.ordinary.input,?_,?_,?_,h.arithmetic.widthValue⟩
  · simp only [dedupLayout,Dedup.Layout.workspace,Dedup.workspaceCapacity,Region.Fits]
    omega
  · simp only [dedupLayout,Dedup.Layout.inputRegion,Dedup.Layout.workspace,Dedup.workspaceCapacity,Region.Separated]
    omega
  · simp only [dedupLayout,Region.Fits]
    omega

/-- Saved public arguments occupy registers beyond every deduplication write. -/
structure Saved (w N : Nat) (l : Layout) (rs : WordRam.Registers w 64) : Prop where
  output : rs outputBase = word w l.outputBase
  count : rs occurrenceCount = word w N
  input : rs originalInput = word w l.inputBase
  scratch : rs scratchBase = word w l.scratchBase
  random : rs randomBase = word w l.randomBase
  width : rs machineWidth = word w w

def entryState (s : State w 64) : State w 64 :=
  ⟨9,update (update (update (update (update (update (update (update (update s.regs
    outputBase (s.regs directory)) occurrenceCount (s.regs count))
    originalInput (s.regs Construction.Registers.input)) scratchBase (s.regs width))
    randomBase (s.regs shift)) machineWidth (s.regs remaining))
    directory (s.regs width)) nodes (s.regs shift)) width (s.regs remaining),s.mem⟩

macro "bounded_reduce" : tactic => `(tactic|
  simp [program_eq,
    run,step,Comparison.test,Operand.eval,State.put,update,RunResult.prepend,
    Construction.Registers.input,count,directory,nodes,width,seed,shift,budget,remaining,distinct,key,
    Construction.Registers.hash,address,oldCount,oldHead,increment,node,temp,status,clearCursor,
    clearRemaining,buckets,table,slots,cursor,slot,flag,rootHead,childCount,tableEnd,roundTarget,size,
    trialsLeft,randomCursor,stage,compactBase,Registers.distinctCount,rootShift,bucketIndex,
    fallbackMode,directoryCursor,tableCursor,outputBase,occurrenceCount,originalInput,scratchBase,
    randomBase,machineWidth, *])

theorem entry (s : State w 64) (rho : RandomMemory w) (hp : s.pc = 0) :
    Steps program rho 9 s (entryState s) [] := by
  apply steps_iff_run.mpr
  unfold entryState
  bounded_reduce

theorem entry_input (h : BuildInput w N l s.regs) :
    Dedup.Input w N (dedupLayout l) (entryState s).regs ∧ Saved w N l (entryState s).regs := by
  rcases h with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8⟩
  change s.regs (0 : Reg 64) = _ at h0
  change s.regs (1 : Reg 64) = _ at h1
  change s.regs (2 : Reg 64) = _ at h2
  change s.regs (3 : Reg 64) = _ at h3
  change s.regs (4 : Reg 64) = _ at h4
  change s.regs (5 : Reg 64) = _ at h5
  change s.regs (6 : Reg 64) = _ at h6
  change s.regs (7 : Reg 64) = _ at h7
  change s.regs (8 : Reg 64) = _ at h8
  constructor
  · simp [Dedup.Input,dedupLayout,entryState,update,Construction.Registers.input,count,
      directory,nodes,width,shift,remaining,outputBase,occurrenceCount,originalInput,
      scratchBase,randomBase,machineWidth,h0,h1,h2,h4,h6,h8]
  · constructor <;> simp [entryState,update,Construction.Registers.input,count,directory,nodes,
      width,shift,remaining,outputBase,occurrenceCount,originalInput,scratchBase,randomBase,
      machineWidth,h0,h1,h2,h4,h6,h8]

theorem dedup_register_preserved (r : Reg 64) (hr : 26 ≤ r.val) :
    ∀ (pc : Nat) (i : Instr 64), Dedup.program[pc]? = some i → i.destination ≠ some r := by
  apply register_preserved_of_check
  have hc : ∀ r : Reg 64, 26 ≤ r.val → ∀ pc : Fin Dedup.program.size,
      Dedup.program[pc.val].destination ≠ some r := by decide
  exact hc r hr

theorem Saved.dedup {s t : State w 64} (h : Saved w N l s.regs)
    (ht : TerminatesIn Dedup.program rho s k t log) : Saved w N l t.regs := by
  have hr (r : Reg 64) (hh : 26 ≤ r.val) := ht.register_frame (dedup_register_preserved r hh)
  constructor
  · rw [hr outputBase (by decide)]; exact h.output
  · rw [hr occurrenceCount (by decide)]; exact h.count
  · rw [hr originalInput (by decide)]; exact h.input
  · rw [hr scratchBase (by decide)]; exact h.scratch
  · rw [hr randomBase (by decide)]; exact h.random
  · rw [hr machineWidth (by decide)]; exact h.width

/-- Seed-independent ghost order established by the executed deduplication pass. -/
def values (xs : List (Word w)) : List (Word w) := (Dedup.collect xs []).reverse

theorem values_nodup (xs : List (Word w)) : (values xs).Nodup := by
  simpa [values] using Dedup.collect_nodup xs [] (by simp)

@[simp] theorem values_membership (xs : List (Word w)) (x : Word w) : x ∈ values xs ↔ x ∈ xs := by
  simp [values]

theorem values_length_le (xs : List (Word w)) : (values xs).length ≤ xs.length := by
  simpa [values] using Dedup.collect_length xs []

theorem values_length (xs : List (Word w)) : (values xs).length = StaticSet.distinctCount xs := by
  rw [← List.toFinset_card_of_nodup (values_nodup xs)]
  unfold StaticSet.distinctCount
  congr 1
  ext x
  simp

/-- The single public policy covers deduplication and every later construction
stage, including failed trials and all interrupted execution prefixes. -/
def policy (w N : Nat) (l : Layout) : AccessPolicy w :=
  ⟨fun a => (l.input N).Contains a ∨ (l.output N).Contains a ∨ (l.scratch N).Contains a,
    fun a => (l.output N).Contains a ∨ (l.scratch N).Contains a,(l.random w N).Contains⟩

theorem dedup_workspace (l : Layout) (N : Nat) (a : Addr w)
    (h : ((dedupLayout l).workspace N).Contains a) : (l.scratch N).Contains a := by
  simp only [dedupLayout,Dedup.Layout.workspace,Dedup.workspaceCapacity,Layout.scratch,
    workspaceCapacity,Region.Contains] at *
  omega

theorem dedup_policy (ha : Admissible w N l) (h : (Dedup.policy (dedupLayout l) N).AllowsTrace log) :
    (policy w N l).AllowsTrace log := by
  intro e he
  have hh := h e he
  cases e with
  | dataRead a v =>
    change ((dedupLayout l).inputRegion N).Contains a ∨ ((dedupLayout l).workspace N).Contains a at hh
    rcases hh with hi | hs
    · exact Or.inl hi
    · exact Or.inr (Or.inr (dedup_workspace l N a hs))
  | dataWrite a v => exact Or.inr (dedup_workspace l N a hh)
  | randomRead a v =>
    change a = word w l.randomBase at hh
    subst a
    have hp : 0 < (l.random w N).size := by simp [Layout.random,randomCapacity]
    exact Region.contains_index ha.random hp

structure Deduplicated (xs : List (Word w)) (l : Layout) (mem : DataMemory w) (s : State w 64) : Prop where
  pc : s.pc = location .deduplicated
  saved : Saved w xs.length l s.regs
  base : s.regs Construction.Registers.input = word w ((dedupLayout l).compact xs.length).base
  count : s.regs Construction.Registers.count = word w (values xs).length
  array : ArrayAt s.mem ((dedupLayout l).compact xs.length).base (values xs)
  frame : ∀ a, ¬ (l.scratch xs.length).Contains a → s.mem a = mem a

/-- Actual bounded-constructor execution reaches a computed distinct array;
its cost retains the deduplication comparison term for the later expectation. -/
theorem deduplicate (xs : List (Word w)) (l : Layout) (ha : Admissible w xs.length l)
    (rho : RandomMemory w) {s : State w 64} (hp : s.pc = 0)
    (hin : BuildInput w xs.length l s.regs) (arr : ArrayAt s.mem l.inputBase xs) :
    ∃ k t log, Steps program rho k s t log ∧
      k ≤ 9+40*(xs.length+1)+9*Dedup.comparisons
        (Dedup.parameters (dedup_admissible ha) (rho (word w l.randomBase))).hash xs [] ∧
      Deduplicated xs l s.mem t ∧ (policy w xs.length l).AllowsTrace log ∧
      log.filterMap Access.randomAddress = [word w l.randomBase] := by
  let u : State w 64 := {entryState s with pc := 0}
  have hi := entry_input hin
  obtain ⟨k,t,log,ht,hk,out,hpolicy⟩ := Dedup.total xs (dedupLayout l) (dedup_admissible ha) rho
    (s := u) rfl hi.1 arr
  have hs := ht.call dedup_embedded dedup_returns
  have hu : u.relocate (location (.block .dedup 0)) = entryState s := rfl
  rw [hu] at hs
  have hh := (entry s rho hp).trans hs
  have hc : t.regs Construction.Registers.count = word w (values xs).length := by
    apply BitVec.eq_of_toNat_eq
    have hf := ha.arithmetic.linearSizes
    have hl := values_length_le xs
    rw [word_toNat_of_lt (by omega)]
    exact out.count
  change k ≤ 40*(xs.length+1)+9*Dedup.comparisons
    (Dedup.parameters (dedup_admissible ha) (rho (word w l.randomBase))).hash xs [] at hk
  have hsave : Saved w xs.length l u.regs := hi.2
  have hsaved := Saved.dedup (s := u) (t := t) hsave ht
  refine ⟨9+k,{t with pc := location .deduplicated},log,by simpa using hh,by omega,
    ⟨rfl,hsaved,out.base,hc,out.array,?_⟩,dedup_policy ha hpolicy,out.randomReads⟩
  intro a had
  exact out.frame a (fun hm => had (dedup_workspace l xs.length a hm))

end PerfectHash.Bounded
