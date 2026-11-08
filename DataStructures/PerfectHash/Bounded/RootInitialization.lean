import DataStructures.PerfectHash.Bounded.Blocks
import DataStructures.PerfectHash.Bounded.Parameters

namespace PerfectHash.Bounded
open WordRam Construction.Registers Registers

set_option maxRecDepth 50000
set_option maxHeartbeats 20000000

macro "setup_regs" : tactic => `(tactic|
  simp_all [roundEntry,rootSetup,update,Construction.Registers.input,count,directory,nodes,width,
    seed,shift,budget,remaining,distinct,key,Construction.Registers.hash,address,oldCount,oldHead,
    increment,node,temp,status,clearCursor,clearRemaining,buckets,table,slots,cursor,slot,flag,
    rootHead,childCount,tableEnd,roundTarget,size,trialsLeft,randomCursor,stage,compactBase,
    Registers.distinctCount,rootShift,bucketIndex,fallbackMode,directoryCursor,tableCursor,
    outputBase,occurrenceCount,originalInput,scratchBase,randomBase,machineWidth])

structure Rounded (xs : List (Word w)) (l : Layout) (s : State w 64) : Prop where
  pc : s.pc = location .rounded
  saved : Saved w xs.length l s.regs
  compact : s.regs compactBase = word w ((dedupLayout l).compact xs.length).base
  distinct : s.regs Registers.distinctCount = word w (values xs).length
  size : s.regs Construction.Registers.size = word w (rootSlots xs)
  shift : s.regs Construction.Registers.shift = word w (w-Hashing.PowerOfTwo.bits (values xs).length)
  array : ArrayAt s.mem ((dedupLayout l).compact xs.length).base (values xs)

structure RootReady (xs : List (Word w)) (l : Layout) (s : State w 64) : Prop where
  pc : s.pc = location .rootChoose
  globals : Globals xs l s.regs
  shift : s.regs Construction.Registers.shift = word w (w-Hashing.PowerOfTwo.bits (values xs).length)
  trials : s.regs trialsLeft = word w w
  cursor : s.regs randomCursor = word w (l.randomBase+1)
  stage : s.regs Registers.stage = word w 0
  fallback : s.regs fallbackMode = word w 0
  array : ArrayAt s.mem ((dedupLayout l).compact xs.length).base (values xs)

variable {w : Nat} {xs : List (Word w)} {l : Layout} {s : State w 64}

theorem Saved.round_entry (h : Saved w N l s.regs) : Saved w N l (roundEntry s).regs := by
  rcases h with ⟨ho,hc,hi,hs,hr,hw⟩
  constructor <;> setup_regs

theorem Saved.rounding (h : Saved w N l s.regs)
    (ht : Construction.Round.RoundPost n w s t) : Saved w N l t.regs := by
  have hr (r : Reg 64) (hs : r ≠ size) (hsh : r ≠ shift) := ht.registers r hs hsh
  constructor
  · rw [hr outputBase (by decide) (by decide)]; exact h.output
  · rw [hr occurrenceCount (by decide) (by decide)]; exact h.count
  · rw [hr originalInput (by decide) (by decide)]; exact h.input
  · rw [hr scratchBase (by decide) (by decide)]; exact h.scratch
  · rw [hr randomBase (by decide) (by decide)]; exact h.random
  · rw [hr machineWidth (by decide) (by decide)]; exact h.width

theorem root_ready (h : Rounded xs l s) : RootReady xs l (rootSetup s) := by
  rcases h with ⟨hp,hs,hc,hd,hm,hsh,ha⟩
  rcases hs with ⟨h56,h57,h58,h59,h60,h61⟩
  have saved : Saved w xs.length l (rootSetup s).regs := by constructor <;> setup_regs
  have glob : Globals xs l (rootSetup s).regs := by
    refine ⟨saved,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> setup_regs <;> rw [word_add]
  refine ⟨rfl,glob,?_,?_,?_,?_,?_,ha⟩ <;> setup_regs <;> rw [word_add]

/-- Compute the root range from the count actually returned by deduplication.
Only register arithmetic is performed between these two simulation points. -/
theorem round_root (ha : Admissible w xs.length l) (h : Deduplicated xs l mem s) (rho : RandomMemory w) :
    ∃ t, Steps program rho (4*Hashing.PowerOfTwo.bits (values xs).length+7) s t [] ∧
      Rounded xs l t ∧ t.mem = s.mem := by
  let u : State w 64 := {roundEntry s with pc := 0}
  have hm := root_slots_bound xs
  have hd := values_length_le xs
  have hf := ha.arithmetic.linearSizes
  have hsizefit : Hashing.PowerOfTwo.size (values xs).length < modulus w := by
    rw [← Hashing.PowerOfTwo.computeSize_eq]
    change rootSlots xs < modulus w
    omega
  have hbits : Hashing.PowerOfTwo.bits (values xs).length ≤ w :=
    Hashing.PowerOfTwo.least (by change (values xs).length ≤ modulus w; omega)
  have hc : u.regs roundTarget = word w (values xs).length := by
    have hh := h.count
    simp only [u]
    setup_regs
  have hm0 : u.regs size = word w (2^0) := by simp [u,roundEntry,update,size,shift]
  have hs0 : u.regs shift = word w (w-0) := by
    have hh := h.saved.width
    simp only [u]
    setup_regs
  obtain ⟨v,hv,hpost⟩ := Construction.Round.round_many rho (values xs).length 0
    (Hashing.PowerOfTwo.bits (values xs).length) (s := u) rfl hc hm0 hs0 (by simp)
    hbits hsizefit ha.arithmetic.widthValue
  have hhalt : step Construction.Round.program rho v = .halt := by
    simp [step,Construction.Round.program,hpost.pc]
  have hterm : TerminatesIn Construction.Round.program rho u
      (4*Hashing.PowerOfTwo.bits (values xs).length+2) v [] :=
    ⟨4*Hashing.PowerOfTwo.bits (values xs).length+1,rfl,hv,hhalt⟩
  have hcall := hterm.call rounding_embedded rounding_returns
  have hu : u.relocate (location (.block .rounding 0)) = roundEntry s := rfl
  rw [hu] at hcall
  have ht := (round_entry s rho h.pc).trans hcall
  have hsave : Saved w xs.length l u.regs := h.saved.round_entry
  have hsave' := Saved.rounding (s := u) (t := v) hsave hpost
  have hcost : 5+(4*Hashing.PowerOfTwo.bits (values xs).length+2) =
      4*Hashing.PowerOfTwo.bits (values xs).length+7 := by omega
  refine ⟨{v with pc := location .rounded},by simpa only [hcost,List.nil_append] using ht,
    ⟨rfl,hsave',?_,?_,?_,hpost.shift,?_⟩,hpost.memory⟩
  · rw [hpost.registers compactBase (by decide) (by decide)]
    have hh := h.base
    simp only [u]
    setup_regs
  · rw [hpost.registers Registers.distinctCount (by decide) (by decide)]
    have hh := h.count
    simp only [u]
    setup_regs
  · rw [hpost.size,rootSlots,Hashing.PowerOfTwo.computeSize_eq]
  · rw [hpost.memory]
    exact h.array

/-- The complete post-deduplication setup is a charged RAM computation with no
ordinary or random memory accesses. -/
theorem initialize_root (ha : Admissible w xs.length l) (h : Deduplicated xs l mem s)
    (rho : RandomMemory w) :
    ∃ t, Steps program rho (4*Hashing.PowerOfTwo.bits (values xs).length+17) s t [] ∧
      RootReady xs l t ∧ t.mem = s.mem := by
  obtain ⟨t,ht,hpost,hmem⟩ := round_root ha h rho
  refine ⟨rootSetup t,?_,root_ready hpost,hmem⟩
  simpa [Nat.add_assoc] using ht.trans (root_setup t rho hpost.pc)

end PerfectHash.Bounded
