import DataStructures.PerfectHash.Bounded.Prelude

namespace PerfectHash.Bounded
open WordRam Construction.Registers Registers

/-- The root bucket count is computed by RAM rounding of the discovered length. -/
def rootSlots (xs : List (Word w)) : Nat := Hashing.PowerOfTwo.computeSize (values xs).length

theorem root_slots_bound (xs : List (Word w)) : rootSlots xs ≤ 2*((values xs).length+1) := by
  rw [rootSlots,Hashing.PowerOfTwo.computeSize_eq]
  exact Hashing.PowerOfTwo.conservative _

theorem root_slots_positive (xs : List (Word w)) : 0 < rootSlots xs := by
  rw [rootSlots,Hashing.PowerOfTwo.computeSize_eq]
  exact Hashing.PowerOfTwo.positive _

/-- Reuse the beginning of deduplication scratch for root linked nodes while
preserving its compact distinct array at the original occurrence-based offset. -/
def rootContext (xs : List (Word w)) (l : Layout) (ha : Admissible w xs.length l) :
    Construction.Root.Context w (rootSlots xs) (values xs).length := by
  have hd := values_length_le xs
  have hm := root_slots_bound xs
  have ho := ha.ordinary.output
  have hs := ha.ordinary.scratch
  have hsep := ha.ordinary.output_scratch
  have hf := ha.arithmetic.linearSizes
  simp only [Layout.output,dictionaryCapacity,Layout.scratch,workspaceCapacity,Region.Fits] at ho hs
  simp only [Layout.output,dictionaryCapacity,Layout.scratch,workspaceCapacity,Region.Separated] at hsep
  refine ⟨((dedupLayout l).compact xs.length).base,l.outputBase+4,l.scratchBase,?_,?_,?_,?_,?_⟩
  · refine ⟨?_,?_,?_⟩
    · simp only [Region.Fits]; omega
    · simp only [Region.Fits]; omega
    · simp only [Region.Separated]; omega
  · simp only [dedupLayout,Dedup.Layout.compact,Region.Fits]
    omega
  · simp only [dedupLayout,Dedup.Layout.compact,Region.Separated]
    omega
  · simp only [dedupLayout,Dedup.Layout.compact,Region.Separated]
    omega
  · omega

/-- Parameters retained across every root/child trial and child allocation. The
current seed, shift, bucket cursor, and retry cursor are tracked separately. -/
structure Globals (xs : List (Word w)) (l : Layout) (rs : WordRam.Registers w 64) : Prop where
  saved : Saved w xs.length l rs
  count : rs Construction.Registers.count = word w (values xs).length
  directory : rs Construction.Registers.directory = word w (l.outputBase+4)
  nodes : rs Construction.Registers.nodes = word w l.scratchBase
  width : rs Construction.Registers.width = word w w
  buckets : rs Construction.Registers.buckets = word w (rootSlots xs)
  compact : rs compactBase = word w ((dedupLayout l).compact xs.length).base
  distinct : rs Registers.distinctCount = word w (values xs).length
  rootShift : rs Registers.rootShift = word w (w-Hashing.PowerOfTwo.bits (values xs).length)

/-- The fixed global register set is disjoint from every trial's destinations. -/
def globalRegister (r : Reg 64) : Bool :=
  ([1,2,3,4,22,36,37,38,56,57,58,59,60,61] : List Nat).contains r.val

theorem Globals.frame (h : Globals xs l rs)
    (hr : ∀ r : Reg 64, globalRegister r = true → rs' r = rs r) : Globals xs l rs' := by
  rcases h with ⟨hs,hc,hd,hn,hw,hb,hcp,hds,hsh⟩
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · constructor
    · rw [hr outputBase (by decide)]; exact hs.output
    · rw [hr occurrenceCount (by decide)]; exact hs.count
    · rw [hr originalInput (by decide)]; exact hs.input
    · rw [hr scratchBase (by decide)]; exact hs.scratch
    · rw [hr randomBase (by decide)]; exact hs.random
    · rw [hr machineWidth (by decide)]; exact hs.width
  · rw [hr Construction.Registers.count (by decide)]; exact hc
  · rw [hr Construction.Registers.directory (by decide)]; exact hd
  · rw [hr Construction.Registers.nodes (by decide)]; exact hn
  · rw [hr Construction.Registers.width (by decide)]; exact hw
  · rw [hr Construction.Registers.buckets (by decide)]; exact hb
  · rw [hr compactBase (by decide)]; exact hcp
  · rw [hr Registers.distinctCount (by decide)]; exact hds
  · rw [hr Registers.rootShift (by decide)]; exact hsh

theorem root_preserves_globals (h : Globals xs l s.regs)
    (ht : TerminatesIn Construction.Root.program rho s k t log) : Globals xs l t.regs := by
  apply h.frame
  intro r hr
  apply ht.register_frame
  apply register_preserved_of_check
  have hc : ∀ r : Reg 64, globalRegister r = true → ∀ pc : Fin Construction.Root.program.size,
      Construction.Root.program[pc.val].destination ≠ some r := by decide
  exact hc r hr

theorem child_preserves_globals (h : Globals xs l s.regs)
    (ht : TerminatesIn Construction.Child.program rho s k t log) : Globals xs l t.regs := by
  apply h.frame
  intro r hr
  apply ht.register_frame
  apply register_preserved_of_check
  have hc : ∀ r : Reg 64, globalRegister r = true → ∀ pc : Fin Construction.Child.program.size,
      Construction.Child.program[pc.val].destination ≠ some r := by decide
  exact hc r hr

theorem allocation_preserves_globals (h : Globals xs l s.regs)
    (ht : TerminatesIn Construction.Allocation.program rho s k t log) : Globals xs l t.regs := by
  apply h.frame
  intro r hr
  apply ht.register_frame
  apply register_preserved_of_check
  have hc : ∀ r : Reg 64, globalRegister r = true → ∀ pc : Fin Construction.Allocation.program.size,
      Construction.Allocation.program[pc.val].destination ≠ some r := by decide
  exact hc r hr

end PerfectHash.Bounded
