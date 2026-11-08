import DataStructures.PerfectHash.Bounded.Metadata

namespace PerfectHash.Bounded
open WordRam Construction.Registers Registers

set_option maxRecDepth 50000
set_option maxHeartbeats 20000000

structure OuterState (xs : List (Word w)) (l : Layout) (a : Word w) (j : Nat) (s : State w 64) : Prop where
  pc : s.pc = location .childLoop
  globals : Globals xs l s.regs
  index : s.regs bucketIndex = word w j
  directory : s.regs directoryCursor = word w (l.outputBase+4+4*j)
  table : s.regs tableCursor = word w (tableCursorAt xs l a j)
  bound : j ≤ rootSlots xs
  «partial» : Partial xs l a j s.mem

def writeHeader (mem : DataMemory w) (base : Nat) (a sh m d : Word w) : DataMemory w :=
  update (update (update (update mem (word w base) a) (word w (base+1)) sh)
    (word w (base+2)) m) (word w (base+3)) d

theorem writeHeader_frame (hf : base+4 < modulus w) (mem : DataMemory w) (a sh m d : Word w)
    (hn : ¬ (Region.mk base 4).Contains addr) : writeHeader mem base a sh m d addr = mem addr := by
  unfold writeHeader
  rw [update_word _ _ _ (by omega),update_word _ _ _ (by omega),
    update_word _ _ _ (by omega),update_word _ _ _ (by omega)]
  simp only [Region.Contains] at hn
  split <;> (try split) <;> (try split) <;> (try split) <;> first | rfl | omega

theorem writeHeader_array (hf : base+4 < modulus w) (mem : DataMemory w) (a sh m d : Word w) :
    ArrayAt (writeHeader mem base a sh m d) base [a,sh,m,d] := by
  intro i
  have hb : i.val < 4 := i.isLt
  change writeHeader mem base a sh m d (word w (base+i.val)) = [a,sh,m,d][i.val]
  unfold writeHeader
  rw [update_word _ _ _ (by omega),update_word _ _ _ (by omega),
    update_word _ _ _ (by omega),update_word _ _ _ (by omega),word_toNat_of_lt (by omega : base+i.val < modulus w)]
  have : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 ∨ i.val = 3 := by omega
  rcases this with hi | hi | hi | hi <;> simp [hi]

variable {w : Nat} {xs : List (Word w)} {l : Layout} {a : Word w} {s : State w 64}

theorem RootFound.header_memory (h : RootFound xs l rs a s) :
    headerMemory s = writeHeader s.mem l.outputBase a
      (word w (w-Hashing.PowerOfTwo.bits (values xs).length))
      (word w (rootSlots xs)) (word w (values xs).length) := by
  unfold headerMemory writeHeader
  rw [h.core.globals.saved.output,h.seed,h.core.globals.rootShift,h.core.globals.buckets,h.core.globals.distinct]
  simp only [word_add]

theorem RootFound.partial (h : RootFound xs l rs a s) (ha : Admissible w xs.length l) :
    Partial xs l a 0 (headerMemory s) := by
  have hf := ha.ordinary.output
  change l.outputBase+64*(xs.length+1) < modulus w at hf
  have hh : l.outputBase+4 < modulus w := by omega
  rw [h.header_memory]
  have hd (b : Fin (rootSlots xs)) (i : Nat) (hi : i < 4) :
      ¬ (Region.mk l.outputBase 4).Contains (word w (Packed.directory l.outputBase b+i)) := by
    simp only [Region.Contains]
    rw [word_toNat_of_lt (Region.index_lt (i := i) (directory_fit ha b) (show i ≤ 4 by omega))]
    unfold Packed.directory
    dsimp only
    omega
  refine ⟨h.accepted,writeHeader_array hh _ _ _ _ _,?_,?_,?_,by intros; omega⟩
  · intro b
    rw [writeHeader_frame hh _ _ _ _ _ (by simpa using hd b 0 (by decide))]
    exact h.grouped.counts b
  · intro b _
    rw [writeHeader_frame hh _ _ _ _ _ (hd b 1 (by decide))]
    exact h.grouped.heads b
  · intro b
    apply (h.grouped.chains b).frame (bucket_indices b) (childContext ha h.accepted b).node_fit
    intro addr had
    symm
    apply writeHeader_frame hh
    have hs := ha.ordinary.output_scratch
    have hv := values_length_le xs
    simp only [Region.Separated,Layout.output,Layout.scratch,dictionaryCapacity,workspaceCapacity] at hs
    simp only [Region.Contains] at *
    omega

theorem RootFound.outer (h : RootFound xs l rs a s) (ha : Admissible w xs.length l) :
    OuterState xs l a 0 (afterRoot s) := by
  have hg : Globals xs l (afterRoot s).regs := by
    apply h.core.globals.frame
    intro r hr
    have hc : ∀ r : Reg 64, globalRegister r = true →
        r ≠ temp ∧ r ≠ bucketIndex ∧ r ≠ directoryCursor ∧ r ≠ tableCursor := by decide
    obtain ⟨ht,hi,hd,htb⟩ := hc r hr
    simp [afterRoot,update,ht,hi,hd,htb]
  refine ⟨rfl,hg,?_,?_,?_,by omega,h.partial ha⟩
  · simp [afterRoot,update,bucketIndex,tableCursor,directoryCursor]
  · have hd : s.regs (2 : Reg 64) = word w (l.outputBase+4) := h.core.globals.directory
    simp [afterRoot,update,directoryCursor,bucketIndex,tableCursor,Construction.Registers.directory,hd]
  · have hd : s.regs (2 : Reg 64) = word w (l.outputBase+4) := h.core.globals.directory
    have hm : s.regs (22 : Reg 64) = word w (rootSlots xs) := h.core.globals.buckets
    simp [afterRoot,update,tableCursor,bucketIndex,Construction.Registers.directory,buckets,hd,hm,
      cursor_start,word_mul,word_add,Nat.mul_comm]

theorem root_header_policy (ha : Admissible w xs.length l) (h : Globals xs l s.regs) :
    (policy w xs.length l).AllowsTrace (headerTrace s) := by
  have hf := ha.ordinary.output
  have hh (i : Nat) (hi : i < 4) : (l.output xs.length).Contains (word w (l.outputBase+i)) :=
    Region.contains_index hf (by change i < 64*(xs.length+1); omega)
  intro e he
  simp only [headerTrace,h.saved.output,word_add,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl | rfl | rfl | rfl
  · exact Or.inl (hh 0 (by decide))
  · exact Or.inl (hh 1 (by decide))
  · exact Or.inl (hh 2 (by decide))
  · exact Or.inl (hh 3 (by decide))

end PerfectHash.Bounded
