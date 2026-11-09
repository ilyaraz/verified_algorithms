import DataStructures.PerfectHash.Source.Children.Loop

namespace PerfectHash.Source
open WordRam PerfectHash.Bounded

/-- Four explicit source stores turn accepted grouping into the initial child
invariant. This lemma concerns memory only and uses no assembly execution. -/
theorem header_partial (ha : Admissible w xs.length l) (hy : rootAccepted xs a = true)
    (hg : Construction.Grouped (rootHash xs a) (l.outputBase+4) l.scratchBase (values xs).reverse mem) :
    Partial xs l a 0 (writeHeader mem l.outputBase a
      (word w (w-Hashing.PowerOfTwo.bits (values xs).length)) (word w (rootSlots xs)) (word w (values xs).length)) := by
  have hf := ha.ordinary.output
  change l.outputBase+64*(xs.length+1) < modulus w at hf
  have hh : l.outputBase+4 < modulus w := by omega
  have hd (b : Fin (rootSlots xs)) (i : Nat) (hi : i < 4) :
      ¬ (Region.mk l.outputBase 4).Contains (word w (Packed.directory l.outputBase b+i)) := by
    simp only [Region.Contains]
    rw [word_toNat_of_lt (Region.index_lt (i := i) (directory_fit ha b) (show i ≤ 4 by omega))]
    unfold Packed.directory
    dsimp only
    omega
  refine ⟨hy,writeHeader_array hh _ _ _ _ _,?_,?_,?_,by intros; omega⟩
  · intro b
    rw [writeHeader_frame hh _ _ _ _ _ (by simpa using hd b 0 (by decide))]
    exact hg.counts b
  · intro b _
    rw [writeHeader_frame hh _ _ _ _ _ (hd b 1 (by decide))]
    exact hg.heads b
  · intro b
    apply (hg.chains b).frame (bucket_indices b) (childContext ha hy b).node_fit
    intro addr had
    symm
    apply writeHeader_frame hh
    have hs := ha.ordinary.output_scratch
    have hv := values_length_le xs
    simp only [Region.Separated,Layout.output,Layout.scratch,dictionaryCapacity,workspaceCapacity] at hs
    simp only [Region.Contains] at *
    omega

end PerfectHash.Source
