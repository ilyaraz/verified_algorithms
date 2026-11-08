import DataStructures.PerfectHash.Sizes
import WordRam.Regions

namespace PerfectHash.Packed
open WordRam
variable {m w base i j k field : Nat} {q : Fin m → Nat}

/-- Prefix slots before directory entry j; only proof-side layout arithmetic. -/
def slotPrefix (q : Fin m → Nat) (j : Nat) : Nat := ∑ i : Fin m, if i.val < j then q i else 0

def directoryBase (base : Nat) : Nat := base+4

def directory (base : Nat) (b : Fin m) : Nat := base+4+4*b.val

def tablesBase (base m : Nat) : Nat := base+4+4*m

def table (base : Nat) (q : Fin m → Nat) (b : Fin m) : Nat := tablesBase base m+2*slotPrefix q b.val

def words (q : Fin m → Nat) : Nat := 4+4*m+2*∑ b : Fin m, q b

def region (base : Nat) (q : Fin m → Nat) : Region := ⟨base,words q⟩

@[simp] theorem prefix_zero (q : Fin m → Nat) : slotPrefix q 0 = 0 := by simp [slotPrefix]

@[simp] theorem prefix_end (q : Fin m → Nat) : slotPrefix q m = ∑ b : Fin m, q b := by
  apply Finset.sum_congr rfl
  intro b _
  simp [b.isLt]

theorem prefix_mono (q : Fin m → Nat) (hjk : j ≤ k) : slotPrefix q j ≤ slotPrefix q k := by
  apply Finset.sum_le_sum
  intro i _
  by_cases hi : i.val < j
  · simp [hi,show i.val < k by omega]
  · simp [hi]

theorem prefix_next (q : Fin m → Nat) (b : Fin m) : slotPrefix q (b.val+1) = slotPrefix q b.val+q b := by
  have he (i : Fin m) : (if i.val < b.val+1 then q i else 0) =
      (if i.val < b.val then q i else 0)+(if i = b then q i else 0) := by
    by_cases h : i = b
    · subst i
      simp
    · have hn : i.val ≠ b.val := fun he => h (Fin.ext he)
      by_cases hi : i.val < b.val <;> simp [h,hi,show (i.val < b.val+1 ↔ i.val < b.val) by omega]
  simp only [slotPrefix,he,Finset.sum_add_distrib]
  simp

theorem prefix_bound (q : Fin m → Nat) (b : Fin m) : slotPrefix q b.val+q b ≤ ∑ i : Fin m, q i := by
  rw [← prefix_next,← prefix_end q]
  exact prefix_mono q (by have := b.isLt; omega)

theorem header_fits (q : Fin m → Nat) : 4 ≤ words q := by unfold words; omega

theorem directory_bound (base : Nat) (q : Fin m → Nat) (b : Fin m) (hf : field < 4) :
    base ≤ directory base b+field ∧ directory base b+field < base+words q := by
  have := b.isLt
  unfold directory words
  constructor <;> omega

theorem table_bound (base : Nat) (q : Fin m → Nat) (b : Fin m) (hi : i < q b) (hf : field < 2) :
    base ≤ table base q b+2*i+field ∧ table base q b+2*i+field < base+words q := by
  have hb := prefix_bound q b
  unfold table tablesBase words
  constructor <;> omega

theorem directory_separated (base : Nat) (b c : Fin m) (hbc : b.val < c.val) :
    (Region.mk (directory base b) 4).Separated ⟨directory base c,4⟩ := by
  left
  simp only [directory]
  omega

theorem tables_separated (base : Nat) (q : Fin m → Nat) (b c : Fin m) (hbc : b.val < c.val) :
    (Region.mk (table base q b) (2*q b)).Separated ⟨table base q c,2*q c⟩ := by
  have hh := prefix_mono q (show b.val+1 ≤ c.val by omega)
  rw [prefix_next] at hh
  left
  simp only [table,tablesBase]
  omega

theorem directory_table_separated (base : Nat) (q : Fin m → Nat) (b c : Fin m) :
    (Region.mk (directory base b) 4).Separated ⟨table base q c,2*q c⟩ := by
  left
  have := b.isLt
  simp only [directory,table,tablesBase]
  omega

theorem contains_header (hf : (region base q).Fits w) (hi : i < 4) :
    (region base q).Contains (word w (base+i)) :=
  Region.contains_index hf (hi.trans_le (header_fits q))

theorem contains_directory (hf : (region base q).Fits w) (b : Fin m) (hi : i < 4) :
    (region base q).Contains (word w (directory base b+i)) := by
  have hb := directory_bound base q b hi
  have hf' : base+words q < modulus w := hf
  change base ≤ _ ∧ _ < base+words q
  rw [word_toNat_of_lt (hb.2.trans hf')]
  exact hb

theorem contains_table (hf : (region base q).Fits w) (b : Fin m) (hi : i < q b) (hj : j < 2) :
    (region base q).Contains (word w (table base q b+2*i+j)) := by
  have hb := table_bound base q b hi hj
  have hf' : base+words q < modulus w := hf
  change base ≤ _ ∧ _ < base+words q
  rw [word_toNat_of_lt (hb.2.trans hf')]
  exact hb

end PerfectHash.Packed
