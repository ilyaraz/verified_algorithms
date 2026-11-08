import WordRam.Blocks
import WordRam.Regions
import Mathlib.Data.Finset.Dedup
import Mathlib.Data.Finset.Card

namespace WordRam

variable {w R : Nat} {r : Region} {a : Addr w}

/-- The executable duplicate remover produces a genuine finite-set listing. -/
theorem eraseDups_nodup {α : Type*} [BEq α] [LawfulBEq α] (xs : List α) : xs.eraseDups.Nodup := by
  cases xs with
  | nil => simp
  | cons a xs =>
    rw [List.eraseDups_cons,List.nodup_cons]
    refine ⟨?_,eraseDups_nodup (xs.filter (fun b => !b == a))⟩
    intro hh
    have hm := eraseDups_subset _ hh
    simp at hm
termination_by xs.length
decreasing_by
  simp_wf
  exact Nat.lt_succ_of_le (List.length_filter_le _ _)

theorem eraseDups_length_le {α : Type*} [BEq α] (xs : List α) : xs.eraseDups.length ≤ xs.length := by
  cases xs with
  | nil => simp
  | cons a xs =>
    rw [List.eraseDups_cons,List.length_cons,List.length_cons]
    have h := eraseDups_length_le (xs.filter (fun b => !b == a))
    have hf := List.length_filter_le (fun b => !b == a) xs
    omega
termination_by xs.length
decreasing_by
  simp_wf
  exact Nat.lt_succ_of_le (List.length_filter_le _ _)

/-- A mathematical set of interval addresses, used only to bound footprint size. -/
def Region.cells (w : Nat) (r : Region) : Finset (Addr w) :=
  (Finset.range r.size).image (fun i => word w (r.base+i))

theorem Region.mem_cells (h : r.Contains a) : a ∈ r.cells w := by
  unfold Region.cells
  apply Finset.mem_image.mpr
  refine ⟨a.toNat-r.base,Finset.mem_range.mpr (by unfold Region.Contains at h; omega),?_⟩
  rw [Nat.add_sub_of_le h.1]
  simpa [word] using BitVec.ofNat_toNat w a

theorem Region.cells_card_le (r : Region) (w : Nat) : (r.cells w).card ≤ r.size := by
  exact (Finset.card_image_le).trans_eq (Finset.card_range _)

/-- Footprint size is bounded by the union of permitted ordinary regions.
No trace length or number of repeated accesses is charged as ordinary space. -/
theorem footprint_three (result : RunResult w R) (r s t : Region)
    (h : ∀ a ∈ result.dataFootprint, r.Contains a ∨ s.Contains a ∨ t.Contains a) :
    result.dataFootprint.length ≤ r.size+s.size+t.size := by
  have hn : result.dataFootprint.Nodup := eraseDups_nodup _
  have hs : result.dataFootprint.toFinset ⊆ (r.cells w ∪ s.cells w) ∪ t.cells w := by
    intro a ha
    rcases h a (List.mem_toFinset.mp ha) with hr | hs | ht
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Region.mem_cells hr))
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ (Region.mem_cells hs))
    · exact Finset.mem_union_right _ (Region.mem_cells ht)
  have hc := Finset.card_le_card hs
  rw [List.toFinset_card_of_nodup hn] at hc
  have h₁ := Finset.card_union_le (r.cells w ∪ s.cells w) (t.cells w)
  have h₂ := Finset.card_union_le (r.cells w) (s.cells w)
  have hr := r.cells_card_le w
  have hs := s.cells_card_le w
  have ht := t.cells_card_le w
  omega

theorem RunResult.exposed_le_reads (result : RunResult w R) :
    result.randomBitsExposed ≤ w*result.randomReads :=
  Nat.mul_le_mul_left w (eraseDups_length_le _)

end WordRam
