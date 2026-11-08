import DataStructures.PerfectHash.Layout
import DataStructures.StaticSet.Specification

namespace PerfectHash.Table
open WordRam

/-- Ghost description of the finite table's stored parameters and slot contents.
The query program receives only the ordinary-memory descriptor and a key. -/
structure Data (w : Nat) where
  buckets : Nat
  rootSeed : Word w
  rootShift : Word w
  count : Fin buckets → Nat
  seed : Fin buckets → Word w
  shift : Fin buckets → Word w
  slots : Fin buckets → Nat
  contents : Fin buckets → Nat → Option (Word w)

def Data.rootIndex (d : Data w) (x : Word w) : Nat :=
  (unsignedShiftRight (d.rootSeed*x) d.rootShift).toNat

def Data.slotIndex (d : Data w) (b : Fin d.buckets) (x : Word w) : Nat :=
  if d.count b = 1 then 0 else (unsignedShiftRight (d.seed b*x) (d.shift b)).toNat

def Data.bucket (d : Data w) (S : Finset (Word w)) (b : Fin d.buckets) : Finset (Word w) :=
  S.filter (fun x => d.rootIndex x = b.val)

/-- All keys in a bucket have unique stored slots; occupied slots contain exactly
those keys. Range is required for every possible query, not just members. -/
structure Valid (S : Finset (Word w)) (d : Data w) : Prop where
  rootRange : ∀ x, d.rootIndex x < d.buckets
  counts : ∀ b, d.count b = (d.bucket S b).card
  sizes : ∀ b, d.slots b = Sizes.childSlots (d.count b)
  slotRange : ∀ b, 0 < d.count b → ∀ x, d.slotIndex b x < d.slots b
  contents : ∀ b i, i < d.slots b → ∀ x,
    d.contents b i = some x ↔ x ∈ S ∧ d.rootIndex x = b.val ∧ d.slotIndex b x = i

/-- Header, directory and occupancy/key cells occupy the packed retained extent.
Unused key cells under zero occupancy flags are allowed to remain dirty. -/
structure View (S : Finset (Word w)) (r : Region) (mem : DataMemory w) (d : Data w) : Prop where
  valid : Valid S d
  geometry : r.size = Packed.words d.slots
  fits : r.Fits w
  headerSeed : mem (word w r.base) = d.rootSeed
  headerShift : mem (word w (r.base+1)) = d.rootShift
  headerBuckets : mem (word w (r.base+2)) = word w d.buckets
  headerCount : mem (word w (r.base+3)) = word w S.card
  directoryCount : ∀ b, mem (word w (Packed.directory r.base b)) = word w (d.count b)
  directorySeed : ∀ b, mem (word w (Packed.directory r.base b+1)) = d.seed b
  directoryShift : ∀ b, mem (word w (Packed.directory r.base b+2)) = d.shift b
  directoryTable : ∀ b, mem (word w (Packed.directory r.base b+3)) = word w (Packed.table r.base d.slots b)
  occupancy : ∀ b i, i < d.slots b →
    mem (word w (Packed.table r.base d.slots b+2*i)) = word w (if (d.contents b i).isSome then 1 else 0)
  keys : ∀ b i, i < d.slots b → ∀ x, d.contents b i = some x →
    mem (word w (Packed.table r.base d.slots b+2*i+1)) = x

variable {w : Nat} {S : Finset (Word w)} {r : Region} {mem mem' : DataMemory w} {d : Data w}

theorem childSlots_keys (b : Nat) : b ≤ Sizes.childSlots b := by
  by_cases hb : b ≤ 1
  · simp [Sizes.childSlots,hb]
  · have hh := Sizes.childSlots_covers (show 2 ≤ b by omega)
    nlinarith

theorem View.packed_fit (v : View S r mem d) : (Packed.region r.base d.slots).Fits w := by
  have hf := v.fits
  simpa only [Region.Fits,Packed.region,v.geometry] using hf

theorem View.nonempty (v : View S r mem d) : 0 < r.size := by
  rw [v.geometry]
  have hh := Packed.header_fits d.slots
  omega

theorem View.four_lt (v : View S r mem d) : 4 < modulus w := by
  have hf := v.fits
  have hh := Packed.header_fits d.slots
  simp only [Region.Fits,v.geometry] at hf
  omega

theorem View.count_fit (v : View S r mem d) (b : Fin d.buckets) : d.count b < modulus w := by
  have hc := childSlots_keys (d.count b)
  rw [← v.valid.sizes b] at hc
  have hs : d.slots b ≤ ∑ i : Fin d.buckets, d.slots i :=
    Finset.single_le_sum (f := d.slots) (fun _ _ => Nat.zero_le _) (Finset.mem_univ b)
  have hf := v.fits
  simp only [Region.Fits,v.geometry,Packed.words] at hf
  omega

theorem View.contains_header (v : View S r mem d) (hi : i < 4) : r.Contains (word w (r.base+i)) := by
  simpa only [Region.Contains,Packed.region,v.geometry] using Packed.contains_header v.packed_fit hi

theorem View.contains_directory (v : View S r mem d) (b : Fin d.buckets) (hi : i < 4) :
    r.Contains (word w (Packed.directory r.base b+i)) := by
  simpa only [Region.Contains,Packed.region,v.geometry] using Packed.contains_directory v.packed_fit b hi

theorem View.contains_table (v : View S r mem d) (b : Fin d.buckets) (hi : i < d.slots b) (hj : j < 2) :
    r.Contains (word w (Packed.table r.base d.slots b+2*i+j)) := by
  simpa only [Region.Contains,Packed.region,v.geometry] using Packed.contains_table v.packed_fit b hi hj

/-- Zero count means no set member hashes to this bucket. -/
theorem Valid.empty_bucket (v : Valid S d) (b : Fin d.buckets) (hc : d.count b = 0)
    (hx : d.rootIndex x = b.val) : x ∉ S := by
  intro hm
  have hc' : (d.bucket S b).card = 0 := (v.counts b).symm.trans hc
  have he := Finset.card_eq_zero.mp hc'
  have hh : x ∈ d.bucket S b := by simp [Data.bucket,hm,hx]
  simpa [he] using hh

/-- The selected slot contains a query key exactly when it belongs to the set. -/
theorem Valid.selected_slot (v : Valid S d) (b : Fin d.buckets) (hc : 0 < d.count b)
    (hx : d.rootIndex x = b.val) :
    d.contents b (d.slotIndex b x) = some x ↔ x ∈ S := by
  rw [v.contents b _ (v.slotRange b hc x) x]
  simp [hx]

/-- All representation facts survive arbitrary changes outside the retained region. -/
theorem View.frame (v : View S r mem d) (ha : AgreeOn r mem mem') : View S r mem' d := by
  refine ⟨v.valid,v.geometry,v.fits,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [← ha _ (by simpa using v.contains_header (i := 0) (by decide))]
    exact v.headerSeed
  · rw [← ha _ (v.contains_header (by decide : 1 < 4))]
    exact v.headerShift
  · rw [← ha _ (v.contains_header (by decide : 2 < 4))]
    exact v.headerBuckets
  · rw [← ha _ (v.contains_header (by decide : 3 < 4))]
    exact v.headerCount
  · intro b
    rw [← ha _ (by simpa using v.contains_directory b (i := 0) (by decide))]
    exact v.directoryCount b
  · intro b
    rw [← ha _ (v.contains_directory b (by decide : 1 < 4))]
    exact v.directorySeed b
  · intro b
    rw [← ha _ (v.contains_directory b (by decide : 2 < 4))]
    exact v.directoryShift b
  · intro b
    rw [← ha _ (v.contains_directory b (by decide : 3 < 4))]
    exact v.directoryTable b
  · intro b i hi
    rw [← ha _ (by simpa using v.contains_table b hi (j := 0) (by decide))]
    exact v.occupancy b i hi
  · intro b i hi x hx
    rw [← ha _ (v.contains_table b hi (by decide : 1 < 2))]
    exact v.keys b i hi x hx

/-- The packed representation meets the frozen retained-space budget whenever
its accepted root satisfies the proved energy and directory bounds. -/
theorem View.retained_linear (v : View S r mem d)
    (hm : d.buckets ≤ 2*(S.card+1)) (he : (∑ b : Fin d.buckets, (d.count b)^2) ≤ 6*S.card) :
    r.size ≤ 64*(S.card+1) := by
  have hs : (∑ b : Fin d.buckets, d.slots b) ≤ 4*(∑ b : Fin d.buckets, (d.count b)^2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro b _
    rw [v.valid.sizes b]
    exact Sizes.childSlots_le _
  rw [v.geometry]
  unfold Packed.words
  omega

/-- The public representation exposes no input array, scratch memory, or history. -/
def representation : StaticSet.Representation where
  Holds S r mem := ∃ d, View S r mem d
  fits := fun ⟨_,h⟩ => h.fits
  nonempty := fun ⟨_,h⟩ => h.nonempty
  locality := fun ⟨d,h⟩ ha => ⟨d,h.frame ha⟩

end PerfectHash.Table
