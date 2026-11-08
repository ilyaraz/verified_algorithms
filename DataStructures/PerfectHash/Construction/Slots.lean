import DataStructures.PerfectHash.Construction.Energy

namespace PerfectHash.Construction
open WordRam

/-- Ghost slot contents, in the order keys were inserted. The RAM stores only
flags and complete keys, never this list. -/
def slotContents (hash : Key → Nat) (seen : List Key) (i : Nat) : Option Key :=
  seen.find? (fun x => hash x == i)

@[simp] theorem slotContents_nil (hash : Key → Nat) (i : Nat) : slotContents hash [] i = none := rfl

@[simp] theorem slotContents_cons (hash : Key → Nat) (x : Key) (xs : List Key) (i : Nat) :
    slotContents hash (x::xs) i = if hash x = i then some x else slotContents hash xs i := by
  by_cases h : hash x = i <;> simp [slotContents,h]

theorem slotContents_none (hash : Key → Nat) (seen : List Key) (i : Nat) :
    slotContents hash seen i = none ↔ i ∉ seen.map hash := by
  simp [slotContents,List.find?_eq_none,List.mem_map]

theorem slotContents_member (hash : Key → Nat) (seen : List Key)
    (hn : (seen.map hash).Nodup) (hx : x ∈ seen) : slotContents hash seen (hash x) = some x := by
  induction seen with
  | nil => simp at hx
  | cons y ys ih =>
    obtain ⟨hy,ht⟩ := List.nodup_cons.mp hn
    rcases List.mem_cons.mp hx with rfl | hx
    · simp
    · have he : hash y ≠ hash x := by
        intro he
        exact hy (List.mem_map.mpr ⟨x,hx,he.symm⟩)
      simpa [he] using ih ht hx

theorem slotContents_some (hash : Key → Nat) (seen : List Key) (hn : (seen.map hash).Nodup) :
    slotContents hash seen i = some x ↔ x ∈ seen ∧ hash x = i := by
  constructor
  · intro hh
    exact ⟨List.mem_of_find?_eq_some hh,by simpa using List.find?_some hh⟩
  · rintro ⟨hx,rfl⟩
    exact slotContents_member hash seen hn hx

/-- Each slot consists of an occupancy word and a key word. Unoccupied key cells
may contain any stale value; only initialized flags are trusted. -/
structure SlotsAt (hash : Word w → Nat) (q base : Nat) (seen : List (Word w)) (mem : DataMemory w) : Prop where
  occupied : ∀ i, i < q → mem (word w (base+2*i)) = word w (slotContents hash seen i).isSome.toNat
  stored : ∀ i, i < q → ∀ x, slotContents hash seen i = some x → mem (word w (base+2*i+1)) = x

variable {w q base : Nat} {hash : Word w → Nat} {seen : List (Word w)} {mem : DataMemory w} {x : Word w}

theorem SlotsAt.empty (ha : ArrayAt mem base (List.replicate (2*q) (word w 0))) :
    SlotsAt hash q base [] mem := by
  refine ⟨?_,by simp⟩
  intro i hi
  simpa using ha ⟨2*i,by simp only [List.length_replicate]; omega⟩

def slotMemory (base i : Nat) (key : Word w) (mem : DataMemory w) : DataMemory w :=
  update (update mem (word w (base+2*i)) (word w 1)) (word w (base+2*i+1)) key

theorem slotMemory_apply (hf : (Region.mk base (2*q)).Fits w) (hi : i < q) (a : Addr w) :
    slotMemory base i x mem a = if a.toNat = base+2*i+1 then x
      else if a.toNat = base+2*i then word w 1 else mem a := by
  unfold slotMemory
  simp only [Region.Fits] at hf
  rw [update_word _ _ _ (by omega),update_word _ _ _ (by omega)]

theorem slotMemory_frame (hf : (Region.mk base (2*q)).Fits w) (hi : i < q) (a : Addr w)
    (ha : ¬ (Region.mk base (2*q)).Contains a) : slotMemory base i x mem a = mem a := by
  rw [slotMemory_apply hf hi]
  simp only [Region.Contains] at ha
  split <;> (try split) <;> first | rfl | omega

/-- The two insertion stores establish the next slot view and preserve all other
slots, including stale key cells in unoccupied slots. -/
theorem SlotsAt.insert (h : SlotsAt hash q base seen mem) (hf : (Region.mk base (2*q)).Fits w)
    (hx : hash x < q) : SlotsAt hash q base (x::seen) (slotMemory base (hash x) x mem) := by
  have hb := hf
  simp only [Region.Fits] at hb
  refine ⟨?_,?_⟩
  · intro i hi
    rw [slotMemory_apply hf hx,word_toNat_of_lt (by omega : base+2*i < modulus w),slotContents_cons]
    by_cases he : hash x = i
    · simp [he]
    · have ha : base+2*i ≠ base+2*hash x+1 := by omega
      have hb : base+2*i ≠ base+2*hash x := by omega
      simp only [ha,hb,he,↓reduceIte]
      exact h.occupied i hi
  · intro i hi y hy
    rw [slotMemory_apply hf hx,word_toNat_of_lt (by omega : base+2*i+1 < modulus w)]
    rw [slotContents_cons] at hy
    by_cases he : hash x = i
    · simp only [he,↓reduceIte,Option.some.injEq] at hy
      subst y
      simp [he]
    · simp only [he,↓reduceIte] at hy
      have ha : base+2*i+1 ≠ base+2*hash x+1 := by omega
      have hb : base+2*i+1 ≠ base+2*hash x := by omega
      simp only [ha,hb,↓reduceIte]
      exact h.stored i hi y hy

/-- A trial's collision flag is exactly the question whether the next hash has
already been inserted. This also distinguishes an occupied zero-valued key. -/
theorem SlotsAt.empty_iff (h : SlotsAt hash q base seen mem) (hf : 1 < modulus w) (hi : i < q) :
    mem (word w (base+2*i)) = word w 0 ↔ i ∉ seen.map hash := by
  rw [h.occupied i hi,← slotContents_none hash seen i]
  cases he : slotContents hash seen i with
  | none => simp
  | some x =>
    simp only [Option.isSome_some,Bool.toNat_true]
    rw [word_eq_iff_of_lt hf (by omega)]
    simp

/-- Stop at the first repeated child position. Earlier occupied slots remain a
valid partial table, and a retry clears precisely this table before reuse. -/
def childAccepted (hash : Key → Nat) (seen : List Key) : List Key → Bool
  | [] => true
  | x::xs => if (seen.map hash).contains (hash x) then false else childAccepted hash (x::seen) xs

theorem childAccepted_iff (hash : Key → Nat) (seen rest : List Key) (hn : (seen.map hash).Nodup) :
    childAccepted hash seen rest = true ↔ ((rest.reverse++seen).map hash).Nodup := by
  induction rest generalizing seen with
  | nil => simp [childAccepted,hn]
  | cons x xs ih =>
    have he : ((x::xs).reverse++seen).map hash =
        (xs.reverse.map hash)++(hash x::seen.map hash) := by
      simp [List.reverse_cons,List.map_append,List.append_assoc]
    rw [childAccepted,he]
    simp only [List.contains_iff]
    split
    · rename_i hh
      simp only [Bool.false_eq_true,false_iff]
      intro hp
      exact (List.nodup_cons.mp (List.nodup_append.mp hp).2.1).1 hh
    · rename_i hh
      have hp : ((x::seen).map hash).Nodup := List.nodup_cons.mpr ⟨hh,hn⟩
      simpa only [List.map_append,List.map_cons] using ih (x::seen) hp

end PerfectHash.Construction
