import Hashing.Family
import Probability.Finite
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.FinRange

/-! Seed-independent distinct-key evolution and the charged chain comparisons.
These are specification objects; the constructor must execute the corresponding
RAM loads, comparisons, stores, and initialization. -/
namespace Dedup

variable {Key Bucket : Type*} [DecidableEq Key] [DecidableEq Bucket]

/-- Number of equality comparisons made by a chain search. -/
def scanComparisons (key : Key) : List Key → Nat
  | [] => 0
  | x :: xs => if key = x then 1 else 1 + scanComparisons key xs

/-- A chain's newest inserted key is first. Only matching hash buckets are searched. -/
def bucket (hash : Key → Bucket) (seen : List Key) (key : Key) : List Key :=
  seen.filter (fun x => hash x == hash key)

/-- Insert at the head only on first occurrence. The state depends on the input,
not on its hash seed, which is essential to the prefix comparison expectation. -/
def insert (key : Key) (seen : List Key) : List Key := if key ∈ seen then seen else key :: seen

def collect : List Key → List Key → List Key
  | [], seen => seen
  | key :: rest, seen => collect rest (insert key seen)

def comparisons (hash : Key → Bucket) : List Key → List Key → Nat
  | [], _ => 0
  | key :: rest, seen => scanComparisons key (bucket hash seen key) +
      comparisons hash rest (insert key seen)

/-- One possible self-comparison is charged separately from all other colliders. -/
def collisions (hash : Key → Bucket) (key : Key) : List Key → Nat
  | [] => 0
  | x :: xs => (if key ≠ x ∧ hash x = hash key then 1 else 0) + collisions hash key xs

variable {seen : List Key} {key x : Key}

@[simp] theorem mem_bucket (hash : Key → Bucket) (seen : List Key) (key : Key) :
    key ∈ bucket hash seen key ↔ key ∈ seen := by simp [bucket]

@[simp] theorem mem_insert : x ∈ insert key seen ↔ x = key ∨ x ∈ seen := by
  unfold insert
  split <;> simp_all

theorem insert_nodup (h : seen.Nodup) : (insert key seen).Nodup := by
  unfold insert
  split <;> simp_all

theorem insert_length : (insert key seen).length ≤ seen.length+1 := by
  unfold insert
  split <;> simp

theorem collect_nodup (xs seen : List Key) (h : seen.Nodup) : (collect xs seen).Nodup := by
  induction xs generalizing seen with
  | nil => exact h
  | cons x xs ih => exact ih _ (insert_nodup h)

@[simp] theorem mem_collect (xs seen : List Key) : x ∈ collect xs seen ↔ x ∈ xs ∨ x ∈ seen := by
  induction xs generalizing seen with
  | nil => simp [collect]
  | cons k xs ih => simp [collect, ih, or_assoc, or_left_comm]

theorem collect_length (xs seen : List Key) : (collect xs seen).length ≤ seen.length+xs.length := by
  induction xs generalizing seen with
  | nil => simp [collect]
  | cons x xs ih =>
    have h := ih (insert x seen)
    have hi := insert_length (key := x) (seen := seen)
    simp only [collect, List.length_cons]
    omega

theorem scan_le_length (key : Key) (xs : List Key) : scanComparisons key xs ≤ xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [scanComparisons, List.length_cons]; split <;> omega

theorem scan_le_collisions (hash : Key → Bucket) (seen : List Key) (key : Key) :
    scanComparisons key (bucket hash seen key) ≤ 1 + collisions hash key seen := by
  induction seen with
  | nil => simp [bucket, scanComparisons, collisions]
  | cons x xs ih =>
    by_cases hh : hash x = hash key
    · by_cases he : key = x
      · simp [bucket, scanComparisons, collisions, hh, he]
      · simpa [bucket, scanComparisons, collisions, hh, he, Nat.add_assoc] using Nat.add_le_add_left ih 1
    · simpa [bucket, collisions, hh] using ih

theorem comparisons_worst (hash : Key → Bucket) (xs seen : List Key) :
    comparisons hash xs seen ≤ xs.length * (seen.length+xs.length) := by
  induction xs generalizing seen with
  | nil => simp [comparisons]
  | cons x xs ih =>
    have hs := (scan_le_length x (bucket hash seen x)).trans (List.length_filter_le _ _)
    have hi := ih (insert x seen)
    have hl := insert_length (key := x) (seen := seen)
    simp only [comparisons, List.length_cons]
    have hb := Nat.mul_le_mul_left xs.length hl
    nlinarith

/-- Relabeling bucket indices injectively leaves every compared chain unchanged. -/
theorem comparisons_injective {Other : Type*} [DecidableEq Other]
    (f : Bucket → Other) (hf : Function.Injective f) (hash : Key → Bucket)
    (xs seen : List Key) : comparisons (fun x => f (hash x)) xs seen = comparisons hash xs seen := by
  induction xs generalizing seen with
  | nil => rfl
  | cons x xs ih =>
    simp only [comparisons,ih]
    congr 2
    unfold bucket
    congr 1
    funext y
    by_cases he : hash y = hash x
    · simp [he]
    · have hn : f (hash y) ≠ f (hash x) := fun h => he (hf h)
      simp [he,hn]

end Dedup
