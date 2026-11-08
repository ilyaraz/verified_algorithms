import Algorithms.Dedup.Specification
import Algorithms.Dedup.Model

namespace Dedup
open WordRam

/-- A key inserted at step d gets index d+1. Inserting a new head leaves every
older node's index unchanged. This is ghost bookkeeping, not a runtime list. -/
def numbered : List Key → List (Key × Nat)
  | [] => []
  | x :: xs => (x, xs.length+1) :: numbered xs

@[simp] theorem numbered_keys (xs : List Key) : (numbered xs).map Prod.fst = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [numbered, ih]

theorem numbered_index (h : (x,i) ∈ numbered xs) : 0 < i ∧ i ≤ xs.length := by
  induction xs with
  | nil => simp [numbered] at h
  | cons y ys ih =>
    simp only [numbered, List.mem_cons, Prod.mk.injEq] at h
    rcases h with ⟨_, rfl⟩ | h
    · simp
    · have := ih h
      simp only [List.length_cons]
      omega

def chain (hash : Key → Nat) (xs : List Key) (b : Nat) : List (Key × Nat) :=
  (numbered xs).filter (fun p => hash p.1 == b)

def firstIndex : List (Key × Nat) → Nat
  | [] => 0
  | p :: _ => p.2

def nodeAddress (base index : Nat) : Nat := base+2*(index-1)

def ChainAt (mem : DataMemory w) (base : Nat) : List (Word w × Nat) → Prop
  | [] => True
  | (key,index) :: rest =>
      mem (word w (nodeAddress base index)) = key ∧
      mem (word w (nodeAddress base index+1)) = word w (firstIndex rest) ∧
      ChainAt mem base rest

/-- Construction-independent chaining invariant for the deduplication pass. -/
structure Representation (w N : Nat) (l : Layout) (m : Nat) (hash : Word w → Nat)
    (seen : List (Word w)) (mem : DataMemory w) : Prop where
  distinct : seen.Nodup
  length : seen.length ≤ N
  head : ∀ b, b < m → mem (word w (l.scratch+b)) = word w (firstIndex (chain hash seen b))
  chains : ∀ b, b < m → ChainAt mem (l.nodes N).base (chain hash seen b)
  compact : ArrayAt mem (l.compact N).base seen.reverse

variable {w N : Nat} {l : Layout}

theorem Admissible.two_lt (h : Admissible w N l) : 2 < modulus w := by
  have hh := h.workspace
  unfold Layout.workspace Region.Fits workspaceCapacity at hh
  simp only at *
  omega

theorem Admissible.positive (h : Admissible w N l) : 0 < w := by
  have hh := h.two_lt
  cases w with
  | zero => simp [modulus] at hh
  | succ w => omega

theorem Admissible.heads_fit (h : Admissible w N l) : (l.heads N).Fits w := by
  have hh := h.workspace
  unfold Layout.workspace Layout.heads Region.Fits workspaceCapacity at *
  simp only at *
  omega

theorem Admissible.nodes_fit (h : Admissible w N l) : (l.nodes N).Fits w := by
  have hh := h.workspace
  unfold Layout.workspace Layout.nodes Region.Fits workspaceCapacity at *
  simp only at *
  omega

theorem Admissible.compact_fit (h : Admissible w N l) : (l.compact N).Fits w := by
  have hh := h.workspace
  unfold Layout.workspace Layout.compact Region.Fits workspaceCapacity at *
  simp only at *
  omega

theorem Layout.heads_nodes (l : Layout) (N : Nat) : (l.heads N).Separated (l.nodes N) := by
  left
  simp [Layout.heads, Layout.nodes]

theorem Layout.heads_compact (l : Layout) (N : Nat) : (l.heads N).Separated (l.compact N) := by
  left
  simp [Layout.heads, Layout.compact]

theorem Layout.nodes_compact (l : Layout) (N : Nat) : (l.nodes N).Separated (l.compact N) := by
  left
  simp [Layout.nodes, Layout.compact]

theorem node_contains (hf : (Region.mk base (2*N)).Fits w) (hi : 0 < i) (hb : i ≤ N) :
    (Region.mk base (2*N)).Contains (word w (nodeAddress base i)) ∧
    (Region.mk base (2*N)).Contains (word w (nodeAddress base i+1)) := by
  constructor
  · exact Region.contains_index hf (by omega : 2*(i-1) < 2*N)
  · have he : nodeAddress base i+1 = base+(2*(i-1)+1) := by unfold nodeAddress; omega
    rw [he]
    exact Region.contains_index hf (by omega : 2*(i-1)+1 < 2*N)

theorem chain_index {Key : Type*} {hash : Key → Nat} {seen : List Key} {key : Key}
    {i b : Nat} (h : (key,i) ∈ chain hash seen b) : 0 < i ∧ i ≤ seen.length :=
  numbered_index (List.mem_of_mem_filter h)

theorem firstIndex_le {Key : Type*} {xs : List (Key × Nat)} {n : Nat}
    (h : ∀ p ∈ xs, p.2 ≤ n) : firstIndex xs ≤ n := by
  cases xs with
  | nil => exact Nat.zero_le _
  | cons x xs => exact h x (by simp)

theorem ChainAt.frame {mem mem' : DataMemory w} {base n : Nat}
    {xs : List (Word w × Nat)} (h : ChainAt mem base xs)
    (hb : ∀ p ∈ xs, 0 < p.2 ∧ p.2 ≤ n)
    (hf : (Region.mk base (2*n)).Fits w)
    (ha : AgreeOn ⟨base, 2*n⟩ mem mem') : ChainAt mem' base xs := by
  induction xs with
  | nil => trivial
  | cons p xs ih =>
    obtain ⟨key,i⟩ := p
    obtain ⟨hk, hn, ht⟩ := h
    have hi := hb (key,i) (by simp)
    have hc := node_contains hf hi.1 hi.2
    refine ⟨?_, ?_, ih ht (fun p hp => hb p (by simp [hp]))⟩
    · rw [← ha _ hc.1]; exact hk
    · rw [← ha _ hc.2]; exact hn

@[simp] theorem chain_nil (hash : Key → Nat) (b : Nat) : chain hash [] b = [] := rfl

@[simp] theorem chain_cons (hash : Key → Nat) (x : Key) (xs : List Key) (b : Nat) :
    chain hash (x::xs) b =
      if hash x = b then (x,xs.length+1)::chain hash xs b else chain hash xs b := by
  by_cases h : hash x = b <;> simp [chain, numbered, h]

theorem chain_keys (hash : Key → Nat) (xs : List Key) (b : Nat) :
    (chain hash xs b).map Prod.fst = xs.filter (fun x => hash x == b) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => by_cases h : hash x = b <;> simp [chain_cons, h, ih]

theorem Representation.empty {mem : DataMemory w} {m : Nat} {hash : Word w → Nat}
    (h : ArrayAt mem l.scratch (List.replicate m (word w 0))) :
    Representation w N l m hash [] mem := by
  refine ⟨by simp, by simp, ?_, ?_, by simp⟩
  · intro b hb
    simpa [firstIndex] using h ⟨b, by simpa using hb⟩
  · intros; trivial

/-- Inserting one new node needs only a new head, two initialized node cells,
framing of the previous nodes, and one appended compact key. -/
theorem Representation.insert {mem mem' : DataMemory w} {m : Nat}
    {hash : Word w → Nat} {seen : List (Word w)} {key : Word w}
    (rep : Representation w N l m hash seen mem)
    (hf : (Region.mk (l.nodes N).base (2*seen.length)).Fits w)
    (fresh : key ∉ seen) (space : seen.length < N)
    (heads : ∀ b, b < m → mem' (word w (l.scratch+b)) =
      if hash key = b then word w (seen.length+1) else mem (word w (l.scratch+b)))
    (newKey : mem' (word w (nodeAddress (l.nodes N).base (seen.length+1))) = key)
    (newNext : mem' (word w (nodeAddress (l.nodes N).base (seen.length+1)+1)) =
      word w (firstIndex (chain hash seen (hash key))))
    (oldNodes : AgreeOn ⟨(l.nodes N).base, 2*seen.length⟩ mem mem')
    (compact : ArrayAt mem' (l.compact N).base (seen.reverse++[key])) :
    Representation w N l m hash (key::seen) mem' := by
  refine ⟨List.nodup_cons.mpr ⟨fresh, rep.distinct⟩, by simp; omega, ?_, ?_, ?_⟩
  · intro b hb
    rw [heads b hb, chain_cons]
    split
    · rfl
    · exact rep.head b hb
  · intro b hb
    have old := (rep.chains b hb).frame (fun _ hp => chain_index hp) hf oldNodes
    rw [chain_cons]
    split
    · rename_i he
      exact ⟨newKey, he ▸ newNext, old⟩
    · exact old
  · simpa using compact

end Dedup
