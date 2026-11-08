import DataStructures.PerfectHash.Sizes
import Probability.FiniteSequence

namespace PerfectHash.Build
open Buckets Sizes FiniteProbability

/-- A bucket with at most one key needs no sampled child seed. -/
inductive ChildChoice (Seed : Type) where
  | direct
  | hashed (seed : Seed)
  deriving DecidableEq, Repr

structure Dictionary (Seed : Type) (m : Nat) where
  root : Seed
  children : Fin m → ChildChoice Seed

/-- Abstract arithmetic and trial predicates. No RAM cost is assigned to Lean
list traversal: later trial refinement must realize each charged trial budget. -/
structure Model (Key Seed : Type) (m : Nat) (xs : List Key) where
  root : Hashing.Family Key Seed m
  child : (a : Seed) → (b : Fin m) → Hashing.Family Key Seed
    (Hashing.PowerOfTwo.computeSize (2*(count (root.eval a) xs b)*(count (root.eval a) xs b)))
  enumeration : List Seed
  attempts : Nat

variable {Key Seed : Type} {m : Nat} {xs : List Key}

def Model.rootSearch (model : Model Key Seed m xs) (samples : Fin model.attempts → Seed) : Option Seed :=
  FiniteSearch.search (rootAccept model.root xs) model.enumeration model.attempts samples

def Model.childKeys (model : Model Key Seed m xs) (root : Seed) (b : Fin m) : List Key :=
  keys (model.root.eval root) xs b

def Model.childSearch (model : Model Key Seed m xs) (root : Seed) (b : Fin m)
    (samples : Fin model.attempts → Seed) : Option (ChildChoice Seed) :=
  if (model.childKeys root b).length ≤ 1 then some .direct
  else (FiniteSearch.search (childAccept (model.child root b) (model.childKeys root b))
    model.enumeration model.attempts samples).map .hashed

/-- Root and each child have separate finite sample blocks. The chosen root may
change the child predicates but never changes those blocks' coordinates. -/
def Model.construct (model : Model Key Seed m xs)
    (rootSamples : Fin model.attempts → Seed) (childrenSamples : Fin m → Fin model.attempts → Seed) :
    Option (Dictionary Seed m) := do
  let root ← model.rootSearch rootSamples
  let children ← sequenceFin (fun b => model.childSearch root b (childrenSamples b))
  pure ⟨root,children⟩

def Model.ChildValid (model : Model Key Seed m xs) (root : Seed) (b : Fin m) : ChildChoice Seed → Prop
  | .direct => (model.childKeys root b).length ≤ 1
  | .hashed seed => childAccept (model.child root b) (model.childKeys root b) seed = true

def Model.Valid (model : Model Key Seed m xs) (dict : Dictionary Seed m) : Prop :=
  rootAccept model.root xs dict.root = true ∧ ∀ b, model.ChildValid dict.root b (dict.children b)

/-- The assumptions needed for abstract finite search. Child collision bounds
are required only following an accepted root, where their capacities fit. -/
structure Hypotheses [Fintype Seed] (model : Model Key Seed m xs) : Prop where
  distinct : xs.Nodup
  buckets_pos : 0 < m
  buckets_cover : xs.length ≤ m
  buckets_bound : m ≤ 2*(xs.length+1)
  root_collision : Hashing.CollisionBound model.root 2
  child_collision : ∀ a, rootAccept model.root xs a = true → ∀ b,
    Hashing.CollisionBound (model.child a b) 2
  enumeration_covers : ∀ a, a ∈ model.enumeration
  enumeration_length : model.enumeration.length = 2^(model.attempts-1)

variable [DecidableEq Key] [Fintype Seed] [Nonempty Seed]

theorem accepted_energy (model : Model Key Seed m xs) {a : Seed}
    (ha : rootAccept model.root xs a = true) : energy (model.root.eval a) xs ≤ 6*xs.length := by
  simpa [rootAccept,energy_identity] using ha

theorem root_search_total (model : Model Key Seed m xs) (hyp : Hypotheses model)
    (samples : Fin model.attempts → Seed) :
    ∃ a, model.rootSearch samples = some a ∧ rootAccept model.root xs a = true := by
  apply FiniteSearch.total _ _ hyp.enumeration_covers
  apply FiniteSearch.good_exists
  exact root_rejection model.root hyp.root_collision hyp.buckets_pos xs hyp.distinct hyp.buckets_cover

theorem child_search_total (model : Model Key Seed m xs) (hyp : Hypotheses model)
    {a : Seed} (ha : rootAccept model.root xs a = true) (b : Fin m)
    (samples : Fin model.attempts → Seed) :
    ∃ c, model.childSearch a b samples = some c ∧ model.ChildValid a b c := by
  by_cases hb : (model.childKeys a b).length ≤ 1
  · exact ⟨.direct,by simp [Model.childSearch,hb],hb⟩
  · have hp : 0 < Hashing.PowerOfTwo.computeSize
        (2*(count (model.root.eval a) xs b)*(count (model.root.eval a) xs b)) := by
      rw [Hashing.PowerOfTwo.computeSize_eq]
      exact Hashing.PowerOfTwo.positive _
    have hcover : 2*(model.childKeys a b).length^2 ≤ Hashing.PowerOfTwo.computeSize
        (2*(count (model.root.eval a) xs b)*(count (model.root.eval a) xs b)) := by
      rw [Hashing.PowerOfTwo.computeSize_eq]
      convert Hashing.PowerOfTwo.covers (2*(count (model.root.eval a) xs b)^2) using 1 <;>
        simp only [Model.childKeys,count] <;> congr 1 <;> ring
    have hreject := child_rejection (model.child a b) (hyp.child_collision a ha b) hp
      (model.childKeys a b) (nodup _ _ _ hyp.distinct) hcover
    obtain ⟨c,hc,hvalid⟩ := FiniteSearch.total _ _ hyp.enumeration_covers
      (FiniteSearch.good_exists _ hreject) model.attempts samples
    exact ⟨.hashed c,by simp [Model.childSearch,hb,hc],hvalid⟩

/-- Exhaustive fallback makes the abstract constructor return a valid dictionary
for every root block and every family of child blocks. -/
theorem construct_total (model : Model Key Seed m xs) (hyp : Hypotheses model)
    (rootSamples : Fin model.attempts → Seed) (childrenSamples : Fin m → Fin model.attempts → Seed) :
    ∃ dict, model.construct rootSamples childrenSamples = some dict ∧ model.Valid dict := by
  obtain ⟨a,ha,hgood⟩ := root_search_total model hyp rootSamples
  have hchildren := fun b => child_search_total model hyp hgood b (childrenSamples b)
  obtain ⟨children,hseq,hvalues⟩ := sequenceFin_total
    (fun b => model.childSearch a b (childrenSamples b)) (fun b => by
      obtain ⟨c,hc,_⟩ := hchildren b
      exact ⟨c,hc⟩)
  refine ⟨⟨a,children⟩,?_,hgood,?_⟩
  · simp only [Model.construct,ha]
    change (sequenceFin (fun b => model.childSearch a b (childrenSamples b))).bind
      (fun cs => some (⟨a,cs⟩ : Dictionary Seed m)) = _
    rw [hseq]
    rfl
  · intro b
    obtain ⟨c,hc,hvalid⟩ := hchildren b
    rw [hvalues b] at hc
    have he := Option.some.inj hc
    simpa [he] using hvalid

end PerfectHash.Build
