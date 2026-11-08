import WordRam.Random
import Mathlib.Data.Finset.Card

/-! Public, construction-independent static membership semantics. No dictionary
algorithm or representation is asserted to exist by this module. -/
namespace StaticSet
open WordRam

/-- The first dictionary implementation reserves a fixed, width-independent register file. -/
def registerCount : Nat := 64

/-- Explicit finite program data; neither array is specialized to width or input. -/
structure DictionaryCode where
  preprocess : Program registerCount
  query : Program registerCount

/-- Half-open natural-number address interval, before conversion to machine words. -/
structure Region where
  base : Nat
  size : Nat
  deriving DecidableEq, Repr

/-- The strict endpoint convention leaves the one-past-end address representable. -/
def Region.Fits (r : Region) (w : Nat) : Prop := r.base + r.size < modulus w

/-- Membership is tested without wrapping either endpoint. -/
def Region.Contains (r : Region) (a : Addr w) : Prop :=
  r.base ≤ a.toNat ∧ a.toNat < r.base + r.size

/-- Sufficient disjointness, also allowing adjacent or empty regions. -/
def Region.Separated (r s : Region) : Prop :=
  r.base + r.size ≤ s.base ∨ s.base + s.size ≤ r.base

/-- Two memories have the same contents throughout a retained region. -/
def AgreeOn (r : Region) (mem mem' : DataMemory w) : Prop :=
  ∀ a, r.Contains a → mem a = mem' a

/-- The input array is the occurrence list, including repetitions. Fit is separate. -/
def ArrayAt (mem : DataMemory w) (base : Nat) (xs : List (Word w)) : Prop :=
  ∀ i : Fin xs.length, mem (word w (base + i.val)) = xs[i]

/-- Distinct count is a specification object, never preprocessing advice. -/
def distinctCount (xs : List (Word w)) : Nat := xs.toFinset.card

theorem distinctCount_le_length (xs : List (Word w)) : distinctCount xs ≤ xs.length :=
  List.toFinset_card_le xs

/-- Only base and extent survive as the runtime descriptor, in registers ⟨0, by decide⟩ and 1. -/
def readDescriptor (rs : Registers w registerCount) : Region :=
  ⟨(rs ⟨0, by decide⟩).toNat, (rs ⟨1, by decide⟩).toNat⟩

/-- A ghost representation interface. Its locality law permits arbitrary changes
outside the retained extent, including erasure of the original input and scratch. -/
structure Representation where
  Holds : {w : Nat} → Finset (Word w) → Region → DataMemory w → Prop
  fits : ∀ {w S r mem}, @Holds w S r mem → r.Fits w
  nonempty : ∀ {w S r mem}, @Holds w S r mem → 0 < r.size
  locality : ∀ {w S r mem mem'}, @Holds w S r mem → AgreeOn r mem mem' → Holds S r mem'

/-- Query starts at PC zero, with base, retained size, and key in registers ⟨0, by decide⟩–2.
All other registers are arbitrary. -/
def QueryInput (r : Region) (q : Word w) (rs : Registers w registerCount) : Prop :=
  rs ⟨0, by decide⟩ = word w r.base ∧ rs ⟨1, by decide⟩ = word w r.size ∧ rs ⟨2, by decide⟩ = q

/-- Exact membership, successful halt, and read-only local execution. The final
halt is included in the instruction count; query exposes no random memory. -/
structure QueryOutput (S : Finset (Word w)) (r : Region) (q : Word w)
    (initial : DataMemory w) (cost : Nat) (result : RunResult w registerCount) : Prop where
  halted : result.reason = .halted
  time : result.steps ≤ cost
  answer : result.state.regs ⟨0, by decide⟩ = word w (if q ∈ S then 1 else 0)
  memory : result.state.mem = initial
  noWrites : result.writeFootprint = []
  noRandomReads : result.randomReads = 0
  readsLocal : ∀ a ∈ result.dataFootprint, r.Contains a

/-- One valid representation supports every word query, arbitrary scratch
registers, and every random image. No construction history is an argument. -/
def QuerySpec (code : DictionaryCode) (rep : Representation) (cost : Nat) : Prop :=
  ∀ (w : Nat), 1 ≤ w → ∀ S r mem, rep.Holds S r mem →
    ∀ (q : Word w) rs, QueryInput r q rs → ∀ rho : RandomMemory w,
      QueryOutput S r q mem cost (run code.query rho cost (.initial rs mem))

/-- This is the ordinary-memory reuse guarantee, directly from representation locality. -/
theorem QuerySpec.after_overwrite (h : QuerySpec code rep cost)
    (hw : 1 ≤ w) (hr : rep.Holds S r mem) (ha : AgreeOn r mem mem')
    (hq : QueryInput r q rs) (rho : RandomMemory w) :
    QueryOutput S r q mem' cost (run code.query rho cost (.initial rs mem')) :=
  h w hw S r mem' (rep.locality hr ha) q rs hq rho

/-- Finite expectation under the existing uniform random-memory law, for natural
resource observations. This uses exactly the averaging convention of expectedSteps. -/
noncomputable def expectedNat (f : RandomMemory w → Nat) : ℝ :=
  (∑ rho : RandomMemory w, (f rho : ℝ)) / Fintype.card (RandomMemory w)

theorem expectedNat_steps (p : Program R) (fuel : Nat) (s : State w R) :
    expectedNat (fun rho => (run p rho fuel s).steps) = expectedSteps p fuel s := rfl

end StaticSet
