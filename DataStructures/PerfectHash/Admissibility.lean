import DataStructures.StaticSet.Specification
import Mathlib.Tactic.Linarith

/-! Explicit sufficient environmental assumptions for the full-word FKS target.
These reservations are a design budget, not a proved algorithmic space bound. -/
namespace PerfectHash
open WordRam StaticSet

/-- Caller-reserved output capacity; the retained prefix will instead depend on d. -/
def dictionaryCapacity (N : Nat) : Nat := 64 * (N + 1)

/-- Temporary chaining, compact keys, grouping, and construction workspace budget. -/
def workspaceCapacity (N : Nat) : Nat := 64 * (N + 1)

/-- Conservative directory bound covering nextPow2(max 1 N), without requiring
rounding code in the public precondition. -/
def bucketCapacity (N : Nat) : Nat := 2 * (N + 1)

/-- One dedup seed, w root attempts, and w attempts for each reserved child. -/
def randomCapacity (w N : Nat) : Nat := 1 + w * (bucketCapacity N + 1)

/-- Caller chooses bases in the two separate address spaces. Random memory need
not be disjoint from ordinary memory: they are different memories. -/
structure Layout where
  inputBase : Nat
  outputBase : Nat
  scratchBase : Nat
  randomBase : Nat
  deriving DecidableEq, Repr

def Layout.input (l : Layout) (N : Nat) : Region := ⟨l.inputBase, N⟩
def Layout.output (l : Layout) (N : Nat) : Region := ⟨l.outputBase, dictionaryCapacity N⟩
def Layout.scratch (l : Layout) (N : Nat) : Region := ⟨l.scratchBase, workspaceCapacity N⟩
def Layout.random (l : Layout) (w N : Nat) : Region := ⟨l.randomBase, randomCapacity w N⟩

/-- All ordinary intervals fit, with no wrapping, and are pairwise separated. -/
structure OrdinaryFit (w N : Nat) (l : Layout) : Prop where
  input : (l.input N).Fits w
  output : (l.output N).Fits w
  scratch : (l.scratch N).Fits w
  input_output : (l.input N).Separated (l.output N)
  input_scratch : (l.input N).Separated (l.scratch N)
  output_scratch : (l.output N).Separated (l.scratch N)

/-- Linear arithmetic budget for counters, accepted energies and rounded child
sizes. Hash multiplication deliberately wraps. No N²-fit assumption is made. -/
structure ArithmeticFit (w N : Nat) : Prop where
  positiveWidth : 1 ≤ w
  widthValue : w < modulus w
  linearSizes : 64 * (N + 1) < modulus w

/-- Sufficient capacity for disjoint random blocks and a representable endpoint. -/
def RandomFit (w N : Nat) (l : Layout) : Prop := (l.random w N).Fits w

/-- The entire numerical assumption ledger; no restriction on any key value. -/
structure Admissible (w N : Nat) (l : Layout) : Prop where
  ordinary : OrdinaryFit w N l
  arithmetic : ArithmeticFit w N
  random : RandomFit w N l

/-- Build starts at PC zero. Registers ⟨0, by decide⟩–8 contain input base, occurrence count,
output base/capacity, scratch base/capacity, random base/capacity, and width.
There is no distinct count or hash seed among the inputs. -/
def BuildInput (w N : Nat) (l : Layout) (rs : Registers w registerCount) : Prop :=
  rs ⟨0, by decide⟩ = word w l.inputBase ∧ rs ⟨1, by decide⟩ = word w N ∧
  rs ⟨2, by decide⟩ = word w l.outputBase ∧ rs ⟨3, by decide⟩ = word w (dictionaryCapacity N) ∧
  rs ⟨4, by decide⟩ = word w l.scratchBase ∧ rs ⟨5, by decide⟩ = word w (workspaceCapacity N) ∧
  rs ⟨6, by decide⟩ = word w l.randomBase ∧ rs ⟨7, by decide⟩ = word w (randomCapacity w N) ∧
  rs ⟨8, by decide⟩ = word w w

/-- Initialize only argument registers; all other initial registers are supplied
by the caller and remain unconstrained in the public theorem. -/
def buildRegisters (w N : Nat) (l : Layout)
    (other : Registers w registerCount) : Registers w registerCount := fun r =>
  match r.val with
  | 0 => word w l.inputBase
  | 1 => word w N
  | 2 => word w l.outputBase
  | 3 => word w (dictionaryCapacity N)
  | 4 => word w l.scratchBase
  | 5 => word w (workspaceCapacity N)
  | 6 => word w l.randomBase
  | 7 => word w (randomCapacity w N)
  | 8 => word w w
  | _ => other r

theorem buildRegisters_input (other : Registers w registerCount) :
    BuildInput w N l (buildRegisters w N l other) := by
  simp [BuildInput, buildRegisters]

/-- Peak reserved ordinary storage includes input, both caller regions, and registers.
Code, semantic traces, and immutable random memory are accounted separately. -/
def peakWords (N : Nat) : Nat :=
  N + dictionaryCapacity N + workspaceCapacity N + registerCount

theorem peakWords_le (N : Nat) : peakWords N ≤ 193 * (N + 1) := by
  simp only [peakWords, dictionaryCapacity, workspaceCapacity, registerCount]
  omega

/-- Packed ordinary layout and an independently based random region. -/
def canonicalLayout (N : Nat) : Layout := ⟨0, N, N + dictionaryCapacity N, 0⟩

/-- Fixed-width sufficient inequalities, suitable for callers to check directly. -/
theorem canonical_admissible (hw : 1 ≤ w)
    (hm : N + 128 * (N + 1) < modulus w)
    (hr : 1 + w * (2 * (N + 1) + 1) < modulus w) :
    Admissible w N (canonicalLayout N) := by
  constructor
  · constructor <;>
      simp only [canonicalLayout, Layout.input, Layout.output, Layout.scratch,
        dictionaryCapacity, workspaceCapacity, Region.Fits, Region.Separated] <;> omega
  · exact ⟨hw, Nat.lt_two_pow_self, by omega⟩
  · simpa only [RandomFit, canonicalLayout, Layout.random, Region.Fits,
      randomCapacity, bucketCapacity, Nat.zero_add] using hr

/-- Elementary growth bound used to make nonvacuity independent of analysis APIs. -/
theorem square_le_two_pow (w : Nat) (hw : 4 ≤ w) : w ^ 2 ≤ 2 ^ w := by
  induction w, hw using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
    rw [show 2 ^ (n + 1) = 2 ^ n * 2 from pow_succ 2 n]
    nlinarith

/-- A deliberately loose explicit width threshold. Every larger width works too. -/
def sufficientWidth (k N : Nat) : Nat := max k (256 * (N + 1))

theorem canonical_admissible_of_large_width (hw : 256 * (N + 1) ≤ w) :
    Admissible w N (canonicalLayout N) := by
  have h4 : 4 ≤ w := by omega
  have hp := square_le_two_pow w h4
  apply canonical_admissible (by omega)
  · unfold modulus
    nlinarith
  · unfold modulus
    have hc : 2 * (N + 1) + 2 ≤ w := by omega
    have := Nat.mul_le_mul_left w hc
    nlinarith

/-- The usual zero-extension of a key; its runtime definition uses no proof advice. -/
def embedWord (w : Nat) (x : Word k) : Word w := word w x.toNat

theorem embedWord_toNat (h : k ≤ w) (x : Word k) :
    (embedWord w x).toNat = x.toNat := by
  apply word_toNat_of_lt
  exact lt_of_lt_of_le x.isLt (Nat.pow_le_pow_right (by decide) h)

theorem embedWord_injective (h : k ≤ w) : Function.Injective (embedWord (k := k) w) := by
  intro x y he
  apply BitVec.eq_of_toNat_eq
  have := congrArg BitVec.toNat he
  simpa only [embedWord_toNat h] using this

/-- Embedding preserves multiplicities and the distinct count, without deduplicating. -/
theorem distinctCount_embed (h : k ≤ w) (xs : List (Word k)) :
    distinctCount (xs.map (embedWord w)) = distinctCount xs := by
  have he : (xs.map (embedWord w)).toFinset = xs.toFinset.image (embedWord w) := by
    ext x
    simp
  unfold distinctCount
  rw [he]
  exact Finset.card_image_of_injective _ (embedWord_injective h)

/-- An explicit array encoding at base zero. Values outside the input are arbitrary. -/
def inputMemory (xs : List (Word w)) (outside : DataMemory w) : DataMemory w :=
  fun a => if h : a.toNat < xs.length then xs[a.toNat] else outside a

theorem inputMemory_array (xs : List (Word w)) (outside : DataMemory w)
    (hfit : xs.length < modulus w) : ArrayAt (inputMemory xs outside) 0 xs := by
  intro i
  have hi : i.val < modulus w := lt_trans i.isLt hfit
  simp [inputMemory, word_toNat_of_lt hi, i.isLt]

/-- Nonvacuity of the complete calling precondition, for every finite list of
k-bit keys and every sufficiently large width. Dirty outside memory and scratch
registers can be chosen arbitrarily. -/
theorem admissible_inputs_at_large_width (xs : List (Word k))
    (hw : sufficientWidth k xs.length ≤ w)
    (other : Registers w registerCount) (outside : DataMemory w) :
    let ys := xs.map (embedWord w)
    let l := canonicalLayout ys.length
    k ≤ w ∧
    Admissible w ys.length l ∧
    BuildInput w ys.length l (buildRegisters w ys.length l other) ∧
    ArrayAt (inputMemory ys outside) l.inputBase ys ∧
    distinctCount ys = distinctCount xs := by
  have hk : k ≤ w := le_trans (Nat.le_max_left _ _) hw
  have hn : 256 * (xs.length + 1) ≤ w := le_trans (Nat.le_max_right _ _) hw
  dsimp only
  have ha : Admissible w (xs.map (embedWord w)).length
      (canonicalLayout (xs.map (embedWord w)).length) := by
    simpa only [List.length_map] using canonical_admissible_of_large_width hn
  refine ⟨hk, ha, buildRegisters_input other, ?_, distinctCount_embed hk xs⟩
  apply inputMemory_array
  have := ha.ordinary.input
  simpa [canonicalLayout, Layout.input, Region.Fits] using this

end PerfectHash
