import WordRam.RandomBlocks
import Hashing.PowerOfTwo
import Hashing.MultiplyShiftCollision

namespace Dedup
open WordRam

/-- Six words per occurrence plus slack cover heads, two-word nodes, and compact
keys. This fits comfortably inside the frozen dictionary scratch reservation. -/
def workspaceCapacity (N : Nat) : Nat := 6*(N+1)

structure Layout where
  input : Nat
  scratch : Nat
  random : Nat
  deriving DecidableEq, Repr

def Layout.inputRegion (l : Layout) (N : Nat) : Region := ⟨l.input, N⟩
def Layout.workspace (l : Layout) (N : Nat) : Region := ⟨l.scratch, workspaceCapacity N⟩
def Layout.heads (l : Layout) (N : Nat) : Region := ⟨l.scratch, 2*(N+1)⟩
def Layout.nodes (l : Layout) (N : Nat) : Region := ⟨l.scratch+2*(N+1), 2*N⟩
def Layout.compact (l : Layout) (N : Nat) : Region := ⟨l.scratch+2*(N+1)+2*N, N⟩

structure Admissible (w N : Nat) (l : Layout) : Prop where
  input : (l.inputRegion N).Fits w
  workspace : (l.workspace N).Fits w
  separated : (l.inputRegion N).Separated (l.workspace N)
  random : (Region.mk l.random 1).Fits w
  width : w < modulus w

def Input (w N : Nat) (l : Layout) (rs : Registers w 64) : Prop :=
  rs ⟨0, by decide⟩ = word w l.input ∧
  rs ⟨1, by decide⟩ = word w N ∧
  rs ⟨2, by decide⟩ = word w l.scratch ∧
  rs ⟨3, by decide⟩ = word w l.random ∧
  rs ⟨4, by decide⟩ = word w w

/-- The compact output contains exactly the input's distinct keys. Its position
is computed from N; neither a distinct count nor a seed is a program argument. -/
structure Output (xs values : List (Word w)) (l : Layout) (initial : DataMemory w)
    (r : RunResult w 64) : Prop where
  halted : r.reason = .halted
  nodup : values.Nodup
  membership : ∀ x, x ∈ values ↔ x ∈ xs
  base : r.state.regs ⟨0, by decide⟩ = word w (l.compact xs.length).base
  count : (r.state.regs ⟨1, by decide⟩).toNat = values.length
  array : ArrayAt r.state.mem (l.compact xs.length).base values
  frame : ∀ a, ¬ (l.workspace xs.length).Contains a → r.state.mem a = initial a
  randomReads : r.randomAddresses = [word w l.random]

end Dedup
