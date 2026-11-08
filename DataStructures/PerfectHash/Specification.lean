import DataStructures.PerfectHash.Admissibility

/-! M0's complete target contract. This module defines the proposition that the
future constructor and query must satisfy; it supplies no constructor witness. -/
namespace PerfectHash
open WordRam StaticSet

/-- Uniform numerical instruction constants, chosen with the fixed code before
quantifying over widths, inputs, placements, initial states, or random images.
Actual values must be derived from code in later milestones. -/
structure ResourceBounds where
  preprocess : Nat
  query : Nat
  worst : Nat
  preprocess_pos : 0 < preprocess
  query_pos : 0 < query
  worst_pos : 0 < worst

/-- All-image instruction bound. This mathematical number is not stored in a register. -/
def worstInstructions (b : ResourceBounds) (w N d : Nat) : Nat :=
  b.worst * (Nat.pow (N + 1) 2 + modulus w * (d + 1))

/-- Sufficient interpreter fuel uses N, never an uncharged distinct-count oracle. -/
def constructionFuel (b : ResourceBounds) (w N : Nat) : Nat :=
  worstInstructions b w N N

/-- Permitted memory effects for every finite execution prefix, including failed
trials. Space refers to reserved cells plus registers, not to interpreter traces. -/
structure BuildAccess (w N : Nat) (l : Layout) (result : RunResult w registerCount) : Prop where
  data : ∀ a ∈ result.dataFootprint,
    (l.input N).Contains a ∨ (l.output N).Contains a ∨ (l.scratch N).Contains a
  writes : ∀ a ∈ result.writeFootprint,
    (l.output N).Contains a ∨ (l.scratch N).Contains a
  random : ∀ a ∈ result.randomAddresses, (l.random w N).Contains a
  peak : result.dataFootprint.length + registerCount ≤ peakWords N

/-- Successful constructor output for an arbitrary random image. Register 2
reports the computed distinct count. All other non-descriptor registers may be
clobbered. The retained representation contains all information query needs. -/
structure BuildOutput (rep : Representation) (b : ResourceBounds)
    (xs : List (Word w)) (l : Layout) (initial : DataMemory w)
    (result : RunResult w registerCount) : Prop where
  halted : result.reason = .halted
  time : result.steps ≤ worstInstructions b w xs.length (distinctCount xs)
  base : (readDescriptor result.state.regs).base = l.outputBase
  retained : (readDescriptor result.state.regs).size ≤ dictionaryCapacity (distinctCount xs)
  computedDistinct : (result.state.regs ⟨2, by decide⟩).toNat = distinctCount xs
  represents : rep.Holds xs.toFinset (readDescriptor result.state.regs) result.state.mem
  inputUnchanged : ∀ a, (l.input xs.length).Contains a → result.state.mem a = initial a
  frame : ∀ a, ¬ (l.output xs.length).Contains a → ¬ (l.scratch xs.length).Contains a →
    result.state.mem a = initial a
  maxRandomReads : result.randomReads ≤ randomCapacity w (distinctCount xs)
  freshRandomReads : result.randomAddresses.Nodup
  exposedBits : result.randomBitsExposed ≤ w * randomCapacity w (distinctCount xs)

/-- Correctness and totality quantify over every complete random-memory image.
All prefix effects, faults, and rejected-trial work remain visible. -/
structure ConstructionCorrect (code : DictionaryCode) (rep : Representation) (b : ResourceBounds)
    (xs : List (Word w)) (l : Layout) (rs : Registers w registerCount) (mem : DataMemory w) : Prop where
  completes : ∀ rho : RandomMemory w,
    BuildOutput rep b xs l mem
      (run code.preprocess rho (constructionFuel b w xs.length) (.initial rs mem))
  prefixes : ∀ (rho : RandomMemory w) (fuel : Nat),
    BuildAccess w xs.length l (run code.preprocess rho fuel (.initial rs mem))
  noFault : ∀ (rho : RandomMemory w) (fuel : Nat) (f : Fault),
    (run code.preprocess rho fuel (.initial rs mem)).reason ≠ .fault f

/-- Expectations use the same fixed input/state and the same random memory for
the whole run. Totality above turns this sufficient-fuel average into cost to
successful completion, including rare exhaustive fallback runs. -/
structure ConstructionExpected (code : DictionaryCode) (b : ResourceBounds)
    (xs : List (Word w)) (rs : Registers w registerCount) (mem : DataMemory w) : Prop where
  time : expectedSteps code.preprocess (constructionFuel b w xs.length) (.initial rs mem) ≤
    (b.preprocess * (xs.length + 1) : Nat)
  randomReads : expectedNat (fun rho =>
    (run code.preprocess rho (constructionFuel b w xs.length) (.initial rs mem)).randomReads) ≤
    (1 + 2 * (distinctCount xs + 1) : Nat)
  exposedBits : expectedNat (fun rho =>
    (run code.preprocess rho (constructionFuel b w xs.length) (.initial rs mem)).randomBitsExposed) ≤
    (w * (1 + 2 * (distinctCount xs + 1)) : Nat)

/-- The final full-word, repeated-input, total-construction target. No injectivity,
prime bound, successful-randomness condition, zero heap, or hidden advice is a
precondition. Layout, registers and ordinary memory are fixed before averaging. -/
structure DictionarySpec (code : DictionaryCode) (rep : Representation) (b : ResourceBounds) : Prop where
  construction : ∀ (w : Nat) (xs : List (Word w)) (l : Layout) rs mem,
    Admissible w xs.length l → BuildInput w xs.length l rs → ArrayAt mem l.inputBase xs →
    ConstructionCorrect code rep b xs l rs mem
  expectation : ∀ (w : Nat) (xs : List (Word w)) (l : Layout) rs mem,
    Admissible w xs.length l → BuildInput w xs.length l rs → ArrayAt mem l.inputBase xs →
    ConstructionExpected code b xs rs mem
  query : QuerySpec code rep b.query

/-- Explicit executable code is data in Type, independent of the ghost
representation and its proof. No extraction from existential proof is needed. -/
structure CertifiedDictionary where
  code : DictionaryCode
  representation : Representation
  bounds : ResourceBounds
  correct : DictionarySpec code representation bounds

/-- Sample final existential signature, derived from a supplied certificate.
M0 does not construct such a certificate. -/
theorem CertifiedDictionary.exists_code (cert : CertifiedDictionary) :
    ∃ (code : DictionaryCode) (rep : Representation) (b : ResourceBounds),
      DictionarySpec code rep b :=
  ⟨cert.code, cert.representation, cert.bounds, cert.correct⟩

/-- The public contract implies genuine successful termination, not a fuel status. -/
theorem DictionarySpec.terminates (h : DictionarySpec code rep b)
    (ha : Admissible w xs.length l) (hi : BuildInput w xs.length l rs)
    (hm : ArrayAt mem l.inputBase xs) (rho : RandomMemory w) :
    Terminates code.preprocess rho (.initial rs mem) := by
  apply terminates_iff_halted.mpr
  exact ⟨constructionFuel b w xs.length,
    ((h.construction w xs l rs mem ha hi hm).completes rho).halted⟩

/-- Every completed table answers all word queries even after arbitrary changes
to original input, scratch, and the unused part of the output reservation. -/
theorem DictionarySpec.query_after_build (h : DictionarySpec code rep b)
    (ha : Admissible w xs.length l) (hi : BuildInput w xs.length l rs)
    (hm : ArrayAt mem l.inputBase xs) (rho : RandomMemory w) :
    let result := run code.preprocess rho (constructionFuel b w xs.length) (.initial rs mem)
    let retained := readDescriptor result.state.regs
    ∀ mem', AgreeOn retained result.state.mem mem' →
      ∀ (q : Word w) queryRegs, QueryInput retained q queryRegs → ∀ queryRho : RandomMemory w,
        QueryOutput xs.toFinset retained q mem' b.query
          (run code.query queryRho b.query (.initial queryRegs mem')) := by
  dsimp only
  intro mem' hagree q queryRegs hquery queryRho
  exact h.query.after_overwrite ha.arithmetic.positiveWidth
    ((h.construction w xs l rs mem ha hi hm).completes rho).represents
    hagree hquery queryRho

end PerfectHash
