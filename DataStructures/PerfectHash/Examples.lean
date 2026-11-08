import DataStructures.PerfectHash.Specification

/-! M0 checks assumptions and encodings, not a still-unimplemented constructor. -/
namespace PerfectHash.Examples
open WordRam StaticSet

/-- Even the empty-input contract has nonzero output and scratch reservations. -/
theorem empty_admissible : Admissible 8 0 (canonicalLayout 0) :=
  canonical_admissible (by decide) (by decide) (by decide)

/-- The concrete example has a duplicate, zero, and the maximum machine word. -/
def repeatedBoundaryInput : List (Word 10) := [word 10 0, word 10 1023, word 10 0]

theorem repeated_boundary_admissible :
    Admissible 10 repeatedBoundaryInput.length (canonicalLayout repeatedBoundaryInput.length) :=
  canonical_admissible (by decide) (by decide) (by decide)

theorem repeated_boundary_distinct : distinctCount repeatedBoundaryInput = 2 := by decide

/-- A real calling state satisfies the contract despite dirty scratch memory. -/
theorem repeated_boundary_encoding :
    BuildInput 10 3 (canonicalLayout 3)
      (buildRegisters 10 3 (canonicalLayout 3) (fun _ => word 10 777)) ∧
    ArrayAt (inputMemory repeatedBoundaryInput (fun _ => word 10 777)) 0 repeatedBoundaryInput ∧
    inputMemory repeatedBoundaryInput (fun _ => word 10 777) (word 10 3) = word 10 777 := by
  refine ⟨buildRegisters_input _, inputMemory_array _ _ (by decide), ?_⟩
  decide

/-- Legal linear storage does not require quadratic intermediate arithmetic to fit. -/
theorem no_quadratic_fit_requirement :
    Admissible 16 500 (canonicalLayout 500) ∧ ¬ 500 ^ 2 < modulus 16 :=
  ⟨canonical_admissible (by decide) (by decide) (by decide), by decide⟩

/-- The strict endpoint policy rejects a reservation ending exactly at the modulus. -/
theorem endpoint_rejected : ¬ Admissible 7 0 (canonicalLayout 0) := by
  intro h
  have := h.ordinary.scratch
  norm_num [canonicalLayout, Layout.scratch, dictionaryCapacity, workspaceCapacity,
    Region.Fits, modulus] at this

/-- Random-address fit is an independent assumption even when ordinary storage fits. -/
theorem random_wrap_rejected :
    ¬ Admissible 10 3 { canonicalLayout 3 with randomBase := 1000 } := by
  intro h
  have := h.random
  norm_num [RandomFit, Layout.random, randomCapacity, bucketCapacity, Region.Fits, modulus] at this

end PerfectHash.Examples
