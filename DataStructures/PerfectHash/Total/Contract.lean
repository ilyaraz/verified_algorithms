import DataStructures.PerfectHash.Total.FallbackProbability

namespace PerfectHash.Total
open WordRam

variable {w : Nat} {xs : List (Word w)} {l : Layout}
  {rs : Registers w 64} {mem : DataMemory w}

/-- Deterministic half of the frozen M0 contract for the two explicit arrays. -/
theorem construction_correct (ha : Admissible w xs.length l)
    (hin : BuildInput w xs.length l rs) (harr : ArrayAt mem l.inputBase xs) :
    ConstructionCorrect ⟨program,Query.program⟩ Table.representation bounds xs l rs mem := by
  constructor
  · intro rho
    exact output (s := .initial rs mem) ha rho rfl hin harr
  · intro rho n
    exact prefix_access (s := .initial rs mem) ha rho rfl hin harr n
  · intro rho n f
    exact (prefixes (s := .initial rs mem) ha rho rfl hin harr n).2.1 f

/-- Expected time, reads, and exposed bits refer to the same complete execution
under the fixed finite random-memory law. -/
theorem construction_expected (ha : Admissible w xs.length l)
    (hin : BuildInput w xs.length l rs) (harr : ArrayAt mem l.inputBase xs) :
    ConstructionExpected ⟨program,Query.program⟩ bounds xs rs mem :=
  ⟨expected_instructions (s := .initial rs mem) ha rfl hin harr,expected_random_reads (s := .initial rs mem) ha rfl hin harr,
    expected_exposed_bits (s := .initial rs mem) ha rfl hin harr⟩

/-- The full original contract: total construction from repeated full-word keys,
expected linear preprocessing, linear memory, and constant-time local queries. -/
theorem specification : DictionarySpec ⟨program,Query.program⟩ Table.representation bounds := by
  constructor
  · intro w xs l rs mem ha hin harr
    exact construction_correct ha hin harr
  · intro w xs l rs mem ha hin harr
    exact construction_expected ha hin harr
  · exact Query.spec program

end PerfectHash.Total
