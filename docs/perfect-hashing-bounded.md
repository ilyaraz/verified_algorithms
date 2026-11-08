# Bounded perfect-hash construction (M8)

`PerfectHash.Bounded.program` is one fixed 231-instruction, 64-register RAM
program. It accepts M0's full-word, repeated-input calling convention and dirty
memory. It runs the verified deduplicator, computes the root range from the
discovered distinct count, retries root grouping, allocates each child, and
retries child insertion. The M6 query program is unchanged.

This milestone has an explicit bounded-search failure outcome. Each hashed
stage gets `w` random attempts; register 18 is `1` on success and `0` on budget
exhaustion. Exhaustion reaches a real halt. M9 adds exhaustive fallback and the
expected bound to successful completion.

## Code and calling convention

[`Program.lean`](../DataStructures/PerfectHash/Bounded/Program.lean) assembles the
existing deduplication, rounding, root, allocation, and child routines with
symbolic labels. A callee halt becomes one charged jump to its continuation.
[`WordRam.TerminatesIn.call`](../WordRam/Refinement.lean) proves this inlining
rule. `Bounded.program_eq` checks the exact decoded array used by the block
proofs against the symbolic program.

Entry PC is zero. Registers 0–8 retain M0's argument convention. A success
returns output base, retained extent, and computed distinct count in registers
0–2. Other registers are scratch. On failure, only the status is an output
contract; a partially populated output region is not a dictionary.

Deduplication reads `randomBase`. Root attempts read the consecutive block
starting at `randomBase+1`. Child `j` uses the block starting at
`randomBase+1+w*(j+1)`. Empty and singleton children use direct placement and
read no random cells. Every retry budget is checked before its sample load.

## Simulation and memory

The named relations follow the concrete control points:

| Relation | Established fact |
| --- | --- |
| `Deduplicated` | The executed pass returns the compact distinct array and its length. |
| `Rounded`, `RootReady` | Executed rounding and setup establish root parameters. |
| `RootSearchState`, `RootFound` | Root retries preserve compact keys and return an accepted grouping or exhausted budget. |
| `OuterState`, `Partial` | Pending heads describe root chains; completed children contain valid metadata and full-key slots. |
| `ChildSetup`, `ChildSearchState`, `ChildFound` | Allocation and retries preserve all completed siblings and memory outside the current child. |
| `Built` | The returned descriptor has the existing retained-local query representation. |

`WordRam.RetryStepContract.run` connects actual instructions and exposed addresses
to `FiniteProbability.Retry.find` and `attempts`. Its per-attempt premise charges
sampling, the trial, and continuation branches. It does not insert an abstract
hash evaluator into the execution.

All packed capacities follow from the accepted root energy bound. Grouping
reuses the beginning of deduplication scratch while preserving the compact
array at its occurrence-count-based offset. Child square arithmetic is performed
only after its fit follows from accepted energy. There is no additional
quadratic fit assumption.

## Main theorems and bounds

`Bounded.total` proves an actual `TerminatesIn` execution for every random
image under the unchanged `Admissible`, `BuildInput`, and `ArrayAt` assumptions.
Every outcome has a public access policy, an instruction bound
`constructionWork`, and a random trace that is a subsequence of its reserved
consecutive schedule. Success establishes `Built`; failure reports zero status.

The pointwise work bound retains deduplication comparisons and the actual finite
retry stopping rules. Root attempts cost at most `20*m+25*d+20`, including retry
overhead. A child with `b` keys and `q` slots charges its own allocation and
`10*q+17*b+20` per attempted candidate. The completed-child sum is bounded using
the accepted root's linear total allocation.

`Bounded.work_le_fuel` proves the sufficient evaluator guard

```text
10000 * ((N+1)^2 + (w+1)*(N+1)).
```

This number is proof-side interpreter fuel, not a register value or an expected
instruction bound. `Bounded.run_total` observes the program's own halt with this
fuel. `Bounded.prefixes` proves no invalid-PC fault and the read/write/random policy
for every finite prefix, including interruptions inside rejected trials. It also
proves preservation outside output and scratch. `Bounded.input_unchanged`
specializes that frame to the input region.

`Bounded.random_reads` proves fresh addresses and at most
`randomCapacity w d` reads for success and failure alike. The tighter schedule
span is `1+w*(m+1)`, where `m` is the computed rounded distinct count.

`Bounded.query_after_build` requires successful status and then proves the
frozen query contract for every word, every query register initialization, and
every random image. It permits arbitrary overwrites outside the actual returned
descriptor. The proof uses M6's representation theorem; it does not reprove query
execution or assume nonmember queries avoid occupied slots.

## Executable checks

`Bounded.Examples` checks the exact assembled interpreter with kernel `decide`:
interleaved duplicates, dirty memory, zero and maximum keys, nonmembers hashing
to occupied slots, queries after overwriting input/scratch, empty and all-equal
inputs, near-end input/random placements, zero retry budget, root and child
budget exhaustion, and success on the last allowed root attempt.

The repeated-input success uses 1,981 instructions and random addresses
`[0,1,13,25]`. Forced bad root seeds halt after 4,809 instructions and exactly
the root block's 12 attempts. Forced child rejection halts after 5,224
instructions. A successful final root attempt completes in 6,023 instructions.
These are integration checks, not substitutes for the general proofs or the
later expectation theorem.

The DataStructures build uses a 128 MiB Lean thread stack for the larger
kernel-checked execution examples. This changes proof-checking resources only.
