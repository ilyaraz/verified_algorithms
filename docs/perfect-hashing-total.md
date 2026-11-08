# Total perfect-hash construction (M9)

`PerfectHash.Total.specification` proves the original M0 `DictionarySpec` for two
explicit, width-independent arrays: `PerfectHash.Total.program` has 238
instructions and `PerfectHash.Query.program` has 33. Both use the same fixed
64-register machine. Inputs may repeat and may contain every word value,
including zero and the maximum word. The constructor discovers the distinct
keys and their count by executing the verified deduplicator.

The specification and admissibility ledger are unchanged. In particular, there
is no distinct-input, successful-randomness, pre-zeroed-memory, prime, or
quadratic-fit assumption. See the [frozen contract](perfect-hashing-spec.md) for
the argument registers, strict interval endpoints, and feasible placements.

## Numerical bounds

Let `N` be the occurrence count, `d` the distinct count, `w` the word width, and
`U = 2^w`. The fixed value `PerfectHash.Total.bounds` supplies:

| Resource | Proved bound |
| --- | --- |
| Expected instructions through successful preprocessing halt | `10000*(N+1)` |
| Instructions for every random-memory image | `10000*((N+1)^2 + U*(d+1))` |
| Query instructions | `33` |
| Retained dictionary words | `64*(d+1)` |
| Reserved construction scratch | `64*(N+1)` |
| Reserved output capacity | `64*(N+1)` |
| Every prefix's distinct ordinary addresses plus registers | `N + 128*(N+1) + 64 ≤ 193*(N+1)` |
| Expected random reads | `1 + 2*(d+1)` |
| Maximum random reads | `1 + w*(2*(d+1)+1)` |
| Expected random bits exposed | `w*(1 + 2*(d+1))` |
| Maximum random bits exposed | `w*(1 + w*(2*(d+1)+1))` |
| Caller random-memory reservation | `1 + w*(2*(N+1)+1)` |

Every exposed random address is fresh. Random reads, distinct exposed cells, and
the reserved address span are separate observations. The ordinary-space bound
includes the input and all registers, but excludes immutable random memory,
program code, and the mathematical execution trace.

The sufficient evaluator fuel is M0's `constructionFuel bounds w N`, which
replaces `d` by `N` in the worst-case bound. It supplies no distinct-count advice
to the program and is not the expected instruction count.

## Executed fallback and refinement

The total array preserves every continuing instruction of the
[bounded constructor](perfect-hashing-bounded.md). It replaces only the bounded
failure halt at PC 230 and appends the deterministic continuation. Success still
halts at PC 228.

A zero random budget branches before another sample. The continuation installs
odd multiplier one on first entry; after each rejected deterministic candidate,
it adds two to the seed register. The existing root and child trials perform the
same charged clearing, grouping, collision tests, and rejection branches.
Enumeration neither allocates a seed array nor reads random memory. The
mathematical enumeration contains `2^(w-1)` candidates; the existence proof shows
that a successful trial occurs within that finite bound.

`WordRam.SearchStepContract.run` composes concrete deterministic candidate steps.
`RootEnumeration` and `ChildEnumeration` connect its ghost index to the actual
seed register, stage, budget, and construction state. Child enumeration preserves
all completed siblings and all memory outside its allocated table. The combined
`root_stage` and `child_stage` theorems return the exact seed selected by the
random-plus-enumeration stopping rule.

`Total.total` then executes deduplication, rounding, root search, header creation,
and the complete child loop. Every random image reaches a successful halt and
establishes M6's `Bounded.Built` representation. `constructionReads` is the exact
number of random loads in that completed execution.

## Expectation under one finite random memory

The input, placement, initial registers, and ordinary memory are fixed before
averaging. All randomness comes from the original immutable `randomMemoryLaw`.
Correctness and termination quantify over every image; only the expected bounds
use its uniform distribution.

The sampler's two-to-one raw-word fibers transfer the multiply-shift rejection
bound to each actual load. A stage has at most one-half rejection probability,
`w` random attempts, and at most `2^(w-1)` enumeration candidates. Its work
majorant charges all random trials and the enumeration bound on exhausted
images. `expected_trial_work` bounds that entire majorant by three per-trial
budgets, including rare fallback executions.

`mean_root_child` proves the product law for the root block and each child's
disjoint block. A child's predicate, keys, and capacity may depend on the complete
root outcome, including a root found by enumeration. Each child is charged by
its own slot count and population. Accepted root energy bounds the sum of those
budgets. Deduplication is averaged separately, and its compact output order is
seed-independent. No proof assumes that sampled values at different addresses
are unequal.

`FallbackEvent` describes exhaustion of the root or any hashed child stage.
`fallback_probability` proves

```text
Pr[any fallback] ≤ (m+1)*(1/2)^w,
```

where `m` is the computed root range and `m ≤ 2*(d+1)`. Direct children never
trigger a random-budget fallback. The stage refinement theorems connect these
stopping events to the actual enumeration continuation.

## Public theorem guide

All names below are in `PerfectHash.Total`:

| Theorem | Guarantee |
| --- | --- |
| `specification` | Complete frozen `DictionarySpec` for the two explicit arrays. |
| `construction_correct` | Successful completion for all images, every-prefix access contract, and no faults. |
| `construction_expected` | Expected instructions, reads, and bits for that same completed run. |
| `output` | All `BuildOutput` fields, including computed count and retained representation. |
| `prefix_access` | Every finite prefix satisfies `BuildAccess`, including its actual peak footprint. |
| `work_le_worst`, `run_total` | Derived all-image cost and sufficient fuel observing the program's own halt. |
| `expected_instructions` | Expected actual instructions to successful completion. |
| `expected_random_reads`, `expected_exposed_bits` | Separate expected randomness resources. |
| `query_after_build` | Every full-word query after any overwrite outside the returned descriptor. |

The query theorem imports the existing representation-local query proof. Queries
return exactly zero or one, preserve all ordinary memory, read only retained
cells, and make no random reads. All queries are covered simultaneously for each
completed table, including adaptively chosen queries.

## Execution checks and trust

`Total.Examples.zero_budget_enters_enumeration` is a kernel-reduced control-flow
check. The larger integration checks evaluate the same proved `WordRam.run` and
program array with `#eval`, throwing an error on any mismatch. They do not
introduce native evaluation axioms or replace general kernel-checked theorems.

| Fixture | Actual instructions |
| --- | ---: |
| Forced root and child fallback, repeated keys, zero and maximum keys | 23,294 |
| Forced child fallback | 1,991 |
| Successful random trials on interleaved repetitions | 1,981 |
| Empty dictionary | 148 |
| Twenty copies of the maximum key | 700 |
| Near-end input and random regions | 413 |

Each fixture checks successful halt, exact cost, computed distinct count, exact
random addresses, and member/nonmember queries after overwriting all unretained
memory. The Lean functional interpreter may need substantial host stack on long
traces; host execution resources are separate from the proved RAM bounds.

The full axiom audit accepts only `propext`, `Classical.choice`, and `Quot.sound`
in proofs. The actual constructor, continuation, bound constants, and execution
helpers are separately audited for no axiom dependencies. The program never
extracts a seed or instruction array from an existential proof. M10 packages the
explicit arrays as a certified value and supplies the extraction/demo interface.
