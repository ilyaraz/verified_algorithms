# Completed dictionary: proof and validation guide (M11)

[`PerfectHash.fksCode_correct`](../DataStructures/PerfectHash/Certified.lean)
proves the complete M0 `DictionarySpec`. `certifiedFKS` packages its explicit
programs, representation, bounds, and proof; `dictionary_algorithms_exist`
derives the uniform existential statement from that value. The constructor has
238 instructions, the query has 33, and both use 64 registers independently of
word width, input size, keys, layout, or random image.

M1–M11 are complete, with a separate commit for each milestone. The specification
and admissibility requirements retain their original meaning. M1 moved the
shared region and array assertions into `WordRam`, retaining the `StaticSet`
compatibility names; it did not strengthen them.

## Assumptions and quantifier order

The [frozen contract reference](perfect-hashing-spec.md) documents the exact
register conventions and every assumption. The public construction and
expectation fields require only:

| Predicate | Caller obligation |
| --- | --- |
| `Admissible w N l` | Positive width; `w < 2^w`; `64*(N+1) < 2^w`; fitting, pairwise separated input/output/scratch intervals; a fitting random interval. |
| `BuildInput w N l rs` | Registers 0–8 contain input base, occurrence count, output base/capacity, scratch base/capacity, random base/capacity, and width. Other registers are arbitrary. |
| `ArrayAt mem l.inputBase xs` | Input memory encodes the occurrence list, with `N = xs.length`. Other memory may be dirty. |

Intervals use the strict condition `base + size < 2^w`, including empty
intervals. Output and scratch each reserve `64*(N+1)` words. Random memory
reserves `1 + w*(2*(N+1)+1)` words in its separate address space.
`canonical_admissible` gives explicit sufficient placement inequalities;
`admissible_inputs_at_large_width` supplies a sufficiently wide embedding for any
finite input. See [Admissibility.lean](../DataStructures/PerfectHash/Admissibility.lean).

The code and constants are fixed first. Width, occurrence list, placement,
registers, and ordinary memory are then fixed independently of the random image.
Correctness, successful termination, and worst-case resources hold for **every**
image. Expectations average those same completed runs under
`WordRam.randomMemoryLaw`. The program executes deduplication to discover `d`;
neither the distinct list nor a successful seed is an input. There is no
distinct-input, prime, or quadratic-fit precondition.

For each completed table, query correctness covers every `Word w`, including
zero, the maximum word, nonmembers colliding with occupied slots, and queries
chosen after inspecting the table. `QueryInput` supplies the descriptor and query
key. `certified_query_after_build` permits arbitrary memory changes outside the
retained descriptor before querying. Queries preserve all ordinary memory and
make no random reads.

## Trace the public result through the implementation

| Step | Source and proof boundary |
| --- | --- |
| Input encoding | `BuildInput`, `ArrayAt`, and `Admissible` in the frozen contract. |
| Executed duplicate removal | [Dedup.Correctness](../Algorithms/Dedup/Correctness.lean) and [Dedup.Expected](../Algorithms/Dedup/Expected.lean) produce the compact distinct keys and charge the occurrence scan. |
| Concrete construction | [Total.total](../DataStructures/PerfectHash/Total/Correctness.lean) composes deduplication, root trials, allocation, child trials, and deterministic fallback. |
| Successful bounded observation | [Total.run_total](../DataStructures/PerfectHash/Total/Fuel.lean) proves the program's own successful halt within the frozen sufficient fuel. |
| Output and every prefix | [Total.output and prefix_access](../DataStructures/PerfectHash/Total/Interface.lean) establish every `BuildOutput` and `BuildAccess` field. |
| Retained representation | [Bounded.Partial.representation](../DataStructures/PerfectHash/Bounded/Representation.lean) supplies the representation field of `Bounded.Built`, establishing [Table.representation](../DataStructures/PerfectHash/Representation.lean). Its locality proof depends only on retained cells. |
| Query | [Query.spec](../DataStructures/PerfectHash/Query/Correctness.lean) implements the representation's full membership test, including occupancy and complete-key comparison. |
| Complete contract | [Total.specification](../DataStructures/PerfectHash/Total/Contract.lean) combines all-image construction, expected resources, and the existing query proof. |
| Public certificate and export | [Certified.lean](../DataStructures/PerfectHash/Certified.lean) packages the result; [Generated.lean](../PerfectHashTools/Generated.lean) proves both exported literal arrays equal the certified code. |

The dependency direction is machine semantics → hash/probability mathematics →
deduplication and FKS bounds → representation/query and construction trials →
bounded constructor → total constructor → certificate → tools. The bounded and
total refinements reuse the same verified trial instructions and query
representation. Their execution theorems all concern the original `WordRam.run`.
The [Lean Atlas](../website/README.md) exposes the elaborated dependencies for
these paths, including private helpers and generated declarations grouped under
their authored parents.

## Numerical resources and their proofs

Let `U = 2^w`. The value `PerfectHash.Total.bounds` fixes preprocessing and
worst-case constants at 10000 and the query constant at 33. All instruction
bounds include executed branches, memory operations, rejected trials, fallback,
and successful halt.

| Resource | Bound | Proof location in `PerfectHash.Total` unless stated otherwise |
| --- | --- | --- |
| Expected preprocessing instructions | `10000*(N+1)` | [`expected_instructions`](../DataStructures/PerfectHash/Total/Expected.lean), using deduplication and the conditional stage bounds. |
| All-image preprocessing instructions | `10000*((N+1)^2 + U*(d+1))` | [`work_le_worst`](../DataStructures/PerfectHash/Total/WorstCase.lean), transferred by `output`. |
| Query instructions | `33` | `PerfectHash.Query.spec`. |
| Retained words | `64*(d+1)` | [`output`](../DataStructures/PerfectHash/Total/Interface.lean) through the packed representation bound. |
| Reserved output and scratch | `64*(N+1)` each | Original capacities; all accesses confined by `prefix_access`. |
| Distinct ordinary addresses plus registers, every prefix | `N + 128*(N+1) + 64 ≤ 193*(N+1)` | `access_of_policy`, `WordRam.footprint_three`, and `PerfectHash.peakWords_le`. |
| Expected random reads | `1 + 2*(d+1)` | [`expected_random_reads`](../DataStructures/PerfectHash/Total/ExpectedRandom.lean). |
| Maximum random reads | `1 + w*(2*(d+1)+1)` | `output`; its `freshRandomReads` field also proves no repeated address. |
| Expected exposed bits | `w*(1 + 2*(d+1))` | [`expected_exposed_bits`](../DataStructures/PerfectHash/Total/ExpectedRandom.lean). |
| Maximum exposed bits | `w*(1 + w*(2*(d+1)+1))` | `output`. |
| Probability of root or child fallback | `(m+1)*(1/2)^w`, with `m ≤ 2*(d+1)` | [`fallback_probability`](../DataStructures/PerfectHash/Total/FallbackProbability.lean). |

The [total-construction reference](perfect-hashing-total.md) explains the stage
budgets and random-block independence. The expectation charges enumeration on
exhausted images. `constructionFuel` substitutes `N` for `d` in the worst-case
bound, so observation does not require an uncharged distinct-count oracle.
Immutable random memory, program code, and semantic execution traces are outside
the ordinary-space accounting. Host interpreter time and stack usage are outside
the RAM instruction model.

## Repeatable checks and trust boundary

After bootstrap, run:

```sh
./check.sh
python3 scripts/build_website.py
python3 -m unittest discover -s scripts -p 'test_website.py' -v
node --check website/assets/app.js
```

`./check.sh` builds every Lake target and then reruns checks that must execute
even when compiled modules are cached:

| Check | Coverage |
| --- | --- |
| `Checks.lean` | Source-module audit of 5,139 declarations, including private helpers and examples. Only `propext`, `Classical.choice`, and `Quot.sound` are accepted in proof dependencies. A separate inventory of 271 executable definitions has no axiom dependencies, including transitive dependencies. |
| `Total/Examples.lean` | Six executions: forced root/child fallback, forced child fallback, ordinary random success, empty input, twenty equal keys, and near-end regions. Each checks actual cost, computed count, exact random addresses, and queries after overwriting unretained memory. A small kernel proof checks zero-budget entry into enumeration. |
| `scripts/check_exports.sh` | Fresh export, byte comparison against the committed artifact, parsing and kernel checking of both equality proofs, and the executable demo. |
| Atlas build and eight Python tests | Complete authored declaration/description inventory, compiler-derived dependencies, certificate/resource/export proof paths, exact source snapshots and anchors, and reverse-index consistency. |

Earlier milestone examples remain in the build: tiny collision/sampler checks,
overflow-safe rejected roots, dirty-memory trials, singleton/direct children,
occupied-slot nonmembers, exhausted budgets, and last-attempt success. General
theorems establish all-input behavior; these examples exercise integration paths.

The full contract and small `decide` checks are kernel-checked proofs. The larger
`#eval` fixtures and IO demo are execution tests that fail on mismatches; they do
not introduce proof axioms. No `sorry`, project-specific axiom, `native_decide`, or
unchecked backend assumption is part of the certified path. The audit itself
inspects declarations and supplies no proof terms to the library.

Export is deterministic Lean source containing literal instruction arrays and
their equality proofs. The [export reference](perfect-hashing-export.md) also
documents the retained word format. A native backend, byte serializer, or external
random provider would require its own connection to the specified semantics.
