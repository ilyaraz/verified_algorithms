# Static membership dictionary: M0 contract

M0 is implemented as a checked specification and a proof that its preconditions
are feasible. It does **not** yet provide a perfect-hashing program, a collision
theorem, or a proof of the target construction bounds. Those are the remaining
milestones in the [roadmap](perfect-hashing-plan.md).

The public entry point is
[`PerfectHash.DictionarySpec`](../DataStructures/PerfectHash/Specification.lean).
It uses the construction-independent membership and representation interface in
[`StaticSet`](../DataStructures/StaticSet/Specification.lean), and the assumption
ledger in [`Admissibility.lean`](../DataStructures/PerfectHash/Admissibility.lean).
`import DataStructures` imports these three modules. `WordRam` remains independent
of dictionary specifications.

## Frozen choices

- Store any `Word w`, including zero and the maximum word. Accept repeated input;
  `N = xs.length` counts occurrences and `d = xs.toFinset.card` counts distinct keys.
  The constructor discovers `d`; neither a distinct array nor a seed is an input.
- Use two-level FKS after an independent chained-table deduplication pass, with
  multiply-shift hashing and an explicit occupancy encoding. This is the selected
  implementation route; the semantic interface does not expose FKS invariants.
- Retain immutable, finite, address-indexed random memory. Each search gets at
  most `w` fresh random attempts, then enumerates odd seeds until success. All
  images must terminate successfully. There is no public budget-failure outcome.
- Preserve the original input. The caller supplies separate input, output, and
  scratch regions. Outside memory may be dirty. Initialization and layout
  calculation are part of executed preprocessing work.
- Reserve 64 registers and fixed program arrays independent of width, input,
  placements, and random memory. Scratch registers need no initial values.
- Add a unit-cost logical-right-shift instruction in **M1**. Its proposed syntax
  is `shr dst x count`, with both operands evaluated in the old register file.
  The unsigned natural value of `count` is the shift amount, without masking or
  reducing it modulo `w`. The result is `floor(x.toNat / 2^count.toNat)` encoded
  as a word, hence zero for counts at least `w`, including width zero. It advances
  PC by one, writes only `dst`, and produces no memory event. Existing instructions
  retain their semantics. M0 does not add this instruction or pretend that the
  current ISA already supplies shifts. The contract uses `WordRam.Program` and
  `WordRam.run`; M1 extends those authoritative definitions and rechecks proofs.

## Calling conventions

Both programs enter at PC zero. The initial register file and ordinary memory
are fixed independently of the sampled random image. Addresses, sizes, and width
are encoded using `word w`; admissibility proves these conversions cannot wrap.

| Register | Preprocess input | Preprocess output | Query input |
| --- | --- | --- | --- |
| 0 | Input base | Dictionary base | Dictionary base |
| 1 | Occurrence count `N` | Retained word count | Retained word count |
| 2 | Output base | Computed distinct count `d` | Query key |
| 3 | Output capacity | Unspecified | Unspecified |
| 4 | Scratch base | Unspecified | Unspecified |
| 5 | Scratch capacity | Unspecified | Unspecified |
| 6 | Random base | Unspecified | Unspecified |
| 7 | Random reservation size | Unspecified | Unspecified |
| 8 | Machine width `w` | Unspecified | Unspecified |
| 9–63 | Unspecified | Unspecified | Unspecified |

Query returns exactly the word `0` or `1` in register 0. Every other register may
be clobbered by query. The caller saves the two-word descriptor when making
repeated queries; it is ordinary runtime data, not a ghost set or proof object.
The computed `d` is available for inspection after construction, but query does
not need it as an extra argument.

`BuildInput`, `QueryInput`, `ArrayAt`, and `readDescriptor` are the exact Lean
interfaces. `buildRegisters` supplies the nine preprocessing arguments while
leaving every other register at an arbitrary caller-provided value.

## Assumption ledger and fixed-width capacity

A region is the half-open natural interval `[base, base + size)`. `Region.Fits`
requires `base + size < 2^w`, deliberately keeping the one-past-end address
representable. The strict convention also applies to empty regions. Separate
regions may be adjacent. Random and ordinary memories are distinct address
spaces, so they may use the same numerical addresses.

| Named assumption | Fields and meaning |
| --- | --- |
| `OrdinaryFit` | Each of the three ordinary regions fits; input/output, input/scratch, and output/scratch are separated. |
| `ArithmeticFit` | `1 ≤ w`, `w < 2^w`, and `64*(N+1) < 2^w`. Counters, linear energy thresholds, and accepted child sizes must be proved to stay within this budget. Hash multiplication wraps intentionally. |
| `RandomFit` | The entire reserved random interval, including its endpoint, fits. |
| `Admissible` | Exactly the three numerical predicates above; no condition on key values or uniqueness. |
| `BuildInput` | The nine argument registers contain the specified bases, capacities, count, and width. Other registers are arbitrary. |
| `ArrayAt` | Input memory contains the supplied occurrence list. Other ordinary memory is unconstrained. |
| `Representation.Holds` | Query has a valid table for the specified set, with a positive, fitting retained extent. No correctness claim is made for malformed tables. |

The output and scratch reservations are **each exactly `64*(N+1)` words**.
A larger caller allocation can expose these prefixes to the routine. Their
constants are frozen design budgets to meet in the implementation, not measured
space bounds of an existing constructor. The retained output must use at most
`64*(d+1)` words, including all header words, directory entries, seeds, keys, and
occupancy information. Empty input still produces a positive-size representation.

The public random reservation is the conservative quantity

```text
bucketCapacity(N)   = 2*(N+1)
randomCapacity(w,N) = 1 + w*(2*(N+1)+1)
randomBase + randomCapacity(w,N) < 2^w.
```

This avoids requiring a power-of-two rounding algorithm merely to express the
calling precondition. It covers the roadmap's tighter reservation using
`mN = nextPow2(max 1 N)`. The implementation's selected block discipline is:

```text
dedup:   randomBase
root:    [randomBase + 1, randomBase + 1 + w)
child j: [randomBase + 1 + w*(j+1), randomBase + 1 + w*(j+2))
```

Only attempted stages read cells. Empty/singleton buckets skip their blocks, and
fallback reads no random memory. The final contract requires that actual random
addresses are distinct. Disjoint-block independence and conditional history
transfer remain M3 proof obligations.

For `canonicalLayout N`, ordinary regions start at `0`, `N`, and
`N + 64*(N+1)`; random memory starts at zero. The proved theorem
`canonical_admissible` requires only

```text
1 ≤ w
N + 128*(N+1) < 2^w
1 + w*(2*(N+1)+1) < 2^w.
```

It derives the remaining arithmetic and separation assumptions. There is **no
requirement that `N²` or `d²` fit in a word**. Rejected root trials must check the
energy threshold before accumulating an overflowing quantity. Internal arithmetic
invariants, accepted-root layout bounds, and overflow checks are later proof
obligations, not additional opaque hypotheses on the caller.

## Nonvacuity and checked examples

`admissible_inputs_at_large_width` proves that, for every finite list of `k`-bit
keys, **every** width

```text
w ≥ sufficientWidth(k,N) = max(k, 256*(N+1))
```

admits the canonical layout, encoded input, and argument registers. This is a
loose sufficient threshold, not a practical sizing recommendation. The sharper
fixed-width inequalities above usually allow much smaller widths.

`embedWord` zero-extends keys. `embedWord_toNat`, `embedWord_injective`, and
`distinctCount_embed` prove value, equality, and distinct-count preservation.
The theorem allows arbitrary memory outside the input and arbitrary initial
scratch registers. It constructs no deduplicated input or perfect seed.

[`Examples.lean`](../DataStructures/PerfectHash/Examples.lean) checks empty input
at width 8; repeated zero and maximum-word keys at width 10; dirty-memory input
encoding; and `N=500, w=16`, where reservations fit even though `N²` does not.
Separate theorems reject an ordinary endpoint exactly at the modulus and a
random interval that would wrap despite legal ordinary placement.

## Required behavior and numerical bounds

For any admissible input, `DictionarySpec.construction` requires
`ConstructionCorrect` for **every** `rho`. Its `BuildOutput` requires successful
halt, the correct retained representation, the computed distinct count, input
preservation, and preservation outside output/scratch. `BuildAccess` restricts
every finite prefix's ordinary accesses and random reads to the supplied regions.
`noFault` rules out invalid-PC faults at every fuel budget. Unsuccessful trials
must obey the same prefix resource restrictions as successful ones.

`ResourceBounds` contains positive natural constants `preprocess`, `query`, and
`worst`. They are chosen with the fixed code, before all width/input/state
quantifiers; their numerical values remain to be derived from actual programs.
The contract requires:

| Quantity | Numerical requirement |
| --- | --- |
| Expected preprocessing instructions | `≤ preprocess*(N+1)` |
| Worst-case preprocessing instructions | `≤ worst*((N+1)^2 + 2^w*(d+1))` |
| Query instructions | `≤ query`, including the final halt |
| Retained dictionary words | `≤ 64*(d+1)` |
| Reserved temporary workspace words | `64*(N+1)` |
| Peak ordinary words, including registers | `peakWords N = N + 128*(N+1) + 64 ≤ 193*(N+1)` |
| Maximum actual random reads | `≤ 1 + w*(2*(d+1)+1)` |
| Expected actual random reads | `≤ 1 + 2*(d+1)` |
| Reserved random words | `1 + w*(2*(N+1)+1)` |
| Exposed random bits | Existing `w * randomFootprint.length` observation; maximum at most `w` times the maximum-read bound, expectation at most `w*(1+2*(d+1))` |
| Register count and code size | Exactly 64 registers; exact finite array sizes `code.preprocess.size` and `code.query.size`, independent of every runtime parameter |

Only `peakWords_le` is already a proved numerical accounting inequality. The
algorithmic inequalities above are fields of the target contract. Peak storage
counts the original input, reserved output and scratch, and registers. Immutable
random memory, fixed code, the semantic PC, and interpreter bookkeeping/traces
are excluded from ordinary workspace. Random reservation is accounted separately;
no operating-system allocator or external random provider is silently assumed.

`constructionFuel` substitutes `N` for `d` in the worst-case expression. It is a
mathematical evaluator budget, never a program argument or a charged instruction
count. `ConstructionExpected.time` uses the existing `WordRam.expectedSteps` at
that budget; `ConstructionCorrect.completes` requires every such execution to
halt successfully. Thus no bad image or fallback work can disappear into a
truncated-prefix expectation. Random-resource expectations use the same finite
uniform average, through `expectedNat`. Input, placement, registers, and ordinary
memory stay fixed while `rho` varies; there is no resampling between phases.

For every valid representation, `QuerySpec` quantifies over **every** query word,
query register file satisfying the convention, and random-memory image. Query
preserves the entire ordinary memory, writes no cells, reads no random memory,
and accesses ordinary memory only inside the retained extent. The local
representation law allows arbitrary changes outside that extent.
`DictionarySpec.query_after_build` proves the resulting end-to-end implication:
a completed table continues to answer all queries after the input, scratch, and
unused output reservation are overwritten. This simultaneous all-query guarantee
also covers adaptively chosen queries and repeated queries.

## Witness and theorem shape

The following is the actual, typechecked target shape; M0 defines its proposition
without asserting an inhabitant:

```lean
∃ (code : StaticSet.DictionaryCode)
  (rep : StaticSet.Representation)
  (bounds : PerfectHash.ResourceBounds),
  PerfectHash.DictionarySpec code rep bounds
```

`CertifiedDictionary` stores these three values and a correctness proof.
`CertifiedDictionary.exists_code` derives the existential from a supplied
certificate; it does not claim that a certificate has already been constructed.
The executable programs live in the `.code` data field and must eventually be
explicit arrays, with no `Classical.choose` or other proof-derived runtime advice.
Representation predicates and ghost sets are never query inputs.

M1 implements the chosen shift and necessary machine infrastructure. M2–M9
supply the hash, search, deduplication, representation, and constructor proofs.
M10 supplies the actual certified value and exported program arrays. The current
checks audit the new namespaces and separately verify that the shipped capacity,
layout, encoding, descriptor, and fuel functions have no axiom dependencies.
