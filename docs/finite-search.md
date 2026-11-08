# Finite random search and exhaustive fallback (M3)

`Probability/Finite.lean` defines finite uniform averages and event probabilities,
proving their agreement with the uniform PMF. It supplies linearity, finite sums,
monotonicity, product averaging, Markov's inequality, and finite union bounds.
All expectations use one fixed finite sample space.

`Probability/Retry.lean` searches an explicitly supplied tuple of `r` candidates.
For a Boolean acceptance predicate whose uniform rejection probability is `q`,
`failed_probability` proves that fallback occurs with probability exactly `q^r`.
When `q ≤ 1/2`, `expected_attempts` bounds random attempts by `2*(1-q^r)` and
`fallback_bound` gives `Pr[fallback] ≤ (1/2)^r`. Rejected trials count as attempts.
The abstract functions return the actual accepted candidate, without using a
proof to choose it.

`Probability/FiniteSearch.lean` follows exhausted random search with deterministic
enumeration. `total` proves successful search for every sample tuple when the
enumeration covers all seeds and at least one seed is accepted. `good_exists`
derives the latter condition from `q ≤ 1/2`. The enumeration list is abstract
proof-side data; the planned RAM implementation increments an encoded seed using
M2's verified operation instead of allocating that list.

For an enumeration of at most `H` candidates and a per-trial instruction allowance
`B`, including retry bookkeeping, the complete cost allowance satisfies

```text
worst work       ≤ B*(r+H)
expected work    ≤ 2*B + (1/2)^r*H*B.
```

`searchWork` counts the candidates actually tested. `work` conservatively charges
all `H` fallback candidates when fallback is reached; `searchWork_le` relates them.
`expected_searchWork` applies the bound to the actual abstract search cost.
Initialization and finishing costs remain separate and must be added by callers.
With `r=w` and `H=2^(w-1)`, `expected_work_word` gives the convenient bound `3*B`.
Bad random images and their fallback work remain in every expectation.

`WordRam/RandomBlocks.lean` transfers these finite laws to the existing immutable
random memory. `coordinatesEquiv` splits a complete image into selected distinct
coordinates and its untouched complement. `mean_coordinates` proves the exact
uniform tuple law. `mean_disjoint` and `mean_disjoint_le` handle arbitrary functions
of earlier coordinates and a disjoint next block; a next-stage predicate or budget
may depend on the earlier history. This avoids assuming that adaptive construction
states are independent of the randomness that produced them.

The block address functions use the frozen discipline: the first cell is for
deduplication, then `stageBase base w stage = base+1+w*stage`. Root is stage zero;
child `j` is stage `j+1`. Fit, injectivity, and separation lemmas prove that valid
reserved blocks do not wrap or overlap. Equal sampled values are allowed. Repeated
addresses fail the injectivity hypothesis. `MultiplyShift.mean_rawSeed` transfers
arbitrary trial-cost observations through the exact raw-word sampler law.

`Probability/Examples.lean` supplies a concrete RAM integration example. It reads
one random candidate, accepting a nonzero word. If rejected, it enumerates zero
and one. For positive widths, every random image halts with a nonzero result.
The program costs three instructions on random success and seven on fallback;
its exact expectation under `WordRam.expectedSteps` is `3+4/2^w ≤ 5`.
It preserves ordinary memory, reads exactly one random cell, and every fuel prefix
obeys the one-cell reservation and cannot fault. Kernel checks exercise forced
fallback, immediate success, and rejection of repeated-address freshness.

These modules establish reusable search and probability infrastructure. They do
not assert that the FKS construction stages or the full dictionary program have
already been refined to RAM instructions; those remain later milestones.
