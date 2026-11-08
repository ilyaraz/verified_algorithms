# FKS combinatorics and abstract construction

M5 implements the two-level mathematical construction in
`DataStructures/PerfectHash/{Buckets,Acceptance,Sizes}` and `Build/`. It assumes a
distinct key list, supplied later by M4's certified deduplication. The full-word
multiply-shift instance uses the same seed domain and hash evaluation as M2.

## Counting and acceptance

Buckets partition the distinct list and retain its order. Their counts sum to
`d`. `Buckets.energy_identity` proves that the sum of squared counts is `d` plus
twice the number of colliding unordered pairs. For collision constant `c` and
`m` buckets, the expectation is bounded by

```text
d + (c/m)*d*(d-1).
```

For multiply-shift and `m ≥ d`, expected energy is at most `3d`. Root acceptance
checks energy at most `6d`; its rejection probability is at most one half. Empty
input is treated directly in the probability proof, without division by zero.

For a child with `b ≥ 2`, choose `q = nextPow2(2*b²)`. Its rejection probability is
at most `b*(b-1)/q`, which is strictly below one half. The child acceptance
predicate is equivalent to injectivity on that bucket. Empty and singleton
children need no sampled seed.

## Space and stage budgets

`Sizes.childSlots` assigns zero slots to an empty bucket, one to a singleton, and
`nextPow2(2*b²)` to other buckets. An accepted root gives:

| Quantity | Bound |
| --- | --- |
| Sum of child slots | `24d` |
| Four-word header, four words per directory entry, two words per slot | `64*(d+1)` |
| Sum of child budgets `q+b+1` | `27d+2` |
| Each child size calculation and allocation | Below `2^w` when `64*(d+1) < 2^w` |

These inequalities require no assumption that `d²` fits in a word. The root trial
must still realize its rejection test without overflowing; M7 supplies that RAM
obligation.

## Executable finite search and stage machine

`Build.Model.construct` tries the capped root samples and then the explicit seed
enumeration. After an accepted root, each nontrivial child searches only its own
sample block and enumeration. Direct children bypass search. `construct_total`
proves a valid result for every collection of sample blocks.

`Build.Model.advance` exposes root, child-prefix, completed, and failure states.
`finish_children` proves that each child extends the initialized prefix while
preserving completed siblings. `advanceMany_total` proves completion in `m+2`
**stages**, with all capped retries and fallback internal to each stage. Completed
states are absorbing. The separate work observation counts every candidate tested
inside those stages.

With `w` random attempts and an enumeration of `2^(w-1)` seeds, the abstract bounds
are:

```text
E[charged trial work] ≤ 90*(d+1)
charged trial work ≤ (30d+5)*(w + 2^(w-1)).
```

A root trial is charged `d+m+1`; a child trial is charged its own `q+b+1`.
Initialization and retry bookkeeping inside a RAM trial must fit a constant
multiple of these budgets. The expectation proof averages the child blocks after
the root block, so root-dependent child membership and capacities are included.
These are abstract work bounds. They do not assert an instruction bound for the
Lean evaluator or the future RAM constructor.

`multiplyShift_hypotheses` instantiates the complete construction for all full-word
distinct lists satisfying the linear capacity condition. The conceptual stored-key
table has injective placement on the input, and comparing the stored full key gives
membership equivalence for every query. M6 realizes that table in ordinary memory
and proves a fixed RAM query program.

## Audits and examples

The finite sequencing function, explicit power-of-two rounder, acceptance
predicates, generic constructor, and stage machine have no axiom dependencies.
Collision and expectation proofs retain the project's standard proof axioms.

Executable examples include empty input, zero and maximum keys, a forced rejected
root, forced root and child fallback, zero-budget fallback, full membership
answers, and an admissible concrete instance of the expected work theorem.
