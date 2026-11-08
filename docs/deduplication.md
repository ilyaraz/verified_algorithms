# Verified chained deduplication

`Algorithms/Dedup` implements M4 independently of perfect hashing. The fixed
57-instruction `Dedup.program` uses 64 registers and the authoritative word-RAM
interpreter. It accepts every word as a key, including zero and the maximum word,
and processes arbitrary repeated input. No distinct count or hash seed is supplied
by the caller.

## Interface and layout

At entry PC 0, registers 0–4 contain the input base, occurrence count `N`, scratch
base, dedicated random address, and word width. Other registers and scratch memory
are arbitrary. `Dedup.Admissible` requires fitting input, scratch, and random-cell
intervals, disjoint ordinary input and scratch intervals, and a representable
width. As in M0, fitting means the natural endpoint is strictly below `2^w`.

The scratch reservation is `6*(N+1)` words. Its layout is:

| Region | Offset from scratch base | Reserved words |
| --- | --- | --- |
| Bucket heads | 0 | `2*(N+1)` |
| Chain nodes: key and next index | `2*(N+1)` | `2*N` |
| Compact distinct keys | `2*(N+1)+2*N` | `N` |

The routine rounds the bucket count to the least power of two covering `N`, using
one bucket for empty input. It clears those heads, reads the one reserved random
cell, and runs the verified odd-seed sampler. Each occurrence searches one chain;
a missing key gets a new node and is appended to the compact array. Links use
one-based node indices, with zero denoting an empty chain. Key values have no
sentinel role.

At halt, register 0 gives the compact array base and register 1 gives its computed
length. `Dedup.Output` proves distinctness, membership equivalence, the array
contents, preservation outside scratch, and exactly one random read. The compact
array follows first-occurrence order. The input remains unchanged.

## Theorems and costs

`Dedup.total` proves successful termination for every random memory. Its bound is
`40*(N+1) + 9*comparisons`, where the comparison model includes every occurrence,
including duplicate searches. `Dedup.run_correct` uses the sufficient fuel guard
`40*(N+1) + 9*N*N`; the guard is not the expected runtime.

`Dedup.expected_instructions` proves

```text
expectedSteps program (fuel N) initialState ≤ 67*(N+1).
```

This is the expectation of actual instructions through successful halt. The proof
charges rounding, clearing dirty memory, sampling, failed comparisons, insertion,
and halt. The seed-independent prefix distinct set permits a collision bound for
each occurrence. At least `N` buckets and multiply-shift's collision constant two
give at most `3N` expected comparisons. The raw-word sampler and one-cell random
memory law transfer that bound to the concrete execution.

The RAM refinement proves six instructions for a matching chain node, nine for a
nonmatching node, and one for an empty chain. `Dedup.prefixes` proves the same
access policy for every finite prefix and excludes invalid-PC faults. The
four-store insertion proof frames existing nodes and every address outside the
workspace. None of these arguments assumes `N² < 2^w`.

## Proof boundaries and checks

`Model` and `Bounds` establish comparison mathematics. `Representation` and
`Insertion` establish the chained memory invariant. `Blocks`, `Clear`, `Round`,
`Search`, and `Loop` connect concrete instructions to that invariant.
`Initialization`, `Correctness`, and `Expected` compose the complete result.

Executable examples cover empty, all-equal, alternating, all-distinct, zero and
maximum keys, a scratch endpoint at the last representable word, dirty memory,
one random read, and input preservation. `Checks.lean` audits all `Dedup`
declarations and separately requires axiom-free executable program definitions.
