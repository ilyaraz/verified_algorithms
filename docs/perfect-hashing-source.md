# Perfect hashing through the C-like source language

The alternative implementation lives in `DataStructures/PerfectHash/Source/`.
The original assembly programs, public contracts, and proofs are unchanged.
Reusable hash functions live in `Hashing/Source/`; construction components will
also use `Algorithms/Dedup/Source/`.

## P0: membership query

`PerfectHash.Source.Query.program` is a checked `ram_program` with two named
functions. `query(base, key)` reads the existing packed header and directory,
returns immediately for an empty bucket, selects a direct singleton slot or
calls `hash(seed, key, shift)`, checks occupancy, and compares the full key.
The helper is definitionally the reusable multiply-shift source function.
Expression temporaries, argument transfer, local spills, frame headers, return
links, branches, and the final halt all contribute to the verified bound.

| Resource | Verified value |
| --- | --- |
| Generated code | 237 instructions |
| Worst-case query execution | at most 237 instructions, including halt |
| Fixed register file | 16 |
| Entry frame | 21 words |
| Hash helper frame | 7 words |
| Maximum live stack | 28 words |
| Random reads | zero |
| Application writes | zero |

The source body has a 221-instruction bound. The generic compiler transfer adds
16 entry/exit instructions. One occupied-slot nonmember fixture takes all 237
instructions; members on that path take 236. The helper body takes 22 instructions,
with its call setup and caller result assignment charged separately.

## Calling convention and memory contract

As authorized for this alternative implementation, query uses ordinary function
calls and may write its separated stack. It uses the shared RamLang ABI:

- Register 12 holds the retained descriptor base; register 13 holds the key.
- Register 0 holds the stack base; register 2 holds its exclusive limit.
- Register 4 returns 0 or 1; register 5 returns runtime status 1.
- PC starts at zero. Every other register and every stack word may be dirty.

`Query.Admissible` requires `237 < 2^w`, a fitting stack with at least 28 words,
and separation between the stack and retained dictionary. These conditions are
explicit additions to the original query's interface, and are feasible already
at width eight. `admissible_after` proves one possible placement; the stack can
also be any reused construction reservation separated from the retained extent.

`Query.Spec` reuses `Table.representation` and gives exact membership for every
word and every random image. `Query.Output` permits writes only to the supplied
stack, preserves every ordinary cell outside it, and forbids random reads. All
reads are inside the retained dictionary or the stack. `execution` proves the
same access policy for every interrupted prefix and bounds the actual stack
pointer throughout execution. Runtime exhaustion is impossible with admissible
capacity. A 27-word fixture instead reaches the distinct exhaustion status 2.

The original `StaticSet.QuerySpec` and its strict global no-write contract remain
proved for the original assembly query. The alternative theorem deliberately has
its own name and ABI; it does not claim that stack writes satisfy that contract.

## Proof structure and reuse

`Query.SourceProof.contract` proves the algorithm against the existing `Table.View`,
including empty, singleton and hashed buckets, dirty unoccupied slots, and
occupied-slot nonmembers. It constructs independent source derivations and
checks their costs. It contains no target PCs or frame-store proof obligations.
`ram_derive (branch_tactic)` assembles the sound primitive, sequence, early-return,
conditional and call rules; mathematical branch facts remain explicit. Lean
checks the generated proof terms. Loops use the existing invariant-based rules.

`Query.Correctness.execution` applies `Contract.compiled` to transfer that proof
to actual machine execution. `representation_preserved` permits repeated queries.
`after_overwrite` allows arbitrary erasure of input, construction scratch and
former stack storage outside the retained descriptor, followed by queries using
a newly supplied valid stack. The fixtures cover zero and maximum keys, exact-fit
stack space near the end of memory, an empty retained extent ending at the last
fitting address, and the overwrite theorem for every key.

P1 construction components, P2 bounded construction, and P3 total successful
construction are the next milestones. They will remain in the separate source
folders and retain the existing mathematical models and reference proofs.
