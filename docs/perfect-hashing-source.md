# Perfect hashing through the C-like source language

The alternative implementation lives in `DataStructures/PerfectHash/Source/`.
The original assembly programs, public contracts, and proofs are unchanged.
Reusable hash functions live in `Hashing/Source/`; reusable deduplication
components live in `Algorithms/Dedup/Source/`.

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

## P1: callable construction components

All components are written in the C-like DSL. Their contracts quantify over an
enclosing program with the required helper entries, so the constructor can share
one copy of each helper. Rounding uses entry 1, fill entry 2, and chain search
entry 4. The leaf helpers have no calls. Statement-style calls such as
`fill(directory, 4 * buckets, 0);` make discarded results explicit without
introducing artificial source variable names.

| Callable body | Instruction allowance | Own frame | Additional live stack |
| --- | --- | --- | --- |
| Odd seed sampler | 32 | 7 | 0 |
| Power-of-two rounding | `19 * bits(n) + 22` | 6 | 0 |
| Full-key chain search | `55 * scanComparisons + 12` | 10 | 0 |
| Deduplication pass | `300 * (N + m + 1) + 55 * comparisons` | 26 | 10 |
| Root trial | `300 * (N + m + 1)` | 29 | 5 |
| Child trial | `200 * (q + b + 1)` | 21 | 5 |
| Child allocation | `160 + 19 * bits(2*b*b)` | 14 | 6 |

These are **body** bounds, including return, with argument transfer and call setup
charged by the enclosing call rule. `N` counts input occurrences, `m` is the
number of root/head buckets, `q` is a child's slot count, and `b` its chain length
or cardinality. `bits` is the existing power-of-two rounding model. Stack columns
combine by adding the caller's frame to the maximum nested peak, rather than
summing historical calls. Width and region-fit hypotheses are explicit.

`Sampling.contract` connects one addressed random read and ordinary word
arithmetic to the existing odd-seed encoding. `Rounding.contract` executes the
doubling loop and writes the resulting shift. `Search.contract` compares complete
keys along one-based links, returning early on a match; its cost uses the probes
actually made. `Pass.contract` initializes dirty head cells, invokes search,
inserts only absent keys, and produces `Dedup.collect` and `Dedup.Representation`.
Its cost retains `Dedup.comparisons` for later expectation analysis. Sampling and
rounding are separate constructor calls, not ghost inputs replacing runtime work.

`Root.contract` clears the directory and implements `groupAccepted`. Each
increment `2 * oldCount + 1` fits by a linear bound and is checked before
subtraction or insertion; a rejected trial never computes a potentially
unrepresentable full energy. Success establishes `Construction.Grouped` through
the existing four-store insertion model. `Child.contract` clears its own table,
follows the linked chain, and implements `childAccepted` and `SlotsAt`. It rejects
at the first occupied slot and preserves every cell outside its own table,
including completed siblings. Occupancy is separate from the complete key.
`Allocation.contract` invokes rounding when needed and initializes exactly the
shift and table-pointer fields, preserving count, head and neighboring tables.

The contracts provide exact effects or access policies, with source framing
available through `Evaluation.frame_of_policy`. All component trial reads are
deterministic once the seed is supplied; only sampling reads random memory.
Ordinary algorithm rejection returns zero with normal runtime status. Stack
exhaustion has its separate runtime status and is ruled out by the frame bounds.

`Components.lean` checks the actual generated programs. Configuration-reading
drivers exercise helpers with more than four parameters; these drivers are
component fixtures, not a new constructor calling convention. Their generated
code sizes are 349 (root), 264 (child), 423 (deduplication), and 154 (allocation).
The fixtures cover duplicates, zero/maximum keys, dirty memory, root and child
rejection, sibling preservation, and allocation with exactly 20 stack words
versus 19. They check exact execution costs as well as results and effects.

## P2: bounded construction

`Bounded.source` contains fifteen named functions, each emitted once. The public
constructor accepts the original nine words: input base/count, output
base/capacity, scratch base/capacity, random base/capacity, and width. It computes
the distinct count and all parameters by ordinary calls. The selected seeds in
the proofs describe actual sampled words; they are never runtime advice.

The empty branch clears eight words and writes a complete empty descriptor with
no random access. Nonempty input is rounded and deduplicated using one random
seed. A capped root search accepts the first root meeting the existing energy
bound, writes the header, and walks the directory. Each child is allocated,
searched and completed before the next is touched. Empty and singleton children
need no sample; larger children use their own capped block. Failure returns
before consuming any later block.

| Resource or interface | Verified value |
| --- | --- |
| Generated public code | 1,720 instructions |
| Public register file | 64, with 16 embedded compiler registers |
| Added width condition | `1720 < 2^w` |
| Constructor frame | 30 words |
| Live frames, empty / nonempty | at most 47 / 88 words |
| Internal stack | scratch suffix after `6*(N+1)`, capacity `58*(N+1)` |
| Fixed evaluator fuel | `100000*((N+1)^2 + (w+1)*(N+1))` |
| Retained extent on success | at most `64*(d+1)` words |
| Peak ordinary reservation including registers | `N + 128*(N+1) + 64`, at most `193*(N+1)` |
| Random schedule | sublist of `1 + w*(rootSlots+1)` consecutive addresses |

The original arithmetic and region assumptions are retained, with the explicit
code-fit condition added. `canonical_admissible` proves nonvacuity using the old
sufficient-width threshold. Every input key remains unrestricted, including
zero and the maximum word. Stack storage is counted once inside scratch.

On success, registers 0 and 1 return descriptor base and extent, register 2 the
computed distinct count, and register 18 algorithm status one. Budget failure
returns algorithm status zero and clears the descriptor/count. In both cases
register 5 contains normal runtime status one. Runtime exhaustion is a separate
outcome excluded by the source frame bound and compiler theorem.

`Constructor.contract` is an independent source proof. `RootSpec` and
`Children.SearchSpec` expose proved search behavior, costs and effects; they are
instantiated by the concrete capped searches. `Children.loop_contract` preserves
completed siblings, and `Partial.representation` transfers the completed memory
to the existing query view. `Machine.execution` applies compiler simulation and
charges the public setup and decode, including halt. `Public.execution` uses a
proved injective register embedding. These theorems do not invoke the original
assembly constructor's execution proofs.

`Bounded.execution` gives the pointwise stopped-work bound and outcome for every
random image. `prefix_safety` covers interrupted argument setup and all partial
algorithm effects. `frame` preserves every cell outside output and scratch at
any fuel. `random_reads` proves sample-address uniqueness and bounds reads by
the reservation based on the distinct count. `query_after_build` permits arbitrary
overwrite outside the retained descriptor and uses the released construction
stack for the alternative constant-time query.

The fresh schedule and instruction allowance include deduplication comparisons,
all rejected trials, dirty-memory clearing, expression temporaries, ordinary
calls and returns, branches, entry setup and final halt. The pointwise work bound
remains sharper than the fixed fuel guard, retaining actual retry stopping times
for the later expectation proof.

Executable integration checks cover repeated keys (10,703 instructions), root
budget failure (26,471), child budget failure (25,781), last-attempt success
(32,610), empty input (355), a maximum-key singleton (1,567), all-equal input
(4,529), and near-end reservations (2,736). They check the exact random schedule,
public statuses, descriptor, distinct count, input preservation and queries after
overwrite. The endpoint fixture has both scratch and random reservations ending
at address 4,095 in a 12-bit address space.

## P3: total successful construction

`Total.source` extends the two capped search functions with deterministic
odd-seed enumeration. Each fallback starts at one, calls the ordinary root or
child trial, returns on acceptance, and otherwise adds two. No seed array,
uncharged oracle, or extra runtime bound is passed to the program. The source
uses the same fifteen functions and retains the shared constructor, allocation,
preparation, and table layout from P2.

`Library.Enumeration.loop_contract` proves termination from a successful finite
candidate prefix. The complete odd-multiplier set supplies that ghost prefix;
the acceptance mathematics proves it contains a successful seed. Random search
contracts expose their failure locals so enumeration continues from the actual
post-state. The deterministic phase preserves compact input or linked nodes,
initializes the successful trial, and makes zero random reads.

| Resource or interface | Verified value |
| --- | --- |
| Generated public code | 1,842 instructions |
| Added width condition | `1842 < 2^w` |
| Live frames, empty / nonempty | at most 47 / 88 words, inside the original scratch reservation |
| Expected actual instructions through successful halt | at most `10000000*(N+1)` |
| Fixed evaluator fuel | `1000 * constructionFuel PerfectHash.Total.bounds w N` |
| Retained extent | at most `64*(d+1)` words |
| Peak ordinary reservation including registers | at most `193*(N+1)` words |
| Query | at most 237 instructions, 28 stack words, zero random reads |

The expectation constant is a conservative compiler bound, not a measured
average. `Total.work_le_model` compares the complete source allowance with
1,000 times the existing pure stopping-time model. Finite averaging transfers
that pointwise inequality to the uniform random-memory law. The proof charges
all occurrences during deduplication, rejected random attempts, the rare full
fallback, dirty-memory initialization, call setup, returns, and halt. The
image-independent fuel is an evaluator guard, never an algorithm argument.

`Total.execution` establishes successful termination for every image.
`Total.expected_instructions` bounds the steps of that actual compiled run.
`Total.specification` packages total correctness, expectation, retained and peak
space, and the alternative query contract. `Total.query_after_build` needs no
success-status premise: it permits arbitrary overwrite outside the retained
extent and reuses the released construction stack. The generated program's
execution proof depends on the source contracts and compiler, while acceptance
and probability lemmas reuse the original mathematical models.

Integration fixtures force root fallback (32,127 instructions) and child fallback
(11,003), check random and last-attempt success, and cover empty, singleton,
all-equal and boundary inputs. Every fixture checks exact work and random
addresses, public results, dirty-memory preservation, and membership after
overwriting unretained storage. Original assembly exports and proofs remain
intact. All milestones in the structured-language design are complete.
