# RamLang contract (L0)

The structured word-RAM roadmap is implemented in dependency order. Existing
perfect-hashing programs and proofs remain available. New perfect-hashing work
belongs in `DataStructures/PerfectHash/Source/`; the generic `RamLang` library
must never import it. Reusable ports belong in `Hashing/Source/` and
`Algorithms/Dedup/Source/`.

## Frozen semantics

The core uses stable natural-number local and function identifiers. A program is
an ordered finite function table and an entry identifier. Named surface syntax
resolves to these identifiers. Primitive operands are local reads or literals;
all reads precede the primitive's write. Arithmetic is exactly `WordRam.Word`
arithmetic, including remainder by zero and oversized logical shifts. Loads,
stores, and addressed immutable-random reads are explicit, ordered operations.

Statements are skip, primitive, sequence, conditional, while, call, and return.
The independent source configuration contains the current statement, local
values, structured continuations, suspended caller activations, and application
memory. Early return discards the current function's continuations. Calling
suspends the caller's locals and continuation; returning restores them and
assigns the result. Recursion and mutual recursion have no syntactic depth bound.
A fuelled evaluator merely observes finite prefixes of the small-step relation.

The checker rejects duplicate names, undefined callees, arity mismatches,
out-of-range variables, reads not definitely initialized, and possible normal
fallthrough from a function. Parameters start initialized. Branch joins intersect
definite initialization on continuing paths; a loop does not establish any new
initializations after itself. Returning branches need not initialize locals used
only by continuing branches. A deliberately conservative return analysis may
require a syntactic return following a divergent loop.

## ABI v1

The baseline compiler has **16 registers**, independent of input and recursion:

| Register | Role |
| --- | --- |
| 0 | `sp`, first free stack word |
| 1 | `fp`, current frame base |
| 2 | exclusive stack limit |
| 3 | incoming/return link |
| 4 | result |
| 5 | runtime status: 0 running, 1 returned, 2 stack exhausted |
| 6, 7 | operand temporaries |
| 8 | slot address temporary |
| 9 | saved caller frame pointer temporary |
| 10, 11 | remaining compiler temporaries |
| 12–15 | entry parameters (at most four) |

Ordinary functions can have any finite arity. The entry-only limit keeps the
external ABI finite without implicit memory reads; a parameter block can be
passed explicitly by pointer. Entry arguments come from registers 12–15. The
caller supplies register 0 = stack base and register 2 = exclusive limit.
The wrapper initializes `fp`, status, and the entry frame using the same checked
allocation protocol as ordinary calls, then sets returned status and halts.
The successful wrapper does not clear freed stack words.

A frame contains saved caller `fp` at offset 0, saved incoming link at offset 1,
then parameters and locals (including expression temporaries) at offsets 2+i.
Thus `F(f) = 2 + numberOfSlots(f)`. No whole-frame clear is implicit. The checker
and simulation justify every local read. Expression lowering evaluates left to
right into caller-owned temporary slots, so calls cannot overwrite live values
or arguments that alias a destination.

Allocation first computes `limit - sp` and compares the callee frame size to it.
The invariant is `base ≤ fp ≤ sp ≤ limit < 2^w`. Insufficient capacity branches
to the status-2 halt **before any callee-frame write**; earlier application and
stack effects remain. On success arguments and saved `fp` are written relative
to old `sp` while old `fp` still identifies caller locals. Then `fp := old sp`,
`sp := old sp + F`, and `call link, entry` transfers control. The first callee
instructions save the link. Return loads link and caller `fp`, sets `sp := fp`,
restores `fp`, and executes `jumpReg link`. The continuation spills register 4
to the caller destination. Each operation is an ordinary charged instruction.

`call` writes `word w (pc+1)` and jumps to a literal target. `jumpReg` reads its
operand before changing the PC. Both cost one and make no memory access. The
machine remains total on malformed instructions: links wrap, and an invalid
computed PC faults on the next fetch. The compiled execution theorem requires
linked code size and generated frame/offset constants to be strictly below
`2^w`; it imposes no new condition on old instruction arrays.

## Capacity, traces, and proof contracts

The capacity-aware source semantics charges active frames and checks capacity at
calls; its application operations are identical to the ideal semantics. Runtime
stack exhaustion, normal return (including an algorithm's failure result), and
evaluator fuel exhaustion are distinct. Frame peaks include partially prepared
callee frames and the entry frame. The source has logical activations; only the
target RAM stores physical return addresses. Target state gains no hidden stack.

The caller reserves a fitting stack region separated from every source data
access. Application memory agrees with target memory outside that region.
Projection removes ordinary stack reads/writes only: a random read at the same
numerical address remains visible. Freed stack memory can be dirty. Source costs
come from verified instruction templates, not a one-instruction-per-statement
convention; the final halt is charged.

The intended public theorem interfaces (statements to implement, not axioms) are:

* `compile_correct`: successful compilation, corresponding initial states,
  representable constants, and separated accesses imply a progress-sensitive
  simulation of capacity-aware source execution by actual `WordRam.Steps`.
* `returns_correct`: a source return with charged time T and peak S, with S
  fitting the supplied capacity, yields `TerminatesIn` at the wrapper's success
  halt, the same result and projected trace, time at most T, peak at most S,
  and preservation outside declared writes plus stack.
* `exhaustion_correct`: source capacity exhaustion yields the dedicated target
  halt without any stack access outside the reservation.
* `prefix_safe`: every target prefix satisfies the combined application/stack
  policy, including prefixes inside call setup and teardown.
* `divergence_correct`: an infinite source execution whose every prefix fits
  yields infinitely many target instructions. Administrative source steps alone
  cannot witness divergence.
* `ideal_of_fits`: capacity-aware and ideal source prefixes agree whenever the
  ideal frame peak fits; no termination assumption is needed.

The source logic has partial-correctness recursion rules and separate total
rules requiring well-founded measures. Mutually recursive contracts are checked
together. Time adds; stack peaks take maxima and include retained caller frames.
A verified VCG comes after sound rules. Expected target costs transfer pointwise
for each fixed random image before applying the existing expectation machinery.

## Surface language and alternate backend

The DSL must support named functions and locals, familiar arithmetic and unsigned
comparisons, braced blocks, `let`, assignment, `if`/`else`, `while`, calls, and
`return`. Diagnostics identify undefined names, wrong arities, and uninitialized
reads. Lean proof expressions cannot become runtime values. Examples must include
a live local across non-tail recursion and mutually recursive forward calls.

L7 remains a generic checked register-only backend for eligible acyclic routines,
with argument aliasing and early returns covered. The user permits the **new**
perfect-hashing query to use the baseline calling convention and write its stack.
Its separate contract preserves retained/application memory, disallows random
reads, and accounts for stack and call costs. The old `StaticSet.QuerySpec` and
its global no-write theorem remain intact. Neither contract is silently weakened.

## Compatibility checklist

L1 updates `Instr`, `step`, symbolic call resolution, relocation, destination
analysis, execution examples, instruction export, and the axiom audit. General
memory/randomness/frame proofs must cover both new instructions. PC-only
relocation is restricted to the checked subset excluding calls and indirect
jumps; existing block embeddings carry the corresponding proof. Compiled code
uses final linked labels. The original generated perfect-hash arrays must remain
byte-for-byte equal to their certified definitions. `./check.sh` verifies this.

## Milestone ledger

| Milestone | Status |
| --- | --- |
| L0 semantics and ABI | complete: this contract |
| L1 ISA and compatibility | pending |
| L2 independent source semantics | pending |
| L3 recursive compiler | pending |
| L4 simulation and resources | pending |
| L5 source logic | pending |
| L6 DSL and generic routines | pending |
| L7 register-only backend | pending |
| P0 alternative query | pending |
| P1 source construction components | pending |
| P2 source bounded constructor | pending |
| P3 source total constructor | pending |

After each completed milestone: run its checks, regenerate the Atlas with all
new declarations and explanations, commit and push, and publish the existing
ChatGPT Site while preserving its audience.
