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
| L1 ISA and compatibility | complete: `WordRam/Calls.lean`, checked relocation subset |
| L2 independent source semantics | complete: checker, source steps/evaluator, ideal-capacity correspondence, recursion examples |
| L3 recursive compiler | complete: deterministic two-pass compilation, frame/code metadata, boundary executions |
| L4 simulation and resources | complete: source derivation soundness, linked simulation, exact instructions, stack peaks, exhaustion, prefix safety, productive loops |
| L5 source logic | complete: total contracts, decreasing loops, self/mutual contract induction, memory frames, recursive sum and iterative fill proofs |
| L6 DSL and generic routines | complete: checked C-like syntax, diagnostics, proof tactics, code reports, fill/copy/traversal/retry contracts |
| L7 register-only backend | complete: checked straight-line subset, leaf-helper inlining, full trace preservation, no compiler memory, overlap/live-local proofs |
| P0 alternative query | pending |
| P1 source construction components | pending |
| P2 source bounded constructor | pending |
| P3 source total constructor | pending |

After each completed milestone: run its checks, regenerate the Atlas with all
new declarations and explanations, commit and push, and publish the existing
ChatGPT Site while preserving its audience.

## L3 executable compiler interface

`RamLang.Compiler.compile` checks the source and returns an executable instruction
array plus function ranges and frame sizes. `lower_length`, `wrapper_length`,
`bodies_length`, `compile_function_count`, and `compile_code_size` prove finite
output sizes. `CompiledProgram.Fits` states code/frame representability; it is an
execution precondition, not a width-dependent compiler input. `report` displays
the resulting instruction and frame counts. No executable definition depends on
proof axioms.

The compiler emits arguments directly into the checked new frame while retaining
the old frame pointer. Core arguments are already atoms; future rich-expression
lowering evaluates them into caller-owned temporaries first. Function bodies are
emitted once, including self-recursive and mutually recursive bodies. The linker
uses final absolute addresses and never applies PC-only relocation to calls.

The kernel-checked L3 fixtures cover dirty memory, live locals, recursion, early
return, entry exhaustion, exact-fit capacity, one-word-short capacity, and reuse
of released frames. The sum example has 65 code instructions and five-word
frames. Input 4 returns 10 in 197 instructions using a 25-word stack; capacity 24
instead reports runtime exhaustion after 108 instructions without accessing an
out-of-reservation word. Two sequential calls reuse a 30-word reservation and
return 20 in 423 instructions. These finite executions and code-size proofs do
**not** constitute the general state/trace/resource simulation required by L4.
The general proof is supplied separately by L4 below.

## L4 checked compiler interface

`Evaluation` is a finite, compositional derivation over the source syntax. It
contains no target execution premise. `Evaluation.sound`, `invocationReturns`,
and `ideal_returns` connect these derivations to the independent small-step
semantics, including the ideal semantics without a capacity limit.

`compile_evaluation` proves simulation for every such derivation, with the
actual emitted code, exact `instructions` charge, application trace projection,
and `extraStack` peak. Calls preserve live caller slots and initialize only
parameters; uninitialized local slots may contain arbitrary initial memory.
`compiled_returns`, `compiled_body_exhausts`, and `compiled_entry_exhausts`
include the entry and termination wrappers. Entry exhaustion takes six
instructions and performs no writes. Stack peaks bound the actual stack pointer
at every intermediate machine state, including partially installed frames.

`Fragment.prefix_policy`, `application_prefix_policy`, and `prefix_noFault`
cover interrupted executions. `project_random_addresses` shows that projection
preserves every addressed random read. Application accesses must be disjoint
from the stack reservation; code, frames, and stack endpoints must fit in words.
These are explicit theorem hypotheses, not assumptions added to the machine.

For infinite executions, `LoopProgress` describes a true loop condition and a
finite body derivation returning to an invariant, permitting terminating
recursive calls inside each iteration. `source_loop_diverges`,
`compiled_loop_diverges`, and `compiled_loop_stackBound` prove independent source
divergence and an infinite target run with bounded stack. The interface is
certificate based: it does not claim completeness of finite derivations or a
translation of arbitrary operational divergence without a progress certificate.

The theorem-based fixtures prove a nineteen-instruction return from dirty RAM
and a genuinely infinite loop with a two-word stack. All source and compiler
proofs pass the project axiom audit. The source logic, C-like DSL, and alternative
perfect-hashing proofs remain subsequent milestones.

## L5 source verification

`RamLang.Logic.Contract` describes a total source execution, a postcondition on
its outcome, memory and application trace, and separate instruction/stack bounds.
`sequence` adds time and takes the maximum of stack peaks. `call` checks the
callee, arguments, arity, capacity, return value, and caller destination; it adds
the verified argument/call overhead and the callee frame. Early returns and
exhaustion propagate through `sequenceStop` without charging discarded code.

`while_total` proves termination using a decreasing natural ghost measure and an
invariant. Its time potential pays for every condition, iteration, and back edge;
its access policy composes over the complete application trace. `recursion` and
`mutual_recursion` discharge contract families by strict well-founded rank
decrease, including calls between different function identifiers. These are proof
rules, with no runtime rank or recursion fuel. `Evaluation.frame` derives memory
preservation from the absence of writes in the source trace.

`Contract.sourceReturns` gives an independent ideal source execution, while
`Contract.compiled` transfers the same proof to the generated program and adds
the public wrapper and entry frame. No verification-condition generator is
introduced here, so there is no additional trusted proof automation.

The general non-tail sum theorem proves exactly `43*n + 25` instructions and a
peak of `5*(n+1)` words, preserving application memory. Its input counter must
fit in a word; the triangular-sum result may wrap. The array-fill proof uses
`while_total` and proves at most `22*n + 30` instructions, five stack words,
every requested array value, preservation outside the array and stack, and the
access policy of every interrupted prefix. It accepts arbitrary initial memory
and proves the pointer/count arithmetic does not wrap. The compiled programs
have 65 and 50 instructions respectively. Exact-fit and empty-array fixtures
also execute the generic fill, including maximum word values and dirty memory.

## L6 C-like programs and reusable library

The [language guide](ramlang-dsl.md) documents `ram_program entry { fn ... }`,
named mutable locals, lexical blocks, forward/self/mutual calls, explicit memory
effects, and rich expressions evaluated left to right. Expression temporaries
are charged caller-owned slots. Rich loop tests are reevaluated on every test.
Elaboration emits an ordinary core constructor term after the existing checker
accepts it. The DSL sum and fill are definitionally equal to the verified L5
cores. Diagnostic fixtures check names, arities, scope, initialization, and returns.

`ram_simp`, `ram_primitive`, and `ram_cost` produce ordinary kernel-checked proof
terms. `report` displays linked code addresses, ranges, and frame sizes. No
annotation supplies a runtime value or an uncharged computation.

The generic library adds disjoint array copy through the traversal rule, with
at most `33*n+30` target instructions and six stack words. `Retry.contract`
supports early-returning attempts, including recursive attempts with contracts,
and charges `(trialWork+5)*n+12` for the source body. It records exactly one
explicit random address per attempt and proves address freshness under a
representable reservation. These execution rules have no probability imports.
The C-like first-nonzero example transfers that rule to a compiled program with
at most `28*n+28` instructions and five stack words, distinguishing budget failure
from runtime exhaustion. Copy, retry, nested calls, mutual calls, and rich loop
tests have kernel-checked execution fixtures in addition to the general proofs.

## L7 checked register-only alternative

`RegisterOnly.compile capacity program` accepts straight-line entry bodies with
primitive statements and calls to straight-line helpers. Helpers contain
primitives and a final return, with no calls. Structured control, recursive
helpers, and nested helper calls are rejected explicitly by this backend; the
baseline compiler continues to support the complete source language. Entry
expressions such as `f(g(x))` work when both helpers are eligible, because their
left-to-right lowering produces sequential entry calls.

This eligibility choice keeps the alternate backend useful for arithmetic,
loads, and other fixed straight-line routines without constraining the main
language. The user-authorized alternative perfect-hashing query will use the
baseline compiler and a separated stack reservation, so P0 does not depend on
extending register-only eligibility to branches.

The alternate ABI uses `capacity+2` registers: result 0, status 1, caller locals
from register 2, followed by a disjoint helper interval. The helper interval is
reused by sequential calls. `Compiled.demand` is caller slots plus the largest
helper slot count. Excess demand is an explicit compilation error. Arguments
are copied before the inline body executes, so permutations, repeated arguments,
and a result overwriting an argument preserve source behavior. Helpers need no
saved link, stack header, or spill access.

`compiled_returns` proves exact termination in `Compiled.code.size` instructions,
including halt, with exactly the source trace and final application memory.
`contract` transfers source contracts and their interrupted-prefix policies.
`compiled_readOnly` proves unchanged memory and the absence of writes in every
prefix for a read-only source proof. No stack reservation, stack initialization,
or word-sized return-address premise appears in these theorems. The proofs
operate on independent source derivations and the authoritative machine.

The general overlap example uses nine local registers plus result/status and
takes fifteen instructions at every word width. Its proof covers dirty initial
registers, swapped/repeated arguments, an overwritten argument, and a caller
local live across two calls. Further fixtures retain a real application load in
the full target trace and check register shortage, recursion, and control-flow
rejection. `Compiled.report` exposes instruction count and register demand.
