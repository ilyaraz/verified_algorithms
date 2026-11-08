# Design: a recursive structured word-RAM language

Status: design and implementation roadmap, 2026-11-08.
Implementation decisions and current progress: [RamLang contract](ramlang-contract.md). This document
does not claim that the language, ISA extensions, or compiler theorems already
exist. The implementation names below are tentative.

Build a small C-like language embedded in Lean, compile it deterministically to
the project's word-RAM assembly, and prove source-level correctness and resource
bounds that transfer to the generated code. Support ordinary recursive and
mutually recursive functions from the outset. Perfect hashing is the first
substantial application; it must not be a dependency of the language library.

## Scope labels

- **LANG**: reusable language, machine, compiler, proof, or tooling work. It must
  be useful independently of perfect hashing and import no hashing modules.
- **PH**: integration with the existing perfect-hashing development. Some ports,
  such as multiply-shift evaluation and deduplication, remain reusable algorithm
  libraries, but are not prerequisites for the language itself.

Milestones use `L0`–`L7` and `P0`–`P3` to avoid confusion with the existing
[perfect-hashing roadmap](perfect-hashing-plan.md)'s `M0`–`M9` milestones.

## 1. Requirements and initial choices

| Area | Proposed choice | Scope |
| --- | --- | --- |
| Embedding | Inductive syntax in Lean; C-like notation elaborates to that syntax. | LANG |
| Runtime values | Existing `Word w`; unsigned comparisons and existing wrapping arithmetic. | LANG |
| Memory | Explicit word loads/stores and addressed reads of immutable random memory. | LANG |
| Control flow | Sequencing, conditionals, loops, named function calls, and return. | LANG |
| Recursion | Self-recursion and mutual recursion, with no static depth limit. | LANG |
| Calling convention | Stack frames in ordinary RAM, a fixed register set, explicit argument/result transfer. | LANG |
| Compilation | Computable, deterministic, finite output; each ordinary function body emitted once. | LANG |
| Proofs | Independent source semantics, compiler simulation, and a sound source program logic. | LANG |
| Resources | Actual target instructions, stack high-water mark, data footprints, and random accesses. | LANG |
| Application | Reimplement query, construction trials, and construction orchestration in the language. | PH |
| Compatibility | Preserve dictionary behavior and memory guarantees; explicitly re-establish numerical bounds for new code. | PH |

The first language need not provide function pointers, address-taking of locals,
heap allocation, structs, exceptions, concurrency, or an optimizing compiler.
Arrays can initially be explicit base-plus-offset operations. These exclusions
do not restrict recursion. Tail-call optimization is optional, not a prerequisite
for recursive calls or a substitute for them.

### What unlimited recursion means

There is no language-level recursion budget, acyclic-call-graph requirement, or
compiler unrolling limit. Recursive programs are finite syntax referring to a
finite function table. Compilation visits function bodies; it does not execute
or recursively expand calls.

At a fixed width `w`, ordinary RAM still has only `2^w` word addresses. Therefore
the language permits arbitrary recursion depth, but a particular machine run
has finite stack capacity. State both of these guarantees:

1. With sufficient stack space, compiled execution implements the source
   execution, including recursive calls and their resource bounds.
2. Without sufficient stack space, generated code reaches a defined
   `stackExhausted` outcome before writing outside the reserved stack region.

An infinite source execution that continually grows its stack cannot be matched
forever by a fixed finite-memory machine. An infinite execution with bounded
stack use can be. Use capacity-aware semantics for the complete implementation
theorem and relate it to the unbounded source semantics under a stack-fit
hypothesis.

Do not add an uncharged, unbounded Lean list of return addresses to the target
machine state. A logical list is appropriate in the source semantics and proof
relation; its target representation occupies ordinary words and incurs costs.

## 2. Source language and semantics — LANG

Illustrative surface syntax, not an existing parser:

```c
fn hash(seed, key, shift) -> word {
    let product = seed * key;
    return product >> shift;
}

fn clear(p, n) -> word {
    while (n != 0) {
        store(p, 0);
        p = p + 1;
        n = n - 1;
    }
    return 0;
}

fn recursive_sum(n) -> word {
    if (n == 0) {
        return 0;
    }
    let saved = n;
    let result = recursive_sum(n - 1);
    // A live local must survive the recursive call; this is not a tail call.
    return result + saved;
}
```

Use a small core with atoms, primitive operations, and explicit calls. Richer
expressions lower to temporaries with a specified left-to-right evaluation order.
Memory loads and random reads should be explicit operations so their order is
visible. All operands of a primitive use the values before that primitive.

Schematic representation:

```text
Atom      := local variable | word literal
Primitive := move | arithmetic | load | store | random_load
Stmt      := skip | primitive | sequence | if | while | call | return
Function  := parameter list + local declarations + body
Program   := ordered finite function table + entry function
```

Start with one word-valued result per function and fixed arity at each function.
An early return propagates through surrounding sequences and loops. Reject
undefined functions, duplicate names, incorrect arities, and reads of
uninitialized locals. Every successful function path must return a value.
Mutable locals have invocation-local meaning, including across recursive calls.

Runtime arithmetic follows [the machine reference](word-ram.md), including
oversized shifts and remainder by zero. Natural-number quantities in proofs are
ghost values. Runtime address arithmetic is still word arithmetic: array bounds,
counter bounds, and absence of unintended wrap require explicit proofs.

Define small-step source semantics with a continuation and a stack of
activations. Derive a finite-execution judgment for compositional proofs. This
supports recursive and diverging programs without asking Lean's termination
checker to accept an arbitrary recursive interpreter. A fuelled interpreter is
useful for examples; its fuel is not a source-language recursion limit.

Keep functional source semantics independent of the compiler. Separately define
resource accounting using the compiler's verified frame layouts and instruction
templates. Proof annotations, loop invariants, mathematical sets, and termination
measures are erased and cannot supply runtime values or uncharged computations.

## 3. Machine extension, calls, and stack layout — LANG

### Instructions

Extend the authoritative [instruction set](../WordRam/Program.lean) and
[machine semantics](../WordRam/Machine.lean), rather than introducing a separate
interpreter used only for compiled programs. A small candidate extension is:

```text
call link, target     link := word(w, pc + 1); pc := target
jumpReg operand       pc := unsigned value of operand
```

Both instructions cost one, access no memory, and otherwise preserve state.
`call` has a literal target, resolved by the linker. A return is `jumpReg link`
after restoring the appropriate saved link. Stack saves, loads, checks, and
pointer updates remain ordinary charged instructions.

The PC is currently a `Nat`, whereas a saved return address is a word. Require
that all generated return addresses fit in a word. A convenient sufficient
condition is that the linked code extent is strictly below `2^w`. Check frame
sizes and other compiler-generated address constants for representability too.
These are width-dependent execution preconditions, not width-specialized code.
Old programs using only the original instructions need no new code-size premise.

Retain total low-level semantics even for malformed calls: an overflowing link
wraps like a word, and an invalid computed PC faults on the subsequent fetch.
The compiler theorem proves those cases unreachable for admissible executions.

### Baseline calling convention

Reserve a fixed collection of registers for stack pointer, frame pointer, stack
limit, link, result, runtime status, and temporary calculations. Initially put
parameters, locals, and expression temporaries in fixed frame slots. This avoids
requiring a register allocator before recursion works. The number of target
registers does not grow with recursion depth or input size.

Use an upward-growing stack with `sp` pointing to the first free word. Each
function has a statically computed frame size `F(f)`, including a saved caller
frame pointer, saved return address, parameters, locals, and required temporaries.
One concrete call protocol to freeze in L0 is:

1. Evaluate argument expressions into caller-owned slots.
2. Check `F(callee) <= limit - sp` before allocating or storing the new frame.
   The invariant `stackBase <= sp <= limit` justifies the subtraction. Do not
   first perform a potentially wrapping `sp + F(callee)` check.
3. Populate the new frame's arguments and saved caller frame pointer while the
   caller's locals are still accessible; install the new frame and stack pointers.
4. Execute `call`; the callee saves its incoming link before any nested call.
5. On return, load the saved link and caller frame pointer, release this frame,
   preserve the result register, and execute `jumpReg` to the caller continuation.
6. The continuation assigns the result to the caller's destination local.

Argument setup, partially initialized frames, early returns, and entry/exit
wrappers all belong in the simulation and peak-space accounting. Freed stack
memory may remain dirty. Prove each slot is initialized before use; do not assume
a zeroed stack or charge an implicit whole-frame clear.

For the generic interface, the caller supplies a fitting stack region separated
from application data. Source load/store policies must exclude this region.
Lacking an address-of-local operation does not by itself prove separation:
source code can still compute an arbitrary numerical address.

Stack exhaustion branches to a dedicated runtime-error halt without unwinding.
It preserves all earlier effects and respects the stack/data access policy.
Give runtime exhaustion a distinct status from an algorithm's ordinary return
value or bounded-search failure. Interpreter fuel exhaustion is a third,
evaluation-only observation, not a runtime error.

### Compatibility and relocation

Adding instruction constructors requires revisiting determinism, framing,
destination-register analysis, access traces, examples, and executable axiom
audits. Prove that execution of old instruction arrays is unchanged.

The existing [relocation theorem](../WordRam/Assembly.lean) changes only the PC
in the state. It does **not** extend unchanged to the proposed instructions:
relocating a call changes the saved link, and relocating an indirect jump requires
relating its stored code address. This is a theorem-design issue, not just two
extra cases in a proof.

Preserve the simple relocation rule for a checked subset containing the old
instructions, updating its callers with that premise. For compiled functions,
prove correctness against a final linked label map and relate saved return
addresses to that map. A more general code-pointer relocation theorem can come
later. Extend symbolic assembly with direct-call labels and check every linked
continuation. Do not confuse the current halt-to-continuation inlining theorem
with a theorem for runtime recursive calls.

## 4. Deterministic compilation and proof interface — LANG

Proposed pipeline:

```text
C-like Lean notation
    -> checked core syntax with stable variable/function identifiers
    -> explicit expression temporaries and fixed frame layouts
    -> symbolic assembly for each function and entry/error wrappers
    -> deterministic whole-program linking
    -> WordRam.Program R + layout/cost metadata
```

Use declaration order and a deterministic fresh-name supply. Self-recursive and
mutually recursive calls resolve through the function table; forward references
do not require expanding bodies. Compilation is a total Lean function returning
`Except CompileError CompiledProgram`. Valid recursive definitions are accepted
without a termination proof. Output code and metadata depend on source syntax,
not runtime inputs, width, random contents, or correctness proofs.

The main simulation relates source locals and activations to frame slots and
registers, application memory to target memory outside the stack, and logical
continuations to linked return addresses. It must describe intermediate states
inside call setup and teardown, not just function boundaries.

For a finite source execution, the intended theorem is schematically:

```text
compile(source) = success(compiled)
initial states correspond; code/frame constants fit; data/stack are separated
source execution returns v with application trace tau,
  charged time at most T and stack high-water mark at most S
S <= supplied stack capacity
--------------------------------------------------------------------------
compiled execution reaches the entry wrapper's successful halt,
returns v, uses at most T actual instructions,
has application trace tau after projecting out compiler stack accesses,
uses at most S stack words, and preserves memory outside permitted regions
```

The full target trace includes stack accesses. Define and justify the projection
using the separated stack region, and separately bound all compiler accesses.
Remove only ordinary reads/writes to that region; random reads at the same
numerical addresses belong to a different memory and must remain in the trace.
Never infer a target no-write guarantee merely from a source program that does
not call `store`.

Also prove capacity-aware exhaustion correspondence and prefix safety. For
divergence, provide a progress-sensitive simulation: administrative source steps
must not account for an infinite execution while the target stops making progress.
Under sufficient capacity for every prefix, an infinite source execution produces
an infinite target execution. Growing-stack executions instead use the explicit
exhaustion contract at finite capacity.

### Resource accounting

| Resource | Generic proof obligation |
| --- | --- |
| Time | Charge expression lowering, local spills, branches, calls, checks, frame operations, and final halt. |
| Stack | Bound the maximum sum of simultaneously active frame sizes, including transient call setup and wrappers. |
| Application memory | Transfer region policies and preservation outside declared writes. |
| Peak ordinary memory | Combine live application storage with stack storage without double-counting shared reservations. |
| Random reads | Preserve addressed random reads and values in order; compiler housekeeping introduces none. |
| Code/registers | Bound generated code from finite source syntax; use a fixed register budget. |

Time composes by addition; peak stack use generally composes by a maximum over
execution, not by summing all historical calls. For an activation that retains
its frame during a nested call, the bound includes `F(caller) + S(callee)`.
Recursive time and stack bounds can be expressed as separate recurrences.

Prove numerical bounds before asymptotic corollaries. Source costs may depend on
verified compilation metadata; counting each source statement as one target
instruction is insufficient. RAM instruction cost is distinct from the Lean
interpreter's runtime and from compiler/proof-checker runtime.

Quantify deterministic simulation over each fixed random image `rho`. If a
source-level pointwise upper bound is `B(rho)`, target time is at most `B(rho)`,
and the stack-fit premise holds for all relevant images, then existing finite
expectation machinery transfers `E[targetTime] <= E[B]`. Independence, fresh
addresses, and successful-retry analysis remain algorithmic obligations.

## 5. Source proof support and a stack-free backend — LANG

Provide sound rules for assignments, memory operations, sequence, conditionals,
loops, calls, early return, and framing. Function specifications describe
parameters/results, memory effects, time, and additional stack space. Use the
existing region assertions where possible; a large new separation-logic library
is not required initially.

Recursive functions need a sound recursive-contract rule. Partial correctness
must not assume termination. Total correctness requires a well-founded measure
or another justified argument; mutually recursive contracts must be checked
together. Time and space recurrences require proofs too. Allowing arbitrary
recursion does not make every recursive program terminating or resource-bounded.

Add a verification-condition generator only after these rules are proved sound.
Generated proofs should expose algorithmic invariants and arithmetic obligations,
while handling routine stack, variable, and control-flow bookkeeping.

The baseline stack compiler is sufficient for general recursive programs, but
it may write memory even for a source function that only reads application data.
Provide a second, verified compilation path for functions whose reachable calls
can be inlined and whose locals fit in registers. This path:

- has checked register assignments and no spills, frames, or stack accesses;
- handles argument aliasing, live caller values, and early returns;
- proves full trace preservation and applicable no-write guarantees;
- may reject unsuitable programs without restricting the general compiler.

This is generic support for memory-read-only routines. A recursive program does
not need to qualify for this path to be accepted by the language.

## 6. Perfect-hashing integration — PH

Reuse the existing mathematical models, collision and probability results,
admissibility reasoning, and representation predicates. Reprove the connection
from source executions to these models, then use compiler correctness to obtain
target execution theorems. Identical generated instruction arrays are not a
requirement; numerical cost constants must be established for the new arrays.

### Query

The current [query contract](perfect-hashing-query.md) requires exact membership
for every word, no random reads, no ordinary writes anywhere, and all reads
inside the retained descriptor. Even restoring a spilled value afterward would
not satisfy its no-write trace requirement.

Compile the query through the generic stack-free path. Inline eligible hash
helpers, prove the register-fit certificate, and retain the current external
query calling convention. Re-establish `StaticSet.QuerySpec` with an explicit
instruction constant; do not assume the current constant 33 survives compilation.
The query must still work after overwriting input, construction scratch, and any
former construction stack outside the retained region.

### Construction

Port hash evaluation/sampling, deduplication, rounding, clearing, grouping,
allocation, and child insertion before composing the constructor. Hashing and
deduplication ports remain in their own reusable algorithm modules.

Use ordinary calls where convenient. Perfect hashing does not need to become
recursive merely because the language supports recursion. With an acyclic call
graph in this application, a constant bound on simultaneously active fixed-size
frames may be available; prove it rather than assume it.

Reserve stack storage inside a proved-disjoint part of the supplied construction
scratch region if the existing capacity permits it. Otherwise propose revised
layout/admissibility constants explicitly and prove feasibility. Do not silently
add a required stack argument to the old calling convention or consume words
already used by grouping and compact keys. Entry wrappers initialize the internal
stack from the public layout.

Return-address fit also adds a code-length condition on the machine width. The
existing arithmetic admissibility assumptions need not imply that condition for
the larger generated program, even on empty input. Prove it from the application
preconditions or explicitly revise them and their nonvacuity theorem.

Constructor proofs must show stack exhaustion impossible under their stated
preconditions for every `rho`. Keep algorithmic retry-budget failure distinct
from runtime exhaustion. Include stack high-water use in peak memory and all
call machinery in actual instruction bounds. A released stack is not part of
the retained dictionary.

The current [bounded constructor](perfect-hashing-bounded.md) may return budget
failure. Migrating it does not establish exhaustive fallback or expected time to
successful construction. That remains a separate application milestone.

## 7. Milestone sequence

All milestones below are proposed. Finish the generic recursive compiler before
using perfect hashing as its correctness argument.

| Order | Milestone | Scope | Depends on | Concrete exit criterion |
| --- | --- | --- | --- | --- |
| 1 | L0 — Freeze semantics and ABI | LANG | — | Written source semantics, stack/exhaustion contract, register roles, frame layout, and theorem statements. |
| 2 | L1 — Extend the machine and assembler | LANG | L0 | Calls/returns execute; old-code semantics and revised relocation obligations are proved; existing checks pass. |
| 3 | L2 — Implement source syntax and semantics | LANG | L0 | Self/mutual recursion, early return, and finite-capacity exhaustion have independent executable/relational semantics. |
| 4 | L3 — Implement deterministic recursive compilation | LANG | L1, L2 | Finite shared function bodies, frame metadata, linking, and recursive execution examples work. |
| 5 | L4 — Prove compiler and resource correctness | LANG | L3 | State/trace simulation, instruction and peak-stack bounds, exhaustion, and prefix safety are checked. |
| 6 | L5 — Build the source proof interface | LANG | L2, L4 | Sound loop and recursive-call rules support a non-tail-recursive verified example with time/space bounds. |
| 7 | L6 — Add notation and reusable routines | LANG | L3, L5 | C-like syntax, proof automation, and generic array/retry examples use the verified pipeline. |
| 8 | L7 — Prove stack-free compilation | LANG | L4, L5 | Checked register-only routines preserve full traces and perform no compiler memory accesses. |
| 9 | P0 — Migrate membership query | PH | L6, L7 | Compiled query satisfies the existing semantic/memory contract with a proved constant time bound. |
| 10 | P1 — Migrate construction components | PH | P0 | Source deduplication, root/child trials, and allocation have contracts linked to existing models. |
| 11 | P2 — Migrate bounded construction | PH | P1 | One compiled constructor has bounded success/failure, stack sufficiency, prefix safety, and query-after-build theorems. |
| 12 | P3 — Complete successful total construction | PH | P2; remaining hashing M9 mathematics | Fallback guarantees success for every image, with expected linear total instruction work and complete space accounting. |

### L0 — Language, machine, and ABI contract [LANG]

Freeze the decisions in sections 1–4, especially return-address encoding,
exhaustion behavior, application/stack separation, and the distinction between
unbounded source recursion and finite machine capacity. Specify the minimum
register budget and entry wrapper. Write the intended theorem signatures before
building a large front end. Produce a compatibility checklist for affected
`WordRam` definitions and proofs.

### L1 — ISA and compatibility foundation [LANG]

Implement `call` and `jumpReg`, symbolic call resolution, and the old-code
conservativity theorem. Revise relocation lemmas with appropriate hypotheses;
audit register preservation and all instruction case analyses. Validate a manual
nested-call example that saves/restores links and preserves a live caller value.
Run the repository build and axiom audit. No source compiler correctness is
claimed at this milestone.

### L2 — Independent source semantics [LANG]

Implement core syntax, name/arity/initialization checks, source configurations,
and small-step semantics. Prove determinism for a fixed `rho`; connect a fuelled
interpreter to the relation. Support self-recursion, mutual recursion, early
return, and capacity-aware failure. State the relation to unbounded semantics.
Include a non-tail-recursive example and a bounded-stack divergent loop.

### L3 — Baseline compiler and linker [LANG]

Compile locals to frame slots, emit each function once, resolve recursive calls,
and generate entry and exhaustion wrappers. Expose frame sizes and code ranges
as metadata. Validate execution for nested calls, mutual recursion, live locals,
and stack reuse. Check exact-fit capacity and rejection of one additional frame
before it writes out of bounds. These executions validate the implementation;
they do not replace L4's general theorem.

### L4 — Simulation and resource preservation [LANG]

Prove primitive, control-flow, call-setup, return, and linking lemmas, then the
complete capacity-aware compiler theorem. Account for all internal stack
accesses, intermediate states, actual instructions, and stack peaks. Prove
application/random trace correspondence, exhaustion safety, prefix safety, and
the progress properties needed for divergence with sufficient capacity.
Derive successful `TerminatesIn` executions under a proved stack bound. Audit
executable compiler definitions and theorem assumptions.

### L5 — Compositional verification [LANG]

Provide contracts and sound rules for loops, calls, recursion, mutual recursion,
memory framing, costs, and stack use. Verify both an iterative array routine and
a non-tail-recursive routine with a caller local live across a call. Show that
these source proofs yield target theorems without manually discussing target PC
values or frame-slot stores. Prove any verification-condition generator sound.

### L6 — Surface syntax and generic library [LANG]

Add readable notation and diagnostics over the checked core. Publish generic
fill/copy/traversal contracts and a bounded-retry combinator with explicit sample
addresses and per-attempt cost. Keep probability results separate from execution
rules and import no hashing modules. Add readable generated-code and resource
reports so compiler choices can be inspected.

### L7 — Register-only compilation [LANG]

Implement checked register placement and eligible call inlining as an alternate
backend or verified pass. Prove that its generated code needs no stack and adds
no memory effects. Validate argument-overlap cases and preserved live values;
reject excessive register demand explicitly. This milestone is reusable for any
strictly read-only routine and does not remove recursive support from L3–L4.

### P0 — Query as the first application [PH]

Express the membership query and hash helper in source syntax, use L7, and prove
correctness against `Table.View` and `StaticSet.QuerySpec`. Cover empty,
singleton, and hashed children; occupied-slot nonmembers; zero and maximum keys;
and scratch/input overwrite. Publish the new code size and actual time bound.

### P1 — Source-level construction components [PH]

Port deduplication and the concrete construction helpers with explicit contracts.
Reuse collision mathematics, bucket models, and existing layout assertions.
Retain early rejection before overflowing energy calculations, charge dirty
memory initialization, and preserve completed siblings. Separate component
instruction costs from trial-attempt counts. Establish stack and clobber bounds
for each callable routine.

### P2 — Bounded constructor and public integration [PH]

Compose the components using source loops and calls. Prove actual success or
retry-budget failure for every random image, sufficient stack for both outcomes,
safe interrupted prefixes, preservation outside allowed regions, and the fresh
random-address schedule. Prove query-after-build using P0, including reuse of
the released stack. Re-establish a concrete fuel bound, pointwise work bound,
and total memory accounting. Keep the existing assembly implementation available
as a reference until these public theorems are established.

### P3 — Total success and expected preprocessing [PH]

Add deterministic seed enumeration after capped random attempts and prove that
it finds successful parameters. Transfer the pointwise compiled costs through
the finite random-memory analysis. Establish successful construction for every
image, expected `O(N+1)` instructions, constant query time, `O(d+1)` retained
words, and `O(N+1)` peak ordinary memory including stack. Include deduplication,
all rejected work, fallback, and final halt. This extends the algorithm beyond
the bounded-constructor migration; it is not needed to declare the generic
language and recursive compiler complete.

## 8. Suggested module boundaries

Tentative new paths:

```text
RamLang/                         # LANG; imports WordRam, never hashing
  Syntax.lean
  WellFormed.lean
  Semantics.lean
  Execution.lean
  Resources.lean
  CallingConvention.lean
  Compiler/Frames.lean
  Compiler/Lower.lean
  Compiler/Link.lean
  Compiler/Correctness.lean
  Compiler/StackFree.lean
  Logic.lean
  VerificationConditions.lean
  Notation.lean
  Library/                      # generic array/retry routines
  Examples.lean

Hashing/Source/                  # PH integration; reusable hashing routines
Algorithms/Dedup/Source/         # PH integration; reusable deduplication
DataStructures/PerfectHash/Source/
  Query.lean
  Trials.lean
  Bounded.lean
  Correctness.lean
```

Machine and assembly changes remain in `WordRam`. Existing mathematical modules
should not acquire dependencies on concrete compiled perfect-hashing programs.
Update the executable/theorem audit in [Checks.lean](../Checks.lean) as each
implementation milestone lands.

## 9. Main risks and completion criteria

| Risk | Planned treatment | Milestone |
| --- | --- | --- |
| Unlimited source recursion mistaken for infinite physical storage | Separate ideal and capacity-aware semantics; prove exhaustion or stack sufficiency. | L0, L2, L4 |
| PC values do not fit into saved word links | Explicit code-address fit and linked continuation invariants. | L0, L1, L4 |
| Existing relocation statements become false | Preserve a restricted old-code rule and use final linked addresses for recursive code. | L1, L4 |
| Source data aliases the compiler stack | Explicit region separation and access-policy premises. | L0, L4, L5 |
| Call setup or live locals are mishandled | State relations cover partial frames, argument evaluation, and preserved caller slots. | L3, L4 |
| Source costs omit compiler work | Template-based numerical accounting and per-run peak-stack bounds. | L4, L5 |
| Query acquires hidden stack writes | Certified stack-free compilation; preserve its full trace contract. | L7, P0 |
| Recursive contract reasoning is circular | Proved recursion rules; separate partial correctness, termination, time, and space. | L5 |
| New constructor silently needs more scratch or a wider word | Prove stack placement or explicitly revise admissibility and feasibility. | P1, P2 |
| Expected bounded work is mistaken for time to successful completion | Keep fallback and total-success expectation as a distinct milestone. | P3 |

The generic language is usable when recursive programs can be written, compiled,
and verified with target time/space and exhaustion guarantees independently of
perfect hashing. The migration is complete when source-level hashing proofs
produce the public target-level contracts, with no uncharged stack, randomness,
initialization, or mathematical advice. Use the standard repository build and
axiom audit for implementation milestones, plus focused execution examples for
the boundary cases described above.
