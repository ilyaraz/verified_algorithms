# Hand-off I: a verified word-RAM language and compiler

## 1. Purpose, scope, and freedom to redesign

This note specifies a fresh Lean development of a word-RAM machine, symbolic
assembly, a small C-like language, a compiler, and reusable correctness and
resource proofs. It is self-contained: it assumes ordinary familiarity with
Lean, inductive definitions, finite sets, and elementary mathematics, but no
particular repository, application, earlier implementation, or paper.

The deliverable is an executable toolchain whose theorem statements describe the
same programs that users can inspect and run. A client should write an algorithm
in the DSL, prove a source contract, and obtain a theorem about actual machine
instructions, memory effects, randomness, and stack use.

Preserve the semantic guarantees in this note. Choose fresh names, module
boundaries, AST encodings, frame layouts, register numbers, proof relations, and
automation. None of the example representations or suggested proof orders is a
required implementation. In particular, numerical costs must be derived from
the new compiler. Reproducing another compiler's instruction array is not a goal.

The baseline language supports arbitrary self-recursion and mutual recursion.
There is no syntactic recursion budget or call-graph acyclicity requirement.
Successful executions nevertheless need enough *finite ordinary memory* for
their live stack. The compiler must also implement safe stack exhaustion.

A useful completion package contains:

- An executable machine and assembler, with exact execution and trace semantics.
- A checked source language with independent semantics and readable notation.
- A total, deterministic compiler with explicit layout metadata.
- Finite-execution, exhaustion, prefix-safety, and progress-sensitive simulation.
- A sound compositional proof interface for functional and resource contracts.
- Generic array and search routines and representative recursive examples.
- A separate checked register-only compilation path for suitable programs.
- An explicit compiled-code export and a documented trust/assumption audit.

Keep the executable foundations independent of algorithm-specific mathematics.
A small standard-library dependency is desirable for words, machine execution,
syntax, compilation, and deterministic proofs. Finite probability can live in a
separate generic layer using a mathematical library.

## 2. Machine values and instruction semantics

Fix a natural word width `w`, and write `U = 2^w`. A word represents an unsigned
integer in `[0,U)`. A data address is a word. Define conversion from a natural
number by reduction modulo `U`; this is also how immediate literals are read.
The machine may be defined at width zero, although clients needing nonzero
words will require positive width.

Use these precise arithmetic operations:

| Operation | Meaning on unsigned representatives |
| --- | --- |
| Addition | `(x + y) mod U` |
| Subtraction | `(x + U - y) mod U` |
| Multiplication | `(x * y) mod U` |
| Unsigned remainder | `x mod y`, with remainder by zero equal to `x` |
| Logical right shift | `floor(x / 2^c)`, where `c` is the full unsigned shift operand |
| Equality/inequality | Equality/inequality of words |
| Unsigned order | Order on representatives in `[0,U)` |

A shift count at least `w` produces zero. Do not mask the shift count. These
choices matter for programs that use a shift of exactly `w`. An executable shift
can use the host's natural-number shift; its specification need not compute an
exponentially large divisor.

The cost model is a word-RAM: every fetched instruction costs one, including
multiplication, remainder, shifts, branches, calls, and the terminating halt.
This is an explicit mathematical machine model. It does not claim unit bit-cost
for operations on arbitrary-precision integers, nor bound Lean evaluation time.

A sufficient instruction set consists of move; the arithmetic operations above;
ordinary load and store; addressed random load; conditional branch; direct jump;
direct call with a destination link register; indirect jump; and halt. Immediate
and register operands suffice. Evaluate *all* operands against the pre-instruction
state, including when a destination aliases an operand.

Choose a fixed finite register file with `R` words. Its size is independent of
input length, word width, and recursion depth. Program code is a finite array of
instructions. A convenient state has a natural-number PC, the register file,
and ordinary memory. The current PC is control metadata; code pointers saved by
a compiled call are words and therefore require representability proofs.

A minimal call instruction has the following meaning:

```text
call link, target:  link := word(pc + 1); pc := target
jumpIndirect x:    pc := unsigned(value of x)
```

Neither instruction allocates memory or saves other registers. Recursion is
implemented by emitted ordinary loads/stores and pointer operations. The target
state must not contain an uncharged, unbounded host-language return stack.

Ordinary memory and random memory are separate total functions from addresses to
words. A store changes exactly one ordinary cell. Random memory is immutable and
is supplied as a fixed parameter `rho` to execution. Numerical equality between
an ordinary and a random address does not make them the same storage.

Give malformed programs total observable semantics: for example, fetching
outside the code array faults. A wrapped link remains a word; an indirect jump
uses its unsigned value. Compiler correctness proves such undesirable behavior
unreachable under its premises. It must not redefine raw machine behavior only
for compiled programs.

## 3. Execution, observations, and regions

Provide both a deterministic one-step function and a relational view of it. A
continuing step records its successor and zero or one memory event. Use event
tags that distinguish ordinary read, ordinary write, and random read, retaining
the address and observed/written value. Branches and arithmetic have empty
memory traces.

Define finite continuing executions with an instruction count and concatenated
trace. Define successful termination by a finite continuing execution followed
by a halt; include that halt in its time. A fuelled evaluator should return its
state, actual steps, complete trace, and stop reason. Zero fuel means evaluator
exhaustion. An invalid fetch can cost zero because it executes no instruction;
state this convention consistently. Earlier work and effects survive every stop.

Establish these general results early:

1. Determinism for a fixed program, initial state, and `rho`.
2. Composition of finite executions and equivalence with the evaluator.
3. Stability once an execution has halted or faulted, given more fuel.
4. Exact accounting for exhausted prefixes and the final halt.
5. Ordinary-memory framing outside written addresses.
6. Agreement/locality: another initial memory or random image gives the same
   execution when it agrees on the cells the execution actually reads, with
   suitable treatment of earlier writes.
7. Access-policy preservation for every prefix of a certified execution.

Distinguish normal return, a language runtime error such as stack exhaustion,
a malformed-machine fault, and exhaustion of an external evaluator budget.
An algorithm's returned failure value is another ordinary result. These outcomes
must not be conflated in public contracts.

Represent a region mathematically by a base and length, with half-open interval
`[base, base + length)`. Define fit, disjointness, containment, agreement of
memories on a region, and an array assertion. Ordinary logical regions can end
at `U`. If an implementation keeps an exclusive endpoint in a word, require
that endpoint to be *strictly* below `U`, or use a different justified encoding.
Record this choice rather than letting conversion to words silently wrap it.

An access policy gives allowed ordinary reads, ordinary writes, and random reads.
Prove frame results from policies. For a loop over a region, relate a natural
index invariant to the actual word address, proving each intermediate arithmetic
operation fits when wrap is unintended. Intentional wrapping arithmetic remains
available without such a hypothesis.

Define resource observations separately:

- Actual instructions, including administrative compiler work.
- Ordered random reads, distinct random addresses, and their counts.
- Ordinary locations touched, permitted reservations, and retained regions.
- Stack high-water mark, including transient setup states.
- Fixed code size and register count.

A reservation is an upper bound on storage a run may use; it need not equal its
actual touched footprint. Count the union of live ordinary reservations plus
register storage for a peak-space claim. Report code and random-memory capacity
separately. Counting only explicit application stores misses stack and metadata.

## 4. Finite addressed randomness

At fixed width, choose `rho` uniformly from all functions `Word w -> Word w`.
This is a finite probability space. Equivalently, each of the `U` cells holds an
independent uniform word. A read of an already read address returns the same
value. Independent cells can contain equal values.

For a function `f` on a finite nonempty space `Omega`, define expectation as
`sum(f omega) / |Omega|`, interpreting counts as real numbers when necessary.
Define event probability by averaging its indicator. This supplies linearity,
monotonicity, product averaging, the union bound, and Markov's inequality. These
can be developed through an existing finite-distribution library with explicit
bridges to the machine's law.

Prove coordinate and block laws: distinct addresses have a uniform product law;
disjoint blocks are independent; conditioning on values in one block leaves the
other block uniform. For adaptive access, the history must depend only on
previously exposed cells, and the next address must be fresh relative to that
history. Merely asserting that an address is fresh without controlling what was
conditioned on is insufficient.

All deterministic execution theorems quantify over every fixed `rho`. Expected
resource theorems fix the source program, input, layout, and initial state
independently of `rho`, then average executions. Compiler simulation preserves
the ordered random events, allowing pointwise execution bounds to be averaged.
The compiler itself introduces no random reads.

Finite memory does not provide an infinite tape of fresh trials. Generic search
libraries must expose finite address budgets. A client can prove total search
using a finite random phase followed by a deterministic terminating continuation.
Probability arguments do not manufacture a runtime seed, address, or result.

## 5. Symbolic assembly and linking

Use symbolic labels for branch and direct-call targets. An assembler should
resolve a finite list of declarations deterministically, rejecting duplicate
labels, unresolved labels, and any other declared static errors. A two-pass
scheme suffices: first compute label positions, then encode instructions.

Prove the length/layout and fetch lemmas needed to reason about a linked block:
its entry label denotes its first instruction; local labels and continuations
resolve correctly; fetching within the block returns the intended instruction;
and distinct generated fragments do not overlap. Handle labels at boundaries
explicitly, especially a label at the end of the program with no instruction.

A caller continuation is the address after its call instruction. It must be a
valid linked continuation and must fit in a saved word. A convenient sufficient
condition is that the entire linked code extent is below `U`. Other formulations
are acceptable if every saved pointer is covered.

Simple relocation changes the PC and direct jump destinations. It does not by
itself relate programs containing saved code pointers: relocating a call changes
the saved link, and an indirect return depends on that value. Either restrict a
simple relocation theorem to an appropriate instruction subset, or formulate a
relation that also translates code pointers. Proving compiled blocks against the
final linked environment is a useful baseline.

Keep direct runtime calls distinct from textual inlining. Replacing a block's
halt with a continuation is a separate transformation with its own hypotheses.

## 6. Source language and independent meaning

A small core can use local-variable references and literals as atoms, primitive
operations with explicit destinations, and structured statements:

```text
statement = skip | primitive | sequence | conditional | loop
          | call(destination, function, arguments) | return(value)
function  = parameters + local slots + body
program   = finite function table + designated entry
```

Function references identify entries in a finite table. Thus a recursive program
is finite data, not a recursively expanded Lean term. Every invocation has its
own locals. Parameters begin initialized; other locals begin uninitialized.
Return leaves the current invocation immediately, including from inside loops
and nested branches.

Define a static checker for names, duplicate declarations, arity, local indices,
definite initialization, and result discipline. A conservative checker can
require a syntactic return after a loop, even if a later proof shows that loop
always returns internally. Well-formedness ensures structural safety, not
termination or correctness of arbitrary computed memory addresses.

Define source small-step semantics independently of target code. A configuration
can contain the current statement/control position, locals, ordinary memory,
and explicit logical continuations/activations. Define ideal execution with no
capacity limit and capacity-aware execution that accounts for live frame sizes.
The capacity policy may be supplied by compiler metadata; source arithmetic,
branching, calls, and memory effects must retain their independent meanings.

For capacity-aware semantics, fix the timing of argument evaluation relative to
the capacity check. A useful policy evaluates arguments first and then checks
space before the first new-frame write. This preserves argument effects when
allocation fails. Early-return and runtime-error propagation through enclosing
statements must be explicit.

Define a finite derivation judgment for source execution and connect it to the
small-step semantics. Define divergence through arbitrarily long executions or
an infinite transition sequence. A fuelled source interpreter is helpful for
examples, but interpreter fuel is never a language recursion limit.

A source derivation may carry ghost instruction and stack annotations. Those
annotations can be computed from verified compilation templates. Functional
semantics must not be defined as “whatever the compiler runs,” which would make
compiler correctness circular.

## 7. A pleasant DSL with a small semantic core

The surface language should support named functions, parameters, mutable locals,
blocks, `if`/`else`, `while`, early `return`, calls in expressions, and statement
calls whose result is discarded. Arithmetic, comparisons, `load`, `store`, and
addressed `random` should have clear syntax and precedence. Explicit base-plus-
offset arrays are sufficient for a first implementation.

For example, this is illustrative syntax, not a prescribed Lean parser:

```c
fn sum(n) {
  if (n == 0) { return 0; }
  let saved = n;
  let smaller = sum(n - 1);
  return saved + smaller;
}
```

Specify evaluation order for rich expressions, preferably left-to-right. Lower
effects to explicit core statements and temporary locals. Evaluate loop-condition
setup on every test, not just once before the loop. Preserve argument evaluation
order and evaluate each argument exactly once. State the treatment of boolean
operators if added, particularly short-circuit behavior.

Collect function signatures before lowering bodies so forward references and
mutual recursion work. Preserve useful source names/positions for diagnostics,
while using stable identifiers internally. Report unknown variables, shadowing
rules, arity errors, uninitialized reads, and missing results near their source.
A small language may reject shadowing instead of implementing it initially.

In an embedded Lean DSL, elaboration can produce ordinary AST constructor terms.
Expose the resulting core and compilation report for inspection. Kernel checking
then verifies theorems about that exact term. This does not automatically prove
that a buggy parser implements the intended surface-language meaning: give the
front end an explicit lowering specification and validation examples, and prove
surface-to-core preservation if surface semantics is part of the trusted public
interface. Avoid an opaque textual program hidden behind a correctness claim.

No dependent proof object or ghost set may supply executable computation. Loop
invariants, termination measures, and cost certificates are proof-side objects.

## 8. Calling convention and baseline compiler

Freeze an ABI as an interface before proving the compiler. Choose register roles
for stack/frame pointers, stack bounds, return link, result, runtime outcome, and
scratch calculations. Register numbers and parameter transport are design choices.
Do not unnecessarily limit ordinary function arity to the number of entry-argument
registers. A verified public adapter may marshal larger entry interfaces.

A practical first compiler assigns parameters, locals, and expression temporaries
to fixed frame slots. Each activation stores enough metadata to restore its caller
and return continuation. Its frame size is a computable function of source syntax.
A different allocator is fine if it proves the same preservation obligations.

For an upward-growing stack, maintain `base <= sp <= limit`, where `sp` is the
first free cell. Check `frameSize <= limit - sp` before allocating or writing a
new frame. The invariant makes subtraction meaningful. Checking a wrapped
`sp + frameSize` after the fact is unsafe. Include frame headers and all transient
argument stores in the checked extent. Exact-fit capacity must succeed.

The call/return protocol must establish:

- Argument values are preserved until copied, including repeated/overlapping
  arguments and expressions that call other functions.
- The caller's live locals survive a nested or recursive call.
- Return links and caller-frame metadata are initialized before use.
- Returning releases exactly the callee frame and transfers the result correctly.
- Every successful return restores the expected continuation and stack state.
- Insufficient capacity reaches a defined exhaustion outcome before writing
  outside the reservation; earlier effects remain visible.

Freed frame words can remain dirty. No theorem may assume they are zero, and no
implicit clearing operation is free. Application loads/stores must be separated
from compiler stack storage; numerical address computation can otherwise alias it.

Compile syntax structurally and emit one copy of each ordinary function body.
Resolve recursive calls through linked labels rather than recursively compiling
the callee at each call site. Add entry, normal-exit, and runtime-error code.
The compiler returns a finite instruction array and metadata, or an explicit
static error. It must terminate on valid recursive and divergent programs.

Compiled code, register budget, and frame layouts depend only on source syntax
and chosen compilation options. Word width, runtime inputs, random contents,
and successful termination proofs do not specialize the code. Width-dependent
fit conditions belong to execution theorems. Keep generated code and metadata
computable without classical choice.

Useful metadata includes function entries/extents, frame sizes, parameter/local
placements, continuation labels, and template lengths. Prove metadata correctness;
do not treat an unverified report as the basis for resource claims.

## 9. Simulation and resource transfer

The main state relation connects source activations and locals to target frames,
logical continuations to linked return addresses, and application memory to target
memory outside the stack. It must cover intermediate instruction sequences,
including partially written frames and epilogues, as well as function boundaries.

Organize local proofs around semantic operations: atom evaluation; each primitive;
tests and control flow; argument setup; frame installation; callee return; caller
resumption; entry and exit. Compose these into the whole-program theorem. This
organization should let client proofs ignore target PCs and individual spill stores.

The successful finite-execution theorem should have this content:

```text
Compilation succeeds; the machine/source initial states correspond.
Code addresses, frame sizes, and generated constants fit the word width.
Application effects are separated from the supplied stack reservation.
A finite source execution returns v, with trace tau and resource bounds.
The stack bound fits the supplied capacity.

Therefore the actual target reaches its normal halt, returns v,
obeys the transferred instruction bound including entry and final halt,
preserves application memory as specified, has projected trace tau,
and stays within its stack bound at every intermediate instruction.
```

Define whether a source contract's time bound includes the entry wrapper and its
own frame; supply an explicit conversion when it does not. Likewise distinguish
“additional stack below this activation” from “total live stack including it.”

Projection removes only compiler ordinary-memory events inside the separated
stack region. It retains all application effects and *all random events*, even
when their numerical address lies in the stack interval. Prove the full target
access policy separately; projection cannot excuse an out-of-bounds compiler
write. A source no-store property implies target application preservation, not a
global target no-write trace when ordinary frames are used.

Also establish the following interfaces:

- **Capacity-aware simulation:** an exhausting source call reaches the designated
  runtime exhaustion outcome with the appropriate preceding effects and costs.
- **Prefix safety:** arbitrary interrupted executions, including argument setup,
  respect the full access policy and do not produce malformed-machine faults.
- **Ideal/capacity agreement:** ideal runs whose live-stack bound fits execute
  identically in the capacity-aware semantics.
- **Progress-sensitive divergence:** under enough capacity for every prefix, an
  infinite source computation yields an infinite target computation. A simulation
  admitting unbounded zero-instruction stuttering does not establish this.

A ranking argument for administrative stutters or a productive-step decomposition
can provide the last result. An endlessly recursive ideal run that grows its stack
is instead covered by finite-capacity exhaustion; finite RAM cannot match its
unbounded stack forever.

For costs, sequence adds time; alternatives use the reached branch; a loop sums
reached iterations and condition tests; a call charges argument evaluation,
checks, saves, the callee, restores, and result assignment. Stack peaks use maxima
across sequential phases and addition across simultaneously live activations.
Bound transient allocation as well as stable frames. State all of this numerically
before deriving asymptotic corollaries.

## 10. Compositional verification and generic libraries

A useful total source contract asserts the existence of an actual finite source
derivation, its result/memory/trace postcondition, an instruction allowance, and
a stack bound. State preconditions over parameters and initial memory separately
or as an implication. This avoids proving a postcondition only for executions
that might never terminate.

Provide sound rules for primitives, sequence, both branches, loops, early return,
calls, framing, and consequence. Ordinary partial correctness can be a separate
interface; label its termination guarantees accurately.

For total loops, use an invariant and a well-founded measure, allowing either
continuation with a decreased measure or early return. For recursive and mutually
recursive functions, assumptions about recursive calls must be justified by
well-founded induction on an input/state measure or by another sound framework.
An unrestricted assumption of the function's own total contract is circular.
Prove time and stack recurrences alongside functional correctness.

Build proof automation on these sound rules. It may normalize local lookups,
assemble finite derivations, discharge routine arithmetic, and generate proof
obligations. It must leave domain invariants, separation, representability, and
termination assumptions visible. Generated proof terms are kernel-checked; no
unchecked verification-condition oracle belongs in the trusted path.

Useful generic routines/rules include:

| Component | Contract content |
| --- | --- |
| Fill | Initializes a region, exact/affine time, preservation outside it |
| Copy | Copies an array with explicit disjointness or specified overlap semantics |
| Traversal | Per-element callback contract, accumulated work, maximum nested stack |
| Capped search | Actual reached attempts, first success or truthful exhaustion, addressed sample prefix |
| Exhaustive search | A successful finite candidate prefix proves termination; candidate generation is executed and charged |
| Recursive sum or tree traversal | Non-tail call, caller value live across it, separate time/stack recurrences |

A retry rule must preserve the stopping-time information needed by clients:
charging the full cap on every successful run can destroy an expected-time proof.
Probability lemmas can reason about a pure candidate/acceptance model, while an
execution theorem proves that the source routine implements that model and cost.

## 11. A separate register-only path

Some clients require a target trace with no writes anywhere. Provide a checked
backend or transformation for a clearly specified subset. For example, begin
with straight-line functions and acyclic eligible helpers, then extend coverage
as independently proved features.

The checker must establish finite register demand, absence of spills/frames,
correct argument copying, preserved caller-live values, and correct result
placement. Argument permutations, repeated arguments, and destinations aliasing
arguments need explicit handling. Reject excessive demand or unsupported control
flow with a diagnostic. This rejection does not restrict the baseline language's
support for recursion and loops.

Prove full source/target trace correspondence for this backend. A no-write source
contract then yields a genuine target no-write theorem. If branching and early
returns are supported, prove them; if they are outside the certified subset,
report that limitation. Do not infer coverage merely because a routine happens
to execute without a stack in a test.

## 12. Trust boundary, exports, and review

Store programs as explicit computable data. A certified package can contain code,
its public interface, and a theorem proving its specification. An existential
“there exists a program” statement follows from that package, rather than being
used with noncomputable choice to produce the implementation.

Document accepted foundational Lean axioms for mathematical proofs. Reject
placeholders, project-specific assumed correctness axioms, and unchecked native
proof oracles. Audit executable definitions separately: the stricter useful
standard is that code generation, code arrays, evaluators, and serializers have
no axiom dependencies, including hidden dependencies in proof-bearing values.
Pin a reproducible toolchain, but do not make a particular old toolchain version
part of the mathematical specification.

Export the exact compiled instruction array and ABI. Prove a round trip or equality
with the certified code, and check regeneration. A faster external emulator, a
native-code backend, or an external random provider has its own refinement/law
obligation; the machine theorem does not automatically certify it.

Suggested delivery order and acceptance evidence:

1. **Machine and observations:** exact primitive behavior, halt/fault/fuel
   distinctions, dirty-memory and boundary examples, frame and agreement lemmas.
2. **Assembly and calls:** deterministic linking, nested manual calls, valid
   continuation links, and a clearly scoped relocation theorem.
3. **Source semantics:** checked recursive programs, determinism, evaluator
   agreement, early return, mutual recursion, and an infinite bounded-stack loop.
4. **Compiler:** each function emitted once, argument preservation, exact-fit
   stack success, one-word-short rejection before out-of-region writes.
5. **Generic proofs:** whole-program simulation, exhaustion and prefix safety,
   numerical instruction/stack transfer, and genuine progress for divergence.
6. **Client proof interface and DSL:** readable recursive/array programs verified
   without manual target-PC reasoning; diagnostics and expression-order checks.
7. **Libraries and register-only backend:** search contracts, finite random-block laws,
   register-only alias tests, and explicit subset rejection.
8. **Packaging:** complete assumption ledger, code/resource reports, executable
   and theorem audits, and certified exported artifacts.

Tests exercise the implementation; general theorems establish its guarantees.
Review in particular dirty/reused frames, a live caller local across non-tail
recursion, mutual recursion, argument aliasing, an early return inside a loop,
oversized shifts, remainder by zero, code-pointer fit, near-end stack limits,
zero-capacity entry, and repeated random reads. A clean reimplementation is
complete when these interfaces are independently usable by a new algorithm,
without importing any application-specific code or proofs.
