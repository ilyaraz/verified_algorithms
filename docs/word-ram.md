# Word RAM model and execution semantics

This library defines a word RAM in Lean with fixed-width unsigned words, a finite register file, mutable data memory, and a separate addressable read-only random memory. Programs are finite arrays of assembly instructions. Multiplication, unsigned remainder, and logical right shift are primitive unit-cost instructions.

Execution is deterministic once the random-memory contents are fixed. A separate probability layer chooses the entire random memory uniformly, which makes its cells independent uniform words. A repeated read of an address returns the same value. A store changes only ordinary data memory.

This reference specifies the machine's state, instruction semantics, execution costs, and probability model. It also documents the Lean interfaces and verified examples. Build instructions and a complete executable example follow the specification.

## Words, addresses, registers, and memory

All definitions live in the `WordRam` namespace. Let `w` denote the word width in bits, `R` the number of registers, and `U = 2^w`. Both `w` and `R` are natural numbers (nonnegative integers), fixed throughout an execution. In the Lean notation below, `A → B` denotes a function from `A` to `B`, and `x.toNat` is a word's unsigned integer value.

| Type or definition | Meaning |
| --- | --- |
| `Word w` | `BitVec w`, representing an unsigned integer in `[0, U)`. |
| `Addr w` | An alias for `Word w`. |
| `word w n` | Convert a natural number to a word by reducing modulo `U`. |
| `Reg R` | `Fin R`, the register indices `0, …, R-1`. |
| `Registers w R` | A function from registers to words. |
| `DataMemory w` | A function from word addresses to words. |
| `RandomMemory w` | A function from word addresses to words, passed read-only to execution. |

Both memories have exactly `U` valid addresses. Every address contains a word. There are no allocation instructions, uninitialized-memory errors, or invalid data addresses in this model. Each memory operation accesses one word; byte ordering and alignment do not arise.

The two memory types have the same underlying function type. Their separation is enforced by the instruction semantics: `store` updates the function in the mutable state, while `rload` reads the external `rho` parameter. Updating one persistent function does not mutate another function, even if they initially have equal contents.

`State w R` contains:

```text
pc   : Nat
regs : Registers w R
mem  : DataMemory w
```

`State.initial regs mem` sets PC to zero and preserves the supplied register and memory functions. `State.zero w R` is a convenience constructor that zeroes both. General theorems do not require zero-initialization. `update f a v` returns the function equal to `f` everywhere except at `a`, where it returns `v`.

The ordinary algorithmic interpretation uses `w > 0`. Definitions remain total at width zero: there is one word, zero, and one address. Zero registers are also allowed, so register-free programs such as `#[.jump 0]` are valid.

### Programs and control flow

`Program R` is `Array (Instr R)`: a finite, immutable array of instructions, indexed from zero. Lean's `#[...]` notation constructs such an array. Write `p` for the program and `rho` for the random-memory image. Both are passed separately to execution and remain fixed; neither is stored in the mutable state. Code occupies its own instruction array, outside both word-addressed memories. `load`, `store`, and `rload` cannot read or modify instructions.

The program counter (PC) is the state's `pc : Nat`. Fetch reads `p[pc]` when `pc < p.size`, where `p.size` is the number of instructions; otherwise execution faults with `invalidPC pc`. Each array element is one instruction, with no byte encoding or variable instruction length in this model. Program length is not constrained by the word-address space size `U`.

| Executed instruction | Next PC |
| --- | --- |
| Move, arithmetic, load, store, or random read | `pc + 1` |
| `.branch cmp x y target`, comparison true | `target` |
| `.branch cmp x y target`, comparison false | `pc + 1` |
| `.jump target` | `target` |
| `.halt` | No next instruction; the state is preserved. |

Both branch and jump targets are literal natural-number indices supplied when constructing the program. They are absolute indices, with no offset calculation or register-based target evaluation. Unlike word-valued data, the PC and targets do not wrap modulo `U`. The instruction set cannot read the PC into a register or perform arbitrary natural-number arithmetic through it.

For example, the existing `Examples.countdown` program has this layout, where `r0` names its only register:

| Index | Instruction |
| --- | --- |
| 0 | `.branch .eq (.reg r0) (.imm 0) 3` |
| 1 | `.sub r0 (.reg r0) (.imm 1)` |
| 2 | `.jump 0` |
| 3 | `.halt` |

At index 0, a zero register value sends execution to index 3; otherwise execution proceeds to index 1. Index 2 returns to index 0. This example supplies the target numbers `3` and `0` directly. `Assembly.compile` also accepts symbolic labels, resolves their instruction offsets, and rejects duplicate definitions or missing targets. Label markers occupy no instructions. `Instr.relocate`, `Embedded.append`, and the execution relocation theorems justify embedding assembled blocks between arbitrary neighboring code. A jump or taken branch may set an out-of-range PC, which faults on the next fetch. Falling off the final instruction also faults.

### Inputs and outputs

An execution is specified by `w`, `R`, a program `p`, a random-memory image `rho`, and an initial state. Inputs are encoded in the initial registers and ordinary memory. A program's correctness statement specifies that encoding and which registers or memory cells contain its output when it halts. There are no distinguished input/output registers, external I/O instructions, or automatic return values. `State.initial` starts at instruction 0; a caller can also supply a state with another PC, for example to resume execution.

## Arithmetic and the instruction set

Addition, subtraction, and multiplication retain the low `w` bits. For unsigned values `x,y < U`:

| Operation | Mathematical result |
| --- | --- |
| Literal `n` | `n mod U` |
| Addition | `(x + y) mod U` |
| Subtraction | `(x + U - y) mod U` |
| Multiplication | `(x * y) mod U` |
| Remainder, `y > 0` | `x mod y` |
| Remainder, `y = 0` | `x` |
| Logical right shift by `c` | `floor(x / 2^c)`; zero for `c ≥ w` |

`unsignedMod` implements remainder by forming a word from `x.toNat % y.toNat`. The theorem `unsignedMod_eq` proves that it equals Lean's `BitVec` remainder. This wrapper avoids an axiom dependency in the bounds proof of the pinned version's built-in remainder definition; it does not change the operation's result.

Multiplication followed by remainder can lose information before the remainder instruction. At width 4, `7 * 3` becomes 5, and taking the result modulo 5 gives 0. At width 8, the product remains 21 and the result is 1. Both executions are checked in `Examples.mulMod_overflow` and `Examples.mulMod_fits`.

The lemmas `add_toNat_of_lt` and `mul_toNat_of_lt` recover ordinary natural-number arithmetic when the corresponding sum or product is below `U`. `mod_lt` requires a positive divisor. A proof that uses nonwrapping arithmetic must establish the required bounds explicitly.

An `Operand R` is either `.reg r` or `.imm n`. Its evaluation reads one register or converts one literal. It cannot contain an expression tree, a Lean function, or a hidden computation. `Instr R` has the following constructors:

| Constructor | Effect |
| --- | --- |
| `.mov dst src` | Write the evaluated source to `dst`. |
| `.add dst x y` | Write the wrapping sum. |
| `.sub dst x y` | Write the wrapping difference. |
| `.mul dst x y` | Write the wrapping product. |
| `.mod dst x y` | Write the unsigned remainder, including the zero-divisor convention. |
| `.shr dst x count` | Shift logically by the full unsigned count, without masking. |
| `.load dst addr` | Read ordinary memory at the evaluated address into `dst`. |
| `.store addr src` | Write the evaluated source to ordinary memory. |
| `.rload dst addr` | Read the fixed random memory at the evaluated address into `dst`. |
| `.branch cmp x y target` | Jump to `target` when the comparison succeeds; otherwise advance PC. |
| `.jump target` | Set PC to `target`. |
| `.halt` | Terminate successfully, preserving the current state. |

`dst` is a register. Other data arguments are operands. Comparisons `.eq`, `.ne`, `.lt`, and `.le` test equality, inequality, less-than, and less-than-or-equal, respectively; ordering is unsigned. The PC changes according to the control-flow table above. Registers and memory cells not explicitly written by an instruction retain their values.

All operands use the **pre-instruction** register file. For example, `.load r0 (.reg r0)` reads the address stored in `r0` before replacing that register. Arithmetic source/destination aliasing and stores whose address and value use the same register are supported and checked.

There is no instruction that stores into random memory. A random value copied into data memory can be overwritten freely, without changing its original cell.

Register indices are checked by their `Fin R` types. Targets are unrestricted natural numbers, with validity checked dynamically at fetch as described above.

The code type is independent of word width. For a uniform algorithm, choose a fixed `R` and one program before quantifying over widths and inputs in its correctness theorem. Using the same type does not by itself forbid constructing a new program for every input; that distinction belongs in the theorem statement.

## Operational semantics and instruction accounting

`step p rho s` is the authoritative transition definition for program `p`, random memory `rho`, and current state `s`. Its result is one of:

```text
StepResult.next nextState optionalAccess
StepResult.halt
StepResult.fault (Fault.invalidPC pc)
```

It executes every instruction, including `rload`. Fixed `p`, `rho`, and `s` determine the result uniquely. `Step p rho s t access` is just the proposition that this function returns `.next t access`.

`run p rho fuel s` repeatedly applies `step`, with a natural-number evaluator budget `fuel`. Its result always contains:

```text
state  : State w R
steps  : Nat
trace  : List (Access w)
reason : StopReason
```

`StopReason` distinguishes `.halted`, `.fault reason`, and `.fuelExhausted`. Both faults and incomplete runs retain their last state and all work performed so far.

The accounting convention is exact:

- Each executed instruction costs one, including loads, stores, random reads, branches, multiplication, remainder, and halt.
- Zero fuel executes nothing and reports fuel exhaustion, even if the current instruction is halt or the current PC is invalid.
- Invalid fetch adds zero executed instructions. It is an evaluator stop, not an executed instruction.
- A jump to an invalid PC costs one. A later fetch detects the fault. If fuel ends immediately after the jump, the result is fuel exhaustion instead.
- Halt costs one and leaves PC, registers, and ordinary memory unchanged.

Thus a single halt instruction needs one unit of fuel. A continuing instruction followed by an invalid fetch needs two units of evaluator fuel to expose the fault, while the result's instruction count is one. Fuel is a budget for observation, not part of the machine state or a termination claim.

An access trace records only memory operations, in execution order:

```text
Access.dataRead address value
Access.dataWrite address value
Access.randomRead address value
```

Instruction fetches, register accesses, arithmetic, and control instructions have no memory-access event. Every executed instruction still contributes to `steps`. Traces and counters are semantic observations: programs cannot read them. A random read is always defined, but only the first read of an address reveals a new cell's value.

The cost model describes abstract machine instructions. It does not assert that Lean's interpreter, functional updates, trace construction, multiplication, or remainder run in constant wall-clock time. The interpreter is a reference semantics, not an optimized emulator for large workloads.

## Execution relations and reusable theorems

`Steps p rho n s t log` describes exactly `n` **continuing** instructions from `s` to `t`, with trace `log`. It excludes halt and fault. Its constructors use `Step`, so the relational interface is derived from the executable semantics.

`TerminatesIn p rho s k t log` means that some `n` continuing instructions lead to `t`, the instruction at `t` is halt, and `k = n+1`. `Terminates` existentially quantifies `k`, `t`, and `log`. `Diverges` means that every finite fuel budget reports fuel exhaustion. A faulting computation therefore does not count as divergence.

| Theorem | Guarantee |
| --- | --- |
| `step_deterministic`, `Steps.deterministic` | A fixed transition or fixed-length continuing execution has a unique result. |
| `Steps.trans` | Continuing execution fragments compose, adding lengths and concatenating traces. |
| `Steps.run_eq` | A proved fragment can precede any bounded continuation. |
| `steps_iff_run` | A continuing execution of length `k` is equivalent to the exact fuel-`k` exhausted result with its state and trace. |
| `terminatesIn_iff_run` | Exact terminating execution corresponds to a halted result with exactly that instruction count. |
| `terminates_iff_halted` | Termination is equivalent to a halted result for some fuel budget. |
| `diverges_iff_steps` | Divergence is equivalent to continuing execution fragments of every finite length. |
| `diverges_not_terminates` | A diverging execution cannot also terminate. |
| `run_steps_le` | Executed instructions do not exceed the supplied fuel. |
| `run_exhausted_steps` | A fuel-exhausted result has used the entire budget. |
| `run_stable` | Additional fuel preserves an already halted or faulted result exactly. |
| `run_resume` | A fuel-exhausted execution can resume from its last state, using the same random memory. |

For `r = run p rho fuel s` with `r.reason = .fuelExhausted`, the resumption equation is:

```text
run p rho (fuel + extra) s
  = (run p rho extra r.state).prepend r.steps r.trace
```

`RunResult.prepend` adds a prefix's instruction count and prepends its trace. It preserves the continuation's final state and stop reason. An exhausted result cannot be treated as stable under more fuel; it may subsequently halt, fault, or continue.

Memory and randomness theorems apply to all bounded runs, including unfinished and faulted runs:

| Theorem | Guarantee |
| --- | --- |
| `step_frame`, `run_frame` | Ordinary memory outside the write footprint is unchanged. Reading a cell does not invalidate this guarantee. |
| `step_random_consistent`, `run_random_consistent` | Every recorded random read returns the corresponding value from `rho`. |
| `repeated_random_read` | Two recorded reads at the same random address have equal values. |
| `step_random_agreement`, `run_random_agreement` | Changing random memory at addresses unread in the reference execution leaves the complete result unchanged. |
| `run_without_random_reads` | If an execution performs no random reads, its result is independent of `rho`. |

The agreement theorem allows adaptive addresses. Its hypothesis concerns the addresses actually read in the run under `rho`; it does not assume that the alternative execution already follows the same path. Its conclusion includes the entire resulting state, trace, instruction count, and stop reason.

To prove a new program correct, establish instruction or block facts using `step`, build continuing fragments with `Steps`, compose them with `Steps.trans`, and finish with a halt. Alternatively, small finite examples can be proved directly from `run`. Separate numeric invariants, memory predicates, and program execution facts so that arithmetic assumptions remain visible.

## Probability semantics

The type `RandomMemory w` allows any memory image. Uniformity is a property of the distribution `randomMemoryLaw w`, not a restriction on which images can be passed to `run`.

There are `U` word values and `U` addresses, hence `U^U` complete random-memory images. `randomMemoryLaw` is a uniform probability mass function (PMF) on this finite function space: each image has probability `1 / U^U`. It is implemented using Mathlib, and `randomMemoryLaw_apply` proves the stated mass.

`runLaw p fuel s` maps this PMF through the deterministic function `rho ↦ run p rho fuel s`. The program and initial state are fixed independently of the sampled image. Every resumed computation or subsequent phase within the same run must keep the same `rho`. A state already influenced by random reads must be modeled jointly with that memory, rather than paired with a newly sampled image.

An event is a predicate on memory images or run results. Write `Pr[E]` for the probability of event `E` under the specified law. The event API is:

| Definition | Meaning |
| --- | --- |
| `eventCount E` | Number of complete memory images satisfying predicate `E`. |
| `probability E` | Real-valued ratio `eventCount E / U^U`. |
| `runProbability p fuel s E` | Probability that the bounded run's result satisfies `E`. |
| `conditionalProbability E H` | `Pr[E ∧ H] / Pr[H]`. Use as conditional probability when `Pr[H] > 0`. |
| `expectedSteps p fuel s` | Average executed instruction count over all memory images. |

These are exact mathematical values, without floating-point rounding. `probability_eq_pmf` proves agreement with the real-valued mass assigned by `randomMemoryLaw`. `runProbability_eq_pmf` proves the analogous statement for `runLaw`. Event probabilities lie between zero and one; true has probability one and false has probability zero.

The definitions are noncomputable mathematical interfaces. They do not allocate a complete random memory, enumerate an astronomical sample space during normal execution, or provide an operating-system random-number generator. Deterministic evaluation uses a supplied function, as in the [complete example](#a-complete-example). Counting arguments prove distribution properties symbolically.

### Independent cells and partial observations

`Matches cells values rho` means that `rho a = values a` for every `a` in the finite set of addresses `cells`, where `values` assigns a word to each address. The values outside this set are irrelevant. Write `cells.card` for the number of addresses in the set. `extensionsEquiv` puts memories matching that table in bijection with arbitrary assignments to its complement. Consequently:

```text
number of matching images = U^(U - cells.card)
Pr[Matches cells values]  = 1 / U^cells.card
```

These are `count_matches` and `probability_matches`. `probability_matches_pos` shows that each such table is a possible observation, so conditioning on it is valid.

The main probability theorems are:

| Theorem | Statement |
| --- | --- |
| `probability_cell` | For fixed `a,x`, `Pr[rho a = x] = 1/U`. |
| `probability_distinct_cells` | For injective `addresses : Fin k → Addr w` and any assigned values, the joint probability is `1/U^k`. |
| `probability_two_cells` | Two distinct cells take any specified pair of values with probability `1/U²`. |
| `probability_repeated_cell` | At the same address, the probability of observing `x,y` is `1/U` if `x=y`, and zero otherwise. |
| `conditional_fresh_cell` | Conditional on `Matches cells values`, an address outside `cells` takes any specified value with probability `1/U`. |

Distinct addresses can contain equal values. Independence refers to the sampled coordinates, not a promise that all stored values differ.

For adaptive code, the next address may depend on earlier observations. The conditional fresh-cell theorem is the foundation for reasoning about such code: establish the observed table and show the chosen address is outside it. The current library does not include a general theorem translating arbitrary adaptive program histories into partial-table conditioning; that connection must be proved for the relevant program or added as a reusable result later.

The standalone probability checks at width one demonstrate masses `1/2` for one cell, `1/4` for a specified pair at distinct cells, zero for conflicting observations at the same cell, and conditional mass `1/2` for the other cell after one cell has been observed. `Examples.randomRoundTrip_probability` also connects the law to an actual four-instruction program.

### Expected bounded work

`expectedSteps p fuel s` averages `(run p rho fuel s).steps` over all `U^U` images, including runs that fault or exhaust their fuel. `expectedSteps_le` proves this expectation is at most `fuel`.

The register-free program `Examples.spin = #[.jump 0]` diverges at PC zero. `Examples.spin_diverges` proves this for every random memory, and `Examples.spin_expectedSteps` proves that its expected bounded cost is exactly the fuel budget. Unfinished work is therefore retained rather than counted as zero.

There is no definition or theorem here for a particular algorithm's unbounded expected running time. Such a result must handle nontermination and distinguish successful termination from faults.

## Resource observations

`RunResult` provides these derived observations:

| API | Meaning |
| --- | --- |
| `steps` | Number of executed instructions, including halt. |
| `dataFootprint` | Distinct ordinary-memory addresses read or written. |
| `writeFootprint` | Distinct ordinary-memory addresses written. |
| `randomAddresses` | Addresses of all random reads in trace order, including duplicates. |
| `randomReads` | Number of random reads. |
| `randomFootprint` | Distinct random-memory addresses read. |
| `randomBitsExposed` | `w * randomFootprint.length`. |

Footprints are lists with duplicates removed. Their order is not part of the resource interpretation. A footprint counts cells touched during the whole bounded execution; it is not a heap allocation count or a measure of peak live storage.

For an algorithm's writable-space bound, account for its ordinary-memory footprint and the fixed `R` registers. Program code, PC, external random memory, and semantic traces are excluded from writable workspace by convention. The total capacity of either memory is always `U` cells regardless of how many are touched.

Random reads cost time even when they revisit an address. Repeated reads do not expose additional independent word coordinates. The bit count records revealed coordinates; it is not a theorem about the Shannon entropy of a variable-length transcript.

## Consequences of finite words and random memory

At fixed `w`, the machine has only `U` independent random cells. A word-valued address counter wraps, and returning to an address reuses its value. To justify a random read as a fresh independent word, an algorithm must establish that the address has not been read before, under the observation assumptions described in the probability section. The model supplies no unbounded stream of fresh randomness.

Every complete image in the finite uniform space has positive probability. Consequently, for a fixed program, initial state, and width, almost-sure termination (termination with probability one) requires successful termination on every image. A single faulting or diverging image has positive probability. This follows from the finite sample space; the library does not provide a general unbounded termination-probability API.

Multiplication wraps before any later remainder, so proofs of mathematical modular products need no-overflow bounds or a different implementation. Reducing a uniform word modulo a positive integer `m` gives uniform residues in `0, …, m-1` exactly when `m` divides `U`: otherwise some residues have more preimages among the `U` word values than others. Uniform words therefore do not automatically give uniform residues.

The instruction set has no bitwise Boolean operations, left shift, full-width multiplication, allocation, or built-in calling convention. Programs requiring those operations must express them using the listed instructions or use an explicitly extended model.

## Regions, blocks, and verified array loops

`Region` uses natural half-open intervals and the strict fit condition
`base + size < 2^w`. `ArrayAt` describes occurrence lists without assuming
uniqueness or zeroed memory. The original `StaticSet` names re-export these same
assertions. `BlockSpec` composes exact `Steps` witnesses, instruction bounds,
and separate read/write/random permissions. `TerminatesIn.prefix_policy`
transfers a complete trace's permissions to every fuel prefix;
`TerminatesIn.noFault` excludes faults at every fuel budget.

`Arrays.program` assembles fill, copy, and read-only traversal loops using four
registers: source cursor, destination cursor, remaining count, and value/temporary.
Fill's first two body instructions are a register move and a store; copy uses a
load and a store; traversal uses a load and a register move. All modes then advance
both cursors, decrement the count, and jump back. Every mode executes exactly
`7*n + 2` instructions including the exit branch and final halt. The zero-count
case performs no memory access. Clear is fill with value zero.

`Arrays.fill_array` establishes the replicated output; `Arrays.copy_array`
establishes the copied occurrence list for separated, fitting source/destination
regions. `Arrays.iterate_frame` preserves all memory outside the destination,
and `Arrays.visit_memory` preserves the whole memory. `Arrays.trace_local`
proves every address lies in the appropriate interval; `trace_random` rules out
random reads. The hypotheses ensure increments reach representable endpoints,
without wrapping accessed addresses. These programs are independent of hashing.

## Build and check

The project pins Lean **4.24.0** and Mathlib revision **`f897ebcf72cd16f89ab4577d0c826cd14afaafc7`**. The committed Lake manifest pins transitive dependencies as well.

For Linux x86-64:

```sh
./bootstrap.sh
./check.sh
```

The bootstrap script downloads the official Lean archive, checks its SHA-256, extracts it under `.toolchain/`, and obtains Mathlib's build cache. It requires Bash, curl, Git, tar with zstd support, and `sha256sum`. The `./lake` wrapper uses only the toolchain in this repository and stores the Mathlib download cache under `.downloads/`. It does not modify shell profiles or install a global toolchain. Downloads and build artifacts are ignored by Git.

After bootstrap, `./check.sh` builds the library and check target, then executes the audit again even if Lake considers the check target current. Builds and checks then work offline.

An existing Elan installation can use the same project configuration with `lake exe cache get`, `lake build`, and `lake env lean Checks.lean` instead. The bundled bootstrap is specifically for Linux x86-64; other platforms should use their usual Lean installation.

## A complete example

The following program reads random cell 3, writes the value 99 to ordinary cell 3, and reads random cell 3 again. It uses two registers. This complete example can be saved as a Lean file in the repository and run with `./lake env lean your-file.lean`.

```lean
import WordRam

open WordRam

def r0 : Reg 2 := ⟨0, by decide⟩
def r1 : Reg 2 := ⟨1, by decide⟩

def demo : Program 2 := #[
  .rload r0 (.imm 3),
  .store (.imm 3) (.imm 99),
  .rload r1 (.imm 3),
  .halt]

-- A specified memory image for deterministic execution, not a random sampler.
def demoRandom : RandomMemory 8 := fun address => address + 1

def result := run demo demoRandom 4 (State.zero 8 2)

#eval (result.reason, result.steps,
  (result.state.regs r0).toNat, (result.state.regs r1).toNat,
  (result.state.mem (word 8 3)).toNat,
  result.randomReads, result.randomFootprint.length,
  result.randomBitsExposed)

example : result.reason = .halted ∧ result.steps = 4 ∧
    result.state.regs r0 = word 8 4 ∧
    result.state.regs r1 = word 8 4 ∧
    result.state.mem (word 8 3) = word 8 99 := by decide
```

The result is halted after four instructions. Both registers contain 4; ordinary cell 3 contains 99. There were two random reads, one distinct random cell, and eight random bits exposed. The initial `demoRandom` function is only a chosen test image. Probabilistic claims use `randomMemoryLaw` instead.

The library's `Examples.randomRoundTrip_spec` proves the analogous program's behavior for **every** width, initial register file, initial data memory, and random-memory image. The probability check `Examples.randomRoundTrip_probability` proves that its first output register is uniform when that image is drawn from the specified law.

## Sources, checks, and proof trust

| File | Contents |
| --- | --- |
| [Word.lean](../WordRam/Word.lean) | Word and address aliases, conversion, remainder wrapper, arithmetic bounds and no-overflow lemmas. |
| [Memory.lean](../WordRam/Memory.lean) | Memory functions and update equations. |
| [Program.lean](../WordRam/Program.lean) | Registers, operands, comparisons, instructions, and finite programs. |
| [Machine.lean](../WordRam/Machine.lean) | State, memory events, faults, and the authoritative step function. |
| [Execution.lean](../WordRam/Execution.lean) | Bounded evaluator, exact execution relations, termination, and divergence. |
| [Properties.lean](../WordRam/Properties.lean) | Composition interfaces, fuel stability, resumption, frame and agreement proofs, resource observations. |
| [Regions.lean](../WordRam/Regions.lean) | Fitting intervals, array assertions, separation, and memory agreement. |
| [Blocks.lean](../WordRam/Blocks.lean) | Block composition, trace permissions, prefix locality, and fault exclusion. |
| [Assembly.lean](../WordRam/Assembly.lean) | Symbolic labels, executable assembly, and execution-preserving relocation. |
| [Arrays.lean](../WordRam/Arrays.lean) | Verified fill, copy, and traversal loops with exact instruction counts. |
| [Random.lean](../WordRam/Random.lean) | Finite instances, probability laws, counting, independence, conditioning, and expected bounded work. |
| [Examples.lean](../WordRam/Examples.lean) | Small assembly programs, semantic specifications, and execution checks. |
| [Checks.lean](../Checks.lean) | Additional arithmetic/probability checks and the axiom audit. |

`import WordRam` imports the full public library. `import WordRam.Properties` imports the deterministic core and its proofs without the Mathlib probability layer. The core imports Lean's `Std`; probability uses Mathlib. Examples and audit commands are not imported by the library's root module.

The validation suite checks wraparound and remainder boundaries, destination/source aliasing, random-memory separation, repeated reads, all comparison kinds, exact loop counts, zero width, zero registers, halt and invalid fetch, falling off code, partial stores, and tiny probability examples. General theorems cover resumption, memory preservation, determinism, and agreement beyond those examples.

The audit rejects `sorryAx` and any project-specific axiom dependency. Proofs may use the standard Lean axioms `propext`, `Classical.choice`, and `Quot.sound`. It separately checks that the executable interpreter, resource observers, and shipped program constants have **no axiom dependencies**. Program constants use explicit bounded register constructors to avoid the proof dependency introduced by the pinned toolchain's generic `Fin` numeral conversion.

The proofs are checked by Lean's kernel. Small execution checks use `decide` or ordinary proof terms; `native_decide` is not used. The audit metaprogram inspects declarations and does not manufacture proofs. As with any formal model, the resulting guarantees concern the definitions here; machine-code performance, an operating-system random source, and an external interpreter require separate arguments.
