# Hand-off II: perfect hashing in a verified word-RAM DSL

## 1. Scope and the complete public goal

This note builds only on [Hand-off I: a verified word-RAM language and
compiler](clean-room-word-ram.md). All additional algorithmic, representation,
collision, and probability ingredients are specified below. Familiarity with
standard finite sums and elementary probability is assumed; no existing hashing
implementation, theorem names, assembly program, or external paper is required.
The pseudocode describes algorithms to encode in the DSL from Hand-off I; it
leaves identifiers, calling conventions, and physical offsets open to redesign.

Implement a static set-membership dictionary over the *entire word domain*.
For an input occurrence sequence `xs`, define the mathematical quantities:

```text
w = word width; U = 2^w
N = number of input occurrences
S = the set of words occurring in xs
d = |S|, with d <= N
```

The program receives the occurrence array, its length, ordinary-memory
reservations, a random-memory reservation, and the correct width value as needed
by the chosen ABI. It must compute its distinct keys, their count, hash seeds,
and table sizes. `S`, `d`, perfect seeds, and ghost lists are not runtime advice.

Choose fixed source programs, compiled programs, register budgets, and numerical
resource constants before quantifying over widths, input contents, lengths,
placements, initial dirty memory, and random images. The same instruction arrays
must work for every admissible instance. An illustrative final theorem has this
quantifier order:

```text
There exist explicit preprocessing/query programs and uniform constants such that,
for every admissible width, occurrence array, layout, and initial state:

  for every random image rho, preprocessing halts successfully and returns
  a retained dictionary representing exactly S;

  averaged over uniform rho, actual instructions through that successful halt
  are at most Cpre * (N + 1);

  every word query, on every such dictionary, returns its membership bit
  within Cquery instructions, with no random reads;

  retained words <= Cret * (d + 1), and
  peak ordinary words, including input, workspace, stack, and registers,
  <= Cpeak * (N + 1).
```

The input, layout, and initial state are fixed independently of the random image
when taking expectation. Query correctness is deterministic and simultaneous for
all keys, including queries selected after inspecting the constructed table.

Use ordinary DSL calls for query. Permit writes to a supplied, separated,
constant-size query stack, while preserving the retained dictionary and every
ordinary cell outside that stack. The query reads only the retained region and
its stack. Construction scratch can supply the stack after construction ends.
A stricter global no-write query is an optional use of Hand-off I's register-only
backend, with a separately proved eligibility and trace theorem.

Specify public status/result decoding, input preservation, no malformed-machine
faults, and access safety for *every interrupted prefix*. Do not give guarantees
for arbitrary corrupted tables without an explicit validation procedure. The
query precondition is a valid representation, not merely a plausible descriptor.

## 2. Dependency structure and algorithm outline

Use four layers, with clear one-way dependencies:

1. Pure finite mathematics: hashing, sets/buckets, rounding, collision counts,
   finite search, and conditional expectations.
2. A retained-memory representation and conceptual membership algorithm.
3. Executable DSL helpers and their source contracts implementing the mathematics.
4. Compiled public programs, obtained through the generic compiler theorem.

The first two layers must not depend on the constructor's instruction array.
Prove query against the representation before proving construction. Construction
then establishes that representation and obtains query correctness by composition.

The algorithm has two levels of hashing, preceded by deduplication:

```text
preprocess occurrences:
  if empty: build a constant-size valid empty dictionary and return
  deduplicate into a compact array of d distinct keys
  choose a root hash whose bucket sizes have small sum of squares
  group distinct keys into linked bucket chains
  for each bucket:
    reserve a secondary table sized for that bucket
    find a hash injective on its keys, or use the empty/singleton shortcut
    finish this bucket without disturbing completed buckets
  return base, retained extent, and computed distinct count
```

Each seed search tries at most `w` fresh random seeds, then deterministically
enumerates all odd word seeds until one succeeds. This produces success for
every finite random image while retaining expected linear time. The algorithm
uses no unbounded stream of fresh randomness.

## 3. Full-word constant-cost hashing

### Mathematical family and runtime evaluator

For `0 <= ell <= w`, let `m = 2^ell`. A seed is an odd word `a`. Define:

```text
h(a, ell, x) = floor(((a * x) mod U) / 2^(w - ell)).
```

The result lies in `[0,m)`. Multiplication wraps deliberately. Store the shift
`w - ell` with the seed, so the runtime evaluator is simply:

```c
fn hash(seed, key, shift) {
  return (seed * key) >> shift;
}
```

This is constant-cost after compilation, including its call overhead. It accepts
zero and the maximum word as ordinary keys. For `m = 1`, shift by `w` produces
zero under the machine semantics. Output uniformity is neither true in general
nor needed: in particular, hashing zero always gives zero.

### Uniform sampling and exhaustive enumeration

For `w >= 1`, there are `H = 2^(w-1)` odd seeds. One uniform raw word `r` gives
an exactly uniform odd seed by:

```c
fn sample_seed(address) {
  let raw = random(address);
  return raw - raw % 2 + 1;
}
```

Each odd word `2i+1` has exactly the two raw preimages `2i` and `2i+1`. Subtraction
and the final addition stay within the unsigned range, including the maximum
word. Prove this two-to-one law, oddness/nonzeroness, and the evaluator's equality
to the mathematical family independently of any dictionary.

Enumerate seeds by starting at one and repeatedly adding two. The first `H`
candidates are exactly `1,3,...,U-1`. Subsequent wrapping is harmless because the
termination proof will show an accepted seed within that first prefix. The
mathematical bound `H` need not be computed or passed at runtime, and no seed
array is allocated.

### Collision bound, with a proof route

The central theorem is, for distinct words `x` and `y`:

```text
Pr over uniform odd a [h(a, ell, x) = h(a, ell, y)] <= 2 / 2^ell.
```

Here is a complete counting strategy, suitable for separate reusable lemmas.
For `ell = 0`, probability is at most one and the stated bound is immediate.
Otherwise set `B = 2^(w-ell)`. Two unsigned products falling in the same interval
of length `B` have modular difference in one of the strict tails
`[0,B)` or `(U-B,U)`.

Let `delta = (y-x) mod U`. Since the keys differ, `0 < delta < U`. Factor
`delta = 2^t * z`, with `z` odd and `0 <= t < w`. Set `L = 2^(w-t)`.
Multiplication by the odd number `z` permutes residues modulo `L` and preserves
oddness. Reducing a uniform odd seed modulo `L` is uniform on its `L/2` odd
residues: each such residue has exactly `2^t` odd lifts modulo `U`. Consequently,

```text
(a * delta) mod U = 2^t * r,
where r is uniform over the odd residues modulo L.
```

If `2^t >= B`, no such nonzero multiple lies in either strict tail: the minimum
positive multiple is at least `B`, and the maximum is at most `U-B`. Thus there
are no collisions in this case.

Otherwise `T = B / 2^t` is an even power of two and `T <= L/2`. The necessary
collision condition is `r < T` or `L-T < r`. Each tail contains exactly `T/2`
odd residues, so at most `T` of the `L/2` possible residues qualify. Their
probability is `2T/L = 2B/U = 2/2^ell`. This proves the bound without assuming
that every tail event is itself a collision.

The required supporting facts are: factorization of a nonzero integer into a
power of two and an odd factor; odd multiplication is a permutation modulo a
power of two; the equal-bucket modular-difference lemma; and counts of odd
residues in these intervals. Prove the finite cardinal inequalities first if
that makes the Lean probability interface simpler.

## 4. Rounding and arithmetic discipline

Define `roundPow2(t)` as the smallest power of two at least `max(1,t)`. Prove:

```text
roundPow2(0) = 1
for t > 0: t <= roundPow2(t) < 2t
roundPow2(t) is a power of two
roundPow2 is monotone
```

The source routine can start with size one and shift `w`, double size until it
covers the target, and decrement shift on each doubling. Return the size and
write the shift to a designated output cell if the DSL has one-word results.
Prove that the loop runs the required logarithmic number of iterations, never
doubles beyond the representable final size, and never underflows its shift.

Although the algorithm uses powers and squares in mathematical specifications,
only explicitly implemented word operations are runtime work. Array offsets,
counters, rounding, links, and allocation cursors need natural-number bounds
before conversion to words. Hash multiplication deliberately wraps; allocation
arithmetic must not accidentally do so.

A particularly important rule is that a rejected root must not compute an
unrestricted square of an occurrence or bucket count. A merely linear memory
hypothesis need not imply that `N^2` fits in a word. The safe test below avoids
needing that stronger assumption.

## 5. Deduplicate occurrences with expected linear work

Use a temporary chained table, independently of the final perfect dictionary.
Let `m0 = roundPow2(N)` and choose one sampled hash seed. Reserve and clear `m0`
head cells. Reserve space for at most `N` nodes of two words each and a compact
array of at most `N` keys. One-based node indices allow zero to mean “no node”
without reserving any key value or excluding ordinary address zero.

Process the input in order. For each key, follow its bucket chain, comparing
complete words. If found, do nothing. Otherwise append the key to the compact
array, write a node containing the key and old head, and update the head. Insert
one node per *distinct* key, never one per occurrence.

The loop invariant should establish:

- The input prefix processed and the untouched input suffix.
- Exact membership and distinctness of keys in the chains and compact prefix.
- Chain links are valid and acyclic, with indices bounded by allocated nodes.
- Every key is in the bucket selected by the sampled hash.
- Compact output is the sequence of first occurrences, independent of the seed.
- All readable node fields are initialized; unrelated memory is preserved.

Inserting each new node with a link to an older node makes positive link indices
strictly decrease during traversal. This supplies a simple termination measure
for chain search, independently of collision probabilities.

The last order property simplifies later independence proofs. Physical chains
may depend on the seed, but the compact key sequence is determined by the input.
A different output order is possible if its dependence on earlier random choices
is explicitly handled by later conditioning arguments.

For occurrence `x_i`, let `D_i` be the set of distinct keys in earlier input
positions. Its number of full-key comparisons is at most:

```text
1 + sum over y in D_i with y != x_i of indicator[h(y) = h(x_i)].
```

A chain contains each earlier distinct key at most once. The optional comparison
with `x_i` itself contributes at most one. This gives the inequality for both a
successful duplicate search and an unsuccessful search followed by insertion.

The sets `D_i` depend only on the input. By the collision bound, when `N > 0`,
expected comparisons per occurrence are at most
`1 + 2*|D_i|/m0 <= 3`. Linearity of expectation needs no independence between
these comparisons. Thus expected total comparisons are at most `3N`, even for
highly skewed repetitions. The all-image comparison bound is quadratic.

Prove a source instruction bound of the form
`A*(N+m0+1) + B*comparisons`, including clearing, full chain traversals, node
writes, compact-array writes, and calls. Then average it. This yields expected
`O(N+1)` instructions, deterministic `O((N+1)^2)` time, and `O(N+1)` workspace.
After success, expose a real compact array and computed `d`; a theorem about a
mathematical duplicate-removal function alone does not implement this step.

## 6. Root selection and overflow-safe grouping

For nonempty compact input, set `m = roundPow2(d)`. Hash each distinct key into
one of `m` buckets. Let `b_j` be the mathematical bucket sizes and define energy
`E = sum_j b_j^2`.

Prove the partition identities `sum_j b_j = d` and:

```text
E = d + 2 * number of colliding unordered pairs.
```

For uniform odd root seed, the collision bound gives:

```text
Expected E <= d + 2*d*(d-1)/m <= 3d.
```

Accept exactly when `E <= 6d`. Since `d > 0`, Markov's inequality gives rejection
probability at most one half. Hence an accepted seed exists in the finite odd
family. The returned root seed can be biased by stopping or fallback; later
proofs require only its acceptance property.

A root trial clears the directory, then groups the compact keys in one pass
into linked lists in scratch. Maintain a remaining budget initially `6d`. If a
bucket currently has count `b`, its next insertion increases energy by `2b+1`:

```c
let increment = 2 * oldCount + 1;
if (budget < increment) { return 0; }
budget = budget - increment;
// Link this key into its bucket and increment the bucket count.
```

Each count is at most `d`, so the increment fits under a suitable linear-size
hypothesis. Accepted prefixes satisfy `budget = 6d - prefixEnergy`. If an
increment would exceed the budget, final mathematical energy also exceeds `6d`,
because subsequent increments are positive. Prove this equivalence to the pure
acceptance predicate, including early rejection.

On success, return a grouping invariant: every compact key occurs in exactly
one chain, the chains partition the distinct keys by root hash, counts match
lengths, and the accepted energy bound holds. On rejection, preserve compact
input and write only the root directory/node workspace. The next trial must
reestablish its initialization invariant. Clearing heads/counts and writing
nodes before linking them can avoid clearing the entire node arena.

Each trial, including a rejected one, costs at most `Aroot*(d+m+1)` plus any
separately stated call/control overhead. Do not rescan the entire input for each
bucket: grouping once is essential for the linear bound.

## 7. Secondary tables and the retained representation

For a bucket with `b` keys, choose its slot count as:

```text
q(0) = 0
q(1) = 1
q(b) = roundPow2(2*b^2) for b >= 2.
```

For `b >= 2`, a union bound over unordered key pairs gives:

```text
Pr[any collision] <= b*(b-1)/q(b) <= (b-1)/(2b) < 1/2.
```

A child trial clears its own occupancy markers, hashes the linked keys, and
rejects on an already occupied slot. Otherwise it writes an occupied marker and
the complete key. It succeeds exactly when that hash is injective on the bucket.
No global key sentinel exists because every word can be a stored key.

The trial costs `O(q+b+1)`, including clearing and rejected work. Its footprint
reads the current chain and writes only the current child table. Preserve the
chain, root metadata needed later, and every completed sibling. Empty children
need no table or random trial. Singleton children use one direct slot and a
fixed conventional seed; they also need no random trial.

Accepted root energy justifies safe secondary allocation:

```text
b_j^2 <= E <= 6d
2*b_j^2 <= 12d
q(b_j) <= 4*b_j^2
sum_j q(b_j) <= 24d.
```

Thus squares, their multiplication intermediates, rounding, and child extents
fit under linear bounds in `d`, without a global assumption that `N^2` fits.
Prove bounds for the actual multiplication order and every pointer intermediate.
Calculate child sizes only after the root has been accepted.

A convenient concrete format is:

| Part | Fields |
| --- | --- |
| Header, four words | Root seed, root shift, root bucket count, distinct count |
| Each root entry, four words | Bucket count, child seed, child shift, child table pointer |
| Each child slot, two words | Occupied flag, complete stored key |

Pack the header, root directory, and child tables into one retained region.
During construction the eventual child-seed field may temporarily hold a linked
head, provided the partial-representation invariant distinguishes these phases.
The completed representation contains no required pointer to construction scratch.

This format yields, for nonempty input:

```text
retained = 4 + 4m + 2*sum_j q(b_j)
         <= 4 + 8d + 48d
         <= 64*(d+1).
```

Here `m < 2d` for `d > 0`; using a weak inequality is sufficient. An eight-word
empty representation with one empty root entry also fits the final bound. Other
formats are valid if they establish their own constants and locality theorem.

Define a construction-independent representation predicate relating the set,
retained region, and ordinary memory. It should assert:

- Valid header values and hash ranges, with every metadata address in the region.
- Disjoint/in-bounds child extents and readable directory entries.
- Root partition counts and appropriate empty/singleton/hashed child semantics.
- Each stored member occupies its selected slot with its exact full key.
- Every occupied slot contains a member belonging to that bucket.
- Occupancy markers encode empty/occupied consistently, for example as zero/one.
- Unoccupied key payloads may be arbitrary and are not consulted by query.

A pure table model plus a predicate explaining its memory encoding is often
convenient. Prove representation locality: changing memory outside the retained
region preserves the representation. Neither original input nor the history of
construction may be a hidden operational dependency of query.

## 8. Query and its source proof

The query follows a constant-depth path:

```c
fn query(base, key) {
  let rootSeed = load(base);
  let rootShift = load(base + 1);
  let bucket = hash(rootSeed, key, rootShift);
  let entry = base + HEADER_WORDS + ENTRY_WORDS * bucket;
  let count = load(entry + COUNT_FIELD);
  if (count == 0) { return 0; }

  let table = load(entry + TABLE_FIELD);
  let slot = table;
  if (count != 1) {
    let seed = load(entry + SEED_FIELD);
    let shift = load(entry + SHIFT_FIELD);
    slot = table + SLOT_WORDS * hash(seed, key, shift);
  }
  if (load(slot + FLAG_FIELD) == 0) { return 0; }
  if (load(slot + KEY_FIELD) == key) { return 1; }
  return 0;
}
```

The uppercase names are fixed layout constants, substituted or supported by the
front end. The two programs must agree on their values. There is no loop over
keys or buckets in query and no computation of a logarithm or random seed.

Prove a total source contract for every valid representation and every word key.
The cases are empty bucket, direct singleton, and hashed child; then unoccupied
slot, occupied member, or occupied nonmember. The final full-key comparison is
necessary: injectivity on stored members alone does not exclude false positives.

At source level, query preserves all ordinary memory and has no random events.
It reads only retained cells. Transfer this through the ordinary compiler:
compiler frames may write the separated query stack, but preserve all application
memory. Derive an explicit constant instruction bound and constant live-stack
bound from the new code, including both hash calls, all branches/spills, the
entry wrapper, and final halt.

Prove that the representation survives every completed query, and that arbitrary
overwrite outside the retained region before a query is allowed with a fresh valid
stack placement. In particular, input, old grouping nodes, unused output capacity,
and released construction stack contents can be overwritten. Query correctness
must not need them to retain their old values.

## 9. Total finite-memory seed search

An uncapped random retry loop is unsuitable for this finite immutable random
memory model: it cannot assume an unlimited supply of fresh cells, and repeatedly
reading a bad cell never changes its value. Use this algorithmic schema for both
root search and each nontrivial child search:

```c
while (tries != 0) {
  seed = sample_seed(address);
  accepted = trial(seed);
  if (accepted != 0) { return seed; }
  address = address + 1;
  tries = tries - 1;
}
seed = 1;
while (1 != 0) {
  accepted = trial(seed);
  if (accepted != 0) { return seed; }
  seed = seed + 2;
}
```

This is a source schema instantiated with the named root or child routine and
its ordinary parameters. It does not require function pointers or an uncharged
predicate oracle. The real trial performs its own initialization and accesses.

The random cap is `w`. A bounded-search contract identifies the exact accepted
candidate or exhaustion, the actual number of reached attempts, the addressed
prefix read, preserved inputs, and effects on both outcomes. On exhaustion it
exposes a state from which deterministic search can continue correctly.

Keep acceptance bits, returned seeds, and runtime status conceptually separate.
If zero denotes bounded-search failure, prove that every sampled/enumerated seed
is nonzero. This convention reserves a seed value, never a stored-key value.

The pure acceptance predicate must depend only on the fixed trial instance and
candidate seed. Establish this by proving that each trial resets the relevant
state and implements that same predicate, regardless of earlier rejected trials.
Otherwise the geometric probability calculation below does not apply.

Prove deterministic continuation from a successful finite candidate prefix.
Existence of a good odd seed and enumeration coverage supply such a prefix of
length at most `H`. A ghost prefix index or the position of the first successful
candidate supplies the termination measure. It need not be an executable search
bound. Every candidate increment, trial, branch, and return is still charged.

For every random image, either a random attempt succeeds or deterministic
enumeration does. No probability-one qualification replaces this all-image result.
If an intermediate bounded-only constructor is useful, give it a truthful budget-
failure status and a distinct theorem; the final constructor must discharge that
failure case by verified fallback.

### Expected cost of one completed search

Let `p <= 1/2` be the rejection probability of a uniform seed for the fixed trial
instance. For `r` independent random attempts, let `A` be attempts actually made
and `F` the event that all `r` fail. Then:

```text
E[A] = sum_(i=0)^(r-1) p^i <= 2
Pr[F] = p^r <= 2^(-r).
```

If `B` bounds one attempt's entire trial/candidate/control cost and fallback tests
at most `H` candidates, pointwise search work is at most
`B * (A + indicator[F] * H)`, plus explicitly charged fixed setup/finish work.
Therefore its expectation is at most `2B + 2^(-r)*H*B`.

Take `r = w` and `H = 2^(w-1)`. The fallback contribution is at most `B/2`, so
`3B` is a convenient conservative bound on trial work. This calculation counts
all bad images and the deterministic work they trigger. Charging merely random
attempts would prove a different and insufficient claim.

The selected successful seed need not be uniform. The cost bound only needs
independent uniform *trial* seeds, a fixed acceptance predicate, and exhaustive
fallback. Separately charge search setup, direct children, and loop continuation,
or absorb them into an explicit per-stage linear allowance.

## 10. Address schedule and conditional probability

Assign disjoint blocks of immutable random memory. One simple schedule, relative
to random base `rbase`, is:

```text
deduplication: rbase
root attempts: rbase + 1 ... rbase + w
child j:      rbase + 1 + w + j*w ... rbase + 1 + w + (j+1)*w - 1
```

The child block exists for every root entry; empty and singleton buckets can leave
it unread. Early success uses a prefix of its block. Fallback uses no random
cells. Addresses never wrap under the reservation fit proof. The random space
is separate from ordinary memory, so their numerical intervals may overlap.

With `m` root entries, the used schedule is contained in `1 + w*(1+m)` cells.
The caller need not know `d`: `m <= m0 = roundPow2(N)` gives a sufficient reserve
`1 + w*(1+m0)`, or the simpler bound `1 + w*(2*(N+1)+1)`.

Transfer the generic block laws of Hand-off I to this schedule. The deduplicated
sequence is independent of its seed, so the root's key sequence is fixed. The
accepted root determines child bucket sizes, chains, and capacities, but child
random blocks remain independent of all root choices, even if root selection
entered deterministic fallback.

For child expectation, condition on a fixed accepted root, and if necessary the
completed prior-child history. For that fixed instance the current child block
has its uniform product law, and the child rejection bound holds. Apply the
single-search bound with that child's actual size. Then average over the root.
Do not assume the accepted root is uniform or that child sizes are constants
before conditioning. Fallback creates no exception to this argument.

For every accepted root:

```text
sum_j (q(b_j) + b_j + 1) <= 24d + d + m <= 27d + 2.
```

Consequently summing the conditional child allowances remains linear. Charging
each child by the largest child's cost and multiplying by the number of buckets
would lose the desired bound. Ordinary memory effects of completed siblings
must be framed out when applying the next child's contract.

If reporting randomness as a resource, derive separate statements:

- Worst-case reads at most `1 + w*(1+m)`; every read address is fresh.
- Expected reads at most `1 + 2*(1+m) <= 4d+7`, with empty input optionally using
  none. Direct children improve this bound but do not need special analysis.
- Raw bits exposed equal `w` times distinct cells read. This is a convention for
  observed raw words, not a claim about entropy of the transformed odd seed.
- Reserved random capacity is separate from mutable workspace and may be larger
  than the prefix actually read.

## 11. Source contracts and construction composition

Prove helpers at source level using Hand-off I's logic. Suggested interfaces are:

| Helper | Functional/effect result | Cost information to retain |
| --- | --- | --- |
| Hash | Exact wrapping multiply-shift, no memory effects | Fixed instruction/call cost |
| Sampler | Exact encoded odd seed, one addressed random read | Fixed cost, exact address |
| Rounding | Correct power of two and shift | Actual doubling iterations |
| Chain search | Full-key membership in a valid chain, preservation | Actual comparisons |
| Deduplication | Seed-independent compact distinct array and computed length | Linear overhead plus comparisons |
| Root trial | Exact acceptance, grouping on success, compact-array preservation | Linear per-trial allowance including rejection |
| Child trial | Exact acceptance, valid slots on success, chain/sibling preservation | Its own `q+b+1` allowance |
| Child allocation | In-bounds next extent, initialized current metadata | Rounding plus constant metadata cost |
| Search | First accepted seed, all-image termination, exact random prefix | Reached random attempts plus charged fallback |
| Constructor | Valid retained representation and public output | Sum of actual component allowances |

Contracts should quantify over dirty permitted memory and an enclosing program
containing the required ordinary helpers. A reusable contract need not depend
on the numerical function identifiers of one monolithic application.

Use an outer-loop invariant after `j` completed buckets. It should retain the
accepted root, correct remaining grouping chains, accurate allocation cursor,
valid metadata, and completed representations for the first `j` children.
The next step allocates its current table, searches, installs the selected seed,
and advances cursors. Failed trials preserve the earlier completed portion.
At the end this partial representation becomes the full query representation.

An empty-input branch should explicitly initialize a valid constant-size empty
table. It can avoid sampling entirely. For nonempty input, deduplication discovers
`d > 0`; root selection/grouping runs once to acceptance; each child is completed
once to acceptance. All loops, retries, hash evaluations, memory initialization,
address calculations, and field updates are source statements and incur costs.

Compose source contracts first. Apply the compiler's generic simulation once at
the public boundary, or through proved module interfaces, to obtain the actual
machine theorem. Any entry/exit adapter must itself have a charged execution and
memory contract. Avoid proving the new source program correct by appealing to an
older assembly constructor's execution theorem.

The target statement should assert successful halt, correct status, descriptor
base/extent and distinct count, representation, complete access policy, fresh
random schedule, numerical work, and stack fit. Prefix/frame consequences cover
arbitrary stopping fuel, including an interrupt during call setup or a rejected
trial. The queried table becomes public only after construction succeeds.

## 12. Numerical costs, worst-case fuel, and ordinary space

### Instruction work and expectation

Retain a pointwise work function of the random image. It should decompose as:

```text
preparation and deduplication comparisons
+ root rounding and reached root-search work
+ sum of allocation and reached child-search work
+ orchestration, ABI setup/teardown, and final halt.
```

Compiler constants multiply these terms but must not add an input-dependent
factor. Charge fixed-size word operations and helper calls through the generic
logic. Rounding loops depend on their targets: their logarithmic costs are
bounded by the corresponding linear sizes, without multiplying by `w`.

Deduplication has expected linear cost in `N`; root search has expected linear
cost in `d+m`; conditional child costs sum linearly in `d`; and all remaining
initialization, rounding, and orchestration are linear. First derive explicit
constants from the new compiler, then conclude
`E[target instructions through successful halt] <= Cpre*(N+1)`.

A useful way to keep proofs manageable is to define a pure, adequately charged
work model and prove `actualTime(rho) <= K*modelWork(rho)+C` for every image, with
fixed `K,C`. The model must include rejected trials and fallback. Averaging this
inequality transfers its bound. The cost model's state must describe the same
computed choices and trial order as the source execution.

### Uniform evaluator fuel

Deduplication is quadratically bounded on every image. Each root/child search
uses at most `w+H` trials. Because accepted-root child allowances sum linearly,
an all-image time bound has the shape:

```text
C * ((N+1)^2 + (w+H+1)*(d+1)).
```

For positive width, `w <= U` and `H <= U`, so another fixed constant gives
`Cworst*((N+1)^2 + U*(d+1))`. Use `d <= N` to obtain a fixed evaluator guard
`Fuel(w,N)` that covers every image. These are mathematical naturals, not word
values the algorithm must store.

Prove the program's own successful termination and that its time is below the
guard. Then `expectedSteps(program, Fuel(w,N), initial)` is the expected time to
successful completion. The guard is allowed to be enormous; using it as the
expected-work bound or stopping the algorithm at the guard would change the goal.

### Lifetimes, retained space, and stack

A straightforward deduplication layout uses `m0` head words, `2N` node words,
and `N` compact-key words. Thus a linear scratch reservation, for example a
conservative `6*(N+1)` algorithm workspace, is enough before adding any stack.
Root grouping can reuse an appropriate node arena once deduplication ends,
while the compact array remains live and separate. Document these lifetimes
before proving overwrite/reuse.

For the illustrative packed format, reserve `64*(N+1)` output words up front,
then return a retained prefix of at most `64*(d+1)`. The remainder is releasable.
Changing the format changes these constants and requires its own proof.

The construction algorithms are iterative with a finite call graph of ordinary
helpers, so the compiler-derived maximum live stack is a constant for the fixed
source program. Derive it as the maximum sum of simultaneously live frames,
including the public adapter and transient setup. Query has its own constant
stack bound. These numbers need not match another implementation.

Place stack and algorithm workspace in separated subregions of one scratch
reservation, or allocate them separately. Count their union once. The total peak
bound includes the `N` input words, full output and scratch reservations while
live, and the fixed register file. Prove an explicit `Cpeak*(N+1)` inequality.
Retained output alone has the sharper `O(d+1)` bound. Random memory and code size
are separate reported resources.

## 13. Admissibility and a nonvacuity proof

Define a short public assumption record whose fields are independently meaningful:

1. Positive width; arbitrary keys are words of that width; runtime parameters
   correctly encode length, bases, capacities, and width.
2. Input array encoding, with no pre-zeroed output, workspace, or stack premise.
3. Fitting and appropriately disjoint ordinary regions and an adequate stack.
4. Generated code/return-address and frame-constant fit from Hand-off I.
5. Linear arithmetic bounds covering counters, budget increments, accepted-root
   secondary sizes, rounding, and all ordinary address intermediates.
6. A fitting random reservation containing every scheduled block, including its
   correctly represented cursor endpoints.

Do not require a good sampled seed, already distinct input, keys below a prime,
or `N^2 < U` to make the algorithm proof convenient. Acceptance-dependent size
bounds must be derived before the corresponding allocation operations. Malformed
public inputs can remain outside this contract; dynamically checking them is an
additional charged feature if desired.

For example, after choosing workspace and stack constants, place input, output,
and scratch consecutively at ordinary base zero, and put the random reservation
at random base zero in its separate address space. Sufficient inequalities can
require the final ordinary endpoint, each needed arithmetic bound, and the
random endpoint `1+w*(2*(N+1)+1)` to be strictly below `U`, together with code fit.
These are explicit constraints at fixed width, not automatic consequences of
`d <= N`.

Prove nonvacuity: for any fixed finite sequence of `k`-bit keys, sufficiently
large `w >= k` admits its embedding, these reservations, and the fixed code.
Exponential `2^w` eventually dominates the linear-in-`w` random reservation and
the fixed ordinary sizes. This is compatible with full-word keys: at any
admissible width no numerical subset of the word domain is excluded. It does
not promise enough memory for every possible input length at a fixed width.

## 14. Delivery sequence and review evidence

A useful implementation sequence is:

1. **Freeze the public contract and representation.** Choose capacities and ABI
   conventions; state the numerical proof obligations and nonvacuity target.
2. **Prove the hash mathematics and implement its helpers.** Check range, sampler
   fibers, collision bound, odd enumeration, and constant-cost source evaluation.
3. **Build pure bucket/search mathematics.** Establish partition identities,
   acceptance probabilities, retained/child-work sums, and finite fallback cost.
4. **Verify query independently.** Include occupied-slot nonmembers, all word
   keys, retained locality, query stack effects, and repeated-query preservation.
5. **Verify deduplication.** Establish the compact sequence, comparison bound,
   all-image termination, expected cost, and dirty-memory/frame contracts.
6. **Verify trials, allocation, and search.** Show exact acceptance predicates,
   safe rejection arithmetic, per-child work, sibling preservation, and correct
   continuation after random exhaustion.
7. **Compose construction and compile it.** Prove public all-image success,
   numerical actual cost, stack sufficiency, and every-prefix memory guarantees.
8. **Close expectation and package the certificate.** Prove conditional stage
   averaging, fixed fuel, all resource bounds, and query after arbitrary overwrite
   outside retained storage. Export the explicit certified program arrays.

Keep algorithmic proof work at the source/model level. Changes to register
numbers or instruction templates should require compiler/cost updates, not a
new mathematical argument about hashing.

Selected executable cases should include empty and singleton input; all-equal
and interleaved duplicates; zero and maximum keys; occupied-slot nonmembers;
root rejection; child rejection with completed siblings present; final random
attempt success; exhaustion followed by actual deterministic success; dirty
initial cells; exact-fit and insufficient generic stack cases; near-end addresses;
and queries after overwriting all unretained memory. For small component widths,
exhaustively check the seed sampler and collision counts as a sanity check.
These examples supplement, rather than replace, the general theorems.

Audit executable code and theorem assumptions using the separation from Hand-off
I. State final constants derived from this implementation, even if conservative.
The public certificate must refer to the same compiled arrays that are exported
and executed. Completion means actual total preprocessing from repeated full-word
keys, expected linear work through success, local constant-time queries, and
linear ordinary space. Dynamic updates, minimal perfect hashing, succinct
representations, cryptographic randomness, and a native backend are separate
extensions with their own obligations.
