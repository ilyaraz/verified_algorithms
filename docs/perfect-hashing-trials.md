# Verified FKS construction trials (M7)

M7 provides fixed, executable RAM blocks for constructing the M6 table format.
The complete retry driver and composition with deduplication are M8–M9. The M0
specification is unchanged.

All programs use the existing 64 registers and `WordRam.step` semantics. Their
contracts count actual executed instructions, including clearing, rejected probes,
status writes, and halt. The implementations use explicit instruction arrays
assembled from checked symbolic labels.

## Deterministic contracts

| Routine | Code words | Actual instruction bound | Principal theorem |
| --- | ---: | --- | --- |
| Contiguous clearing | 6 | `5n + 1` continuing instructions | `Construction.Clear.clear_many` |
| Power-of-two rounding | 5 | `4r + 1` continuing instructions | `Construction.Round.round_many` |
| Root trial | 39 | `20m + 25d + 9` through halt | `Construction.Root.total` |
| Child trial | 29 | `10q + 17b + 7` through halt | `Construction.Child.total` |
| Child allocation | 21 | `4 bits(2b²) + 18` through halt | `Construction.Allocation.total` |
| Standalone odd-seed enumeration | 5 | `1 + 3·2^(w−1)` through halt | `Construction.Enumeration.total` |

Here `d` is the distinct array length, `m` the root directory length, `b` the
current child cardinality, and `q` its slot count. The rounding parameter `r`
counts remaining doublings. The enumeration theorem is expressed at positive
width `w+1` in Lean, with `2^w` seeds.

The clear and rounding contracts end at a continuation PC before the standalone
halt. `WordRam.BodyEmbedded` preserves their continuing instructions when their
halt is replaced by caller code. Register-frame theorems also identify registers
that arbitrary compositions must preserve.

## Root trial and overflow

The caller supplies a compact input array, a `4m`-word directory, a `2d`-word
node region, a seed, and a shift. Their natural-address regions fit and are
pairwise separated. Input registers are documented in
`Construction.Root.Input`; other registers may be dirty.

The trial clears the entire directory, then reads each input key once. Directory
fields zero and one temporarily store the bucket count and a one-based node
index. Each node stores a full key and the previous head index. Zero terminates
an index chain; zero-valued keys remain ordinary data.

The machine starts with energy allowance `6d`. Before inserting into a bucket of
current size `c`, it computes `2c+1`, compares it with the remaining allowance,
and rejects if the increment is too large. The subtraction and count update
occur only after that check. `energy_increment_fit` and `energy_budget_fit`
derive word fit from `64(d+1) < 2^w`, including unsuccessful trials.

`Root.LoopState` relates the machine's directory and chains to the processed
prefix. `groupAccepted_iff` proves that early rejection agrees exactly with the
full energy test. The root guard is equal to M5's `rootAccept`, not an additional
sufficient condition. On success the linked chains represent the reverse input
order. On rejection status is zero and no completed dictionary is claimed.

All root reads and writes satisfy `Root.policy`. Input and memory outside the
directory/node regions are preserved. A successful grouping iteration takes 25
instructions; a rejected probe and epilogue take 12.

## Allocation and child trials

Allocation loads the computed bucket count and saves its linked head. Empty and
singleton buckets use zero and one slots. Nontrivial buckets compute `2b²` and
round it to a power of two using the verified RAM loop. The accepted root energy
bounds every `b²`; `Allocation.accepted_fit` derives the required arithmetic
bounds from the frozen linear capacity assumption. It does not add a global
`d² < 2^w` precondition.

The allocation epilogue computes the next packed cursor and stores the shift and
absolute table pointer in directory fields two and three. The root head remains
available in register 27. Publishing a chosen child seed is the retry driver's
responsibility; allocation alone does not establish a valid query table.

A child trial clears its own `2q`-word allocation and walks only its root bucket's
linked nodes. Each key is hashed, and the occupancy word is inspected before
insertion. A nonzero occupancy word rejects the seed. Otherwise the program
writes occupancy one and the complete key, then follows the next link.

`SlotsAt` permits arbitrary values in unoccupied key cells. Its occupancy test is
proved equivalent to repeated hash detection, including when the stored key is
zero. `child_acceptance` identifies the concrete guard with M5's `childAccept`
for distinct input keys. A successful traversal iteration takes 17 instructions;
a rejected probe and epilogue take 13.

`Child.policy` permits writes only in the current child table. Thus successful
siblings and all node data survive both rejection and success. The same trace
policy bounds interrupted prefixes through `TerminatesIn.prefix_policy`.

## Enumeration and abstract budgets

The enumeration control loop starts at odd word one, advances by two, and stops
when the word wraps back to one. It stores neither the modulus nor a list of
seeds. `Enumeration.visits` gives the exact RAM prefix reaching every candidate;
`Enumeration.covers` connects these prefixes to the multiply-shift seed family.
The complete trial-and-retry composition is proved in later milestones.

`Construction.Refinement` transfers the local instruction bounds to M5's trial
budgets: root work is at most `40(d+m+1)`, child work at most `20(q+b+1)`, and
allocation at most `22(q+b+1)`. These are deterministic per-block bounds; M7 does
not yet claim expected time for an assembled preprocessing program.

## Checked boundary executions

`Construction.Examples` kernel-checks concrete executions for root acceptance
and rejection, child collisions, an occupied zero key, a maximum-word direct
singleton, empty allocation, dirty memory, sibling preservation, and allocations
ending at the last representable word.

A 14-bit example uses 128 distinct keys with `128² = 2^14`, so the square does not
fit in a word. The bad root seed safely rejects after 3,253 instructions, with 27
inserted nodes and remaining energy allowance 39. Tiny-width enumeration also
runs through all candidates and halts without memory accesses.

The public imports, executable axiom audit, and Lean Atlas include every M7
module. Executable guards use Boolean list operations to keep their runtime
implementations free of proof-axiom dependencies.
