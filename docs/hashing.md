# Verified multiply-shift hashing (M2)

`import Hashing` exposes the mathematical collision interface, the concrete
multiply-shift family, its raw-word sampler, and fixed RAM programs. It does not
provide the dictionary constructor or the finite-retry controller yet.

For a positive machine width `W = w+1`, the seed indices are `Fin (2^w)`.
`MultiplyShift.encode i` is the word `2*i+1`; it covers every odd word exactly
once. For `bits ≤ W`, the hash is

```text
h(a,x) = ((a*x) mod 2^W) / 2^(W-bits).
```

`eval_range` proves that this value is below `2^bits` for all word keys.
`collision_bound` proves `CollisionBound (family w bits hb) 2`: the number of
colliding seeds times `2^bits` is at most twice the number of seeds.
`CollisionBound.probability` interprets that integer inequality under the finite
uniform PMF, giving collision probability at most `2 / 2^bits`. No restriction
on key values is assumed. Hashing zero always gives zero; outputs need not be
uniform or pairwise independent.

The proof factors a nonzero wrapped key difference into a power of two and an
odd factor. Multiplication by the odd factor permutes residues. Equal high bits
force the multiplied difference into two short intervals beside zero modulo
`2^W`. The `Modular` lemmas count odd residues in those intervals, including
arbitrary trailing-zero counts in the original difference. All arguments are
kernel-checked; small-width enumeration is supplementary validation.

The executable sampler is `r - (r % 2) + 1`, with machine-word arithmetic.
`sample_eq_encode` handles every positive width, including width one where the
literal two wraps to zero. `rawEquiv` separates a raw word into its seed index
and discarded low bit; `raw_fiber_card` proves exactly two preimages per seed.
`raw_seed_probability` supplies the uniform raw-word law, and
`cell_sample_probability` connects the sampler directly to the existing
address-indexed `WordRam.probability`. Reusing an address still reuses its value;
independence of distinct blocks remains M3's obligation.

The runtime evaluator uses four registers: result, seed, key, and shift amount.
It performs multiplication, right shift, then halt: exactly three instructions,
no memory events, and only the result register changes. The sampler uses remainder,
subtraction, addition, then halt: exactly four instructions. It clobbers result
and key. Their exact theorems preserve the entire ordinary memory and apply to
arbitrary initial registers and random images. The stored shift is `W-bits`;
its encoding requires `W < 2^W`, already included in M0 admissibility.

Enumeration starts at one and increments by two. `candidate_covers` proves every
odd seed appears within `2^w` candidates; `candidate_wrap` identifies the first
repeated seed. No register needs to hold `2^W`, and no seed list is allocated.
`advanceSeed_exact` charges the increment instruction. M3 supplies finite-search
bounds; M7 will integrate this increment with the concrete trial controller.

`PowerOfTwo` specifies the least covering power of two and proves positivity,
coverage, minimality, and a bound below twice a positive request. Its ceiling
logarithm is mathematical bookkeeping; the later constructor must implement and
charge its doubling loop.

`./check.sh` checks all proofs, audits the `Hashing` namespace, and separately
requires axiom-free runtime encoders, sampler, evaluator, enumerator, program
arrays, and executable checks. The mathematical indexed family carries range
proofs and is not the runtime representation. Exhaustive checks cover every key,
seed, and output range at widths one through four, plus sampler and enumeration
boundaries and concrete RAM evaluation.
