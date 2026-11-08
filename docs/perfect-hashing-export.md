# Certified programs and Lean-source export (M10)

`PerfectHash.certifiedFKS` is the concrete certified dictionary. Its code is
`PerfectHash.fksCode`, containing the same 238-instruction preprocessing and
33-instruction query arrays proved correct in M9. The arrays are explicit data
and can be evaluated or exported independently of proof fields. No program or
seed is recovered from an existential proof.

Import `DataStructures.PerfectHash.Certified` for these public declarations:

| Declaration | Purpose |
| --- | --- |
| `fksCode` | Direct executable projections `preprocess` and `query`. |
| `fksCode_correct` | Full original `DictionarySpec`, with no construction invariants in its statement. |
| `certifiedFKS` | Code, retained representation, uniform bounds, and correctness in one value. |
| `certifiedFKS_code` | Certificate projection equals the direct executable code value. |
| `dictionary_algorithms_exist` | The requested uniform existential theorem, derived from the certificate. |
| `certified_query_after_build` | Build once and query every word, even after overwriting unretained memory. |

The assumptions and constants are listed in the
[total-construction reference](perfect-hashing-total.md). They are identical for
the packaged code and the directly named arrays.

## Run the demonstration

Build the tools and execute the small Lean interpreter entry point:

```sh
./lake build PerfectHashTools
./lake env lean -s 131072 --run PerfectHashTools/Main.lean demo
```

The demo builds `[0,4095,0,4095]` at width 12, starting with dirty memory. Its
admissibility and input-array encoding are kernel-checked. The actual run reports
413 instructions, two distinct keys, and 16 retained words. It queries zero and
4095 successfully and rejects one and 4094. A mismatched halt or answer makes the
entry point fail.

This is execution of the proved Lean interpreter. It does not claim correctness
of a separate C/Rust backend or establish a probability law for an external PRNG.
The supplied deterministic demo image is covered by all-image correctness.

## Export and validate the exact arrays

The committed artifact is
[`PerfectHashTools/Generated.lean`](../PerfectHashTools/Generated.lean). Regenerate
it from the certified code with:

```sh
./lake env lean --run PerfectHashTools/Main.lean export PerfectHashTools/Generated.lean
```

The destination directory must already exist.

It contains literal arrays with explicit register-bound proofs. No assembler,
input size, word width, source keys, or runtime advice is needed to interpret the
array literals themselves. The arrays use the ordinary `WordRam.Instr`
constructors and the frozen 64-register calling convention.

The exporter also emits `preprocess_roundtrip` and `query_roundtrip`. Lean parses
the emitted source, then its kernel checks that both reconstructed arrays equal
the exact `fksCode` projections. Thus the serialized artifacts are tied to the
same values used by the correctness theorem. The export check regenerates a
fresh file, compares it byte-for-byte with the committed artifact, checks both
round-trip proofs, and runs the demo:

```sh
scripts/check_exports.sh
```

The Lake `PerfectHashTools` library also imports the generated artifact, so its
round-trip proofs are part of the normal project build. Serialization is to Lean
source; no additional binary or JSON dictionary serializer is introduced.

## Retained dictionary format

The representation is an array of RAM words, documented in full in the
[query and layout reference](perfect-hashing-query.md):

- Four header words store root seed, root shift, root range, and distinct count.
- Each root bucket has four directory words: count, child seed, child shift, and
  absolute child-table address.
- Each child slot uses an occupancy flag followed by the complete stored key.
  Zero is a valid key; emptiness is determined by the flag.
- The returned base and retained extent delimit every cell needed by query.
  Unretained output capacity, input, and scratch can be overwritten.

The format specifies words and absolute addresses rather than byte order. A
separate byte encoding or faster interpreter would need its own validation or
refinement argument. Exported programs retain the current wrapping arithmetic,
shift semantics, charged instructions, and immutable addressed-random-memory
behavior.
