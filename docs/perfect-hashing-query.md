# Packed representation and verified query

M6 defines a construction-independent FKS memory representation and a fixed
33-instruction query program. `PerfectHash.Query.spec` proves the frozen
`StaticSet.QuerySpec` with cost 33 for any preprocessing program that establishes
`PerfectHash.Table.representation`.

## Runtime format

The descriptor contains the ordinary-memory base and retained word count. Header
and directory fields are full machine words. Addresses stored in directory entries
are absolute addresses.

| Location | Fields in order |
| --- | --- |
| Four-word header | Root seed, root shift, root bucket count, distinct count |
| Four-word entry for each root bucket | Key count, child seed, child shift, child table address |
| Two-word child slot | Occupancy flag, full key |

The directory starts at `base+4`. Child tables follow the complete directory and
are packed in bucket order. Empty buckets have no slots. Singleton buckets have
one slot and bypass child hashing. Other buckets use the rounded allocation from
M5. Occupancy is zero or one, separately from the key; unused key cells may remain
dirty.

`PerfectHash.Packed` proves prefix allocation, disjoint directory/table regions,
and bounds for every header, directory, and slot address. `Table.View` connects the
stored words to a ghost description of the table. Its range obligations cover
all possible query words. Its slot-content condition states exactly which set
member occupies each slot.

`Table.View.retained_linear` derives the frozen `64*(d+1)` bound from the accepted
root's energy and directory-size bounds. The descriptor's strict fit condition
keeps the retained endpoint representable.

## Query behavior and theorem

At PC zero, registers 0 and 1 contain the descriptor, and register 2 contains the
query key. Other registers are arbitrary. The program hashes the key into the
root directory, rejects an empty bucket, selects the direct singleton slot or
computes the child hash, checks occupancy, and compares the full stored key.
Register 0 returns exactly zero or one.

The proof concerns the authoritative `WordRam.run` and establishes:

- Successful halt within 33 actual instructions, including halt.
- Membership equivalence for every word, including zero and the maximum word.
- Exact preservation of ordinary memory.
- No ordinary writes or random reads.
- Every read lies inside the retained descriptor.

The program contains 33 instructions; the longest executed branch takes 30.
Executable fixtures also exercise 13-instruction empty-bucket rejection,
22-instruction singleton lookup, and 27-instruction empty-slot rejection.

`Table.View.frame` proves that changing any memory outside the retained extent
preserves the representation. `Query.after_overwrite` applies query correctness
to that changed memory. `Query.representation_preserved` supports repeated
queries with the saved descriptor. Neither input memory, scratch memory,
construction history, nor a distinct-count argument is needed by query.

## Validation

A concrete valid hashed table is proved to represent `{0,1}` over 8-bit words.
Its tests include a nonmember hashing into an occupied slot, dirty empty-key
cells, readonly execution, and erasure outside the retained region. Additional
executions cover an empty dictionary ending at the last representable word and
a singleton containing the maximum word. The query program is separately
included in the executable axiom audit.
