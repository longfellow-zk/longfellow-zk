# LFC3: Longfellow Circuit 3

LFC3 is the native v2 circuit format. The compiler, reader and circuit identity
use the same three streams directly. Sumcheck v2 privately partitions each layer
into eleven working streams once, preserving the original circuit and its
segmentation. There is no reserved One input wire. V1 and its LFC1/LFC2 encodings remain unchanged.
LFA2 continues to package LFC3 payloads without any archive-format change.

## Coefficients and records

Every circuit owns a coefficient table, serialized in full. No indices are
reserved. Before splitting streams, the runtime scans this table once and
classifies each value as zero, one, minus one, or general. Stream splitting
uses the cached classification. In binary fields, minus one is classified as
one. Compression may reorder all entries; duplicate values are permitted.

Each layer has exactly these streams:

| Stream | Record | In-memory record bytes | Meaning |
|---|---|---:|---|
| quadratic | `(g,l,r,k)` | 16 | add `constants[k] * W[l] * W[r]` to output `g` |
| linear | `(g,l,k)` | 12 | add `constants[k] * W[l]` to output `g` |
| constant | `(g,k)` | 8 | add `constants[k]` to output `g` |

In quadratic and linear streams, `constants[k] = 0` is an assertion marker: require
`W[l] * W[r] = 0` or `W[l] = 0`, respectively, and emit no output contribution.
Every assertion receives an independent transcript coefficient, in quadratic
then linear traversal order. It replaces the whole output-weighted coefficient,
so a zero output weight cannot erase an assertion. Constant records require
`constants[k] != 0`. Unit streams use addition and subtraction directly.

The layer stores its input width, its logarithm, the three streams, and cached
quadratic/linear assertion counts. `Layer::with_assertions` derives those counts from the
compressed dictionaries. Counts are not serialized. Rebuild the layer after
replacing streams so its derived metadata remains consistent.

## File encoding

The file starts with `LFC3DIR3`. `DIR3` identifies the directory layout and
the 64-bit segmented circuit-ID convention. Earlier revisions and files without
a revision marker are rejected. Lengths are unsigned
LEB128 decoded into `u64` and converted to `usize` with overflow checking.
Stream records, delta indices and tokens retain the specialized four-byte
`u32` encoding. Coordinates use zigzag encoding of signed wrapping `u32`
deltas. Coefficient indices are absolute.

The header contains, in order: field ID, output wire count, copy count (always
one), public input count, input count, layer count, and coefficient count.

The complete directory follows the header, before any coefficient or term data:

1. For every layer, from outputs toward inputs: its input width, then the
   quadratic, linear and constant stream descriptors. Each descriptor contains
   six counts: deltas, segments, stored delta indices, tokens, expanded terms,
   and encoded payload bytes.
2. For every stream in the same layer/stream order: every segment's length.
   Their sum must equal the stream's declared stored-index count.

All array sizes are therefore known before the payload is allocated. The
reader validates the complete directory, using checked arithmetic for its
aggregate sizes. It then reads the full coefficient table, followed by each
stream's delta records, flat delta-index array and token array. Each payload
must consume exactly its declared byte length and produce exactly its declared
expanded term count. The last field is the raw 32-byte circuit ID.

In memory, segment ends delimit slices of one flat `Vec<u32>`. Individual
segments have no heap allocation. The layer logarithm is derived from its
validated width rather than serialized separately. Coordinates accumulate
across segment boundaries and repeated tokens; each stream starts at zero.
The reader checks coefficient, dictionary and token indices and translated
coordinate bounds without expanding repeated segments.

Named global limits live in `v2/limits.rs`: 128 layers, 8,388,608 total wires
including inputs and outputs, and 10 MiB of segment/token metadata including
directory offsets and decoder summaries. There are no separate per-layer,
per-stream, input or output caps. The global term ceiling is 16,777,216 for
expanded terms and for stored coefficients/deltas/indices combined, so unused
dictionary data remains bounded. A caller may lower the expanded-term ceiling.
Container/file I/O also has a coarse 64 MiB ceiling; v2 archives contain at
most three entries. The zstd window is bounded by the metadata limit.

Structural validation and circuit-ID verification always run. The reader
hashes the validated stored representation and rejects a mismatching ID.
`core::proto::v2::CircuitReader::from_bytes`
and `core::proto::v2::CircuitWriter::to_bytes` select this LFC3 layout directly.
V2 archive loading uses its own checked LFA2 reader. Slice readers check that
the declared payload and circuit ID remain before allocating circuit arrays.
Streaming arrays grow as records arrive, within the directory's fixed final
counts. The archive loader likewise allocates only for bytes actually present.
Compressed v2 archives contain exactly one zstd frame; additional frames and
compressed trailing data are rejected. V1 readers, LFC1/LFC2
encodings and frozen proofs remain unchanged.

## Circuit identity

The SHA-256 domain is `LFC3-v2-segmented-id-v2`. Its input is the following
fixed-width encoding, independent of the file's variable-length integers:

1. Field kind (binary = 1, otherwise 0) and serialized element width as `u64`,
   then the canonical encoding of minus one.
2. `noutput`, `logv`, `ninput`, `npublic_input`, layer count, and coefficient
   count, all as `u64`.
3. Every coefficient-table entry in order, in canonical fixed-width encoding,
   including duplicates and unused entries.
4. Each layer from outputs toward inputs: `nw` and `logw` as `u64`, then the
   quadratic, linear and constant streams.

Each stream starts with its `u64` tag (0, 1 or 2), then four `u64` counts:
dictionary records, segments, stored indices and tokens. These precede the
dictionary records, segment lengths, flat dictionary-index array and token
array. Every integer in the ID input uses eight little-endian bytes, regardless
of its storage width. Coordinate components are signed numerical deltas,
sign-extended from the stored wrapping `u32` representation to `i64`.
Coefficient indices, segment lengths, dictionary indices and tokens are
unsigned, widened to `u64`. All stored entries participate,
including unused records and segments. Expanded-term counts and assertion
counts are derived and are not additional hash inputs.

Hashing visits each stored entry once, without expanding repeated segments.
Segmentation, dictionary interning and coefficient-table reordering change the
identity. The compiler returns an identity-free `RawCircuit`; segmentation
consumes it and computes the final `Circuit` ID. The runtime's private stream
partition does not change this stored representation or its identity. Changing
zstd settings or file integer encodings does not change the identity. Changes
to the identity convention require a new domain and file revision. V1's circuit
ID remains unchanged.
