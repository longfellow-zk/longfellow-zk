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

The file starts with `LFC3DIR1`. `DIR1` identifies the directory layout;
LFC3 files without this revision marker are rejected. Lengths are unsigned
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

Structural validation always runs. Circuit-ID enforcement is optional for
trusted application artifacts. `core::proto::v2::CircuitReader::from_bytes`
and `core::proto::v2::CircuitWriter::to_bytes` select this LFC3 layout directly.
V2 archive loading uses its own checked LFA2 reader. V1 readers, LFC1/LFC2
encodings and frozen proofs remain unchanged.

## Circuit identity

The SHA-256 domain is `LFC3-v2-three-streams-v2`. The identity includes the field
kind and encoding, circuit dimensions, layer widths/logarithms, and, for each of
the three streams, its tag, expanded term count, absolute coordinates and actual
coefficient values. Dimensions, tags, counts and coordinates are encoded as
little-endian `u64`; field elements use their canonical fixed-width encoding.
Assertions are identified by their zero coefficient value.

Dictionary interning, segmentation, and reordering coefficient-table
entries preserve the identity. Stream traversal order is authenticated. Changes
to this format's semantics use a new identity domain. V1's circuit ID remains
unchanged.
