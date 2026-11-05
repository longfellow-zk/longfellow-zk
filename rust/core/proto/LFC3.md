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

All integers use unsigned LEB128 with at most four bytes, except the final raw
32-byte circuit ID. Coordinates use zigzag encoding of signed wrapping `u32`
deltas. Coefficient indices are absolute, never delta-encoded.

The header is:

1. Four bytes `LFC3`.
2. Field ID.
3. Number of output wires.
4. Number of copies, always 1.
5. Number of public input wires.
6. Number of input wires.
7. Number of layers.
8. Number of coefficients in the complete table.
9. Those field elements, using the field's fixed-width little-endian encoding.

Every coefficient is explicit, including zero, one, and minus one when used.
There is no coefficient-policy byte.

Layers appear from circuit outputs toward inputs. Each layer stores `logw` and
`nw`, with `nw > 0` and `logw = ceil(log2(nw))`, then the quadratic, linear and
constant streams. Each stream stores:

1. Delta-dictionary length followed by its exact-arity records.
2. Segment-dictionary length; each segment is a length followed by delta indices.
3. Token count followed by segment indices.

Coordinates accumulate across all records of the expanded stream, including
segment boundaries and repeated tokens. Each stream starts its coordinates at
zero. Empty streams store three zero counts. Parsing validates coefficient,
dictionary and token indices, translated coordinate bounds, dimensions, and
per-layer/whole-circuit expanded-term limits without expanding repeated segments.

The final field is the circuit ID. The reader can enforce it independently of
structural validation. `core::proto::v2::CircuitReader::from_bytes` and
`core::proto::v2::CircuitWriter::to_bytes` select LFC3 directly. LFC1/LFC2 are rejected by the v2
reader.

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
