# LFC3: v2 Longfellow circuits

LFC3 is emitted by `compile_v2` (also named `compile_v2`). The
compiler returns `core::proto::v2::Circuit` directly. Each layer owns eleven
concrete streams, without boxed or optional child layers. V2 lowering removes
the source API's reserved One slot. Circuits and runtime assignments have no One wire.

LFA2 remains the archive container: its entries are opaque, length-delimited
payloads. The application `circuit_version` is independent of the payload format.
Legacy LFC1/LFC2 codecs remain supported. Temporary experiment formats are unsupported;
sumcheck v2's reader accepts LFC3 only.

## Header

All integers use the existing bounded, at-most-four-byte ULEB128 encoding.

1. Magic `LFC3` (four bytes).
2. Coefficient-policy mask: bit 0 separates one, bit 1 separates minus one.
3. Field ID.
4. Output count.
5. Copy count, required to be one.
6. Public input count.
7. Subfield boundary, required to be zero.
8. Total input count.
9. Layer count.
10. Coefficient count, followed by fixed-width field elements.

Masks 0–3 support the coefficient-class ablation API. Default: 3. Binary fields
use mask 1 by default because minus one equals one; bit 1 must be clear. Unknown
bits are rejected. Disabled coefficient streams must encode empty dictionaries,
segments and tokens. The mask never changes the number or order of streams.

## Layers and streams

Layers run from outputs toward inputs. Each starts with `logw, nw`, with
`logw = ceil(log2(nw))` and `nw > 0`, followed by all eleven streams:

| Order | Layer field | Absolute record | Dictionary bytes | Meaning |
|---:|---|---|---:|---|
| 1 | `quadratic` | `(g,l,r,k)` | 16 | add `coeff[k] W[l] W[r]` |
| 2 | `quadratic_one` | `(g,l,r)` | 12 | add `W[l] W[r]` |
| 3 | `quadratic_minus_one` | `(g,l,r)` | 12 | subtract `W[l] W[r]` |
| 4 | `quadratic_assertions` | `(g,l,r)` | 12 | require `W[l] W[r] = 0` |
| 5 | `linear` | `(g,l,k)` | 12 | add `coeff[k] W[l]` |
| 6 | `linear_one` | `(g,l)` | 8 | add `W[l]` |
| 7 | `linear_minus_one` | `(g,l)` | 8 | subtract `W[l]` |
| 8 | `linear_assertions` | `(g,l)` | 8 | require `W[l] = 0` |
| 9 | `constant` | `(g,k)` | 8 | add `coeff[k]` |
| 10 | `constant_one` | `(g)` | 4 | add one |
| 11 | `constant_minus_one` | `(g)` | 4 | subtract one |

Every stream independently stores:

1. Delta count and dictionary records at the exact arity above.
2. Segment count, then each segment's length and delta indices.
3. Token count and segment indices.

Coordinates use wrapped `u32` differences and zigzag encoding. Accumulators start
at zero independently for each stream and continue across segment occurrences.
`k` is an absolute coefficient-table index. Empty streams encode three zero counts.
There is no constant assertion stream.

General streams reject coefficient zero and any coefficient selected by the mask.
Assertions retain diagnostic `g` coordinates, but independently sampled `rho`
replaces the whole output-weight/coefficient factor. Assertions do not contribute
an output value. Final outputs must also be zero.

The reader checks dimensions, coefficients, dictionary indices, translated
coordinate bounds, and per-layer/global expanded-term budgets. It decodes directly
into concrete streams and keeps repeated segments shared in memory.

## Circuit identity

The payload ends with a 32-byte SHA-256 ID, domain `LFC3-v2-streams-v1`.
Identity integers use little-endian `u64` encoding, in this order:

1. Policy mask, binary-field flag, field-element byte size, serialized minus one.
2. Output count, output log width, input count, public input count, subfield boundary,
   layer count.
3. For each layer: `nw, logw`, then degrees quadratic/linear/constant tagged 0/1/2.
   Each term kind contributes its streams in table order. Each stream contributes its
   expanded term count and absolute coordinates. General terms additionally
   contribute the serialized coefficient value, not its index.

The ID authenticates class membership and order while allowing dictionary
deduplication, macro compression and coefficient renumbering to preserve it.
LFC3 changes circuit IDs, LFA2 combined IDs and associated proof/cache artifacts.
Historical measurements retain their historical IDs.

## Compiler and sumcheck

`segment_circuit_v2` compresses native record dictionaries directly. Only
dictionary-index compression is shared with the legacy compressor; streams never
convert into quadratic records. `CircuitWriter::to_bytes_lfc3` and
`CircuitReader::from_bytes_lfc3` expose the codec. `to_bytes_v2` and `from_bytes_v2`
are aliases for these operations.

Numerical bind/evaluation loops visit each class explicitly. General loops perform
uniform coefficient multiplication. Dedicated one/minus-one loops use their own
arithmetic. Linear terms contribute a public `L(u)` correction and do not enter the
quadratic binding. Constants bind once per layer. Quadratic and linear assertions
sample independent weights in a fixed order.

The historical [class ablation](../../benches/results/2026-10-29-class-ablation/README.md)
records sizes, timing, term counts, proofs and memory for the earlier experiments.
