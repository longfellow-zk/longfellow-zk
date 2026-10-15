# Lexicographic traversal with unchanged LFC2 segmentation

2026-09-11. Follow-up to [the Morton investigation](MORTON_REPORT.md).

## Conclusion

Accepting a new prover/verifier removes the need to restore Morton order. LFC2's
existing delta dictionary, segment dictionary, and segment-token stream can all
be retained, including the compact in-memory representation. However, a plain
global lexicographic sort of the existing wires does not solve compression: both
input-major orientations regress both mdoc fixtures, and neither reaches 500 kB
for MLDSA-44. This is an offline experiment, not an adopted scheduling policy.

All wire labels, coefficients, input/output positions, terms, layer widths,
depth, and witnesses are frozen. MLDSA remains at period 6. The existing
scheduler, including its pre-existing component-size majority switch, is not
changed or endorsed by this experiment.

## Algorithm

For each layer, expand its existing terms, sort by the indicated coordinate key
with coefficient bytes as the final tie-breaker, then compute ordinary
`(delta_g, delta_h0, delta_h1, coefficient_index)` records from zero. Pass that
stream through the existing `segment_circuit` implementation without modification.
The stock LFC2 reader reads these files directly into segmented layers. There is
no component-map format, implicit template expansion, or Morton sort on decode.

Every reordered circuit is sorted back into the original canonical Morton order
and checked for exact LFC1 equality with the frozen original. Every segmented
lexicographic file is round-tripped through the existing LFC2 reader with circuit
ID enforcement and checked for exact equality with the corresponding lexicographic
LFC1 file. Thus these controls change traversal only, not the circuit equations.

## Input-major results

Complete segmented LFC2 files, bytes; zstd level 22 without an external dictionary:

| Circuit | Current Morton | `(h1,h0,g)` | `(h0,h1,g)` |
|---|---:|---:|---:|
| mdoc signature | 117,854 | 223,467 | 167,387 |
| mdoc hash | 161,848 | 1,869,218 | 309,539 |
| MLDSA-44, period 6 | 2,091,823 | 1,645,461 | 4,343,114 |

Distinct complete delta tuples across all layers, including coefficient index:

| Circuit | Current Morton | `(h1,h0,g)` | `(h0,h1,g)` |
|---|---:|---:|---:|
| mdoc signature | 14,192 | 49,195 | 27,427 |
| mdoc hash | 18,449 | 712,517 | 55,182 |
| MLDSA-44, period 6 | 174,923 | 378,756 | 989,603 |

LFC2 dictionaries are per layer; summing their sizes gives larger counts than
this global distinct-tuple statistic. The full logs also include raw LFC1/LFC2,
zstd-16, segment counts, and compact memory payload estimates.

## What lexicographic order fixes, and what it does not

The two output-major controls are worse as well (segmented LFC2, zstd-22 bytes):

| Circuit | `(g,h0,h1)` | `(g,h1,h0)` |
|---|---:|---:|
| mdoc signature | 378,444 | 377,088 |
| mdoc hash | 7,066,773 | 7,067,765 |
| MLDSA-44, period 6 | 5,459,345 | 5,538,799 |

These reject a sort-only change on the existing numbering. They do not establish
that a scheduler designed jointly for lexicographic order and wire numbering
cannot work.

A fixed translation of every coordinate preserves lexicographic order. For an
isolated component whose entire term list is a translated copy, successive
ordinary deltas therefore match, except for its initial transition. This removes
the demonstrated absolute-Morton translation problem.

But this theorem is about translated term lists, not arbitrary globally sorted
circuit layers. Shared inputs/constants do not translate with component interiors;
different internal permutations remain different; and mixing terms from different
components changes which terms are consecutive. Lexicographic order also gives
up Morton's joint locality in the two input coordinates. Consequently, removing
translation sensitivity does not imply a smaller global delta dictionary or file.
The measured dictionary increases above demonstrate that distinction. These
controls do not apportion each regression among the remaining causes.

## Runtime and proof implications

For `(h1,h0,g)`, all terms sharing an operand pair remain adjacent, so the current
`HQuad::bind_g` aggregation applies. Its adjacent sparse-corner folding can then
process all low-to-high bits of h0, followed by all low-to-high bits of h1. For
`(h0,h1,g)`, reverse the hands. This requires coordinated changes to the prover's
round schedule, verifier's transcript schedule, and verifier's HQuad evaluation.
It does not require expanding/reordering the whole circuit into Morton form.

Output-major `(g,h0,h1)` or `(g,h1,h0)` is a separate control: equal operand pairs
need not be adjacent after binding g, so simply swapping the round loops is not
sufficient. A new aggregation/evaluation strategy would be needed.

For input-major folding, the number and degree of sumcheck round polynomials can
remain unchanged. No extra wires or witnesses are introduced by sorting. This
does not establish byte-identical proofs: the current circuit ID hashes term
order, and a different transcript can affect variable-length commitment openings.
A changed round schedule also needs explicit protocol identification/versioning.
No new prover/verifier or proof-size benchmark is implemented in this experiment.
The coordinate-only folding unit test is not a cryptographic proof test.

## Reproduction

```
MORTON_LEX_ORDER_ONLY=1 cargo test -p mdoc-zk-circuits analyze_signature_morton -- --ignored --nocapture
MORTON_LEX_ORDER_ONLY=1 cargo test -p mdoc-zk-circuits analyze_hash_morton -- --ignored --nocapture
MORTON_LEX_ORDER_ONLY=1 cargo test -p circuits-experimental analyze_mldsa44_morton -- --ignored --nocapture
```

Add `MORTON_LEX_OUTPUT_MAJOR=1` to run the two output-major controls instead.
Each orientation is explicitly selected for diagnosis; no per-circuit selection
or compress-both-and-pick policy is implemented.

Decoder timings in the logs are median-of-three zstd-16 decompression plus native
LFC2 reading and ID computation. Other experiments ran concurrently, so these are
indicative observations, not controlled runtime comparisons. Exact LFC1 equality
checks occur outside the timed region. Memory estimates include delta payloads,
segment entries/tokens and segment Vec headers, but exclude spare capacity,
allocator overhead, constants and geometry.

All six fixture/orientation-group runs passed their exact round-trip checks.
Both unit tests passed in both packages (six executions because the mdoc harness
includes this module twice). `git diff --check` passed.

Complete logs, including all LFC1/native-LFC2/segmented-LFC2 raw and compressed sizes:

- Input-major: [signature](results/lex-signature.log), [hash](results/lex-hash.log), [MLDSA](results/lex-mldsa.log).
- Output-major: [signature](results/lex-output-signature.log), [hash](results/lex-output-hash.log), [MLDSA](results/lex-output-mldsa.log).
