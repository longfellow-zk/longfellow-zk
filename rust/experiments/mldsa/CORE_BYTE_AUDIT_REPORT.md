# Where the template-core MLDSA bytes go

2026-09-12. Diagnostic of the saved `wire_whole / shape_classes / reuse`
period-6 candidates from [the core experiment](TEMPLATE_CORE_LFC2_REPORT.md).
No circuit source, compiler default, prover, verifier, or mdoc artifact changed.

## Exact raw byte ownership

The categories below partition the **actual saved LFC2 bytes**, including delta
tables, segment dictionaries, token streams, constants and headers. A dictionary
entry used by both core and residual terms is counted once under mixed usage.
Core-only includes placement/boundary bytes, not just the shared interior.

| Stored bytes | MLDSA-44 | MLDSA-65 |
|---|---:|---:|
| Core-only, including boundaries | 1,712,493 | 1,808,385 |
| Residual-only | 811,644 | 820,132 |
| Shared between core and residual | 76,932 | 105,842 |
| Constants, headers, geometry, ID | 27,103 | 27,295 |
| **Total LFC2** | **2,628,172** | **2,761,654** |
| **Actual whole-file zstd-22** | **889,499** | **901,065** |

Core-only bytes split further into interior-only 1,668,185 / 1,759,426;
boundary-only 33,463 / 35,945; and entries used by both interiors and boundaries
10,845 / 13,014. All these are ordinary LFC2 structures, not runtime template maps.

There is no unique additive ownership of a whole zstd stream: matches can cross
these categories. As a **separate compression diagnostic**, collect each
category's existing encoded bytes in original order and compress it alone:

| Isolated zstd-22 bytes; not contributions to the whole file | MLDSA-44 | MLDSA-65 |
|---|---:|---:|
| Core-only | 447,467 | 448,845 |
| Residual-only | 414,564 | 414,157 |
| Mixed | 34,006 | 46,753 |
| Metadata/constants | 3,713 | 3,739 |
| Sum of independent streams | 899,750 | 913,494 |

These are diagnostic byte streams, **not independently executable circuits**.
Their sum differs from the actual 889,499 / 901,065 bytes above.

## Why terms enter the residual stream

The extractor first requires an **exact entire local layer program match** across
global components. Only afterward does it extract translated subcores from that
family. Thus it is not yet a general partial-template matcher: a common body
inside an unmatched component is never offered to the trimming stage.

| Reason | MLDSA-44 terms | MLDSA-65 terms |
|---|---:|---:|
| No second instance of the exact local program | 698,531 | 816,623 |
| One-term program: no interior delta to share | 130,676 | 156,068 |
| Singleton coordinate-translation class within a repeated program | 254,573 | 296,187 |
| Shape disagreement across instances | 0 | 0 |
| **All residual terms** | **1,083,780** | **1,268,878** |
| Core terms | 5,497,007 | 6,685,110 |

Bytes used exclusively by the first reason are **792,694 / 798,537**: 97.7% /
97.4% of residual-only bytes. Singleton translation classes alone consume just
13,922 / 15,713 bytes; one-term programs alone consume 4,860 / 5,656. The remaining
small amount is shared across reasons. Consequently, irregular input offsets
inside an otherwise matching template are **not the dominant residual byte cost**.

## Source attribution: SHAKE dominates residual bytes, not residual terms

Freshly compiled assertion symbols were checked against the saved original
circuit by exact wire-coordinate/coefficient term multisets. Assertion labels
were propagated backward through their dependencies, stopping at constants and
original inputs, then transported through the verified wire bijections. This is
attribution to consuming assertions, not instruction-level source provenance.
Shared dictionary usage is tracked separately rather than double-counted.

| Source category | Residual terms, 44 | Residual-only bytes, 44 | Residual terms, 65 | Residual-only bytes, 65 |
|---|---:|---:|---:|---:|
| SHAKE assertions | 243,523 | **714,816** | 245,377 | **693,134** |
| Sample-in-ball excluding SHAKE | 455,570 | 77,130 | 572,236 | 104,873 |
| Other assertions, including Booleanity | 352,621 | 11,973 | 418,194 | 14,016 |
| Inverse NTT | 2,048 | 3,309 | 3,072 | 4,396 |
| Forward NTT | 2,560 | 556 | 3,072 | 450 |
| Hints | 19,486 | 1,734 | 18,443 | 1,352 |
| Z norm | 7,168 | 822 | 7,680 | 609 |
| W1 encoding | 768 | 35 | 768 | 35 |

Small unlabelled and cross-source dictionary entries account for the remainder.
SHAKE is **88.1% / 84.5% of residual-only raw bytes**. Sampling and Booleanity
have many residual terms but cheap regular encodings.

For another non-additive compression diagnostic, all bytes used exclusively by
SHAKE, whether core or residual, compress alone to **738,805 / 743,329** bytes.
Forward NTT bytes compress alone to 85,791 / 86,425, inverse NTT to 42,742 / 40,433,
and sampling to 17,905 / 19,120. These are not independent circuit-file sizes or
additive zstd ownership, but they identify SHAKE as the main storage target.

### Which SHAKE regions fail matching?

Every residual SHAKE term has reason "unmatched local program". All of them
belong to **three components whose assertion paths end at Keccak round 5**:

| Component's consuming assertion | MLDSA-44 unmatched terms | MLDSA-65 unmatched terms |
|---|---:|---:|
| Sample-in-ball SHAKE, first six-round chunk | 111,963 | 113,817 |
| Challenge SHAKE round-5 component A | 119,620 | 119,620 |
| Challenge SHAKE round-5 component B | 11,940 | 11,940 |

These are unmatched terms, not the total sizes of those components. Some layer
programs within a component can still match. The existing symbol paths identify
rounds but do not uniquely name the challenge hash's absorption-block index.

A controlled check erased all coefficient indices from each local program while
preserving local wire labels. **None of the unmatched SHAKE programs acquired a
second match.** Different round constants alone are therefore not a sufficient
explanation under the current correspondence. This check is not a general
graph-isomorphism test and does not rule out recoverable internal permutations.

The relevant source mechanisms are visible in `src/mldsa/shake.rs`:

- `assert_hash` begins with constant XOR-basis state, pads with fixed bytes, and
  absorbs blocks before calling the permutation. Initial, full interior, and
  partially padded blocks therefore enter the first chunk differently.
- `absorb_block` converts input bits to `1-2*b` and multiplies them into the
  XOR-basis state. Multiplication by a constant initial state, fixed padding bits,
  and variable state/message multiplication simplify differently.
- `permute` makes the next chunk start from a fresh witnessed state at rounds
  5, 11, 17 and 23. Later chunks have a much more uniform interface.
- Round constants and 22-bit assertion packing also affect local programs, but
  the coefficient-erasure result rules out explaining these misses by coefficient
  variation alone.

This supports boundary specialization plus too-coarse matching as the leading
explanation. It does not establish a measured savings figure for a finer matcher.
The compiler has legitimately simplified distinct boundary conditions; the
extractor currently fails to recover common subprograms inside those results.

## Can the source be improved?

**First priority: recover shared interior round/subgate programs inside the three
special SHAKE components, without requiring the enclosing component's entire
layer program to match.** This extends the user's "remove the exceptional terms"
idea to the stage where the current implementation is still too restrictive.
It can be attempted purely as offline ordering/renumbering with no witnesses,
geometry changes or new runtime format. It needs exact correspondence checks;
coefficient-blind matching is only a diagnostic and is not valid template reuse.

A source-side alternative is to make absorption/boundary adapters explicit and
preserve common round interfaces with carefully placed `precious` sums. That
could limit propagation of boundary-specific algebraic flattening. It is an
**untested intervention**, not a guarantee of smaller files: existing SHAKE
already uses `precious` before chi, constant expressions are not made variable by
`precious`, and new internal stages can add copies/depth. Disabling all constant
folding just to obtain identical blocks could make the circuit larger.

An extra witnessed state with constraints tying it to absorption would give a
uniform permutation input, but adds witnesses/checks and can increase proof size.
It is not a free wire-ordering change and has not been implemented here.

Sampling has genuine source specialization: per-step rejection bounds change,
per-byte indices are constants, and the position trace is triangular. More uniform
source constraints or lookup-style checks are possible research directions, but
the measured byte cost is much smaller and checks must not be dropped.

### The FFT is flattened, but it is not the residual-byte obstruction

`src/mldsa/circuit.rs::ntt` and `inverse_ntt` express butterflies with ordinary
add/subtract/scalar multiplication and no stage barriers. `algsimp.rs` flattens
ordinary sums and distributes scalar multiplication. The measured core counts
confirm dense transforms:

- MLDSA-44: forward **327,680 = 5 × 256²** terms; inverse approximation
  **1,310,720 = 4 × 5 × 256²** terms.
- MLDSA-65: forward **393,216 = 6 × 256²**; inverse approximation
  **2,359,296 = 6 × 6 × 256²** terms.

The inverse transform has also absorbed the pointwise sum over L matrix-vector
products plus the challenge/key product. Almost all these terms are already in
cores; the tiny residual remainder comprises equality/marker/copy plumbing.
Stage `precious` barriers could preserve butterfly factoring without adding
external witnesses, but change internal wires/depth and potentially proof size.
That deserves a separate measured source experiment; it is not the main SHAKE
exception fix, and a term reduction is not automatically a compressed-byte win.

**The 500,000-byte goal remains unmet.** This audit identifies where to work; it
does not claim that the proposed source changes have achieved that goal.

## Audit implementation and checks

- `core_audit.rs` is an offline helper; `tests/core_audit.rs` is its ignored driver.
- Optional extractor tracing identifies each exact term's role and exclusion
  reason. Non-audit callers retain the same ordering.
- Saved candidate term streams and circuit IDs matched exactly on both circuits.
  The byte audit parses and verifies every serialized integer, coefficient and
  final ID; all ownership categories sum exactly to the saved file length.
- Two fresh compile/audit runs passed. 31 audit-harness and 38 ordering-harness
  non-ignored tests passed; workspace/all-targets check passed without warnings.
- No proof benchmark was rerun: the stored circuits, IDs, geometry and witnesses
  are unchanged. No mdoc or production source was modified by this audit.

Reproduce from the Rust workspace root, with the saved candidate fixtures present:

```sh
ORDER_DATASET=mldsa44 cargo test -p circuits-experimental --release \
  --test core_audit mldsa_core_bytes -- --ignored --nocapture
ORDER_DATASET=mldsa65 cargo test -p circuits-experimental --release \
  --test core_audit mldsa_core_bytes -- --ignored --nocapture
```

Machine-readable data are in `results/core-byte-summary.csv`,
`core-byte-categories.csv`, `core-byte-ownership.csv`, `core-term-attribution.csv`
and `core-unmatched-programs.csv`.

CSV masks: role 1=interior, 2=boundary, 4=residual; summary mask 1 merges both
core roles, mask 5 denotes mixed core/residual use. Reason masks are `1<<reason`,
where 0=core, 1=unmatched program, 2=one-term program, 3=shape mismatch,
4=singleton translation class, 5=unselected nonsingleton class. Source bits:
1=SHAKE, 2=inverse NTT, 4=forward NTT, 8=sampling, 16=hints, 32=Z norm,
64=W1 encoding, 128=other assertions. Zero source means metadata or unlabelled
terms. Byte-category axes 0/1/2 are role/reason/source. Composite masks indicate
shared usage and must not be counted twice. Term depths start at 1 next to inputs.
