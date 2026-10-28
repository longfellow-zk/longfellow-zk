# Dual-packing implementation audit, 2026-10-28

The current zk-v2 path uses the generic trace-zero protocol in `generic.rs` for
all field extensions. Binary arithmetic uses the shared polynomial transpose
and trace-dual kernels in `algebra::packing::binary128`. The standalone binary
API remains covered by independent equation and differential tests.

## Protocol and implementation

`PackingExtension` describes a trusted embedding K into F, its native basis,
coordinates and relative Frobenius. `PackingParameters` owns the selected basis,
trace dual and any coordinate conversion. Shipped profiles are GF128/GF2,
GF128/GF256, the MLDSA sextic/prime extension and identity extensions.

For a nontrivial extension of degree m, the committed mask cells are
`t_1,...,t_(m-1),r,b`, with dependent `t_0=sum_(j>0) beta_j*t_j`. Honest setup
sets `b=sigma(r)`; the verifier deliberately permits arbitrary committed b,
as in the paper and Lean native-verifier bound. The prover sends all m
trace-zero U coordinates before the verifier samples independent delta
coordinates, then sends A. Both resulting native linear equations authenticate
against the original commitment. Dropping the first equation is unsound;
an adversarial regression constructs a false target accepted by the second
alone. Identity extensions have one direct equation and no masks, packing
messages or challenges, including nonunit singleton bases.

Tests compare the two native residuals with literal paper equations for
arbitrary cells and messages. Small odd-characteristic fields exercise signed
coefficients, nonunit bases and characteristic dividing the extension degree.
Exhaustive GF9 challenges allow arbitrary b and check the native 1/|F| bound.
The optimized binary transpose is checked against direct coefficient sums.
Generic binary, GF256, sextic and identity equations are also authenticated by
Polygero against their originally committed words and auxiliary cells.

## Integration and ownership

Ordinary `ZkProver` and `ZkVerifier` own the packing/Polygero boundary. There is
one application-facing v2 proof path. Witness generators return ordinary
ambient-field circuit inputs. The wrapper validates private-input membership
in K and packs them once; public inputs pass through unchanged. The physical
layout is:

```text
packed private inputs | packing masks | GKR pads and products
```

Product preparation and constraint compilation share the same physical pad
layout. The compiler consumes its symbolic constraints, moves the single dense
input-weight vector into the logical packing claim, and emits physical GKR
rows. The wrapper consumes that claim and authenticates both native rows.
Dense claims and temporary native rows are released before Polygero proving.
The identity adapter retains no extra committed-word copy through sumcheck.

Mdoc's six private MAC masks and seven public MAC values are ordinary bit
inputs. The circuit reconstructs the field values and checks the MAC equations.
A direct circuit regression rejects changes to message, mask, tag and challenge.
The former external MAC claims, six dense MAC coefficient vectors and caller
auxiliary API have been removed. The semantic input manifest carries counts,
SHA variant and witness recipe, with no packing basis or MAC-coordinate map.
The compiler checks that committed witness-recipe outputs are independent of
public MAC values derived after commitment.

## Transcript, validation and serialization

The extension descriptor, circuit ID and layout counts are bound before the
root. Mdoc additionally binds its combined archive identifier before both
roots. The public statement precedes sumcheck, the logical claim precedes U,
all U coordinates precede delta, and A precedes Polygero's statement digest.
Malformed input membership and response shapes are rejected before advancing
the corresponding protocol transcript. Tests cover tampering with root,
public input, U, A, GKR claims, backend responses and opened rows.

All combined v2 proofs use LFV4 with ambient-only PLG8. Trusted geometry fixes
the response length; noncanonical encodings, truncation and older markers are
rejected. Development caches use MDOCBIT6 and MDOCNEXT3; the semantic input
manifest uses LFHASH02. V2 requires `subfield_boundary=0`. LFC1/LFC2 retain that
metadata for V1, whose serialization and subfield sampling remain separate.
Interpolation now exposes only `apply`; V1 still samples its declared subfield
rows, then encodes them using ordinary interpolation. Saved legacy proofs and
newly generated deterministic proofs are checked for exact compatibility.

## Findings fixed during this audit

- A custom basis with the wrong distinguished coordinate could weaken U's
  masking. In GF9, the basis `[x,1]` with `x^2=2` gives disjoint first-response
  supports for two witnesses satisfying the same claim. Construction now
  requires the first coordinate of one to be nonzero, equivalently that
  `{1,beta_1,...,beta_(m-1)}` is a basis. An exhaustive regression checks the
  leaking example, rejection, and full response support for an admissible
  basis. The shipped profiles and mask sampling are unchanged.
- The packed reserved One input must equal one. Binary and sextic prover and
  verifier paths enforce this, with rejection checked before statement binding.
- Repeated packing, dense input-claim copies, retained identity witness copies,
  repeated trace validation and unused native coordinate matrices were removed.
  Optimized adapter hooks now check the lengths used by the protocol.
- Verifier errors preserve public-input and sumcheck failures instead of
  reporting every failure as a Polygero error.

## Second pass: soundness boundaries

The second pass followed the verifier from circuit loading through both native
packing equations to the authenticated Polygero rows. No additional soundness
flaw was found in the new packing path. In particular:

- Polygero stores the received commitment and rejects a missing or different
  root. A proof cannot substitute an unbound root after sumcheck or packing.
- Private coordinates come from the originally committed words; both packing
  rows, the layer equations and the original pad products use that same root.
  The compiler substitutes every public contribution exactly once, preserving
  the affine target's signs and original pad coordinates.
- The identity path authenticates its final input equation even with no
  layers, no private inputs, or all-zero input weights. It does not discard
  a remaining constant equation. Nontrivial paths reject malformed U and
  authenticate A through the first native row.
- Field, embedding, chosen basis, circuit, witness count and pad layout are
  fixed before challenges. Neither the chosen numerical kernel nor untrusted
  proof lengths choose those parameters.

This pass found a coverage gap: the old constraint-compiler oracle exercised
the retained direct-field reference's final row. The regression now also
passes the same arbitrary symbolic constraints through the production compiler
and packing/backend handoff. Its residuals match an independent numerical
oracle over binary and prime fields, with zero challenges, zero alpha, zero
layers and every public-prefix size. The identity input equation has the
opposite sign to the reference, which the comparison checks explicitly.

The following application/setup premises remain explicit:

- Circuit bytes, field/extension implementations and interpolation domains
  are trusted. Mdoc's `load_trusted` checks archive metadata on each invocation;
  it does not recompute payload circuit IDs. Untrusted bundles require the
  strict loader (`from_compressed`/`load`) before use. This is the existing
  application loading contract, not authentication of arbitrary circuit files.
- The existing NEXT namespace limitation also applies to v9: requested
  namespace IDs must agree, but the circuit does not authenticate those IDs.
  Changing all IDs together is not prevented. Attribute names and values are
  bound. This preexisting application limitation remains unresolved.

## Validation and limits

Validation covers field arithmetic and sampling contracts, interpolation,
Ligero, Polygero, zk-v1/v2, generic packing, mdoc MAC constraints, codecs,
dependency boundaries and separate proof-role builds. Full application
benchmarks verify their generated proofs, reject altered public inputs, and
check equality across the binary numerical kernels. Commands and measurements
are in the [integration report](../../benches/results/2026-10-28-integrated-packing/README.md).

No sampling algorithm, random-draw schedule, specification document or Lean
source was changed by this audit. Earlier sampler fixes in this work are
covered by explicit byte-count and bit-mask tests.

The existing Lean `linear_native_soundness_probability` theorem bounds the
interactive native verifier error by 1/|F| for a false target and fixed committed
vector, allowing arbitrary mask cells and an adaptive second response.
`linear_backend_composition_card` keeps backend authentication failure as a
separate event. This does not establish a Rust-to-Lean refinement, a composed
Fiat–Shamir bound, or joint zero knowledge of the integrated Rust protocol.
Earlier measurements are retained in the [trace-zero report](../../benches/results/2026-10-28-trace-zero/README.md)
and [MLDSA report](../../benches/results/2026-10-28-packed-mldsa/README.md).
