# ZK V2

Ordinary `ZkProver` and `ZkVerifier` compose sumcheck v2, generic dual packing,
and ambient-only Polygero. Mdoc and MLDSA use these same entry points.

Witness generators return ordinary `F::E` circuit inputs. `commit` consumes
private inputs and retains them for numerical sumcheck; `prove` consumes the
commitment state and takes public inputs. Public inputs pass through unchanged,
including values outside the packing base field. The constraint compiler
substitutes their contribution into the final input claim.

The field's `PackingField::Packing` adapter selects F/K. The wrapper validates
private-input membership in K and packs internally. `new_full_field` selects
the identity adapter for circuits with unrestricted field-valued inputs,
including historical NEXT v8. `with_extension` selects another trusted adapter.
Parameters and initialization state are explicitly owned.

## Shared layout and compilation

The physical witness is:

```text
packed private inputs | packing masks | GKR pads and products
```

One shared layout determines the GKR pad start and product triples passed to
Polygero. The constraint compiler uses that same physical pad layout. Symbolic
products require only this layout; dual packing translates the final linear
claim over private inputs.

`commitment.rs` owns packing parameters and native-row compilation. Its separate
prover/verifier role modules own Polygero state and the packing/backend handoff.
They receive the final input claim and compiled GKR layer equations, independently
of sumcheck's symbolic representation. All rows use `sum_w A[c,w]*w + b[c] = 0`.
The ordinary zk-v2 roles retain the numerical/symbolic sumcheck orchestration.
The compiler moves its dense input-weight vector into this handoff. Inputs are
packed once, and temporary claims and rows are released before Polygero proving.
Identity commitments retain no second committed-word vector through sumcheck.

Mdoc v9 supplies every hash-circuit input as a field-valued bit, including its
six private MAC masks and seven public MAC values. The circuit reconstructs
those field values and checks its MAC equations. There are no separate MAC
auxiliary cells or external MAC claims. The semantic witness manifest contains
only input counts, the SHA compiler variant and the Boolean witness recipe.
The compiler checks that committed recipe outputs are independent of the public
MAC values derived after commitment.

## Transcript and formats

The extension descriptor, circuit ID and layout counts are bound before the
root. Public inputs are bound before sumcheck. Dual packing then absorbs U,
samples independent delta coordinates, and absorbs A. The Polygero source
statement identifier follows A. Both native packing equations are authenticated
against the original root alongside the GKR layer equations. Packing adds no
product constraints. Identity extensions use one input per word and send no
packing masks, messages or challenges.

Every v2 proof uses `LFV4`: root, sumcheck, the degree-dependent packing response,
and ambient-only `PLG8`. Trusted geometry fixes the response length; the adapter
descriptor is transcript-bound. Identity responses occupy zero bytes. Earlier
LFV3/LFB4/LFM1 envelopes are rejected. Development caches use `MDOCNEXT3` and
`MDOCBIT6`; the v9 semantic manifest is `LFHASH02`. V1 formats are unchanged.
LFC1/LFC2 preserve legacy `subfield_boundary`; v2 requires zero. Polygero has no
subfield argument and samples every mask in the ambient field.
Interpolation exposes only `apply`; the legacy subfield encoding hint was removed.

## Validation and limits

Tests cover binary, sextic and identity profiles, partial words, arbitrary
full-field public inputs, canonical decoding, truncation, adversarial messages,
exact native-row residuals, shared pad products, and proof equality across
Boolean numerical kernels. The optional Boolean kernel uses the ordinary
kernel when public inputs are not Boolean. Role and dependency checks keep
prover/verifier implementations and V1/V2 implementations separate.
Sampling functions and specification documents were unchanged by this integration.
Custom bases must complement K at coordinate zero; construction rejects bases
that violate the mask relation's privacy requirement.

The existing [Lean model](../../../formal/lfzk-v2/README.md) proves its stated
extraction bound under explicit premises; it does not certify this new packing
composition. No composed Fiat–Shamir bound, joint zero-knowledge simulation,
or formal Rust refinement is claimed. See the [dual-packing audit](../dual-packing/AUDIT.md)
and [integration benchmarks](../../benches/results/2026-10-28-integrated-packing/README.md).
