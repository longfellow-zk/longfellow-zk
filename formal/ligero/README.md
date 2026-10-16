# Ligero V1/V2/V3 extraction and soundness

This development proves scalar Ligero IOP extraction and false-statement
soundness. It includes exact v7/v8 component certificates for all three
variants and separate local challenge/query count certificates.

**V1 is the shipped protocol. V2 and V3 are alternative protocols under
development.**

## Certified v7/v8 bounds

At 132 distinct column openings, the IOP error is at most `2^-s`, with the
following integer exponents:

| Component | V1 | V2 | V3 |
|---|---:|---:|---:|
| v7 signature (all attribute counts) | 127 | 191 | 191 |
| v7 hash (1–4 attributes) | 125 | 126 | 126 |
| v8 signature (all attribute counts) | 127 | 191 | 191 |
| v8 hash (1–4 attributes) | 125 | 126 | 126 |

The V1 entries use Hahn/Delsarte certificates for the unchecked-mask list
below the Johnson threshold. The degree 9–17 certificates improve the
previous V1 bounds from 125/124/125/123 to 127/125/127/125 bits.
The V2/V3 hash entries use the integer three-set packing bound to certify
a shared decoded-witness list of at most two candidates, improving 125 to
126 bits. The list bound applies to the complete proximity-tested matrix.

For the v7 hash components, a separate [four-slice V1 IOP theorem](../lfzk/Lfzk/V1StrongV7Interactive.lean)
uses the response actually transmitted by V1. It bounds acceptance with
response-assisted extraction failure for any challenge-adaptive payload, and
also bounds ordinary acceptance when the committed lift list has no satisfying
witness. The exact rational coefficients give these approximate decimal
exponents; the V2/V3 columns are their existing checked-mask IOP certificates.

| v7 hash attributes | V1 general response | V1 four-slice response | V2 | V3 |
|---|---:|---:|---:|---:|
| 1 | 125.158571 | **125.511851** | 126.162713 | 126.162713 |
| 2 | 125.063102 | **125.433177** | 126.152485 | 126.152485 |
| 3 | 125.139915 | **125.456238** | 126.163808 | 126.163808 |
| 4 | 125.096525 | **125.419222** | 126.154433 | 126.154433 |

The four-slice V1 theorem is specific to v7. The general-response v7/v8
certificates and the V2/V3 integer bounds in the table above remain valid.
The V1 improvement does not transfer to V2 or V3: those verifiers check four
mask rows and use distinct response and decoder types. No stronger V2/V3 IOP
theorem is established by the four-slice argument.
The challenge-adaptive response step is a generic finite-counting lemma in
[ResponsePairCounting](LigeroFamily/Soundness/ResponsePairCounting.lean); the
balanced hash-decoder bridge remains in Longfellow.

[OptimizedIOPCertificates](examples/Ligero/Longfellow/OptimizedIOPCertificates.lean)
checks all geometry, field-order, clique/Johnson, Hahn/Delsarte, and
rational-budget premises.
The [IOP catalog](examples/Ligero/Longfellow/optimized-iop-certified-results.json)
records exact parameters and theorem names.

Each signature geometry covers one through four attributes. Hash components
have separate records for each attribute count. The signature field is the
P-256 base field; the hash field has order `2^128`.

The v8 instance dimensions are:

| Component | openings r | payload w | block k | encoded length | tested n | witness rows | total rows |
|---|---:|---:|---:|---:|---:|---:|---:|
| Signature | 132 | 362 | 494 | 4445 | 3458 | 12 | 18 |
| Hash, 1 attribute | 132 | 452 | 584 | 5255 | 4088 | 165 | 171 |
| Hash, 2 attributes | 132 | 451 | 583 | 5246 | 4081 | 173 | 179 |
| Hash, 3 attributes | 132 | 451 | 583 | 5246 | 4081 | 181 | 187 |
| Hash, 4 attributes | 132 | 451 | 583 | 5246 | 4081 | 189 | 195 |

All use `rateinv = 7`, `k = r+w`, and
`n = encoded length - (2*k-1)`. The
[parameter records](examples/Ligero/Longfellow/v8-extracted-parameters.json)
retain the current Rust source provenance and generated circuit identifiers.

## Major proved results

| Result | Main theorem or interface | Source |
|---|---|---|
| Reed–Solomon minimum distance and the concrete multiplicative-code instance | `ReedSolomon.evaluation_code_minimum_distance`, `LongfellowIOP.certificateCodeFacts` | [Distance](ReedSolomon/Distance.lean), [IOPParameters](examples/Ligero/Longfellow/IOPParameters.lean) |
| Selected-MCA proximity bounds from affine triple counting and punctured globalization | `SelectedMCA.directionallyNonliftableParameters_card_le_direct`, `closeCombinationChallengesOn_card_le_of_direction_far` | [DirectLineExtraction](SelectedMCA/DirectLineExtraction.lean), [Punctured](SelectedMCA/Punctured.lean) |
| Reed–Solomon JB agreement with the η³ threshold, including checked inverse-η parameters | `JBAgreement.lineFailureBound_of_johnsonConditions`, `lineFailureBound_of_inverseEtaConditions` | [Certificate](JBAgreement/Certificate.lean), [InverseEtaCertificate](JBAgreement/InverseEtaCertificate.lean) |
| Delsarte LP bound using Hahn kernels for uniform intersection families (Johnson is degree one), with decidable integer certificates | `CodingTheory.HahnDelsarte.card_le_of_delsarte`, `hahnKernel_gram_nonneg`, `uniformFamilyBound_of_certificate` | [HahnDelsarte](CodingTheory/ListDecoding/HahnDelsarte.lean), [UniformFamily](CodingTheory/ListDecoding/UniformFamily.lean) |
| Integer one- and two-candidate packing bounds, and an independent packing interface for the shared decoded-witness list | `CodingTheory.uniformFamilyBound_one_of_two_mul_gt`, `uniformFamilyBound_two_of_three_mul_gt`, `SchemeLiftCandidate.univ_card_le_uniformFamilyBound` | [UniformFamily](CodingTheory/ListDecoding/UniformFamily.lean), [SchemeFixedLiftList](LigeroFamily/Soundness/SchemeFixedLiftList.lean) |
| V1 unchecked-mask list bounded by any uniform-family bound (Johnson above, Hahn/Delsarte below the Johnson threshold) | `Ligero.V1.responseWordsAgreeingAtLeast_card_le_of_bound`, `Ligero.V1.V1MaskRange` | [MaskAgreement](Ligero/V1/Soundness/MaskAgreement.lean), [V1Profile](Ligero/V1/Soundness/V1Profile.lean), [HahnMaskCertificates](examples/Ligero/Longfellow/HahnMaskCertificates.lean) |
| Validity and agreement guarantees for the response-assisted extractor | `LigeroFamily.ScalarGapExtraction.extract_valid`, `extract_agreement_errors` | [ScalarGapExtraction](LigeroFamily/Soundness/ScalarGapExtraction.lean) |
| Scalar IOP extraction for V1, V2, and V3 | `Ligero.V1/V2/V3.scalarGap_extraction_failure`, `scalarGap_iop_extraction_failure` | [V1](Ligero/V1/ScalarGapExtraction.lean), [V2](Ligero/V2/ScalarGapExtraction.lean), [V3](Ligero/V3/ScalarGapExtraction.lean) |
| Refined IOP extraction with a single response-uniform envelope | `Ligero.V1/V2/V3.scalarGap_profiled_extraction_failure`, `ScalarGapExtraction.profiledUniformEnvelope_mean_of_strategies` | [V1](Ligero/V1/ScalarGapProfiled.lean), [V2](Ligero/V2/ScalarGapProfiled.lean), [V3](Ligero/V3/ScalarGapProfiled.lean), [Shared proof](LigeroFamily/Soundness/ScalarGapProfiled.lean) |
| V1 v7 four-slice response IOP extraction and no-decoded-solution soundness | `V1StrongV7Interactive.v7_v1_payload_iop_uniform_failure_le`, `v7_v1_payload_iop_uniform_acceptance_of_noDecoded_le` | [Four-slice IOP](../lfzk/Lfzk/V1StrongV7Interactive.lean) |
| Graded, extraction-first V1 IOP bound for any checked monotone agreement potential | `Ligero.V1.scalarGap_profiled_potential_extraction_failure_le`, `scalarGap_profiled_potential_acceptance_of_noDecoded` | [PotentialExtraction](Ligero/V1/PotentialExtraction.lean), [PotentialProfile](LigeroFamily/Soundness/PotentialProfile.lean) |
| False-statement soundness from extractor validity | `ScalarGapExtraction.Certificate.false_statement`, `CertifiedResult.v1/v2/v3_interactive` | [ScalarGapExtraction](LigeroFamily/Soundness/ScalarGapExtraction.lean), [ProfiledExtraction](examples/Ligero/Longfellow/ProfiledExtraction.lean) |
| Merkle prefix binding and consistency of accepted openings | `Merkle.MH.PrefixBindingGame.bad_ratio_le`, `PrefixBindingFamily.boundMessage_game_eq` | [PrefixBinding](../merkle/Merkle/PrefixBinding.lean) |
| Exact IOP instances and local count certificates for v7/v8 geometries | `Optimized.v7*/v8*` extraction and interactive endpoints; `CountCertificate` | [IOP certificates](examples/Ligero/Longfellow/OptimizedIOPCertificates.lean), [count certificates](examples/Ligero/Longfellow/AdaptiveOptimizedCertificates.lean) |

Example theorem names in the table abbreviate the shared namespace
`Ligero.Examples.Grid`. `CertifiedResult` is in
`Ligero.Examples.Grid.LongfellowProfiledExtraction`; component endpoints are
in its `Optimized` namespace.

## Protocol variants and extraction

V1 uses the original unchecked arithmetic masks. V2 uses four checked
base-code mask rows. V3 checks quadratic rows directly in opened columns and
retains the full witness layout. Scalar batching is used throughout.

For V1, the arithmetic profile charges probability one only below the mask
threshold. Above it, the response-code words agreeing with an unchecked mask on
at least `a` columns form `a`-subsets meeting pairwise in at most `2k-1`
columns, so any uniform-family bound limits them. The Johnson count gives a
finite bound only for `a² > n(2k-1)`. One Hahn/Delsarte certificate of degree
9–17 extends the bound 38–68 agreement levels further down. Its cutoff is
selected against the complete extraction budget. By size monotonicity it
covers every level up to the Johnson threshold. Each certificate is an
integer nonnegative combination of Hahn kernels, checked against every
realizable overlap by the proved Gram-kernel interface. The polynomial
construction used to generate candidates is not an assumption of the proof.

The extractor takes the committed oracle, statement, challenge, and response.
A successful extraction returns a witness satisfying the original constraints.
The IOP extraction-failure event is verifier acceptance together with the
extractor returning `none`. Its bound holds for arbitrary statements and
prover response strategies; false-statement soundness follows by validity.

In the IOP experiment, the oracle is committed before the uniform batching
challenge, and the response precedes the independent uniform fixed-size
column query. The refined proof supplies one envelope fixed from the oracle
and statement that bounds every response's query acceptance probability.
Its challenge mean supplies the error coefficient used in the Longfellow analysis.

## Local count certificates

The local V1, V2, and V3 challenge/query counts come from their profiled
agreement proofs, uniformly over the response fixed before the query draw.
The count certificates below are checked arithmetic statements for those
local budgets.

Exact v7/v8 profile thresholds give the following **per-round count**
exponents. For each entry, both the escape-challenge fraction and the
doomed-challenge accepting-query fraction are at most `2^-b`. The optimized
hash geometries and their validity and count proofs are checked in
[AdaptiveHashCertificates](examples/Ligero/Longfellow/AdaptiveHashCertificates.lean).
Here "optimized" records improved certified choices; the development does not
prove that no other parameters or certificates give a stronger bound.
[AdaptiveCountCertificates](examples/Ligero/Longfellow/AdaptiveCountCertificates.lean)
supplies the integer counts and V1/V2/V3 escape-budget adapters. V2 and V3
use the same checked-mask counts.
The V1 signature rows are in
[AdaptiveSignatureCertificates](examples/Ligero/Longfellow/AdaptiveSignatureCertificates.lean).
They use separate, checked
[Hahn mask certificates](examples/Ligero/Longfellow/HahnMaskFSSignature.lean)
with the Johnson line geometry; their verifier and mask policy remain V1.

| Geometry | V1 `b` | V2 `b` | V3 `b` |
|---|---:|---:|---:|
| v7 signature | 132 | — | — |
| v7 hashes 1–4 | 117 | 120 | 120 |
| v8 signature | 131 | — | — |
| v8 hashes 1–4 | 117 | 120 | 120 |

The V2/V3 signature entries at 191 bits in the IOP table above are certified
flat IOP bounds, not local challenge/query count certificates. No local count
record for those signature rows is asserted here.

The exact integer escape count has a rounding cost strictly below one
challenge point, as proved by `CountCertificate.escape_ratio_lt`.

## Organization and checking

The common protocol and extraction proofs are in `LigeroFamily`. Variant
bridges are in `Ligero/V1`, `Ligero/V2`, and `Ligero/V3`.
[FiniteResponse](LigeroFamily/Protocol/FiniteResponse.lean) supplies finite
response instances, while
[FirstOccurrenceTrace](../bcs/Bcs/FirstOccurrenceTrace.lean) supplies query-slot
bookkeeping. [Certificate](examples/Ligero/Certificate.lean) contains the shared
example arithmetic. `Ligero.API` exposes the extraction surface, and
`Ligero.APITest` checks it together with representative component endpoints.

From `formal/`, build the ordinary Longfellow development with:

```sh
lake build Lfzk
lake build Lfzk.V1StrongV7Interactive  # separate v7 V1 four-slice IOP bound
```

The improved Ligero local-count certificates, including the V1
signature Hahn checks above, have a separate target. Its script builds the
independent v7/v8 radius ranges two at a time before assembling the public
certificate theorems; the assembly does not repeat the polynomial checks.
The aggregate
[AdaptiveOptimizedCertificates](examples/Ligero/Longfellow/AdaptiveOptimizedCertificates.lean)
module preserves the existing import path. Hash-only users can build
`examples.Ligero.Longfellow.AdaptiveHashCertificates` without importing the
signature range checks.

```sh
ligero/examples/Ligero/scripts/build_ligero_local_counts.sh
```

To regenerate the V1 Hahn/Delsarte mask certificates (stdlib-only Python,
with exact polynomial generation and independent Gram-kernel checks), run:

```sh
python3 ligero/examples/Ligero/scripts/hahn_mask_certificates.py \
  --lean-module ligero/examples/Ligero/Longfellow/HahnMaskCertificates.lean
```

The exact concrete certificates use native arithmetic checks.
