# Ligero V1/V2/V3 extraction and soundness

This development proves scalar Ligero IOP extraction, false-statement
soundness, and Fiat–Shamir extraction with Merkle binding. It includes exact
v7/v8 component certificates for all three variants.

**V1 is the shipped protocol. V2 and V3 are alternative protocols under
development.**

## Certified v7/v8 bounds

The exact IOP error is at most `2^-s`, with the following integer exponents:

| Component | V1 | V2 | V3 |
|---|---:|---:|---:|
| v7 signature (all attribute counts) | 123 | 191 | 191 |
| v7 hash (1–4 attributes) | 122 | 125 | 125 |
| v8 signature (all attribute counts) | 122 | 191 | 191 |
| v8 hash (1–4 attributes) | 121 | 125 | 125 |

For comparison, let `L = log₂(Q+1)`. The FS columns below give bits for the
FS term; the total error also includes `bindingError`. Each FS bit entry is
capped below at zero.

| Component | IOP V1 | IOP V2 | IOP V3 | FS V1 | FS V2 | FS V3 |
|---|---:|---:|---:|---:|---:|---:|
| v7 signature | 123 | 191 | 191 | 123−L | 191−L | 191−L |
| v7 hashes | 122 | 125 | 125 | 122−L | 125−L | 125−L |
| v8 signature | 122 | 191 | 191 | 122−L | 191−L | 191−L |
| v8 hashes | 121 | 125 | 125 | 121−L | 125−L | 125−L |

[OptimizedIOPCertificates](examples/Ligero/Longfellow/OptimizedIOPCertificates.lean)
checks all geometry, field-order, clique/Johnson, and rational-budget premises.
[EnvelopeFSCertificates](examples/Ligero/Longfellow/EnvelopeFSCertificates.lean)
instantiates the local FS contract, extraction, and soundness for all 30
component/variant records. The
[IOP catalog](examples/Ligero/Longfellow/optimized-iop-certified-results.json)
and [FS catalog](examples/Ligero/Longfellow/envelope-fs-certified-results.json)
record their exact parameters and theorem names.

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
| Validity and agreement guarantees for the response-assisted extractor | `LigeroFamily.ScalarGapExtraction.extract_valid`, `extract_agreement_errors` | [ScalarGapExtraction](LigeroFamily/Soundness/ScalarGapExtraction.lean) |
| Scalar IOP extraction for V1, V2, and V3 | `Ligero.V1/V2/V3.scalarGap_extraction_failure`, `scalarGap_iop_extraction_failure` | [V1](Ligero/V1/ScalarGapExtraction.lean), [V2](Ligero/V2/ScalarGapExtraction.lean), [V3](Ligero/V3/ScalarGapExtraction.lean) |
| Refined IOP extraction with a single response-uniform envelope | `Ligero.V1/V2/V3.scalarGap_profiled_extraction_failure`, `ScalarGapExtraction.profiledUniformEnvelope_mean_of_strategies` | [V1](Ligero/V1/ScalarGapProfiled.lean), [V2](Ligero/V2/ScalarGapProfiled.lean), [V3](Ligero/V3/ScalarGapProfiled.lean), [Shared proof](LigeroFamily/Soundness/ScalarGapProfiled.lean) |
| False-statement soundness from extractor validity | `ScalarGapExtraction.Certificate.false_statement`, `CertifiedResult.v1/v2/v3_interactive` | [ScalarGapExtraction](LigeroFamily/Soundness/ScalarGapExtraction.lean), [ProfiledExtraction](examples/Ligero/Longfellow/ProfiledExtraction.lean) |
| Merkle prefix binding and consistency of accepted openings | `Merkle.MH.PrefixBindingGame.bad_ratio_le`, `PrefixBindingFamily.boundMessage_game_eq` | [PrefixBinding](../merkle/Merkle/PrefixBinding.lean) |
| Typed Fiat–Shamir extraction with a linear query factor | `Bcs.EnvelopeFiatShamir.FixedKey.extraction_ratio_le_capped` | [FixedKeyEnvelopeFiatShamir](../bcs/Bcs/FixedKeyEnvelopeFiatShamir.lean) |
| Merkle-committed Ligero Fiat–Shamir extraction and false-statement soundness | `LigeroFamily.EnvelopeFS.extraction_ratio_le`, `soundness_ratio_le` | [EnvelopeCompiler](LigeroFamily/Soundness/EnvelopeCompiler.lean) |
| Exact IOP and Fiat–Shamir instances for every v7/v8 signature/hash geometry and variant | `Optimized.v7*/v8*` extraction, interactive, uniform-envelope, and FS endpoints | [IOP certificates](examples/Ligero/Longfellow/OptimizedIOPCertificates.lean), [FS certificates](examples/Ligero/Longfellow/EnvelopeFSCertificates.lean) |

Example theorem names in the table abbreviate the shared namespace
`Ligero.Examples.Grid`. `CertifiedResult` is in
`Ligero.Examples.Grid.LongfellowProfiledExtraction`; component endpoints are
in its `Optimized` namespace.

## Protocol variants and extraction

V1 uses the original unchecked arithmetic masks. V2 uses four checked
base-code mask rows. V3 checks quadratic rows directly in opened columns and
retains the full witness layout. Scalar batching is used throughout.

The extractor takes the committed oracle, statement, challenge, and response.
A successful extraction returns a witness satisfying the original constraints.
The IOP extraction-failure event is verifier acceptance together with the
extractor returning `none`. Its bound holds for arbitrary statements and
prover response strategies; false-statement soundness follows by validity.

In the IOP experiment, the oracle is committed before the uniform batching
challenge, and the response precedes the independent uniform fixed-size
column query. The refined proof supplies one envelope fixed from the oracle
and statement that bounds every response's query acceptance probability.
Its challenge mean supplies the error coefficient used by the FS compiler.

## Fiat–Shamir bound and experiment

For IOP error coefficient `epsilon`, the compiled bound is

```text
bindingError + min(1, (Q+1)*epsilon)
```

`Q` is the adversary's random-oracle query budget. The proof obtains the
`Q+1` factor from the fixed-key typed compiler and its defining-query
completion. The response-uniform envelope supplies the coefficient directly.

The formal experiment uses independent finite Merkle and typed FS tapes,
a shared commitment prefix preceding the FS experiment, and a defining alpha
key and typed adversary fixed independently of the Merkle tape. Merkle prefix
binding supplies the opening-consistency event and its error term.

## Organization and checking

The common protocol and extraction proofs are in `LigeroFamily`. Variant
bridges are in `Ligero/V1`, `Ligero/V2`, and `Ligero/V3`.
[FiniteResponse](LigeroFamily/Protocol/FiniteResponse.lean) supplies finite
response instances, while
[FirstOccurrenceTrace](../bcs/Bcs/FirstOccurrenceTrace.lean) supplies query-slot
bookkeeping. [Certificate](examples/Ligero/Certificate.lean) contains the shared
example arithmetic. `Ligero.API` exposes the extraction surface, and
`Ligero.APITest` checks it together with representative component endpoints.

From `formal/`, build and audit with:

```sh
lake build
python3 ligero/examples/Ligero/scripts/audit_envelope_fs.py
```

The FS audit checks 19 general core theorems, 90 component FS endpoints, all
30 catalog geometries, and the coefficient table. General core theorems use
Lean's foundational axioms. Exact concrete certificates also use explicitly
identified native arithmetic checks.
