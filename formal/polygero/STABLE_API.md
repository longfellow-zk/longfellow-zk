# Precious Polygero API

Until explicit further user order, the declarations marked **precious** in
[StableAPI.lean](StableAPI.lean) are a stable API. This includes the top-level
recursive extraction and soundness results, the major existing lemmas used in
the Polygero paper, and the public definitions and data contracts they use.

The development covers the paper's protocol and its formal proof machinery.
Hahn/Delsarte is a numerical counting refinement of that same protocol. Its
certificates must preserve the verifier, messages, commitment timing, challenge
and query distributions, and extraction algorithm. An additional protocol
variant requires explicit user order.

Preserve their fully qualified names, import paths, universe parameters,
hypotheses, conclusions, binder order and implicitness, and mathematical
meaning. Preserve public constructors and projections of protected data types.
Do not delete or rename these declarations, weaken their contracts, or replace
an extraction theorem with a soundness-only theorem. Proof improvements,
additional theorems, and internal refactoring are allowed while preserving this
surface. Retain compatibility declarations when introducing a new interface.
A different contract or removal of protection requires explicit user order.

The manifest uses `precious_api name fingerprint`, which applies the persistent
`precious` marker and checks the declaration's universe parameters and type
against a frozen fingerprint. Constructors and projections are checked too.
Fingerprints use the repository's pinned Lean toolchain and ignore binder names,
which are irrelevant to alpha-equivalence and may change when a declaration
moves. They retain binder order, types, and implicitness. They are compatibility
checks, not cryptographic digests. Proof bodies are excluded. **Do not regenerate
existing fingerprints merely to make a changed API pass.** Preservation of the
mathematical meaning of public definitions also requires review.

Import `polygero` to obtain the complete marked surface. The marker is available
as `[precious]`; tools can query
`RecursivePolygero.StableAPI.isPrecious env declarationName`.
`lake build polygero.APITest` checks the manifest, marker persistence, concrete
proof dependencies, and the existing foundational axiom audit.

The following table identifies the main paper results and their existing Lean
counterparts. Names below are under `RecursivePolygero`; supporting lemmas in
these modules are included in the manifest as well.

| Paper component | Protected declarations |
|---|---|
| MDS explosion (`lem:mds-explosion`) | `explosion`; `ProximityGap.support_extension_alternative`, `support_extension_eq_top`, `error_lower_bound`. |
| Slow growth and canonical MDS core (`lem:mds-growth`, `thm:mds-core`) | `ProximityGap.polynomialSpace_slow_growth`; `Local.Shift.quotient_growth_bound`, `rank_on_core_subset`, `restriction_rank_eq_min`, `canonicalSubset_rank`, `canonicalSubset_unitfree`. |
| Polynomial proximity gap | `ProximityGap.polynomial_error_threshold`, `dimension_proximity_gap`, `agreement_count_alternative`. |
| Consistency probabilities (`lc:lem:cons`, `lc:lem:rank`) | `Local.fixedConsistent_density`; `Local.ReducedSystems.badChallenges_card`, `low_defect_of_not_bad`. |
| Canonical reduction, closure and coverage (`lc:lem:reduction`, `lc:lem:closure`, `lc:lem:coverage`) | `Local.PolynomialClosure.canonical_core`, `closure_geometry`; `Local.ConsistencyClosure.inter_closure_canonicalSubset`, `solutions_closure`, `deleted_coordinate_witness`; `Local.ReducedSystems.assign`, `capacity_witness`. |
| Overlap identifies a system (`lc:lem:core-union`, `lc:lem:systems`) | `Local.PolynomialClosure.core_union_mds`, `canonical_closures_eq`; `Local.ReducedSystems.associated_intersection`. |
| Fixed rows and arithmetic exceptions (`lc:lem:full`, `lc:lem:residual-identity`, `lc:lem:exceptional`) | `affine_rows_of_full_consistency`, `identities_of_agreement`, `polynomialArithmeticMatches_card`; `ProfileAnalysis.systemExceptions_card`, `certify`. |
| Punctured decoding and the large-good-set dichotomy (`lc:lem:fixed-decoding`, `lc:lem:arithmetic-response-equality`, `lc:lem:dichotomy`) | `PuncturedDecoder` and its validity/completeness contract; `recoverRow_eq_some`, `recoverOnAt_decoder`, `scanRecoverAt_valid`, `scanRecoverAt_columns`; `primary_eq_of_full_set_agreement`; `ProfileAnalysis.large_response`. |
| Accepting-query count (`lc:lem:acceptance`) | `Local.Polygero.verify_openOracle_iff`; `ProfileAnalysis.responseCount_le_columns`, `response_fraction_le_envelope`. |
| Direct binomial counting and excess | `DirectBinomial.linear_bound`, `normalized_linear`, `excess_le`, `normalized_excess_le`; `DiscreteThreshold.sum_le_threshold`. |
| Exceptional maximum and response-uniform envelope (`lc:lem:maximum`, `thm:local-profile`) | `SystemException.weighted_sum_le_small_sum`, `mean_envelope_of_gated_frequency`, `random_target_envelope_mean`; `ProfileAnalysis.systemCap_excess`, `localEnvelope_mean`. |
| Recursive coefficient substitution (`lem:substitution`) | `coefficientStatement_satisfies`, `verifier_factorization`, `packed_response_satisfies`; `Child.verify_iff`. |
| Random-target recursive composition | `Protocol.ProfileProof.inducedFamily_frequency`, `randomTargetProbability_le`, `extraction_failure_le`. |
| Recursive knowledge extraction (`thm:deterministic-extraction`) | `Protocol.ProfileProof.extractTranscript_valid`, `extractWitness_valid`, `extractWitness_failure`, `wireExtract_valid`, `wire_extraction_failure`. |
| Product and additive errors; soundness corollaries | `Protocol.ProfileProof.error_eq_product`, `error_le_sum`, `soundness_of_extraction`, `false_statement`, `wire_false_statement`. |

The imported Hahn analysis is protected by the same policy. Its major API
consists of `DirectBinomial.active_card_le_of_uniformFamilyBound`,
`normalized_excess_le_of_uniformFamilyBound_threshold`,
`normalized_excess_le_of_uniformFamilyBound_direct`,
`normalized_excess_le_of_activeFamilyBound`, `HahnSystemCertificate` and its
constructors, and `ProfileAnalysis.systemCap_excess_of_hahn` and
`localEnvelope_mean_of_hahn`. The recursive endpoints and error identities in
`Protocol.HahnProfileProof` are precious, together with the original-profile
conversion. The extractor and error conversion lemmas live alongside their
definitions in `Recursion/Extractor.lean` and `Recursion/Error.lean`; the
witness and wire equalities live in `Theorems/Extraction.lean` and
`Theorems/WireExtraction.lean`. `Theorems/AnalysisInvariant.lean` proves
independence from packing certificate choices. Their names and signatures are
listed in the same manifest.

The decoder entry protects the formal validity/completeness contract and its
implementation here; it does not identify that implementation with the paper's
algorithmic runtime claim. The table maps formal counterparts, while the
manifest is the authoritative list of protected declarations.
