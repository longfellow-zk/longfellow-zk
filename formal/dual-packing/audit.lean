import DualPacking

#print axioms DualPacking.canonical_bit
#print axioms DualPacking.binary_card
#print axioms DualPacking.ArtinSchreier.trace_mask
#print axioms DualPacking.ArtinSchreier.trace_coordinates
#print axioms DualPacking.ArtinSchreier.trace_forms
#print axioms DualPacking.ArtinSchreier.Instance.error_ne_zero
#print axioms DualPacking.ArtinSchreier.Instance.acceptance_forces_dot
#print axioms DualPacking.ArtinSchreier.frobenius_batch_card_le
#print axioms DualPacking.ArtinSchreier.Instance.verify_iff_native
#print axioms DualPacking.ArtinSchreier.Instance.contract_mask
#print axioms DualPacking.ArtinSchreier.Instance.adapterCell_count
#print axioms DualPacking.ArtinSchreier.Instance.native_completeness
#print axioms DualPacking.ArtinSchreier.Instance.native_soundness_probability
#print axioms DualPacking.ArtinSchreier.Instance.backend_composition_card
#print axioms DualPacking.ArtinSchreier.soundness_binary128

-- Audited simplification: no Frobenius-consistency premise or verification gate.
#print axioms DualPacking.affine_batch_card_le
#print axioms DualPacking.ArtinSchreier.Instance.linearTwo_iff_affine_dot
#print axioms DualPacking.ArtinSchreier.frobenius_affine_card_le
#print axioms DualPacking.ArtinSchreier.Instance.linearVerify_iff_native
#print axioms DualPacking.ArtinSchreier.Instance.nativeLinearVerify_affine
#print axioms DualPacking.ArtinSchreier.Instance.native_linear_completeness
#print axioms DualPacking.ArtinSchreier.Instance.linear_native_soundness_probability
#print axioms DualPacking.ArtinSchreier.Instance.linear_backend_composition_card
#print axioms DualPacking.ArtinSchreier.linear_soundness_binary128
#print axioms DualPacking.ArtinSchreier.Audit.inconsistentFrobenius_false
#print axioms DualPacking.ArtinSchreier.Audit.inconsistentFrobenius_linear_accepts
#print axioms DualPacking.ArtinSchreier.Audit.inconsistentFrobenius_checked_rejects

-- Public precomputation computes the same dual used by the verifier theorem.
#print axioms DualPacking.traceDual_eq_gramDual
#print axioms DualPacking.traceDual_eq_of_pairings
#print axioms DualPacking.powerBasis_traceDual
#print axioms DualPacking.dual_quotient_leading
#print axioms DualPacking.dual_quotient_recurrence
#print axioms DualPacking.dual_derivative_ne_zero
#print axioms DualPacking.ArtinSchreier.coefficient_gramDual

-- The paper's trace-first exposition and its exact link to public coefficients.
#print axioms DualPacking.ArtinSchreier.trace_bit
#print axioms DualPacking.ArtinSchreier.trace_pow_sum
#print axioms DualPacking.ArtinSchreier.trace_one
#print axioms DualPacking.ArtinSchreier.exists_trace_one
#print axioms DualPacking.ArtinSchreier.trace_pairing_nondegenerate
#print axioms DualPacking.ArtinSchreier.artinSchreier_ker
#print axioms DualPacking.ArtinSchreier.trace_zero_iff_exists
#print axioms DualPacking.ArtinSchreier.trace_base_inner_product
#print axioms DualPacking.ArtinSchreier.base_claim_iff_trace_zero
#print axioms DualPacking.ArtinSchreier.base_claim_iff_exists
#print axioms DualPacking.ArtinSchreier.trace_rowAdjoint
#print axioms DualPacking.ArtinSchreier.coefficient_eq_rowAdjoint
#print axioms DualPacking.ArtinSchreier.coefficient_eq_dualPack

-- Actual finite-field operations, cardinality bridge, and binary recovery.
#print axioms DualPacking.extension_card
#print axioms DualPacking.ArtinSchreier.frobenius_fixed_iff
#print axioms DualPacking.ArtinSchreier.trace_mem_base
#print axioms DualPacking.ArtinSchreier.trace_frobenius
#print axioms DualPacking.ArtinSchreier.trace_inverse_degree
#print axioms DualPacking.ArtinSchreier.frobenius_coordinates
#print axioms DualPacking.ArtinSchreier.Instance.combined_frobenius_offset
#print axioms DualPacking.ArtinSchreier.Instance.proverMessage_count
#print axioms DualPacking.ArtinSchreier.linear_soundness_by_basis_size
#print axioms DualPacking.ArtinSchreier.linear_soundness_degree_six
#print axioms DualPacking.ArtinSchreier.linear_soundness_prime_degree_six
#print axioms DualPacking.ArtinSchreier.frobenius_binary
#print axioms DualPacking.ArtinSchreier.trace_zero_iff_exists_binary
#print axioms DualPacking.ArtinSchreier.Instance.honestU_binary
#print axioms DualPacking.ArtinSchreier.Instance.nativeLinearVerify_binary
#print axioms DualPacking.ArtinSchreier.Instance.nativeVerify_binary

-- The complete verifier on an actual odd-characteristic extension.
#print axioms DualPacking.ArtinSchreier.FiniteFieldCases.frobenius_not_square
#print axioms DualPacking.ArtinSchreier.FiniteFieldCases.honest_accepts
#print axioms DualPacking.ArtinSchreier.FiniteFieldCases.malicious_false
#print axioms DualPacking.ArtinSchreier.FiniteFieldCases.malicious_accepts_one_challenge
#print axioms DualPacking.ArtinSchreier.FiniteFieldCases.malicious_rejects_checked
#print axioms DualPacking.ArtinSchreier.FiniteFieldCases.malicious_soundness
