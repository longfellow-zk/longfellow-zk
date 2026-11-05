import LfzkV2
import LfzkV2.Native.APITest
import LfzkV2.Linear.Tests.APITest
import Lean.Util.CollectAxioms

/-! Build the public API and reject unchecked proof dependencies. -/

open Lean Elab Command

run_cmd do
  for endpoint in #[``LfzkV2.CommittedSlot.index_injective,
      ``SumcheckV2.affine_layer_completeness, ``SumcheckV2.affine_layer_reduction,
      ``LfzkV2.Native.buildConstraints_correct, ``LfzkV2.Native.buildFrom_products,
      ``LfzkV2.Native.compiled_iff_clear, ``LfzkV2.Native.CircuitLayer.effective_truth,
      ``LfzkV2.Native.Circuit.soundness_reduction,
      ``LfzkV2.Native.Circuit.compiled_circuit_reduction,
      ``LfzkV2.Native.Circuit.prove_complete, ``LfzkV2.Native.Circuit.tests_valid,
      ``LfzkV2.Native.Circuit.tests_soundness, ``LfzkV2.Native.Circuit.tests_budget_le_sharp,
      ``LfzkV2.Native.Circuit.constraints_tests_soundness,
      ``LfzkV2.Native.Replay.read_constraints,
      ``LfzkV2.Native.Replay.reconstructionFromAnswers_eq_of_prefix,
      ``LfzkV2.Native.Replay.reconstructionFromAnswers_padKeys,
      ``LfzkV2.Native.Replay.semanticData_valid,
      ``LfzkV2.Native.Replay.semantic_bad_of_accepts,
      ``LfzkV2.Native.Replay.semanticData_eq_of_prefix,
      ``LfzkV2.Native.Replay.pointData_valid, ``LfzkV2.Native.Replay.pointData_eq,
      ``LfzkV2.Packed.FiatShamir.pointBad_sum_le,
      ``LfzkV2.Packed.FiatShamir.path_charge_ge_one,
      ``LfzkV2.Packed.FiatShamir.event_soundness_le,
      ``LfzkV2.Packed.FiatShamir.slotBudget_sum,
      ``LfzkV2.Packed.CompiledSide.path_charge_ge_one,
      ``LfzkV2.Packed.CompiledSide.accepts_of_extraction,
      ``LfzkV2.Packed.TwoFieldReplay.hashInput_injective,
      ``LfzkV2.Packed.TwoFieldPotential.extract_valid,
      ``LfzkV2.Packed.TwoFieldPotential.path_charge_ge_one,
      ``LfzkV2.Packed.TwoFieldFS.extraction_le,
      ``LfzkV2.Packed.TwoFieldCommitmentFS.extraction_le,
      ``LfzkV2.Packed.TwoFieldReplay.preparedProof_coherent,
      ``LfzkV2.Packed.RawExtraction.key_coherent,
      ``LfzkV2.Packed.RawExtraction.probability_eq_annotated,
      ``LfzkV2.Packed.RawExtraction.probability_small_merkle,
      ``LfzkV2.Packed.RawExtraction.probability_le,
      ``LfzkV2.Packed.Statement.rows_iff_native,
      ``LfzkV2.Packed.Statement.satisfies_rows,
      ``LfzkV2.Packed.Statement.source_claim_iff,
      ``LfzkV2.Packed.Statement.frontend_or_bad,
      ``LfzkV2.Packed.Statement.unpack_binary_bit,
      ``LfzkV2.Packed.Statement.sampled_candidates_card_le,
      ``LfzkV2.Packed.Compiled.satisfies_frontend_or_bad,
      ``LfzkV2.Packed.Compiled.side, ``LfzkV2.Packed.Direct.side,
      ``LfzkV2.Packed.Compiled.profiledSide,
      ``LfzkV2.Packed.Compiled.profiledSide_profiled,
      ``LfzkV2.Packed.Direct.profiledSide,
      ``LfzkV2.Packed.Direct.profiledSide_profiled,
      ``LfzkV2.Packed.RuntimeCost.error_le,
      ``LfzkV2.Packed.RuntimeSecurity.tsec_117_of_merkle_ge,
      ``LfzkV2.Packed.RawRuntimeExtraction.probability_bound,
      ``LfzkV2.Packed.RawRuntimeExtraction.extraction_117,
      ``LfzkV2.buildConstraints_correct, ``LfzkV2.productsHold_iff,
      ``LfzkV2.compiled_iff_clear, ``LfzkV2.chain_completeness,
      ``LfzkV2.compiled_reduction, ``LfzkV2.CircuitLayer.effective_truth,
      ``LfzkV2.Circuit.execution_consistent, ``LfzkV2.Circuit.soundness_reduction,
      ``LfzkV2.Circuit.prove_complete, ``LfzkV2.compiled_circuit_reduction,
      ``LfzkV2.ChallengeTest.card_bad_le, ``LfzkV2.Circuit.tests_soundness,
      ``LfzkV2.Circuit.tests_budget_le,
      ``LfzkV2.assertionIndices_card_le_one, ``LfzkV2.Circuit.tests_budget_le_sharp,
      ``LfzkV2.RoundReplay.roundTests_eq, ``LfzkV2.RoundReplay.bad_card_le,
      ``LfzkV2.RoundReplay.dataAt_eq_of_message_prefix,
      ``LfzkV2.RoundReplay.round_bad_iff,
      ``LfzkV2.OutputReplay.outputTests_eq, ``LfzkV2.AssertionReplay.assertionTests_eq,
      ``LfzkV2.OutputReplay.dataAt_budget,
      ``LfzkV2.ChallengeBlocks.output_bad_card,
      ``LfzkV2.ChallengeBlocks.assertion_bad_card,
      ``LfzkV2.ChallengeBlocks.Data.card_bad_le,
      ``LfzkV2.ChallengeBlocks.Sampler.raw_bad_card,
      ``LfzkV2.AssertionReplay.indices_model_eq,
      ``LfzkV2.Transcript.prefix_answers, ``LfzkV2.Transcript.at_eq_of_message_prefix,
      ``LfzkV2.Transcript.context_off_of_fiber,
      ``LfzkV2.FiatShamir.Setup.soundness_le,
      ``LfzkV2.FiatShamir.Setup.fixed_candidate_soundness_le,
      ``LfzkV2.FiatShamir.OracleSetup.soundness_le,
      ``LfzkV2.FiatShamir.OracleSetup.fixed_candidate_soundness_le,
      ``LfzkV2.FiatShamir.BlockOracleSetup.soundness_le,
      ``LfzkV2.FiatShamir.OracleSetup.weightedCharge_sum_le,
      ``LfzkV2.FiatShamir.OracleSetup.weighted_charge_mean_le,
      ``LfzkV2.Backend.decoded_compiled,
      ``LfzkV2.Reconstruction.decoded_accepts,
      ``LfzkV2.Reconstruction.satisfies_accepts,
      ``LfzkV2.Nizk.frontend_soundness, ``LfzkV2.Nizk.composed_soundness,
      ``LfzkV2.ComposedFS.soundness_le,
      ``RecursivePolygero.Counting.committedCandidates_card_le,
      ``RecursivePolygero.Counting.exists_committedCandidate,
      ``RecursivePolygero.NonrecursiveFS.decoded_outside_list_le,
      ``LfzkV2.Interactive.soundness_le,
      ``LfzkV2.Interactive.soundness_le_fiatShamir_frontend,
      ``LfzkV2.Masking.uniform_fiber,
      ``LfzkV2.PolygeroMasking.translate_response, ``LfzkV2.PolygeroMasking.translate_openings,
      ``LfzkV2.PolygeroMasking.correction_properties,
      ``LfzkV2.PolygeroMasking.arithmetic_response_preserved,
      ``LfzkV2.PolygeroMasking.sameDistribution_adaptive,
      ``LfzkV2.PolygeroPrimaryMasking.translate_response,
      ``LfzkV2.PolygeroPrimaryMasking.translate_openings,
      ``LfzkV2.PolygeroPrimaryMasking.response_eval,
      ``LfzkV2.PolygeroPrimaryMasking.sameDistribution,
      ``LfzkV2.PolygeroCoreMasking.productWidth_bounds,
      ``LfzkV2.PolygeroCoreMasking.product_mem,
      ``LfzkV2.PolygeroCoreMasking.encoding_mem,
      ``LfzkV2.PolygeroCoreMasking.encoding_product,
      ``LfzkV2.PolygeroCoreMasking.zero_encoding_linearValue,
      ``LfzkV2.PolygeroCoreMasking.translate_openings,
      ``LfzkV2.PolygeroZk.payload_verifies,
      ``LfzkV2.PolygeroZk.toSim_opening, ``LfzkV2.PolygeroZk.toSim_payload,
      ``LfzkV2.PolygeroZk.toSim_injective,
      ``LfzkV2.PolygeroZk.adaptive_translate,
      ``LfzkV2.PolygeroZk.sameDistribution_adaptive,
      ``LfzkV2.PolygeroZk.statClose_adaptive,
      ``LfzkV2.BackendEncoding.rows_supported,
      ``LfzkV2.BackendEncoding.compatible_encoded,
      ``LfzkV2.BackendEncoding.compatible_compiled,
      ``LfzkV2.Replay.readFrom_wellFormed,
      ``LfzkV2.Replay.read_constraints,
      ``LfzkV2.Replay.layerSlot_injective,
      ``LfzkV2.Replay.layer_budget_sum,
      ``LfzkV2.Replay.budget_sum,
      ``LfzkV2.Replay.semantic_bad_of_accepts,
      ``LfzkV2.Replay.semanticData_eq_of_prefix,
      ``LfzkV2.Replay.message_parse_eq,
      ``LfzkV2.Replay.prefixData_eq,
      ``LfzkV2.Replay.ancestor_at,
      ``LfzkV2.Replay.pointData_eq,
      ``LfzkV2.Replay.frontendSetup_bad_of_accepts,
      ``LfzkV2.Replay.frontend_soundness_le,
      ``LfzkV2.Replay.reconstruction_accepts,
      ``LfzkV2.Replay.reconstruction_eq_of_answers,
      ``LfzkV2.Replay.context_eq_of_off_two,
      ``RecursivePolygero.NonrecursiveFS.committed_composition_le,
      ``RecursivePolygero.MerkleCompiler.verify_of_accepts,
      ``RecursivePolygero.MerkleCompiler.verify_of_extraction,
      ``LfzkV2.ConcreteFS.soundness_le,
      ``LfzkV2.CommitmentFS.cutOracle_off,
      ``LfzkV2.CommitmentFS.soundness_le,
      ``RecursivePolygero.NonrecursiveFS.maxFailureAgreement_tail_le_profile,
      ``RecursivePolygero.NonrecursiveFS.failure_potential_mean_le,
      ``RecursivePolygero.NonrecursiveFS.failure_challenge_hash_charge_le,
      ``RecursivePolygero.NonrecursiveFS.failure_query_hash_charge_le,
      ``RecursivePolygero.NonrecursiveFS.query_hash_charge_le_of_noSat,
      ``RecursivePolygero.NonrecursiveFS.terminalPotential,
      ``RecursivePolygero.NonrecursiveFS.step_potential_mean_le,
      ``RecursivePolygero.NonrecursiveFS.stepTerminalPotential,
      ``LfzkV2.Replay.readFrom_eq_of_prefix,
      ``LfzkV2.Replay.reconstructionFromAnswers_eq_of_prefix,
      ``LfzkV2.GradedReplay.hashInput_injective,
      ``LfzkV2.GradedReplay.parent_view_eq,
      ``LfzkV2.GradedReplay.child_view_eq,
      ``LfzkV2.GradedFS.charge_sum_le,
      ``LfzkV2.GradedFS.path_charge_ge_one,
      ``LfzkV2.GradedFS.event_soundness_le,
      ``LfzkV2.GradedFS.soundness_le,
      ``LfzkV2.GradedFS.compiled_soundness_le,
      ``LfzkV2.GradedFS.compiled_extraction_failure_le,
      ``LfzkV2.GradedCommitmentFS.soundness_le,
      ``LfzkV2.TwoFieldReplay.hashInput_key,
      ``LfzkV2.TwoFieldReplay.hashInput_injective,
      ``LfzkV2.TwoFieldReplay.prefix_one,
      ``LfzkV2.TwoFieldReplay.prefix_two,
      ``LfzkV2.TwoFieldReplay.prefix_two_first,
      ``LfzkV2.TwoFieldReplay.sum_hashInput,
      ``LfzkV2.CompiledSide.charge_sum_le,
      ``LfzkV2.CompiledSide.accepts_of_extraction,
      ``LfzkV2.CompiledSide.path_charge_ge_one,
      ``LfzkV2.MacData.affine,
      ``LfzkV2.Mac.collision_card_le_one,
      ``LfzkV2.Mac.uniform_tag_card,
      ``LfzkV2.Mac.uniform_joint_tag_card,
      ``LfzkV2.MacData.collision,
      ``LfzkV2.MacData.charge_sum_le,
      ``LfzkV2.TwoFieldPotential.charge_sum_le,
      ``LfzkV2.TwoFieldPotential.extract_none_iff,
      ``LfzkV2.TwoFieldPotential.extract_valid,
      ``LfzkV2.TwoFieldPotential.path_charge_ge_one,
      ``LfzkV2.TwoFieldFS.extraction_le,
      ``LfzkV2.TwoFieldFS.extraction_le_of_total,
      ``LfzkV2.TwoFieldFS.prepared_extraction_le,
      ``LfzkV2.GradedFS.slotBudget_sum,
      ``LfzkV2.TwoFieldFS.slotBudget_sum,
      ``LfzkV2.GradedFS.maxBudget_div_eq,
      ``LfzkV2.GradedFS.slotBudget_sum_div_eq,
      ``LfzkV2.TwoFieldFS.error_eq,
      ``LfzkV2.RuntimeProfiles.Profile.potential_budgets_le,
      ``LfzkV2.RuntimeProfiles.Hash.profile,
      ``LfzkV2.RuntimeProfiles.Signature.profile,
      ``LfzkV2.CompiledSide.withProfile_statement,
      ``LfzkV2.CompiledSide.withProfile_accepts,
      ``LfzkV2.CompiledSide.withProfile_budgets_le,
      ``LfzkV2.RuntimeCost.error_le,
      ``LfzkV2.RuntimeSecurity.tsec_114,
      ``LfzkV2.RuntimeSecurity.tsec_117_of_ge,
      ``LfzkV2.RuntimeSecurity.tsec_117_of_merkle_ge,
      ``Merkle.MH.path_depth_lt_seen_length,
      ``Merkle.MH.childrenEarlier_of_not_childHit,
      ``Merkle.MH.smallBudget_acceptance_ratio_le,
      ``Merkle.MH.OpeningClaim.distinctLeafInputs_of_index,
      ``Merkle.MH.numberedBudget_acceptance_ratio_le,
      ``Bcs.TotalOracleCommit.Setup.merkle_small_ratio_le,
      ``Bcs.TotalOracleCommit.Setup.merkle_numbered_ratio_le,
      ``LfzkV2.TwoFieldCommitmentFS.failureProbability_le_one,
      ``LfzkV2.TwoFieldCommitmentFS.failureProbability_le,
      ``LfzkV2.RuntimeExtraction.extraction_114,
      ``LfzkV2.RuntimeExtraction.extraction_117_of_ge,
      ``LfzkV2.RawRuntimeExtraction.key_coherent,
      ``LfzkV2.RawRuntimeExtraction.probability_eq_annotated,
      ``LfzkV2.RawRuntimeExtraction.probability_bound,
      ``LfzkV2.RawRuntimeExtraction.probability_small_merkle,
      ``LfzkV2.RawRuntimeExtraction.probability_numbered_merkle,
      ``LfzkV2.RawRuntimeExtraction.extraction_114,
      ``LfzkV2.RawRuntimeExtraction.extraction_117_of_ge,
      ``LfzkV2.RawRuntimeExtraction.extraction_117,
      ``Bcs.TotalOracle.CtxGrinding.verifierQuery_budget_le,
      ``Bcs.TotalOracle.CtxGrinding.potential_ratio_le_of_total,
      ``LfzkV2.TwoFieldReplay.prepareBody_fixLeft,
      ``LfzkV2.TwoFieldReplay.preparedProof_coherent,
      ``LfzkV2.TwoFieldCommitmentFS.cutOracle_off,
      ``LfzkV2.TwoFieldCommitmentFS.check_contains_one,
      ``LfzkV2.TwoFieldCommitmentFS.check_contains_two,
      ``LfzkV2.TwoFieldCommitmentFS.extraction_le,
      ``LfzkV2.TwoFieldCommitmentFS.zeroQuery_verifierEvent_ratio_eq,
      ``LfzkV2.TwoFieldCommitmentFS.zeroQuery_verifierEvent_ratio_le] do
    for ax in ← collectAxioms endpoint do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom in V2 endpoint {endpoint}: {ax}"

namespace LfzkV2.APITest

open SumcheckV2 Classical

-- A scalar layer has no rounds but still needs the terminal product check.
private def scalarTranscript : LayerTranscript (Fin 2) (Fin 3) ℚ :=
  ⟨[], [], 0, 0, 0, 1, 2, 0⟩

private def scalarConstraints : Constraints (Fin 2) (Fin 3) ℚ :=
  ⟨[scalarTranscript.constraint zeroClaim], scalarTranscript.nextClaim⟩

example : buildConstraints [scalarTranscript] = some scalarConstraints := rfl

example : buildConstraints [{scalarTranscript with challenges := [1]}] = none := rfl
example : buildConstraints [{scalarTranscript with rounds := [(⟨0, 0⟩, 0, 1)]}] = none := rfl

private def badProducts : Fin 3 → ℚ := ![1, 1, 0]

-- All affine rows accept, including the input row, if the product slot is unconstrained.
-- The separate product check rejects this witness and the clear verifier rejects it.
example :
    RowsHold (compile scalarConstraints Fin.castSucc Fin.elim0
      (fun _ : Fin 1 => 1) (fun _ => 1) Fin.elim0) badProducts ∧
      ¬ ProductsHold scalarConstraints Fin.castSucc badProducts ∧
      ¬ ClearAccepts (badProducts ∘ Fin.castSucc) 0 [scalarTranscript] 1 := by
  norm_num [RowsHold, compile, compileLayer, compileInput, scalarConstraints,
    scalarTranscript, LayerTranscript.constraint, zeroClaim, mapTerms,
    LayerTranscript.nextClaim, PadExpression.claimNext, PadExpression.subtractClaimProduct,
    PadExpression.eval, ProductsHold, ClearAccepts, LayerTranscript.clearRounds,
    LayerTranscript.clearA, LayerTranscript.clearB, verify_multi_round, badProducts, dot]
  decide

-- Assertion occurrences must survive even when every ordinary output is zero.
private def assertionLayer : CircuitLayer (Cube 0) (Cube 0) (Fin 1) ℚ :=
  ⟨fun _ _ _ => 0, fun _ => (), fun _ => ()⟩

private def falseAssertion : Circuit ℚ 0 0 := .layer 1 assertionLayer .input

example : falseAssertion.eval (fun _ => 1) = 0 := by
  funext i
  simp [falseAssertion, Circuit.eval, CircuitLayer.outputs, assertionLayer, quadratic]

example : ¬ falseAssertion.Satisfies (fun _ => 1) := by
  simp [Circuit.Satisfies, falseAssertion, Circuit.AssertionsValid, Circuit.eval,
    assertionLayer, CircuitLayer.residuals]

-- Assertion weights replace the whole weighted coefficient, even at output weight zero.
example : assertionLayer.effective (fun _ => 0) (fun _ => 7) () () = 7 := by
  simp [CircuitLayer.effective, CircuitLayer.assertionKernel, assertionLayer]

example : AssertionBad (0 : ℚ) 0 (fun _ : Fin 1 => 0) (fun _ => 1) := by
  refine ⟨0, ?_, ?_⟩
  · intro j hj
    exact (by omega : False).elim
  · simp [BadLinear, assertionOffset]

-- A proof without layers still has an input equation and cannot skip its zero claim.
example : buildConstraints ([] : List (LayerTranscript Unit Unit ℚ)) =
    some ⟨[], zeroClaim⟩ := rfl

example (pads : Unit → ℚ) : ¬ ClearAccepts pads 0
    ([] : List (LayerTranscript Unit Unit ℚ)) 1 := by
  norm_num [ClearAccepts]

-- The first scalar layer has three committed slots, after all private inputs.
example : (CommittedSlot.pad (nPrivate := 5)
    (GeometrySlot.claim (rounds := 0) (rest := []) 2)).index = 7 := rfl

example : (GeometrySlot.there
    (GeometrySlot.claim (rounds := 2) (rest := []) 2) : GeometrySlot [0, 2]).index = 9 := rfl

end LfzkV2.APITest
