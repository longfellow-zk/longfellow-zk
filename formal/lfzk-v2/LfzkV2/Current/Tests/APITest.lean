import LfzkV2.Current
import LfzkV2.Current.Tests.Algebra
import LfzkV2.Current.Tests.SharedSHA
import LfzkV2.Current.Tests.Joint
import LfzkV2.Current.Tests.EarlyOutputs
import LfzkV2.Current.Tests.FrontendReplay
import LfzkV2.Current.Tests.FrontendVerifier
import LfzkV2.Current.Tests.FrontendBody
import LfzkV2.Current.Tests.FrontendSchedule
import LfzkV2.Current.Tests.ApplicationPrefix
import LfzkV2.Current.Tests.ApplicationViews
import LfzkV2.Current.Tests.FrontendTopology
import LfzkV2.Current.Tests.OpeningBody
import LfzkV2.Current.Tests.BackendBody
import LfzkV2.Current.Tests.BackendChallenges
import LfzkV2.Current.Tests.BatchPacket
import LfzkV2.Current.Tests.ByteCodecs
import LfzkV2.Current.Tests.ProofBodyCodec
import LfzkV2.Current.Tests.MdocAdvice
import LfzkV2.Current.Tests.ConcreteSetup
import LfzkV2.Current.Tests.ConcreteMetadata
import LfzkV2.Current.Tests.MdocIdentifiers
import LfzkV2.Current.Tests.MdocDefaults
import LfzkV2.Current.Tests.QueryCodec
import LfzkV2.Current.Tests.QueryRuntime
import LfzkV2.Current.Tests.WireBlocks
import LfzkV2.Current.Tests.OpeningSampling
import LfzkV2.Current.Tests.ReplayCongruence
import LfzkV2.Current.Tests.Tightness
import LfzkV2.Current.Tests.ZeroKnowledgeBackend
import LfzkV2.Current.Tests.ZeroKnowledgeBackendCells
import LfzkV2.Current.Tests.ZeroKnowledgeBackendStatement
import LfzkV2.Current.Tests.ZeroKnowledgeBackendCompiled
import LfzkV2.Current.Tests.ZeroKnowledgeBackendRuntime
import LfzkV2.Current.Tests.ZeroKnowledgeBackendRuntimeEncoding
import LfzkV2.Current.Tests.ZeroKnowledgeBackendRuntimeReal
import LfzkV2.Current.Tests.ZeroKnowledgeBackendRuntimeSatisfaction
import LfzkV2.Current.Tests.ZeroKnowledgeBackendRuntimeSimulator
import LfzkV2.Current.Tests.ZeroKnowledgeBackendRuntimeMixed
import LfzkV2.Current.Tests.ZeroKnowledgeCanonicalPublic
import LfzkV2.Current.Tests.ZeroKnowledgeCanonicalCompletion
import LfzkV2.Current.Tests.ZeroKnowledgeCompleteBody
import LfzkV2.Current.Tests.ZeroKnowledgeCompleteSimulator
import LfzkV2.Current.Tests.ZeroKnowledgeCompleteVerifier
import LfzkV2.Current.Tests.ZeroKnowledgeFrontend
import LfzkV2.Current.Tests.ZeroKnowledgeFrontendAdapter
import LfzkV2.Current.Tests.ZeroKnowledgePacking
import LfzkV2.Current.Tests.ZeroKnowledgePackingCells
import LfzkV2.Current.Tests.ZeroKnowledgeGlobalCoins
import LfzkV2.Current.Tests.ZeroKnowledgeHash
import LfzkV2.Current.Tests.ZeroKnowledgeFrontendPrefix
import LfzkV2.Current.Tests.ZeroKnowledgeFrontendComplete
import LfzkV2.Current.Tests.ZeroKnowledgeFrontendSetup
import LfzkV2.Current.Tests.ZeroKnowledgeProbabilityInstances
import LfzkV2.Current.Tests.ZeroKnowledgeHonestTranscript
import LfzkV2.Current.Tests.ZeroKnowledgeHonestTranscriptMdoc
import LfzkV2.Current.Tests.ZeroKnowledgeHonestTranscriptRecording
import LfzkV2.Current.Tests.ZeroKnowledgeHonestRunRows
import LfzkV2.Current.Tests.ZeroKnowledgeMdocPublicSetup
import LfzkV2.Current.Tests.ZeroKnowledgeMdocWitness
import LfzkV2.Current.Tests.ZeroKnowledgeMdocSHAWindow
import LfzkV2.Current.Tests.ZeroKnowledgeMdocRawSHAWindow
import LfzkV2.Current.Tests.ZeroKnowledgeSHASetup
import LfzkV2.Current.Tests.ZeroKnowledgeSHAComplement
import LfzkV2.Current.Tests.ZeroKnowledgeSHAGlobalWindow
import LfzkV2.Current.Tests.ZeroKnowledgeTranscriptObserver
import LfzkV2.Current.Tests.ZeroKnowledgeTranscriptObserverExperiment
import LfzkV2.Current.Tests.ZeroKnowledgeTranscriptObserverTrace
import LfzkV2.Current.Tests.ZeroKnowledgeTranscriptOracleProbability
import LfzkV2.Current.Tests.ZeroKnowledgeRequestedSimulator
import LfzkV2.Current.Tests.ZeroKnowledgeSHAOracle
import LfzkV2.Current.Tests.ZeroKnowledgeError
import LfzkV2.Current.Tests.ZeroKnowledgeCommonLabels
import LfzkV2.Current.Tests.ZeroKnowledgeOracleBytes
import LfzkV2.Current.Tests.ZeroKnowledgeOracleCanonicalAncestors
import LfzkV2.Current.Tests.ZeroKnowledgeOracleHonest
import LfzkV2.Current.Tests.ZeroKnowledgeOracleNormalization
import LfzkV2.Current.Tests.ZeroKnowledgeOracleWindow
import LfzkV2.Current.Tests.ZeroKnowledgeOracleProgramming
import LfzkV2.Current.Tests.ZeroKnowledgeOraclePrimaryFreshness
import LfzkV2.Current.Tests.ZeroKnowledgeOracleRefresh
import LfzkV2.Current.Tests.ZeroKnowledgeOracleRuntime
import LfzkV2.Current.Tests.ZeroKnowledgeOracleView
import LfzkV2.Current.Tests.ZeroKnowledgeTerminalOpening
import LfzkV2.Current.Tests.ZeroKnowledgeObserver
import LfzkV2.Current.Tests.ZeroKnowledgeMerkle
import LfzkV2.Current.Tests.ZeroKnowledgeMerkleOracleWindow
import LfzkV2.Current.Tests.ZeroKnowledgeMerkleRuntimeTransport
import LfzkV2.Current.Tests.ZeroKnowledgeMerkleBackend
import LfzkV2.Current.Tests.ZeroKnowledgeMerkleCache
import LfzkV2.Current.Tests.ZeroKnowledgeMerklePrequery
import LfzkV2.Current.Tests.ZeroKnowledgeMerkleRefresh
import LfzkV2.Current.Tests.ZeroKnowledgeMerkleCommitRefresh
import LfzkV2.Current.Tests.ZeroKnowledgeMerkleCommitLabels
import LfzkV2.Current.Tests.ZeroKnowledgeMerkleCommitPrepared
import LfzkV2.Current.Tests.ZeroKnowledgeMerklePreparation
import LfzkV2.Current.Tests.ZeroKnowledgeMerklePreparationLabels
import LfzkV2.Current.Tests.ZeroKnowledgeBackendRuntimeContext
import LfzkV2.Current.Tests.ZeroKnowledgeBackendRuntimeContextEncoding
import LfzkV2.Current.Tests.ZeroKnowledgeBackendRuntimeContextGlobal
import LfzkV2.Current.Tests.ZeroKnowledgeBackendRuntimeContextReal
import LfzkV2.Current.Tests.ZeroKnowledgeBackendRuntimeContextRealCoins
import LfzkV2.Current.Tests.ZeroKnowledgeBackendRuntimeContextRealProgrammed
import LfzkV2.Current.Tests.ZeroKnowledgeBackendRuntimeContextRealView
import LfzkV2.Current.Tests.ZeroKnowledgeBackendRuntimeContextSimulator
import LfzkV2.Current.Tests.ZeroKnowledgeBackendRuntimeReachable
import LfzkV2.Current.Tests.ZeroKnowledgeBackendRuntimeRealCoins
import LfzkV2.Current.Tests.ZeroKnowledgeBackendRuntimeRefreshCoins
import LfzkV2.Current.Tests.ZeroKnowledgeBackendRuntimeRefreshedKey
import LfzkV2.Current.Tests.ZeroKnowledgeBackendRuntimeRegroup
import LfzkV2.Current.Tests.ZeroKnowledgeContextRefresh
import LfzkV2.Current.Tests.ZeroKnowledgeMdocOracleWindows
import LfzkV2.Current.Tests.ZeroKnowledgeObserverStateful
import LfzkV2.Current.Tests.ZeroKnowledgeOracleHonestRefreshResult
import LfzkV2.Current.Tests.ZeroKnowledgeOracleMarginals
import LfzkV2.Current.Tests.ZeroKnowledgeOracleRefreshObservation
import LfzkV2.Current.Tests.ZeroKnowledgeRequestedContext
import LfzkV2.Current.Tests.ZeroKnowledgeMdocContextPrivacy
import LfzkV2.Current.Tests.ZeroKnowledgeMdocZeroKnowledge
import TranscriptV2.Tests.Framing
import LfzkV2.Current.EntryChallenges
import TranscriptV2.SharedCharging
import TranscriptV2.SharedReduction
import Mathlib.Data.ZMod.Basic
import Lean.Util.CollectAxioms

namespace LfzkV2.Current.Tests

def scalar : Frontend := ⟨[⟨[⟨0, 1⟩], [⟨0, 0, 0, 0⟩], 0⟩], []⟩
def fragmented : Frontend :=
  ⟨[⟨[⟨0, 2⟩, ⟨1, 0⟩], [⟨0, 0, 0, 0⟩, ⟨1, 0, 1, 2⟩], 1⟩], [⟨2, 1⟩]⟩

def geometry : Geometry where
  binary := fragmented
  prime := scalar
  binaryCells := 3
  primeCells := 2
  packingDegree := 2
  packingPositive := by decide
  rowDimension := 4
  maskingDegree := 1
  columns := 8
  openings := 2
  openingsPositive := by decide
  openings_lt := by decide
  openings_le := by decide
  responseFits := by decide
  productFits := by decide

-- Empty vectors do not add or remove boundaries. Fragments share a layer query.
example : scalar.roles .prime =
    [.assertions .prime 0 [⟨0, 1⟩] [⟨0, 0, 0, 0⟩],
      .terminal .prime 0, .combine .prime 0 []] := by decide +kernel

example : (fragmented.roles .binary).map Role.domain =
    [.assertions, .sumcheck, .terminal, .combine] := by decide

example : (Frontend.roles .binary ⟨[], [⟨0, 1⟩]⟩) =
    [.inputAssertions .binary [⟨0, 1⟩]] := by decide

-- A shallower circuit enters at the next stage; terminals remain global.
example : (Frontend.roles .binary
    ⟨[⟨[⟨0, 1⟩], [⟨0, 0, 0, 0⟩], 2⟩,
      ⟨[⟨1, 1⟩], [⟨0, 1, 0, 0⟩, ⟨1, 0, 0, 0⟩], 1⟩], []⟩).map Role.domain =
    [.assertions, .sumcheck, .sumcheck, .terminal, .combine,
      .assertions, .sumcheck, .terminal, .combine] := by decide

example : geometry.roles.map Role.domain =
    [.fingerprint, .assertions, .terminal, .combine, .rowBatching, .rescaling,
      .conversion, .assertions, .sumcheck, .terminal,
      .combine, .packing, .batching, .opening] := by decide

example : geometry.roles.length + 1 = 15 := by decide
example : geometry.actions.take 4 =
    [.bind .setup, .query .fingerprint, .bind .fingerprints, .bind (.frontend .prime)] := by decide

example : ({geometry with packingDegree := 1, packingPositive := by decide}.roles).length = 13 :=
  by decide
example : packingActions 1 = [] := rfl
example : geometry.affineRows .binary = 5 ∧ geometry.affineRows .prime = 3 := by decide
example : geometry.dataRows .binary = 3 ∧ geometry.dataRows .prime = 2 := by decide

abbrev fields : Fields | .binary => ZMod 2 | .prime => ZMod 5
instance (side : Side) : Zero (fields side) := by cases side <;> exact inferInstance

example : Samples geometry fields .fingerprint =
    (((Fin 3 → ZMod 2) × (Fin 3 → ZMod 2)) × ((Fin 2 → ZMod 5) × (Fin 2 → ZMod 5))) := rfl
example : Samples geometry fields .conversion = (Fin 2 → {x : ZMod 5 // x ≠ 0}) := rfl
example : Samples geometry fields .opening = (Fin 2 ↪ Fin 8) := rfl
example : Fintype.card (Samples geometry fields (.terminal .binary 0)) = 1 := by decide
example : Fintype.card (Samples geometry fields (.sumcheck .binary 0 0)) = 2 := by decide

abbrev OneInput := Input [.fingerprint] Bool Bool Bool Bool
def first : OneInput := .round ⟨0, by decide⟩ false true
def finalSealInput (link body : Bool) : OneInput := .finalSeal (false, true, link) body

example : Input.parent first = none := rfl
example (link body : Bool) : Input.parent (finalSealInput link body) = some first := rfl
example (link body : Bool) : Input.claimed false (finalSealInput link body) = link := rfl
example (link body : Bool) : Input.rank (finalSealInput link body) = 1 := rfl
example (link body : Bool) : Input.domain first ≠ Input.domain (finalSealInput link body) := by
  simp [Input.domain, first, finalSealInput]
example (link : Bool) : finalSealInput link false ≠ finalSealInput link true := by
  intro h
  have := Input.finalSeal_body_bound h
  cases this
example (body : Bool) : finalSealInput false body ≠ finalSealInput true body := by
  intro h
  have := congrArg (Input.claimed false) h
  cases this

-- Changing the final answer cannot change the reconstructed earlier answer.
example (link body : Bool) (H : OneInput → Bool × Bool) :
    (finalSealInput link body).priorAnswers H ⟨0, by change 0 < 1; decide⟩ = (H first).2 := rfl

example (link body : Bool) (H H' : OneInput → Bool × Bool)
    (h : Bcs.TotalOracle.AgreeOff (finalSealInput link body) H H') :
    (finalSealInput link body).priorAnswers H = (finalSealInput link body).priorAnswers H' :=
  Input.priorAnswers_off _ h

-- A zero-boundary protocol still has a body-binding final query.
example (context body : Bool) :
    Input.parent (.finalSeal context body : Input [] Bool Bool Bool Bool) = none := rfl

end LfzkV2.Current.Tests

open Lean Elab Command

run_cmd do
  for endpoint in #[
      ``LfzkV2.Current.EntryChallenges.entry_assertion_truth,
      ``LfzkV2.Current.EntryChallenges.entry_assertion_reduction,
      ``LfzkV2.Current.EntryChallenges.combine_entry_error,
      ``LfzkV2.Current.EntryChallenges.combine_entry_reduction,
      ``LfzkV2.Current.EntryChallenges.last_layer_reduction,
      ``LfzkV2.Current.EntryChallenges.block_bad_card_mul_le,
      ``LfzkV2.Current.EntryChallenges.sequential_entry_cover,
      ``LfzkV2.Current.EntryChallenges.sequential_combine_cover,
      ``LfzkV2.Current.EntryChallenges.two_events_card_mul_le,
      ``LfzkV2.Current.FrontendReplay.slots_positive,
      ``LfzkV2.Current.FrontendReplay.slots_eq,
      ``LfzkV2.Current.FrontendReplay.queryIndex_lt,
      ``LfzkV2.Current.FrontendReplay.queryIndex_ge,
      ``LfzkV2.Current.FrontendReplay.readFrom_eq_of_prefix,
      ``LfzkV2.Current.FrontendReplay.constraints_total,
      ``LfzkV2.Current.FrontendTranscript.readFrom_writeFrom,
      ``LfzkV2.Current.FrontendTranscript.read_write,
      ``LfzkV2.Current.FrontendTranscript.layerMessage_readFrom_congr,
      ``LfzkV2.Current.FrontendTranscript.layerMessage_prefix,
      ``LfzkV2.Current.FrontendVerifier.constraints_built,
      ``LfzkV2.Current.FrontendVerifier.PrimeSetup.replay,
      ``LfzkV2.Current.FrontendVerifier.PackedSetup.replay,
      ``LfzkV2.Current.FrontendBody.read_exists_iff_shape,
      ``LfzkV2.Current.FrontendBody.decode_exists_iff_shape,
      ``LfzkV2.Current.FrontendBody.read_write,
      ``LfzkV2.Current.FrontendVerifier.PrimeSetup.prepareBody_decoded,
      ``LfzkV2.Current.FrontendVerifier.PrimeSetup.prepareBody_exists_iff_shape,
      ``LfzkV2.Current.FrontendVerifier.PackedSetup.prepareBody_decoded,
      ``LfzkV2.Current.FrontendVerifier.PackedSetup.prepareBody_exists_iff_shape,
      ``LfzkV2.Current.FrontendBody.prefix_message_of_some,
      ``LfzkV2.Current.FrontendSchedule.Plan.coalesced,
      ``LfzkV2.Current.FrontendSchedule.Plan.fits,
      ``LfzkV2.Current.FrontendSchedule.Plan.stage_widths,
      ``LfzkV2.Current.FrontendSchedule.Plan.slots_eq_roles_length,
      ``LfzkV2.Current.FrontendSchedule.Plan.frontend_role_get_queryIndex,
      ``LfzkV2.Current.FrontendSchedule.Plan.locatedRole_side,
      ``LfzkV2.Current.FrontendSchedule.Plan.locatedRole_coordinates_le,
      ``LfzkV2.Current.Replay.Encoding.readAt_replay,
      ``LfzkV2.Current.Replay.Encoding.protocol_readAt,
      ``LfzkV2.Current.StatementCompiler.equationIndex_value,
      ``LfzkV2.Current.StatementCompiler.compile_fields,
      ``LfzkV2.Current.StatementCompiler.compile_selected_views,
      ``LfzkV2.Current.ApplicationPrefix.readPrime_spec,
      ``LfzkV2.Current.ApplicationPrefix.readBinary_spec,
      ``LfzkV2.Current.ApplicationPrefix.decodeChecked_spec,
      ``LfzkV2.Current.ApplicationPrefix.prime_payload_agrees,
      ``LfzkV2.Current.ApplicationPrefix.binary_payload_agrees,
      ``LfzkV2.Current.ApplicationPrefix.decodeChecked_off,
      ``LfzkV2.Current.ApplicationViewReplay.strictAnswer_replay,
      ``LfzkV2.Current.ApplicationViewReplay.frontendTape_replay_eq,
      ``LfzkV2.Current.ApplicationViewReplay.messages_replay_eq,
      ``LfzkV2.Current.ApplicationViewReplay.readAt_replay_eq,
      ``LfzkV2.Current.ApplicationViewReplay.readPrimePacket_from_late,
      ``LfzkV2.Current.ApplicationViewReplay.readPrime_from_late,
      ``LfzkV2.Current.ApplicationViewReplay.readAdapter_of_readBinary,
      ``LfzkV2.Current.ApplicationViewReplay.readAdapter_from_late,
      ``LfzkV2.Current.ApplicationViewReplay.readBinaryPacket_from_late,
      ``LfzkV2.Current.ApplicationViewReplay.readPackingPacket_of_readBinaryPacket,
      ``LfzkV2.Current.ApplicationViews.readPackingPacket_off,
      ``LfzkV2.Current.ApplicationViews.primeView_from_late,
      ``LfzkV2.Current.ApplicationViews.binaryView_from_late,
      ``LfzkV2.Current.RuntimeRoles.prime_single,
      ``LfzkV2.Current.RuntimeRoles.binary_single,
      ``LfzkV2.Current.RuntimeRoles.rowBatching_single,
      ``LfzkV2.Current.RuntimeRoles.rescaling_single,
      ``LfzkV2.Current.RuntimeRoles.conversion_single,
      ``LfzkV2.Current.RuntimeRoles.packing_single,
      ``LfzkV2.Current.RuntimeRoles.fingerprint_single,
      ``LfzkV2.Current.RuntimeBackend.failure_charged,
      ``LfzkV2.Current.RuntimeParameters.binary_list_card,
      ``LfzkV2.Current.RuntimeParameters.prime_list_card,
      ``LfzkV2.Current.RuntimeParameters.querySetup,
      ``LfzkV2.Current.RuntimeShape.publicQueries,
      ``LfzkV2.Current.FrontendTopology.Same.plan,
      ``LfzkV2.Current.FrontendTopology.Same.frontend,
      ``LfzkV2.Current.FrontendTopology.Same.capacity,
      ``LfzkV2.Current.ApplicationSetup.BinaryPublic.same_template,
      ``LfzkV2.Current.ApplicationSetup.BinaryPublic.planFromTemplate_frontend,
      ``LfzkV2.Current.ApplicationSetup.BinaryPublic.planFromTemplate_capacity,
      ``LfzkV2.Current.RuntimeAdaptiveRate7.ratio_le,
      ``LfzkV2.Current.CanonicalRate7.ratio_le,
      ``LfzkV2.Current.IdealRate7.ratio_le,
      ``LfzkV2.Current.IdealProofRate7.ratio_le,
      ``LfzkV2.Current.MdocProofRate7.ratio_le,
      ``LfzkV2.Current.MdocRuntime.quotient_base,
      ``LfzkV2.Current.MdocIdentifiers.setup,
      ``LfzkV2.Current.MdocIdentifiers.parameters,
      ``LfzkV2.Current.ConcreteMetadata.primeData_readback,
      ``LfzkV2.Current.MdocAdvice.read_encode,
      ``LfzkV2.Current.MdocAdvice.decode_total,
      ``LfzkV2.Current.MdocAdvice.decode_three_iff,
      ``LfzkV2.Current.ProofOutput.read_encode,
      ``LfzkV2.Current.ProofOutput.read_canonical,
      ``LfzkV2.Current.ProofOutput.seen_map,
      ``LfzkV2.Current.ProofOutput.window_map,
      ``LfzkV2.Current.IdealRuntime.rawSampler_decode,
      ``LfzkV2.Current.IdealRuntime.querySampler_decode,
      ``LfzkV2.Current.IdealRuntime.samplerLaws,
      ``LfzkV2.Current.OpeningSampling.orderedEquiv,
      ``LfzkV2.Current.OpeningSampling.decoder,
      ``LfzkV2.Current.OpeningFisherYates.ordered_succ,
      ``LfzkV2.Current.OpeningFisherYates.queryDecoder,
      ``LfzkV2.Current.RequestedApplication.true_at_request,
      ``LfzkV2.Current.CanonicalRuntime.encodings_eq,
      ``LfzkV2.Current.CanonicalRuntime.batching_publics,
      ``LfzkV2.Current.CanonicalRuntime.decoded_request,
      ``LfzkV2.Current.CanonicalRuntime.decoded_true_at_request,
      ``LfzkV2.Current.CanonicalReplay.Runtime.canonical_of_blocks,
      ``LfzkV2.Current.CanonicalVerifierAgreement.decode_eq,
      ``LfzkV2.Current.CanonicalVerifierAgreement.checks_iff,
      ``LfzkV2.Current.CanonicalOracle.atOracle_eq,
      ``LfzkV2.Current.MerkleWireCodec.codec_inj,
      ``LfzkV2.Current.MerkleWireCodec.leaf_encode_physical,
      ``LfzkV2.Current.MerkleWireCodec.role_ranges_disjoint,
      ``LfzkV2.Current.OpeningSampling.query_fiber_card,
      ``LfzkV2.Current.OpeningFisherYates.ordered,
      ``LfzkV2.Current.PrefixCodec.encode_injective,
      ``LfzkV2.Current.ByteOracleTransport.Codec.window_ratio_le_full,
      ``LfzkV2.Current.QueryRuntime.Runtime.toPoint_injective,
      ``LfzkV2.Current.QueryRuntimeProbability.joint_ratio_le,
      ``LfzkV2.Current.WireOpening.ordinary_fromRequest_opening,
      ``LfzkV2.Current.OpeningBody.leafEquiv,
      ``LfzkV2.Current.OpeningBody.leaf_witness,
      ``LfzkV2.Current.OpeningBody.leaf_masks,
      ``LfzkV2.Current.OpeningBody.leaf_proximity,
      ``LfzkV2.Current.OpeningBody.raw_nonce,
      ``LfzkV2.Current.ZeroKnowledge.Frontend.History.opening_properties,
      ``LfzkV2.Current.ZeroKnowledge.RequestedSimulator.frontendBody,
      ``LfzkV2.Current.ZeroKnowledge.RequestedExperiment.frontendBody,
      ``LfzkV2.Current.ZeroKnowledge.RequestedBackend.statement,
      ``LfzkV2.Current.ZeroKnowledge.RequestedBackend.batching,
      ``LfzkV2.Current.ZeroKnowledge.RequestedBackend.responses,
      ``LfzkV2.Current.ZeroKnowledge.RequestedBackend.complete,
      ``LfzkV2.Current.Response.evaluationEquiv_symm_polynomial,
      ``LfzkV2.Current.Response.evaluationEquiv_eval,
      ``LfzkV2.Current.BackendChallenges.rowOrder_u,
      ``LfzkV2.Current.BackendChallenges.rowOrder_m,
      ``LfzkV2.Current.BackendChallenges.rowOrder_witness,
      ``LfzkV2.Current.BackendChallenges.polynomialsEquiv_eval,
      ``LfzkV2.Current.BackendChallenges.fieldEquiv,
      ``LfzkV2.Current.BackendChallenges.decoder,
      ``LfzkV2.Current.BackendChallenges.read_u_eval,
      ``LfzkV2.Current.BackendChallenges.read_m_eval,
      ``LfzkV2.Current.BackendChallenges.read_witness_eval,
      ``LfzkV2.Current.BackendChallenges.jointRead_coin,
      ``LfzkV2.Current.RuntimeVerifier.statementAt_off,
      ``LfzkV2.Current.RuntimeVerifier.statementAt_spec,
      ``LfzkV2.Current.RuntimeVerifier.decode_spec,
      ``LfzkV2.Current.RuntimeVerifier.verify_true_iff,
      ``LfzkV2.Current.RuntimeVerifier.encoding_opening,
      ``LfzkV2.Current.RuntimeVerifier.encoding_fresh_before,
      ``LfzkV2.Current.RuntimeVerifier.encodeResponses_injective,
      ``LfzkV2.Current.Replay.Encoding.replay_block,
      ``LfzkV2.Current.Replay.Encoding.point_block,
      ``LfzkV2.Current.Replay.Encoding.withFrontend_wire,
      ``LfzkV2.Current.Replay.Encoding.withFrontend_message,
      ``LfzkV2.Current.Replay.Encoding.withOpening_frontendWire,
      ``LfzkV2.Current.Replay.Encoding.withOpening_frontendMessage,
      ``LfzkV2.Current.FrontendReplay.dataAtRole_valid,
      ``LfzkV2.Current.FrontendReplay.bad_at_role,
      ``LfzkV2.Current.FrontendReplay.accepted_failure_cover,
      ``LfzkV2.Current.FrontendReplay.dataAtRole_eq_of_inclusive_prefix,
      ``LfzkV2.Current.FrontendReplay.sampleAtRole_eq_of_current,
      ``LfzkV2.Current.FrontendReplay.badAt_eq_of_inclusive_prefix,
      ``LfzkV2.Current.FrontendReplay.badAt_from_prefix,
      ``LfzkV2.Current.Input.answersWith_off,
      ``LfzkV2.Current.Replay.Encoding.point_priorPoints,
      ``LfzkV2.Current.Replay.Encoding.point_atRank,
      ``LfzkV2.Current.Replay.Encoding.point_answersWith,
      ``LfzkV2.Current.Selection.atPoint_replay,
      ``LfzkV2.Current.Selection.atPoint_replay_same,
      ``LfzkV2.Current.FrontendReplay.local_test_cover,
      ``LfzkV2.Current.FrontendReplay.badAt_card_mul_le,
      ``LfzkV2.Current.FrontendReplay.badAt_prefix_card_mul_le,
      ``LfzkV2.Current.SelectedFrontendOracle.bad_off,
      ``LfzkV2.Current.SelectedFrontendOracle.bad_of_prefix,
      ``LfzkV2.Current.SelectedFrontendOracle.bad_card_mul_le,
      ``LfzkV2.Current.Application.System.rows_reduction,
      ``LfzkV2.Current.Application.adapter_products_of_roots,
      ``LfzkV2.Current.Application.Authentication.extraction_failure_cover,
      ``LfzkV2.Current.ApplicationOracle.SelectionSource.rowBatching_off,
      ``LfzkV2.Current.ApplicationOracle.SelectionSource.rowBatching_card_mul_le,
      ``LfzkV2.Current.ApplicationOracle.SelectionSource.rescale_off,
      ``LfzkV2.Current.ApplicationOracle.SelectionSource.rescale_card_mul_le,
      ``LfzkV2.Current.ApplicationOracle.SelectionSource.conversion_off,
      ``LfzkV2.Current.ApplicationOracle.SelectionSource.conversion_card_mul_le,
      ``LfzkV2.Current.ApplicationOracle.SelectionSource.packing_off,
      ``LfzkV2.Current.ApplicationOracle.SelectionSource.packing_card_mul_le,
      ``LfzkV2.Current.BackendFS.failure_charged,
      ``LfzkV2.Current.BackendFS.rank_sum,
      ``LfzkV2.Current.BackendFS.opening_sum,
      ``LfzkV2.Current.BackendFS.high_sum,
      ``LfzkV2.Current.BackendOracle.single_off,
      ``LfzkV2.Current.BackendOracle.single_sum,
      ``LfzkV2.Current.BackendOracle.point_budget,
      ``LfzkV2.Current.CommitmentOracle.cutOracle_off,
      ``LfzkV2.Current.CommitmentOracle.merkle_accepts,
      ``LfzkV2.Current.CommitmentOracle.verify_of_explains,
      ``LfzkV2.Current.OrderedOpening.decode_indices,
      ``LfzkV2.Current.OrderedOpening.decode_values,
      ``LfzkV2.Current.OrderedOpening.read_replay,
      ``LfzkV2.Current.OrderedOpening.read_indices_replay,
      ``LfzkV2.Current.BackendVerifier.encodeResponses_injective,
      ``LfzkV2.Current.BackendVerifier.encodeResponses_body,
      ``LfzkV2.Current.ChainedFS.digest_card,
      ``LfzkV2.Current.ChainedFS.ratio_le,
      ``LfzkV2.Current.ChainedFS.ratio_le_support,
      ``TranscriptV2.Memoize.normalizeRight_output,
      ``TranscriptV2.Memoize.normalizeRight_support,
      ``TranscriptV2.Memoize.normalizeRight_left_state,
      ``TranscriptV2.Memoize.normalizeSetup_ctxAt,
      ``TranscriptV2.Memoize.normalizeSetup_merkleOracle,
      ``TranscriptV2.Memoize.normalizeSetup_MerkleAccepts,
      ``TranscriptV2.Memoize.normalizeSetup_Explains,
      ``TranscriptV2.Memoize.ratio_le_from_potential_support,
      ``LfzkV2.Current.Input.finiteEquiv,
      ``LfzkV2.Current.Input.card,
      ``LfzkV2.Current.Geometry.get_eq_batching_iff,
      ``LfzkV2.Current.Geometry.get_eq_opening_iff,
      ``LfzkV2.Current.BackendPath.parent_point,
      ``LfzkV2.Current.BackendPath.opening_eq,
      ``LfzkV2.Current.BackendPath.statement_replay,
      ``LfzkV2.Current.Application.Authentication.statement_of_prefix,
      ``LfzkV2.Current.ApplicationCharging.PrefixConfiguration.single_off,
      ``LfzkV2.Current.ApplicationCharging.PrefixConfiguration.single_sum,
      ``LfzkV2.Current.GlobalCharges.single_off,
      ``LfzkV2.Current.GlobalCharges.single_sum,
      ``LfzkV2.Current.GlobalCharges.pair_sum,
      ``LfzkV2.Current.ApplicationSetup.BinaryPublic.inputs_eq_bits,
      ``LfzkV2.Current.ApplicationSetup.BinaryPublic.circuit_pads,
      ``LfzkV2.Current.ApplicationSetup.decodeChecked,
      ``LfzkV2.Current.CellLayout.Prime.rows_avoid_fingerprint,
      ``LfzkV2.Current.CellLayout.Prime.batch_fingerprint_zero,
      ``LfzkV2.Current.ZkJoint.authenticate_statement,
      ``LfzkV2.Current.Tests.EarlyOutputs.accepted_false_output,
      ``LfzkV2.Current.Domain.tag_injective,
      ``LfzkV2.Current.Stage.roles_length,
      ``LfzkV2.Current.Frontend.roles_length,
      ``LfzkV2.Current.Geometry.roles_eq,
      ``LfzkV2.Current.Geometry.roles_length,
      ``LfzkV2.Current.Geometry.last_action,
      ``LfzkV2.Current.Input.parent_round_succ,
      ``LfzkV2.Current.Input.claimed_round_succ,
      ``LfzkV2.Current.Input.parent_finalSeal,
      ``LfzkV2.Current.Input.claimed_finalSeal,
      ``LfzkV2.Current.Input.parent_rank,
      ``LfzkV2.Current.Input.finalSeal_body_bound,
      ``LfzkV2.Current.Input.priorPoints_rank,
      ``LfzkV2.Current.Input.priorAnswers_off,
      ``LfzkV2.Current.Input.points_chal_samples,
      ``LfzkV2.Current.Input.priorPoints_context,
      ``LfzkV2.Current.Replay.Encoding.advance_parent,
      ``LfzkV2.Current.Replay.Encoding.advance_link,
      ``LfzkV2.Current.Replay.Encoding.replay_coherent,
      ``LfzkV2.Current.Replay.Encoding.point_context,
      ``LfzkV2.Current.Replay.Encoding.finalSealPoint_body,
      ``LfzkV2.Current.Proof.finalSealInput_body,
      ``LfzkV2.Current.Proof.finalSealInput_authentication,
      ``LfzkV2.Current.Selection.Context.extract_valid,
      ``LfzkV2.Current.Selection.Context.authenticated_pair,
      ``LfzkV2.Current.Selection.atPoint_off,
      ``LfzkV2.Current.FingerprintRows.rows_iff,
      ``LfzkV2.Current.FingerprintRows.realize_project,
      ``LfzkV2.Current.FingerprintRows.rows_realized,
      ``LfzkV2.Current.FingerprintRows.decoded_view,
      ``LfzkV2.Current.BackendSelection.recovered_selected,
      ``LfzkV2.Current.BackendSelection.extraction_reduction,
      ``LfzkV2.Current.Frontend.Packed.rows_satisfy_or_bad,
      ``LfzkV2.Current.Frontend.Prime.rows_satisfy_or_bad,
      ``LfzkV2.Current.Composition.rows_reduction,
      ``LfzkV2.Current.BackendQueries.Parent.statement_off,
      ``LfzkV2.Current.BackendQueries.Parent.oracle_off,
      ``LfzkV2.Current.BackendQueries.Parent.child_injective,
      ``LfzkV2.Current.mdoc_chained_budget,
      ``LfzkV2.Current.MerkleReplay.proof_eq,
      ``LfzkV2.Current.MerkleReplay.proof_context,
      ``LfzkV2.Current.MerkleReplay.terminal_point,
      ``LfzkV2.Current.Prime.batchRows_eval,
      ``LfzkV2.Current.Prime.batch_bad_card_mul_le,
      ``LfzkV2.Current.Prime.compiled_batched_reduction,
      ``LfzkV2.Current.Prime.rescaling_bad_card,
      ``LfzkV2.Current.Prime.Claim.true_or_rescaling_bad,
      ``LfzkV2.Current.Prime.Claim.fromRow_residual,
      ``LfzkV2.Current.Handoff.residual_eq,
      ``LfzkV2.Current.Handoff.product_handoff,
      ``LfzkV2.Current.Handoff.batched_handoff,
      ``LfzkV2.Current.Adapter.difference_cast,
      ``LfzkV2.Current.Adapter.difference_bound,
      ``LfzkV2.Current.Adapter.bad_card,
      ``LfzkV2.Current.Adapter.two_bad_probability_le,
      ``LfzkV2.Current.Adapter.product_check_iff,
      ``LfzkV2.Current.Adapter.Tree.reduce_prod,
      ``LfzkV2.Current.Adapter.Tree.masked_leaf,
      ``LfzkV2.Current.Adapter.Tree.product_check,
      ``LfzkV2.Current.Adapter.Circuit.pairValue_prod,
      ``LfzkV2.Current.Adapter.Circuit.satisfies_product_check,
      ``LfzkV2.Current.Adapter.Circuit.Fragment.full_product_check,
      ``LfzkV2.Current.Adapter.Mdoc.generator_order,
      ``LfzkV2.Current.Adapter.Mdoc.orderFactors_product,
      ``LfzkV2.Current.Adapter.Mdoc.orderFactors_prime,
      ``LfzkV2.Current.Adapter.Mdoc.primitive_order_of_check,
      ``LfzkV2.Current.Adapter.Mdoc.generator_order_of_check,
      ``LfzkV2.Current.Adapter.Mdoc.quotient_base_of_check,
      ``LfzkV2.Current.Adapter.Mdoc.quotient_base,
      ``LfzkV2.Current.Adapter.Mdoc.conversion_probability_le,
      ``RecursivePolygero.Local.ReducedSystems.Joint.overlap,
      ``RecursivePolygero.Local.ReducedSystems.Joint.assign,
      ``RecursivePolygero.ProfileAnalysis.response_eq_of_common_columns,
      ``LfzkV2.Joint.Participant.verify_iff_columns,
      ``LfzkV2.Joint.Participant.assign_columns,
      ``LfzkV2.Joint.Participant.exception_of_columns,
      ``LfzkV2.Current.JointResponse.verify_iff,
      ``LfzkV2.Current.JointResponse.response_eq,
      ``LfzkV2.Current.JointResponse.extraction_high_mass_mean,
      ``LfzkV2.Current.JointResponse.parent_mass_le,
      ``LfzkV2.Current.JointResponse.low_raw_le,
      ``LfzkV2.Current.JointResponse.outside_raw_le,
      ``LfzkV2.Current.JointResponse.linked_high_raw_le,
      ``LfzkV2.Current.JointResponse.failure_charged,
      ``LfzkV2.Current.JointResponse.openingCharge_sum,
      ``LfzkV2.Current.JointResponse.rankCharge_sum,
      ``LfzkV2.Current.JointResponse.highCharge_sum,
      ``TranscriptV2.feedback_sum,
      ``TranscriptV2.Chain.recompute_result,
      ``TranscriptV2.SharedReduction.failure_ratio_le,
      ``TranscriptV2.shared_queried_sum_le,
      ``LfzkV2.Current.SHARouting.cut_run,
      ``LfzkV2.Current.SHALazy.setup_cut_run,
      ``LfzkV2.Current.MdocSHAExperiment.original_output,
      ``LfzkV2.Current.MdocSHAExperiment.setup_same,
      ``LfzkV2.Current.MdocSHAExperiment.metadata_same,
      ``LfzkV2.Current.MdocSHAExperiment.cut_preserved,
      ``LfzkV2.Current.MdocSHAExperiment.verify_merge,
      ``LfzkV2.Current.MdocSHAExperiment.event_iff,
      ``LfzkV2.Current.MdocSharedSHASoundness.ratio_le] do
    for ax in ← collectAxioms endpoint do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {endpoint}"
