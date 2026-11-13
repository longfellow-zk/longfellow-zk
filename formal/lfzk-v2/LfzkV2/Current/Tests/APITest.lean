import LfzkV2.Current.Tests.ProofAudit
import LfzkV2.Current.Tests.RuntimeBoundary
import LfzkV2.Current.Tests.ZeroKnowledgeReachability
import LfzkV2.Current.Tests.MdocSoundness
import LfzkV2.Current.Tests.EndpointStatements
import LfzkV2.Current.Tests.StrandLinearReplay
import LfzkV2.Current.Tests.StrandMerkleBounds
import LfzkV2.Current.Tests.StrandMerkleMissingQueries
import LfzkV2.Current.Tests.StrandMerkleSelector
import LfzkV2.Current.Tests.StrandRecordedReplay
import LfzkV2.Current.Tests.ZeroKnowledgeBackendAdaptive
import LfzkV2.Current.Tests.ZeroKnowledgeStrandHonestExecution
import LfzkV2.Current.Tests.ZeroKnowledgeStrandHonestFrontend
import LfzkV2.Current.Tests.ZeroKnowledgeStrandCompleteness
import LfzkV2.Current.Tests.ZeroKnowledgeStrandHonestRuntime
import Survival.Axioms
import LfzkV2.Current
import LfzkV2.Current.Tests.Algebra
import LfzkV2.Current.Tests.Absorption
import LfzkV2.Current.Tests.StrandSearch
import LfzkV2.Current.Tests.StrandRuntime
import LfzkV2.Current.Tests.StrandVerifier
import LfzkV2.Current.Tests.StrandAcceptedPath
import LfzkV2.Current.Tests.StrandCut
import LfzkV2.Current.Tests.StrandCutObservation
import LfzkV2.Current.Tests.StrandCommitment
import LfzkV2.Current.Tests.StrandMerkleReceiving
import LfzkV2.Current.Tests.StrandAuthentication
import LfzkV2.Current.Tests.StrandExecution
import LfzkV2.Current.Tests.StrandWindow
import LfzkV2.Current.Tests.StrandRoleSampling
import LfzkV2.Current.Tests.StrandLocalCharges
import LfzkV2.Current.Tests.StrandBackendCharges
import LfzkV2.Current.Tests.StrandCharges
import LfzkV2.Current.Tests.StrandComposition
import LfzkV2.Current.Tests.StrandDecoder
import LfzkV2.Current.Tests.StrandRealization
import LfzkV2.Current.Tests.StrandProtocol
import LfzkV2.Current.Tests.StrandDomains
import LfzkV2.Current.Tests.MdocStrandSoundness
import LfzkV2.Current.Tests.MdocStrandOracle
import LfzkV2.Current.Tests.StrandRealizationBounds
import LfzkV2.Current.Tests.StrandOriginalSeal
import LfzkV2.Current.Tests.ByteOracleTag
import LfzkV2.Current.Tests.Joint
import LfzkV2.Current.Tests.EarlyOutputs
import LfzkV2.Current.Tests.FrontendReplay
import LfzkV2.Current.Tests.FrontendVerifier
import LfzkV2.Current.Tests.FrontendBody
import LfzkV2.Current.Tests.FrontendSchedule
import LfzkV2.Current.Tests.ApplicationPrefix
import LfzkV2.Current.Tests.ApplicationViews
import LfzkV2.Current.Tests.OpeningBody
import LfzkV2.Current.Tests.BackendBody
import LfzkV2.Current.Tests.BackendChallenges
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
import LfzkV2.Current.Tests.ZeroKnowledgeStrandCanonicalHiding
import LfzkV2.Current.Tests.ZeroKnowledgeStrandCanonicalByteOracle
import LfzkV2.Current.Tests.ZeroKnowledgeMdocStrandPrivacy
import LfzkV2.Current.Tests.ZeroKnowledgeBackendCells
import LfzkV2.Current.Tests.ZeroKnowledgeBackendStatement
import LfzkV2.Current.Tests.ZeroKnowledgeCanonicalPublic
import LfzkV2.Current.Tests.ZeroKnowledgeFrontend
import LfzkV2.Current.Tests.ZeroKnowledgeFrontendAdapter
import LfzkV2.Current.Tests.AdapterFragment
import LfzkV2.Current.Tests.ZeroKnowledgePacking
import LfzkV2.Current.Tests.ZeroKnowledgePackingCells
import LfzkV2.Current.Tests.ZeroKnowledgeGlobalCoins
import LfzkV2.Current.Tests.ZeroKnowledgeHash
import LfzkV2.Current.Tests.ZeroKnowledgeFrontendComplete
import LfzkV2.Current.Tests.ZeroKnowledgeFrontendSetup
import LfzkV2.Current.Tests.ZeroKnowledgeProbabilityInstances
import LfzkV2.Current.Tests.ZeroKnowledgeHonestRunRows
import LfzkV2.Current.Tests.ZeroKnowledgeMdocPublicSetup
import LfzkV2.Current.Tests.ZeroKnowledgeSHASetup
import LfzkV2.Current.Tests.ZeroKnowledgeSHAGlobalWindow
import LfzkV2.Current.Tests.ZeroKnowledgeTranscriptObserver
import LfzkV2.Current.Tests.ZeroKnowledgeSHAOracle
import LfzkV2.Current.Tests.ZeroKnowledgeOracleWindow
import LfzkV2.Current.Tests.CanonicalRequestBinding
import LfzkV2.Current.Tests.ZeroKnowledgeMerkle
import LfzkV2.Current.Tests.ZeroKnowledgeMerkleOracleWindow
import LfzkV2.Current.Tests.ZeroKnowledgeMerklePrequery
import LfzkV2.Current.Tests.ZeroKnowledgeMerkleRefresh
import LfzkV2.Current.Tests.ZeroKnowledgeMerkleCommitRefresh
import LfzkV2.Current.Tests.ZeroKnowledgeMerkleCommitLabels
import LfzkV2.Current.Tests.ZeroKnowledgeMerkleCommitPrepared
import LfzkV2.Current.Tests.ZeroKnowledgeMerklePreparation
import LfzkV2.Current.Tests.ZeroKnowledgeStrandCanonicalBridge
import LfzkV2.Current.Tests.ZeroKnowledgeStrandGhostMerkle
import TranscriptV2.Tests.Framing
import LfzkV2.Current.EntryChallenges
import TranscriptV2.SharedCharging
import TranscriptV2.PathCharges
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
    [.fingerprint, .assertions, .terminal, .combine, .rescaling,
      .conversion, .assertions, .sumcheck, .terminal,
      .combine, .packing, .batching, .opening] := by decide

example : geometry.roles.length + 1 = 14 := by decide
example : geometry.actions.take 4 =
    [.bind .setup, .query .fingerprint, .bind .fingerprints, .bind (.frontend .prime)] := by decide

example : ({geometry with packingDegree := 1, packingPositive := by decide}.roles).length = 12 :=
  by decide
example : packingActions 1 = [] := rfl
-- The prime statement has its unbatched layer row, the native split row and
-- the two fingerprint rows.
example : geometry.affineRows .binary = 5 ∧ geometry.affineRows .prime = 4 := by decide
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

/- Audit every declaration imported from the surviving V2 implementation
and generic component modules, rather than a historical endpoint whitelist. -/
run_cmd do
  let env ← getEnv
  let modules := env.header.moduleNames
  let owner := fun name => match env.getModuleIdxFor? name with
    | some index => modules[index.toNat]!
    | none => env.mainModule
  let mut checked := 0
  for (name, info) in env.constants do
    let moduleName := (owner name).toString
    unless moduleName == "LfzkV2" || moduleName.startsWith "LfzkV2." do continue
    if info.isAxiom then throwError "Unexpected V2 axiom declaration: {name}"
    for ax in ← collectAxioms name do
      unless #[``propext, ``Classical.choice, ``Quot.sound].contains ax do
        throwError "Unexpected axiom {ax} in {name}"
    checked := checked+1
  logInfo m!"Audited {checked} current V2 and shared component declarations: standard Lean axioms only."
