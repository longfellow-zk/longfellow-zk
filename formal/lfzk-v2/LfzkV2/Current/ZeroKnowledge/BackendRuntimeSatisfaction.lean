import LfzkV2.Current.ZeroKnowledge.BackendRuntime
import LfzkV2.Current.ZeroKnowledge.FrontendFullSatisfaction
import LfzkV2.Current.ZeroKnowledge.FrontendRuntimeStatement

/-! The concrete mdoc backend statement is true on the cells committed by
the honest runtime. Public values are installed from the selected request;
the pointwise frontend coupling is used only to identify the actual parser
input. Its root may depend on the committed cells. No independence of that
root and no backend-satisfaction certificate is assumed here. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.BackendRuntimeSatisfaction
open Application ApplicationSetup ConcreteSetup Frontend SumcheckV2
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1400000
variable {B : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
local notation "N" => Adapter.Mdoc.P
variable (binary : BinaryCircuit B) (prime : PrimePublic N 768)
variable (primePlan : FrontendSchedule.Plan N prime.circuit) (binaryNodes : Fin 2792 ↪ B)
variable (scalars : MdocRuntime.Scalars B)
variable (inputFits : 768+prime.remaining+prime.pads < 2^64) (privateFits : binary.nPrivate < 2^64)
variable (setup : FingerprintPrefix.Setup)
local notation "G" => CompleteSimulation.geometry binary prime primePlan
local notation "Sh" => MdocRuntime.shape binary.description prime binary.plan primePlan inputFits privateFits
  (RuntimeStatement.degreeFits binary)
local notation "Repr" => MdocRuntime.representations scalars
local notation "Answer" => MdocRuntime.Answer binary.description prime binary.plan primePlan binaryNodes
local notation "Cfg" => RuntimeStatement.configuration binary prime primePlan binaryNodes scalars inputFits privateFits setup
local notation "First" => backend binaryNodes binary.description.cells
local notation "Second" => backend ConcreteSetup.primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)
local notation "bCount" => RuntimeStatement.binary_count binary prime primePlan inputFits privateFits
local notation "pCount" => RuntimeStatement.prime_count binary prime primePlan inputFits privateFits
variable (metadata : CanonicalRequest.Metadata (Advice := MdocAdvice.Value)
  (C := MdocRuntime.Answer binary.description prime binary.plan primePlan binaryNodes)
  (MdocRuntime.shape binary.description prime binary.plan primePlan inputFits privateFits (RuntimeStatement.degreeFits binary)) binary.nPublic)
variable (original : CanonicalRequest.Request
  (MdocRuntime.shape binary.description prime binary.plan primePlan inputFits privateFits (RuntimeStatement.degreeFits binary)) binary.nPublic →
    Fin binary.nPrivate → Bool)
variable (remaining : CanonicalRequest.Request
  (MdocRuntime.shape binary.description prime binary.plan primePlan inputFits privateFits (RuntimeStatement.degreeFits binary)) binary.nPublic →
    Fin prime.remaining → N)
variable (H : QueryRuntime.Runtime.Point (MdocRuntime.representations scalars)
  (MdocRuntime.shape binary.description prime binary.plan primePlan inputFits privateFits (RuntimeStatement.degreeFits binary))
  setup binary.nPublic → Digest × MdocRuntime.Answer binary.description prime binary.plan primePlan binaryNodes)
local notation "Request" => CanonicalRequest.Request Sh binary.nPublic
local notation "Point" => QueryRuntime.Runtime.Point Repr Sh setup binary.nPublic
local notation "Prefix" => Request × List (Observer.Event (QM := Bytes) (AM := Digest) (QT := Point) (AT := Digest × Answer))
local notation "Coins" => CompleteHonest.Tape binary prime × CompleteHonest.Masks (B := B)

def hashTruth (coins : Coins) (earlier : Prefix) (labels : Fin (2*2443-1) → Digest) : Prop :=
  let request := earlier.1
  let root := labels ⟨2*2443-2,by decide⟩
  let b := RequestedSimulator.requestedBinary binary prime primePlan Sh request
  let p := RequestedSimulator.requestedPrime binary prime primePlan Sh pCount request
  let config := RequestedSimulator.configuration binary prime primePlan binaryNodes Repr Sh setup Cfg pCount request
  let samples := CompleteSimulator.samples b p primePlan binaryNodes Repr Sh setup config
  let writer := CompleteSimulator.base b p primePlan binaryNodes Repr Sh setup config bCount metadata request root
  let source := RequestedSimulator.privateFrontendEquiv binary prime primePlan Sh pCount request coins.1
  let first := CompleteTranscript.step writer H (CompleteTranscript.initial (FingerprintPrefix.context request root) samples.fallback)
  let raw := HonestRuntime.frontendAtRoot b p primePlan binaryNodes Repr Sh setup config bCount metadata
    (original request) (remaining request) request root H source coins.2
  HonestAdapter.hashChecks b p primePlan samples writer H
    (HonestRunRows.native b p primePlan samples writer H first.2 raw) (original request) source

theorem satisfied (coins : Coins) (earlier : Prefix) (labels : Fin (2*2443-1) → Digest)
    (pivotOne : binary.basis 0 = 1)
    (hashAll : BackendRuntime.hashChecks binary prime primePlan binaryNodes Repr Sh setup Cfg bCount pCount metadata original H earlier labels)
    (primitive : Current.Adapter.Mdoc.generatorCheck (MdocRuntime.polynomialX binary.basis) = true)
    (signature :
      let b := RequestedSimulator.requestedBinary binary prime primePlan Sh earlier.1
      let p := RequestedSimulator.requestedPrime binary prime primePlan Sh pCount earlier.1
      p.circuit.Satisfies (CompleteHonest.primeInputs b p (original earlier.1) (remaining earlier.1)))
    (hash : hashTruth binary prime primePlan binaryNodes scalars inputFits privateFits setup metadata original remaining H coins earlier labels) :
    (BackendRuntime.statements binary prime primePlan binaryNodes Repr Sh setup Cfg bCount pCount metadata original remaining H coins earlier labels).1.Satisfies
      (Backend.logical (BackendRuntime.cells binary prime primePlan binaryNodes Repr Sh setup original remaining coins earlier).1) ∧
    (BackendRuntime.statements binary prime primePlan binaryNodes Repr Sh setup Cfg bCount pCount metadata original remaining H coins earlier labels).2.Satisfies
      (Backend.logical (BackendRuntime.cells binary prime primePlan binaryNodes Repr Sh setup original remaining coins earlier).2) := by
  let request := earlier.1
  let root := labels ⟨2*2443-2,by decide⟩
  let b := RequestedSimulator.requestedBinary binary prime primePlan Sh request
  let p := RequestedSimulator.requestedPrime binary prime primePlan Sh pCount request
  let config := RequestedSimulator.configuration binary prime primePlan binaryNodes Repr Sh setup Cfg pCount request
  let samples := CompleteSimulator.samples b p primePlan binaryNodes Repr Sh setup config
  let writer := CompleteSimulator.base b p primePlan binaryNodes Repr Sh setup config bCount metadata request root
  let source := RequestedSimulator.privateFrontendEquiv binary prime primePlan Sh pCount request coins.1
  let selection := fun answer => ((Cfg).fingerprintBinary answer,(Cfg).fingerprintPrime answer)
  let binaryRequest := CanonicalRuntime.binaryRequest binary.description prime First Second Repr Sh setup
    (CompleteCanonicalVerifier.basePublic binary.description prime binaryNodes ConcreteSetup.primeNodes Repr Sh setup Cfg) bCount
  let publicCoins := FullCoupling.coupling b p primePlan samples writer H (FingerprintPrefix.context request root)
    (original request) (remaining request) pivotOne hashAll selection (source,coins.2)
  let result := CompleteSimulation.simulate b p primePlan samples writer H (FingerprintPrefix.context request root) publicCoins
  let body := CompleteFrontendBody.body b p primePlan root result
  let proof : CanonicalRequest.Output (g := G) (fields := MdocRuntime.fields B) (Advice := MdocAdvice.Value) := ⟨body,fun _ => 0⟩
  let E := CanonicalRequest.encoding Repr Sh setup binary.nPublic binaryRequest metadata request
  let point := (E.chain (Cfg).initialLink).point proof H (G).batchingIndex.val
  have view : BackendRuntime.front binary prime primePlan binaryNodes Repr Sh setup Cfg bCount pCount metadata original remaining H
      coins earlier labels = body := by
    have coupled := FullCoupling.coupling_view b p primePlan samples writer H (FingerprintPrefix.context request root)
      (original request) (remaining request) pivotOne hashAll selection source coins.2
    convert congrArg (CompleteFrontendBody.rawBody b p primePlan root) coupled using 1 <;> rfl
  obtain ⟨system,statement,decoded,compiled,holds⟩ := FullSatisfaction.statement_exists b p primePlan samples Sh Repr setup
    (⟨0,by decide⟩ : MdocAdvice.Value) binary.nPublic binaryRequest metadata request root H (Cfg).initialLink
    (original request) (remaining request) pivotOne hashAll selection source coins.2 binaryNodes primitive signature hash
  have pointEq : CompleteCanonicalVerifier.batchingPoint binary.description prime binaryNodes ConcreteSetup.primeNodes
      Repr Sh setup Cfg bCount metadata request body H = point := by
    unfold CompleteCanonicalVerifier.batchingPoint
    exact BackendPath.parent_point _ _ _ _ _
  have primeStart : (G).primeStart ≤ (G).batchingIndex.val := by
    exact le_trans (Nat.le_add_right _ _) (ParserApplication.prime_window binary prime primePlan)
  have hbits := CanonicalRuntime.hashPublic_replay binary.description prime First Second Repr Sh setup
    (CompleteCanonicalVerifier.basePublic binary.description prime binaryNodes ConcreteSetup.primeNodes Repr Sh setup Cfg)
    bCount metadata request (Cfg).initialLink proof H (G).batchingIndex.val
  have hinputs := CanonicalRuntime.primePublic_replay binary.description prime First Second Repr Sh setup
    (CompleteCanonicalVerifier.basePublic binary.description prime binaryNodes ConcreteSetup.primeNodes Repr Sh setup Cfg)
    bCount pCount metadata request (Cfg).initialLink proof H (G).batchingIndex.val (G).batchingIndex.isLt.le primeStart
  have application : RuntimeAdaptive.application binary.description prime First Second
      (CompleteCanonicalVerifier.publicConfig binary.description prime binaryNodes ConcreteSetup.primeNodes Repr Sh setup Cfg)
      (CanonicalRequest.hashPublic binary.nPublic)
      (CanonicalRuntime.decodePrimePublic binary.description prime First Second Repr Sh setup
        (CompleteCanonicalVerifier.basePublic binary.description prime binaryNodes ConcreteSetup.primeNodes Repr Sh setup Cfg) pCount)
      point (point.priorAnswers H) = some system := by
    rw [RequestedApplication.application_eq _ _ _ _ _ _ _ point (point.priorAnswers H) request.publicBits
      (fun i => request.primeInputs (Fin.cast (pCount).symm i)) hbits hinputs]
    exact decoded
  have rank := (E.chain (Cfg).initialLink).point_rank proof H (G).batchingIndex.isLt.le
  change point.rank = (G).batchingIndex.val at rank
  have fingerprint := SimulationParsed.strictAnswer_lookup H samples.fallback point 0 (by
    rw [rank]
    have positive := (ParserApplication.positions binary prime primePlan).1
    simp only [ApplicationPrefix.rowBatchingIndex,Geometry.primeStart] at positive
    omega)
  have targets := Parser.read_fingerprints Repr Sh setup binary.nPublic binaryRequest metadata request (Cfg).initialLink proof H
    (G).batchingIndex.val (G).batchingIndex.isLt.le primeStart
  have parsed : CompleteCanonicalVerifier.statementAt binary.description prime binaryNodes ConcreteSetup.primeNodes
      Repr Sh setup Cfg bCount pCount metadata request body H = some ⟨system,statement⟩ := by
    unfold CompleteCanonicalVerifier.statementAt
    rw [pointEq]
    dsimp only
    unfold RuntimeAdaptive.statementAt
    erw [application,BackendStatement.addresses_checked binaryNodes ConcreteSetup.primeNodes,fingerprint,targets]
    simp only [Option.bind_eq_bind,Option.bind_some]
    erw [compiled]
    rfl
  unfold BackendRuntime.statements
  rw [view,parsed]
  simp only [Option.map_some,Option.getD_some]
  exact holds

end LfzkV2.Current.ZeroKnowledge.BackendRuntimeSatisfaction
