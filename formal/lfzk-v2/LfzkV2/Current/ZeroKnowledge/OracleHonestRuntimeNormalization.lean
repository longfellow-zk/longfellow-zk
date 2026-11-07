import LfzkV2.Current.ZeroKnowledge.OracleHonestNormalization
import LfzkV2.Current.ZeroKnowledge.OracleCompleteNormalization

/-! Canonical-coordinate normalization of the actual honest complete prover.
The existing source pending/finish decomposition keeps parser aborts,
real backend responses, actual authentication and the normal final seal. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.OracleHonestRuntimeNormalization
open Application ApplicationSetup ConcreteSetup RecursivePolygero LigeroFamily
open Frontend SumcheckV2 Merkle.RandomOracle
open scoped Classical
set_option maxHeartbeats 1600000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
variable {B C : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
local notation "N" => Adapter.Mdoc.P
variable (binary : BinaryCircuit B) (prime : PrimePublic N 768)
variable (primePlan : FrontendSchedule.Plan N prime.circuit) (binaryNodes : Fin 2792 ↪ B)
variable (repr : ProofBodyCodec.Representations (MdocRuntime.fields B) MdocAdvice.Value)
variable (shape : WireBlocks.Shape (CompleteSimulation.geometry binary prime primePlan) (MdocRuntime.fields B))
variable (setup : FingerprintPrefix.Setup)
variable (cfg : RuntimeVerifier.Public (g := CompleteSimulation.geometry binary prime primePlan)
  binary.description prime (backend binaryNodes binary.description.cells)
  (backend ConcreteSetup.primeNodes (CellLayout.Prime.cells prime.remaining prime.pads))
  (fields := MdocRuntime.fields B) (Advice := MdocAdvice.Value)
  (Base := CanonicalRequest.Base repr shape setup binary.description.nPublic)
  (Key := FingerprintPrefix.Key binary.description.nPublic) (C := C) (Salt := Fin 2443 × Digest))
variable (binaryCount : shape.binaryPublic = binary.description.nPublic)
variable (metadata : CanonicalRequest.Metadata (Advice := MdocAdvice.Value) (C := C) shape binary.description.nPublic)
local notation "G" => CompleteSimulation.geometry binary prime primePlan
local notation "Point" => QueryRuntime.Runtime.Point repr shape setup binary.description.nPublic

variable (original : Fin binary.nPrivate → Bool) (remaining : Fin prime.remaining → N)
variable (tape : HonestRuntime.Tape binary prime binaryNodes)
variable (request : CanonicalRequest.Request shape binary.description.nPublic) (HM : Bytes → Digest)

variable (primeCount : shape.primePublic = prime.nPublic)
variable (H H' : QueryRuntime.Runtime.Point repr shape setup binary.description.nPublic → Digest × C)
variable (draw : C → RuntimeVerifier.RawSamples binary.description prime
  (backend binaryNodes binary.description.cells)
  (backend ConcreteSetup.primeNodes (CellLayout.Prime.cells prime.remaining prime.pads))
  (CompleteCanonicalVerifier.publicConfig binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg))
variable (bodyFits : ProofBodyBounds.bodyBound repr (CompleteSimulation.geometry binary prime primePlan) ≤ CanonicalPrefix.maxLength)
variable (agree : OracleNormalization.Agree repr shape setup binary.description.nPublic H H')
local notation "Public" => CompleteCanonicalVerifier.publicConfig binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg
local notation "P" => backend binaryNodes binary.description.cells
local notation "R" => backend ConcreteSetup.primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)
local notation "First" => RuntimeVerifier.first binary.description prime P R Public
local notation "Second" => RuntimeVerifier.second binary.description prime P R Public
local notation "Data" => Σ A : RuntimeVerifier.System binary.description prime (C := C), StatementData A First Second
local notation "Output" => CanonicalRequest.Output (g := G) (fields := MdocRuntime.fields B) (Advice := MdocAdvice.Value)
local notation "Result" => CanonicalRuntime.Output (Advice := MdocAdvice.Value) binary.description shape
local notation "Body" => Current.Body G (MdocRuntime.fields B) MdocAdvice.Value (OpeningBody.Authentication G)
local notation "binaryRequest" => CanonicalRuntime.binaryRequest binary.description prime P R repr shape setup
  (CompleteCanonicalVerifier.basePublic binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg) binaryCount
local notation "rootAt" => OracleHonestCanonical.root binary prime primePlan binaryNodes repr shape setup cfg original remaining tape HM
local notation "baseAt" => OracleHonestCanonical.writer binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM
local notation "samplers" => CompleteSimulator.samples binary prime primePlan binaryNodes repr shape setup cfg

def pendingFrom (sample : Fin 361 → B) (frontend : Output) (oracle : Point → Digest × C) : Option Output := do
  let data ← CompleteCanonicalVerifier.statementAt binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg
    binaryCount primeCount metadata request frontend.body oracle
  let coin := CompleteCanonicalVerifier.batchingCoin binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg
    binaryCount metadata draw request frontend.body oracle
  let responses := CompleteVerifier.wireResponses binary.description prime binaryNodes ConcreteSetup.primeNodes Public
    (CompleteResponse.realResponses binary.description prime binaryNodes ConcreteSetup.primeNodes Public
      (HonestRuntime.logical binary prime binaryNodes original remaining tape) data.2.statement coin
      (OracleHonestRuntime.tapeAt binary prime binaryNodes tape sample).backend)
  pure ⟨HonestRuntime.responseBody binary prime primePlan frontend.body responses,fun _ => 0⟩

include agree bodyFits in
theorem pendingFrom_eq (sample : Fin 361 → B) (frontend : Output) :
    pendingFrom binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request primeCount draw sample frontend H =
    pendingFrom binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request primeCount draw sample frontend H' := by
  let build := fun (parsed : Option Data) (coin : JointResponse.Coin
      (RuntimeVerifier.first binary.description prime P R Public).participant
      (RuntimeVerifier.second binary.description prime P R Public).participant) => do
    let data ← parsed
    let responses := CompleteVerifier.wireResponses binary.description prime binaryNodes ConcreteSetup.primeNodes Public
      (CompleteResponse.realResponses binary.description prime binaryNodes ConcreteSetup.primeNodes Public
        (HonestRuntime.logical binary prime binaryNodes original remaining tape) data.2.statement coin
        (OracleHonestRuntime.tapeAt binary prime binaryNodes tape sample).backend)
    pure (⟨HonestRuntime.responseBody binary prime primePlan frontend.body responses,fun _ => 0⟩ : Output)
  exact congrArg₂ build
    (OracleCompleteNormalization.statement_eq binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg
      binaryCount primeCount metadata bodyFits request H H' agree frontend.body)
    (OracleCompleteNormalization.batchingCoin_eq binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg
      binaryCount metadata bodyFits request H H' agree draw frontend.body)

include agree bodyFits in
theorem pending_eq (sample : Fin 361 → B) (pivotOne : binary.basis 0 = 1)
    (hash : ∀ responses coin converted, FullCoupling.hashChecks binary prime primePlan samplers (baseAt sample) H
      (FingerprintPrefix.context request (rootAt sample)) original responses coin converted) :
    OracleHonestRuntime.pending binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape request HM H draw sample =
    OracleHonestRuntime.pending binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape request HM H' draw sample := by
  let lift := fun (raw : CompleteSimulation.RawResult binary prime primePlan
      (FingerprintPrefix.Key binary.description.nPublic) (CanonicalRequest.Base repr shape setup binary.description.nPublic) C) => (⟨CompleteFrontendBody.rawBody binary prime primePlan (rootAt sample) raw,fun _ => 0⟩ : Output)
  have front := congrArg lift (OracleHonestNormalization.frontend_eq binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata
    original remaining tape request HM H H' bodyFits sample pivotOne hash agree)
  have fields := congrArg (fun frontend => pendingFrom binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata
    original remaining tape request primeCount draw sample frontend H) front
  exact fields.trans (pendingFrom_eq binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata
    original remaining tape request primeCount H H' draw bodyFits agree sample
    (OracleHonestRuntime.frontend binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM H' sample))

def terminalBody (sample : Fin 361 → B) (proof : Output) (indices : Fin 84 ↪ Fin 2443) : Body :=
  let source := OracleHonestRuntime.tapeAt binary prime binaryNodes tape sample
  CompleteBody.fill (First).participant (Second).participant cfg.binaryField cfg.primeField cfg.binaryRows cfg.primeRows cfg.openings
    ((CompleteCanonicalVerifier.merkleCodec binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg).withOracle HM)
    indices source.nonces (HonestRuntime.columns binary prime primePlan binaryNodes repr shape setup cfg original remaining source)
    proof.body (proof.body.binaryBackend.response,proof.body.primeBackend.response) setup.jointContext
    (HonestRuntime.frontier_capacity binary prime primePlan binaryNodes repr shape setup cfg HM indices original remaining source)

include agree bodyFits in
theorem finish_eq (sample : Fin 361 → B) (proof : Output) :
    OracleHonestRuntime.finish binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM H sample proof =
    OracleHonestRuntime.finish binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM H' sample proof := by
  let e := CompleteCanonicalVerifier.encoding binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg binaryCount metadata request
  let first := cfg.sample (H ((e.encoding.chain cfg.initialLink).point proof H (G).openingIndex.val)).2
  let second := cfg.sample (H' ((e.encoding.chain cfg.initialLink).point proof H' (G).openingIndex.val)).2
  have indices : first = second := congrArg (fun answer : Digest × C => cfg.sample answer.2)
    (OracleNormalization.answer_eq repr shape setup binary.description.nPublic binaryRequest metadata request bodyFits cfg.initialLink proof H H' agree
      (G).openingIndex.val (Nat.le_of_lt (G).openingIndex.isLt))
  change (⟨request,OracleRuntime.finalize repr shape setup binary.description.nPublic binaryRequest metadata request cfg.initialLink
      (terminalBody binary prime primePlan binaryNodes repr shape setup cfg original remaining tape HM sample proof first) H⟩ : Result) =
    ⟨request,OracleRuntime.finalize repr shape setup binary.description.nPublic binaryRequest metadata request cfg.initialLink
      (terminalBody binary prime primePlan binaryNodes repr shape setup cfg original remaining tape HM sample proof second) H'⟩
  rw [indices]
  exact congrArg (fun complete => (⟨request,complete⟩ : Result))
    (OracleNormalization.finalize_eq repr shape setup binary.description.nPublic binaryRequest metadata request bodyFits cfg.initialLink
      (terminalBody binary prime primePlan binaryNodes repr shape setup cfg original remaining tape HM sample proof second) H H' agree)

include agree bodyFits in
theorem prove_eq (sample : Fin 361 → B) (pivotOne : binary.basis 0 = 1)
    (hash : ∀ responses coin converted, FullCoupling.hashChecks binary prime primePlan samplers (baseAt sample) H
      (FingerprintPrefix.context request (rootAt sample)) original responses coin converted) :
    (HonestRuntime.prove binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw
      original remaining (OracleHonestRuntime.tapeAt binary prime binaryNodes tape sample) request HM H).1 =
    (HonestRuntime.prove binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw
      original remaining (OracleHonestRuntime.tapeAt binary prime binaryNodes tape sample) request HM H').1 := by
  rw [OracleHonestRuntime.prove_pending binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
      original remaining tape request HM H draw sample,
    OracleHonestRuntime.prove_pending binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
      original remaining tape request HM H' draw sample,
    pending_eq binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM
      primeCount H H' draw bodyFits agree sample pivotOne hash]
  have functions : OracleHonestRuntime.finish binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata
      original remaining tape request HM H sample =
      OracleHonestRuntime.finish binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata
        original remaining tape request HM H' sample := by
    funext proof
    exact finish_eq binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM
      H H' bodyFits agree sample proof
  exact congrArg (fun finish => Option.map finish
    (OracleHonestRuntime.pending binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
      original remaining tape request HM H' draw sample)) functions

def maskSample : Fin 361 → B :=
  (Response.evaluationEquiv B (OraclePrimaryFreshness.nodes binaryNodes)
    (OraclePrimaryFreshness.nodes_injective binaryNodes)) tape.backend.1.2.2

omit [Fintype B] in
theorem tapeAt_maskSample :
    OracleHonestRuntime.tapeAt binary prime binaryNodes tape
      (maskSample binary prime binaryNodes tape) = tape := by
  cases tape with
  | mk frontend selectors backend nonces =>
    rcases backend with ⟨⟨core,masks,primary⟩,prime⟩
    simp only [OracleHonestRuntime.tapeAt,maskSample,Equiv.symm_apply_apply]

include agree bodyFits in
theorem prove_original_eq (pivotOne : binary.basis 0 = 1)
    (hash : ∀ responses coin converted, FullCoupling.hashChecks binary prime primePlan samplers
      (baseAt (maskSample binary prime binaryNodes tape)) H
      (FingerprintPrefix.context request (rootAt (maskSample binary prime binaryNodes tape))) original responses coin converted) :
    (HonestRuntime.prove binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw original remaining tape request HM H).1 =
    (HonestRuntime.prove binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw original remaining tape request HM H').1 := by
  have normalized := prove_eq binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM
    primeCount H H' draw bodyFits agree (maskSample binary prime binaryNodes tape) pivotOne hash
  rw [tapeAt_maskSample] at normalized
  exact normalized

end LfzkV2.Current.ZeroKnowledge.OracleHonestRuntimeNormalization
