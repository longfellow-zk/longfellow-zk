import LfzkV2.Current.ZeroKnowledge.HonestRuntime
import LfzkV2.Current.ZeroKnowledge.OracleJointPrimaryFreshness

/-! The successful opening input of the actual honest runtime. Replacing
only the binary primary-mask polynomial leaves all logical cells fixed.
The earlier frontend and Merkle root are recomputed normally and may depend
on the replacement. Parsing failure creates no opening input. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.OracleHonestRuntime
open Application ApplicationSetup ConcreteSetup RecursivePolygero LigeroFamily
open Frontend Merkle Polynomial
open scoped Classical
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
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
variable (primeCount : shape.primePublic = prime.nPublic)
variable (metadata : CanonicalRequest.Metadata (Advice := MdocAdvice.Value) (C := C) shape binary.description.nPublic)
local notation "G" => CompleteSimulation.geometry binary prime primePlan
local notation "P" => ConcreteSetup.backend binaryNodes binary.description.cells
local notation "R" => ConcreteSetup.backend ConcreteSetup.primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)
local notation "Public" => CompleteCanonicalVerifier.publicConfig binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg
local notation "First" => RuntimeVerifier.first binary.description prime P R Public
local notation "Second" => RuntimeVerifier.second binary.description prime P R Public
local notation "Point" => QueryRuntime.Runtime.Point repr shape setup binary.description.nPublic
local notation "Output" => CanonicalRequest.Output (g := G) (fields := MdocRuntime.fields B) (Advice := MdocAdvice.Value)
local notation "Mask" => Fin 361 → B

def tapeAt (tape : HonestRuntime.Tape binary prime binaryNodes) (sample : Mask) : HonestRuntime.Tape binary prime binaryNodes :=
  { tape with backend :=
      ((tape.backend.1.1,tape.backend.1.2.1,
        (Response.evaluationEquiv B (OraclePrimaryFreshness.nodes binaryNodes)
          (OraclePrimaryFreshness.nodes_injective binaryNodes)).symm sample),tape.backend.2) }

theorem logical_tapeAt (original : Fin binary.nPrivate → Bool) (remaining : Fin prime.remaining → N)
    (tape : HonestRuntime.Tape binary prime binaryNodes) (sample : Mask) :
    HonestRuntime.logical binary prime binaryNodes original remaining (tapeAt binary prime binaryNodes tape sample) =
      HonestRuntime.logical binary prime binaryNodes original remaining tape := rfl

variable (original : Fin binary.nPrivate → Bool) (remaining : Fin prime.remaining → N)
variable (tape : HonestRuntime.Tape binary prime binaryNodes)
variable (request : CanonicalRequest.Request shape binary.description.nPublic)
variable (HM : Bytes → Digest)
variable (H : QueryRuntime.Runtime.Point repr shape setup binary.description.nPublic → Digest × C)
variable (draw : C → RuntimeVerifier.RawSamples binary.description prime
  (ConcreteSetup.backend binaryNodes binary.description.cells)
  (ConcreteSetup.backend ConcreteSetup.primeNodes (CellLayout.Prime.cells prime.remaining prime.pads))
  (CompleteCanonicalVerifier.publicConfig binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg))

def frontend (sample : Mask) : Output :=
  let privateTape := tapeAt binary prime binaryNodes tape sample
  let root := HonestRuntime.commitment binary prime primePlan binaryNodes repr shape setup cfg original remaining HM privateTape
  ⟨CompleteFrontendBody.rawBody binary prime primePlan root
    (HonestRuntime.frontendResult binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata
      original remaining request HM H privateTape),fun _ => 0⟩

def statementAt (sample : Mask) :=
  CompleteCanonicalVerifier.statementAt binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg
    binaryCount primeCount metadata request
    (frontend binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM H sample).body H

def zeroStatement : JointResponse.Statement (First).participant (Second).participant :=
  (⟨fun _ _ _ _ => 0,fun _ => 0⟩,⟨fun _ _ _ _ => 0,fun _ => 0⟩)

def statement (sample : Mask) :=
  ((statementAt binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape request HM H sample).map
    (fun data => data.2.statement)).getD (zeroStatement binary prime primePlan binaryNodes repr shape setup cfg)

def pending (sample : Mask) : Option Output := do
  let early := frontend binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM H sample
  let data ← statementAt binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape request HM H sample
  let coin := CompleteCanonicalVerifier.batchingCoin binary.description prime binaryNodes ConcreteSetup.primeNodes
    repr shape setup cfg binaryCount metadata draw request early.body H
  let responses := CompleteVerifier.wireResponses binary.description prime binaryNodes ConcreteSetup.primeNodes Public
    (CompleteResponse.realResponses binary.description prime binaryNodes ConcreteSetup.primeNodes Public
      (HonestRuntime.logical binary prime binaryNodes original remaining tape) data.2.statement coin
      (tapeAt binary prime binaryNodes tape sample).backend)
  pure ⟨HonestRuntime.responseBody binary prime primePlan early.body responses,fun _ => 0⟩

def active (sample : Mask) : Prop :=
  (statementAt binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape request HM H sample).isSome

variable (fits : (CompleteSimulation.geometry binary prime primePlan).roles.length < 2^64)

def input (sample : Mask) : Bytes :=
  match pending binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape request HM H draw sample with
  | none => []
  | some proof => OracleBytes.openingBytes repr shape setup binary.description.nPublic fits
      (CanonicalRuntime.binaryRequest binary.description prime P R repr shape setup
        (CompleteCanonicalVerifier.basePublic binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg) binaryCount)
      metadata request cfg.initialLink proof H

theorem batchingPoint (sample : Mask) :
    CompleteCanonicalVerifier.batchingPoint binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg
      binaryCount metadata request
      (frontend binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM H sample).body H =
    OracleJointPrimaryFreshness.batching binary prime primePlan binaryNodes ConcreteSetup.primeNodes repr shape setup Public
      (CanonicalRuntime.binaryRequest binary.description prime P R repr shape setup
        (CompleteCanonicalVerifier.basePublic binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg) binaryCount)
      metadata request H
      (frontend binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM H) sample := by
  unfold CompleteCanonicalVerifier.batchingPoint
  rw [BackendPath.parent_point]
  rfl

theorem input_active (sample : Mask)
    (enabled : active binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape request HM H sample) :
    input binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape request HM H draw fits sample =
      OracleJointPrimaryFreshness.input binary prime primePlan binaryNodes ConcreteSetup.primeNodes repr shape setup Public
        (CanonicalRuntime.binaryRequest binary.description prime P R repr shape setup
          (CompleteCanonicalVerifier.basePublic binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg) binaryCount)
        metadata request H draw (HonestRuntime.logical binary prime binaryNodes original remaining tape)
        tape.backend.1.1 tape.backend.1.2.1 tape.backend.2
        (frontend binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM H)
        (statement binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape request HM H)
        fits sample := by
  unfold active at enabled
  cases parsed : statementAt binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape request HM H sample with
  | none => simp only [parsed,Option.isSome_none,Bool.false_eq_true] at enabled
  | some data =>
      simp only [input,pending,parsed,statement,Option.map_some,Option.getD_some,
        OracleJointPrimaryFreshness.input,OracleJointPrimaryFreshness.proof,OracleJointPrimaryFreshness.response]
      simp only [CompleteCanonicalVerifier.batchingCoin,batchingPoint]
      rfl

variable (bodyFits : ProofBodyBounds.bodyBound repr (CompleteSimulation.geometry binary prime primePlan) ≤ CanonicalPrefix.maxLength)

include bodyFits in
theorem active_queries (prior : Finset Bytes) (queries : ℕ) (budget : prior.card ≤ queries) :
    ((Finset.univ.filter fun sample : Mask =>
      active binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape request HM H sample ∧
      input binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape request HM H draw fits sample ∈ prior).card : ℚ) /
      (2 : ℚ)^46208 ≤ (queries : ℚ)/(2 : ℚ)^46208 := by
  exact OracleJointPrimaryFreshness.active_input_queries binary prime primePlan binaryNodes ConcreteSetup.primeNodes
    repr shape setup Public
    (CanonicalRuntime.binaryRequest binary.description prime P R repr shape setup
      (CompleteCanonicalVerifier.basePublic binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg) binaryCount)
    metadata request H draw (HonestRuntime.logical binary prime binaryNodes original remaining tape)
    tape.backend.1.1 tape.backend.1.2.1 tape.backend.2
    (frontend binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM H)
    (statement binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape request HM H)
    fits bodyFits
    (active binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape request HM H)
    (input binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape request HM H draw fits)
    (input_active binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape request HM H draw fits)
    prior queries budget

def finish (sample : Mask) (pendingProof : Output) :
    CanonicalRuntime.Output (Advice := MdocAdvice.Value) binary.description shape :=
  let privateTape := tapeAt binary prime binaryNodes tape sample
  let e := CompleteCanonicalVerifier.encoding binary.description prime binaryNodes ConcreteSetup.primeNodes
    repr shape setup cfg binaryCount metadata request
  let indices := cfg.sample (H ((e.encoding.chain cfg.initialLink).point pendingProof H (G).openingIndex.val)).2
  let responses := (pendingProof.body.binaryBackend.response,pendingProof.body.primeBackend.response)
  let full := CompleteBody.fill (First).participant (Second).participant cfg.binaryField cfg.primeField
    cfg.binaryRows cfg.primeRows cfg.openings
    ((CompleteCanonicalVerifier.merkleCodec binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg).withOracle HM)
    indices privateTape.nonces
    (HonestRuntime.columns binary prime primePlan binaryNodes repr shape setup cfg original remaining privateTape)
    pendingProof.body responses setup.jointContext
    (HonestRuntime.frontier_capacity binary prime primePlan binaryNodes repr shape setup cfg HM indices original remaining privateTape)
  ⟨request,OracleProgramming.finalize e cfg.initialLink full H⟩

theorem prove_pending (sample : Mask) :
    (HonestRuntime.prove binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw
      original remaining (tapeAt binary prime binaryNodes tape sample) request HM H).1 =
      (pending binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape request HM H draw sample).map
        (finish binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM H sample) := by
  unfold HonestRuntime.prove pending finish frontend
  rw [logical_tapeAt]
  simp only [statementAt,frontend,Option.bind_eq_bind,Option.pure_def,Option.map_bind,
    Function.comp_def,Option.map_some]
  rfl

end LfzkV2.Current.ZeroKnowledge.OracleHonestRuntime
