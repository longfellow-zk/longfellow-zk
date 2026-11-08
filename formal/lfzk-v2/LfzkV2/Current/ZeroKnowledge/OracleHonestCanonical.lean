import LfzkV2.Current.ZeroKnowledge.OracleHonestRuntime
import LfzkV2.Current.ZeroKnowledge.HonestTranscriptGood
import LfzkV2.Current.ZeroKnowledge.HonestTranscriptMdocRank
import LfzkV2.Current.ZeroKnowledge.FrontendCanonicalSimulation
import LfzkV2.Current.ZeroKnowledge.FrontendFullCoupling

/-! The honest source frontend's batching query is its actual canonical
complete-body prefix. The existing pointwise frontend coin equivalence
transports the checked simulator encoder identity, preserving the full state.
The only circuit premise is the same trusted-hash relation used by frontend
privacy; no oracle consistency or replay certificate is supplied. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.OracleHonestCanonical
open Application ApplicationSetup ConcreteSetup RecursivePolygero LigeroFamily
open Frontend SumcheckV2
open scoped Classical
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

private theorem state_query_congr {g : Geometry} {fields : Fields} {Advice Auth Key Base C : Type}
    (base : (i : Fin g.roles.length) → (Fin (i.val+1) → ProtocolWrites.Fresh g fields Advice) →
      (Fin i.val → C) → Base)
    {first second : CompleteTranscript.State g fields Advice Key Base C}
    (same : first = second) (firstInside : first.rank.val < g.roles.length)
    (secondInside : second.rank.val < g.roles.length) :
    CompleteTranscript.query (Authentication := Auth) base first firstInside =
      CompleteTranscript.query (Authentication := Auth) base second secondInside := by
  cases same
  rfl

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
  (Key := FingerprintPrefix.Key binary.description.nPublic) (C := C) (Salt := Fin 2443 × MerkleNonce))
variable (binaryCount : shape.binaryPublic = binary.description.nPublic)
variable (metadata : CanonicalRequest.Metadata (Advice := MdocAdvice.Value) (C := C) shape binary.description.nPublic)
local notation "G" => CompleteSimulation.geometry binary prime primePlan
local notation "Point" => QueryRuntime.Runtime.Point repr shape setup binary.description.nPublic

variable (original : Fin binary.nPrivate → Bool) (remaining : Fin prime.remaining → N)
variable (tape : HonestRuntime.Tape binary prime binaryNodes)
variable (request : CanonicalRequest.Request shape binary.description.nPublic) (HM : Bytes → Digest)

def root (sample : Fin 361 → B) : Digest := HonestRuntime.commitment binary prime primePlan binaryNodes repr shape setup cfg
  original remaining HM (OracleHonestRuntime.tapeAt binary prime binaryNodes tape sample)

def writer (sample : Fin 361 → B) := CompleteSimulator.base binary prime primePlan binaryNodes repr shape setup cfg
  binaryCount metadata request (root binary prime primePlan binaryNodes repr shape setup cfg original remaining tape HM sample)

variable (H : QueryRuntime.Runtime.Point repr shape setup binary.description.nPublic → Digest × C)

def result (sample : Fin 361 → B) := HonestRuntime.frontendResult binary prime primePlan binaryNodes repr shape setup cfg
  binaryCount metadata original remaining request HM H (OracleHonestRuntime.tapeAt binary prime binaryNodes tape sample)

omit [DecidableEq B] in
/-- Keep the commitment root and private frontend tape abstract while
checking the runtime wrapper. Instantiation must not evaluate either one. -/
private theorem frontendAtRoot_run (commitment : Digest)
    (frontendTape : CompleteHonest.Tape binary prime) (selectors : CompleteHonest.Masks (B := B)) :
    HonestRuntime.frontendAtRoot binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata
      original remaining request commitment H frontendTape selectors =
      CompleteHonest.run binary prime primePlan
        (CompleteSimulator.samples binary prime primePlan binaryNodes repr shape setup cfg)
        (CompleteSimulator.base binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata request commitment)
        H (fun answer => (cfg.fingerprintBinary answer,cfg.fingerprintPrime answer))
        (FingerprintPrefix.context request commitment) original remaining frontendTape selectors := rfl

/-- Identify the frontend computation before projecting any of its fields.
Rewriting this equality avoids reducing the full honest execution while
checking ranks, histories or the coupling. -/
theorem result_run (sample : Fin 361 → B) :
    result binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM H sample =
      CompleteHonest.run binary prime primePlan
        (CompleteSimulator.samples binary prime primePlan binaryNodes repr shape setup cfg)
        (writer binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM sample)
        H (fun answer => (cfg.fingerprintBinary answer,cfg.fingerprintPrime answer))
        (FingerprintPrefix.context request (root binary prime primePlan binaryNodes repr shape setup cfg original remaining tape HM sample))
        original remaining tape.frontend tape.selectors := by
  exact frontendAtRoot_run binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata
    original remaining request H
    (root binary prime primePlan binaryNodes repr shape setup cfg original remaining tape HM sample)
    tape.frontend tape.selectors

/-- Expose only the body of the honest frontend. Query proofs use this
small interface instead of reducing the commitment and frontend generators. -/
theorem frontend_body (sample : Fin 361 → B) :
    (OracleHonestRuntime.frontend binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata
      original remaining tape request HM H sample).body =
      CompleteFrontendBody.rawBody binary prime primePlan
        (root binary prime primePlan binaryNodes repr shape setup cfg original remaining tape HM sample)
        (result binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM H sample) := rfl

omit [DecidableEq B] in
/-- The verifier wrapper uses exactly the ordinary canonical request encoder.
Keep this definitional conversion at one boundary, not in every query proof. -/
theorem verifier_encoding :
    (CompleteCanonicalVerifier.encoding binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg
      binaryCount metadata request).encoding =
      CanonicalRequest.encoding repr shape setup binary.description.nPublic
        (CanonicalRuntime.binaryRequest binary.description prime (backend binaryNodes binary.description.cells)
          (backend ConcreteSetup.primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) repr shape setup
          (CompleteCanonicalVerifier.basePublic binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg) binaryCount)
        metadata request := rfl

theorem result_rank (sample : Fin 361 → B) :
    (result binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM H sample).state.rank.val =
      (G).batchingIndex.val := by
  have counted := HonestTranscript.Mdoc.program_rank binary prime primePlan
    (CompleteSimulator.samples binary prime primePlan binaryNodes repr shape setup cfg)
    (writer binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM sample)
    (fun answer => (cfg.fingerprintBinary answer,cfg.fingerprintPrime answer))
    (FingerprintPrefix.context request (root binary prime primePlan binaryNodes repr shape setup cfg original remaining tape HM sample))
    original remaining tape.frontend tape.selectors H
  rw [HonestTranscript.Mdoc.program_output] at counted
  rw [result_run]
  exact counted

theorem result_good (sample : Fin 361 → B) :
    History.Good
      (writer binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM sample) H
      (FingerprintPrefix.context request (root binary prime primePlan binaryNodes repr shape setup cfg original remaining tape HM sample))
      (result binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM H sample).state := by
  rw [result_run]
  exact HonestTranscript.Mdoc.run_good binary prime primePlan
      (CompleteSimulator.samples binary prime primePlan binaryNodes repr shape setup cfg)
      (writer binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM sample)
      (fun answer => (cfg.fingerprintBinary answer,cfg.fingerprintPrime answer))
      (FingerprintPrefix.context request (root binary prime primePlan binaryNodes repr shape setup cfg original remaining tape HM sample))
      original remaining tape.frontend tape.selectors H

/-- The honest frontend and its coupled simulator have the same complete
state. Prove this conversion once; query lemmas below transport this opaque
equality instead of reconstructing the coupling at each boundary. -/
def simulationCoins (sample : Fin 361 → B) (pivotOne : binary.basis 0 = 1)
    (hash : ∀ responses coin converted, FullCoupling.hashChecks binary prime primePlan
      (CompleteSimulator.samples binary prime primePlan binaryNodes repr shape setup cfg)
      (writer binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM sample) H
      (FingerprintPrefix.context request (root binary prime primePlan binaryNodes repr shape setup cfg original remaining tape HM sample))
      original responses coin converted) : CompleteSimulation.Coins binary prime :=
  FullCoupling.coupling binary prime primePlan
    (CompleteSimulator.samples binary prime primePlan binaryNodes repr shape setup cfg)
    (writer binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM sample)
    H (FingerprintPrefix.context request (root binary prime primePlan binaryNodes repr shape setup cfg original remaining tape HM sample))
    original remaining pivotOne hash (fun answer => (cfg.fingerprintBinary answer,cfg.fingerprintPrime answer))
    (tape.frontend,tape.selectors)

theorem result_eq_simulate (sample : Fin 361 → B) (pivotOne : binary.basis 0 = 1)
    (hash : ∀ responses coin converted, FullCoupling.hashChecks binary prime primePlan
      (CompleteSimulator.samples binary prime primePlan binaryNodes repr shape setup cfg)
      (writer binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM sample) H
      (FingerprintPrefix.context request (root binary prime primePlan binaryNodes repr shape setup cfg original remaining tape HM sample))
      original responses coin converted) :
    result binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM H sample =
      (CompleteSimulation.simulate binary prime primePlan
        (CompleteSimulator.samples binary prime primePlan binaryNodes repr shape setup cfg)
        (writer binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM sample)
        H (FingerprintPrefix.context request (root binary prime primePlan binaryNodes repr shape setup cfg original remaining tape HM sample))
        (simulationCoins binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM H sample pivotOne hash)).raw := by
  rw [result_run]
  exact FullCoupling.coupling_view binary prime primePlan
      (CompleteSimulator.samples binary prime primePlan binaryNodes repr shape setup cfg)
      (writer binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM sample)
      H (FingerprintPrefix.context request (root binary prime primePlan binaryNodes repr shape setup cfg original remaining tape HM sample))
      original remaining pivotOne hash (fun answer => (cfg.fingerprintBinary answer,cfg.fingerprintPrime answer))
      tape.frontend tape.selectors

theorem batching_query (sample : Fin 361 → B) (pivotOne : binary.basis 0 = 1)
    (hash : ∀ responses coin converted, FullCoupling.hashChecks binary prime primePlan
      (CompleteSimulator.samples binary prime primePlan binaryNodes repr shape setup cfg)
      (writer binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM sample) H
      (FingerprintPrefix.context request (root binary prime primePlan binaryNodes repr shape setup cfg original remaining tape HM sample))
      original responses coin converted) :
    let current := result binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM H sample
    let inside : current.state.rank.val < (G).roles.length := by
      rw [result_rank binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM H sample]
      exact (G).batchingIndex.isLt
    CompleteTranscript.query
      (writer binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM sample) current.state inside =
      CompleteCanonicalVerifier.batchingPoint binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg
        binaryCount metadata request
        (OracleHonestRuntime.frontend binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM H sample).body H := by
  let samplers := CompleteSimulator.samples binary prime primePlan binaryNodes repr shape setup cfg
  let base := writer binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM sample
  let context := FingerprintPrefix.context request (root binary prime primePlan binaryNodes repr shape setup cfg original remaining tape HM sample)
  let coins := simulationCoins binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM H sample pivotOne hash
  have same : result binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM H sample =
      (CompleteSimulation.simulate binary prime primePlan samplers base H context coins).raw :=
    result_eq_simulate binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM H sample pivotOne hash
  dsimp only
  rw [frontend_body]
  unfold CompleteCanonicalVerifier.batchingPoint
  rw [BackendPath.parent_point, verifier_encoding]
  change CompleteTranscript.query base
      (result binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM H sample).state _ =
    ((CanonicalRequest.encoding repr shape setup binary.description.nPublic
      (CanonicalRuntime.binaryRequest binary.description prime (backend binaryNodes binary.description.cells)
        (backend ConcreteSetup.primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) repr shape setup
        (CompleteCanonicalVerifier.basePublic binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg) binaryCount)
      metadata request).chain cfg.initialLink).point
      ⟨CompleteFrontendBody.rawBody binary prime primePlan
        (root binary prime primePlan binaryNodes repr shape setup cfg original remaining tape HM sample)
        (result binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM H sample),fun _ => 0⟩ H (G).batchingIndex.val
  have simInside : (CompleteSimulation.simulate binary prime primePlan samplers base H context coins).state.rank.val < (G).roles.length := by
    rw [(SimulationWrites.simulate_properties binary prime primePlan samplers base H context coins).1]
    exact (G).batchingIndex.isLt
  have querySame : CompleteTranscript.query (Authentication := OpeningBody.Authentication G) base
      (result binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM H sample).state
      (by rw [result_rank]; exact (G).batchingIndex.isLt) =
      CompleteTranscript.query (Authentication := OpeningBody.Authentication G) base (CompleteSimulation.simulate binary prime primePlan samplers base H context coins).state simInside := by
    exact state_query_congr (Auth := OpeningBody.Authentication G) base
      (congrArg CompleteSimulation.RawResult.state same) _ _
  rw [querySame]
  conv_rhs => rw [same]
  exact CanonicalSimulation.batching_query binary prime primePlan samplers shape repr setup (⟨0,by decide⟩ : MdocAdvice.Value)
    binary.description.nPublic
    (CanonicalRuntime.binaryRequest binary.description prime (backend binaryNodes binary.description.cells)
      (backend ConcreteSetup.primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) repr shape setup
      (CompleteCanonicalVerifier.basePublic binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg) binaryCount)
    metadata request (root binary prime primePlan binaryNodes repr shape setup cfg original remaining tape HM sample)
    H cfg.initialLink coins

def openingState (sample : Fin 361 → B)
    (responses : Response G B × Response G N) :=
  CompleteTranscript.bind
    (CompleteTranscript.step
      (writer binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM sample) H
      (result binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM H sample).state).2
    (fun written => { written with responses := some responses })

theorem opening_rank (sample : Fin 361 → B) (responses : Response G B × Response G N) :
    (openingState binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM H sample responses).rank.val =
      (G).openingIndex.val := by
  dsimp only [openingState, CompleteTranscript.bind]
  rw [SimulationWrites.step_rank, result_rank, Nat.min_eq_right (Nat.le_of_lt (G).batchingIndex_next)]
  exact (G).openingIndex_val.symm

theorem opening_query (sample : Fin 361 → B) (pivotOne : binary.basis 0 = 1)
    (hash : ∀ responses coin converted, FullCoupling.hashChecks binary prime primePlan
      (CompleteSimulator.samples binary prime primePlan binaryNodes repr shape setup cfg)
      (writer binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM sample) H
      (FingerprintPrefix.context request (root binary prime primePlan binaryNodes repr shape setup cfg original remaining tape HM sample))
      original responses coin converted)
    (responses : Response G B × Response G N) :
    let current := openingState binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM H sample responses
    let inside : current.rank.val < (G).roles.length := by
      rw [opening_rank]
      exact (G).openingIndex.isLt
    CompleteTranscript.query
      (writer binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM sample) current inside =
      ((CompleteCanonicalVerifier.encoding binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg
        binaryCount metadata request).encoding.chain cfg.initialLink).point
        ⟨OracleResponse.fillBoth
          (OracleHonestRuntime.frontend binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM H sample).body
          responses, fun _ => 0⟩ H (G).openingIndex.val := by
  let samplers := CompleteSimulator.samples binary prime primePlan binaryNodes repr shape setup cfg
  let base := writer binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM sample
  let context := FingerprintPrefix.context request (root binary prime primePlan binaryNodes repr shape setup cfg original remaining tape HM sample)
  let coins := simulationCoins binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM H sample pivotOne hash
  have same : result binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM H sample =
      (CompleteSimulation.simulate binary prime primePlan samplers base H context coins).raw :=
    result_eq_simulate binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM H sample pivotOne hash
  let after := fun (raw : CompleteSimulation.RawResult binary prime primePlan
      (FingerprintPrefix.Key binary.description.nPublic) (CanonicalRequest.Base repr shape setup binary.description.nPublic) C) =>
    CompleteTranscript.bind (CompleteTranscript.step base H raw.state).2
      (fun written => { written with responses := some responses })
  have next : (after (CompleteSimulation.simulate binary prime primePlan samplers base H context coins).raw).rank.val < (G).roles.length := by
    change (CompleteTranscript.step base H (CompleteSimulation.simulate binary prime primePlan samplers base H context coins).state).2.rank.val < _
    rw [SimulationWrites.step_rank,(SimulationWrites.simulate_properties binary prime primePlan samplers base H context coins).1]
    have := (G).batchingIndex_next
    omega
  have querySame := state_query_congr (Auth := OpeningBody.Authentication G) base (congrArg after same)
    (show (after (result binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM H sample)).rank.val < (G).roles.length from by
      change (openingState binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM H sample responses).rank.val < _
      rw [opening_rank]; exact (G).openingIndex.isLt) next
  dsimp only
  rw [show CompleteTranscript.query (Authentication := OpeningBody.Authentication G) base
      (openingState binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM H sample responses) _ =
      CompleteTranscript.query (Authentication := OpeningBody.Authentication G) base
        (after (CompleteSimulation.simulate binary prime primePlan samplers base H context coins).raw) next from querySame]
  rw [frontend_body, verifier_encoding]
  change _ = ((CanonicalRequest.encoding repr shape setup binary.description.nPublic
    (CanonicalRuntime.binaryRequest binary.description prime (backend binaryNodes binary.description.cells)
      (backend ConcreteSetup.primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) repr shape setup
      (CompleteCanonicalVerifier.basePublic binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg) binaryCount)
    metadata request).chain cfg.initialLink).point
    ⟨OracleResponse.fillBoth (CompleteFrontendBody.rawBody binary prime primePlan
      (root binary prime primePlan binaryNodes repr shape setup cfg original remaining tape HM sample)
      (result binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM H sample)) responses,fun _ => 0⟩ H (G).openingIndex.val
  conv_rhs => rw [same]
  exact CanonicalSimulation.opening_query binary prime primePlan samplers shape repr setup (⟨0,by decide⟩ : MdocAdvice.Value)
    binary.description.nPublic
    (CanonicalRuntime.binaryRequest binary.description prime (backend binaryNodes binary.description.cells)
      (backend ConcreteSetup.primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) repr shape setup
      (CompleteCanonicalVerifier.basePublic binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg) binaryCount)
    metadata request (root binary prime primePlan binaryNodes repr shape setup cfg original remaining tape HM sample)
    H cfg.initialLink coins responses

end LfzkV2.Current.ZeroKnowledge.OracleHonestCanonical
