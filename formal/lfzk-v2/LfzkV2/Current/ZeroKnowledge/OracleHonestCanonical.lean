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
  (Key := FingerprintPrefix.Key binary.description.nPublic) (C := C) (Salt := Fin 2443 × Digest))
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
  exact counted

theorem result_good (sample : Fin 361 → B) :
    History.Good
      (writer binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM sample) H
      (FingerprintPrefix.context request (root binary prime primePlan binaryNodes repr shape setup cfg original remaining tape HM sample))
      (result binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM H sample).state :=
  HonestTranscript.Mdoc.run_good binary prime primePlan
    (CompleteSimulator.samples binary prime primePlan binaryNodes repr shape setup cfg)
    (writer binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM sample)
    (fun answer => (cfg.fingerprintBinary answer,cfg.fingerprintPrime answer))
    (FingerprintPrefix.context request (root binary prime primePlan binaryNodes repr shape setup cfg original remaining tape HM sample))
    original remaining tape.frontend tape.selectors H

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
  let coefficients := fun answer => (cfg.fingerprintBinary answer,cfg.fingerprintPrime answer)
  let coins := FullCoupling.coupling binary prime primePlan samplers base H context original remaining pivotOne hash coefficients
    (tape.frontend,tape.selectors)
  have same : result binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM H sample =
      (CompleteSimulation.simulate binary prime primePlan samplers base H context coins).raw :=
    FullCoupling.coupling_view binary prime primePlan samplers base H context original remaining pivotOne hash coefficients tape.frontend tape.selectors
  dsimp only
  unfold CompleteCanonicalVerifier.batchingPoint
  rw [BackendPath.parent_point]
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
  change (CompleteTranscript.step _ H _).2.rank.val = _
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
  let coefficients := fun answer => (cfg.fingerprintBinary answer,cfg.fingerprintPrime answer)
  let coins := FullCoupling.coupling binary prime primePlan samplers base H context original remaining pivotOne hash coefficients
    (tape.frontend,tape.selectors)
  have same : result binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM H sample =
      (CompleteSimulation.simulate binary prime primePlan samplers base H context coins).raw :=
    FullCoupling.coupling_view binary prime primePlan samplers base H context original remaining pivotOne hash coefficients tape.frontend tape.selectors
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
