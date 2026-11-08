import LfzkV2.Current.ZeroKnowledge.OracleHonestCanonical
import LfzkV2.Current.ZeroKnowledge.HonestTranscriptRefresh
import LfzkV2.Current.ZeroKnowledge.OracleRefreshActive

/-! The actual honest runtime's preopening computation as a bounded tree.
It captures private coins and the Merkle oracle, but receives no transcript
oracle in its constructor. Parsing, real H/Z arithmetic and the abort flag
are pure functions of the returned frontend state and batching answer. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.OracleHonestTree
open Application ApplicationSetup ConcreteSetup RecursivePolygero LigeroFamily
open Frontend SumcheckV2 Merkle.RandomOracle
open scoped Classical
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

private theorem query_congr {g : Geometry} {fields : Fields} {Advice Auth Key Base C : Type}
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
variable (primeCount : shape.primePublic = prime.nPublic)
variable (metadata : CanonicalRequest.Metadata (Advice := MdocAdvice.Value) (C := C) shape binary.description.nPublic)
local notation "G" => CompleteSimulation.geometry binary prime primePlan
local notation "Public" => CompleteCanonicalVerifier.publicConfig binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg
local notation "P" => ConcreteSetup.backend binaryNodes binary.description.cells
local notation "R" => ConcreteSetup.backend ConcreteSetup.primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)
local notation "First" => RuntimeVerifier.first binary.description prime P R Public
local notation "Second" => RuntimeVerifier.second binary.description prime P R Public
local notation "Point" => QueryRuntime.Runtime.Point repr shape setup binary.description.nPublic
local notation "Raw" => CompleteSimulation.RawResult binary prime primePlan
  (FingerprintPrefix.Key binary.description.nPublic) (CanonicalRequest.Base repr shape setup binary.description.nPublic) C
local notation "Pending" => HonestTranscript.Mdoc.Pending binary prime primePlan
  (Key := FingerprintPrefix.Key binary.description.nPublic) (Base := CanonicalRequest.Base repr shape setup binary.description.nPublic) (C := C)
local notation "Output" => CanonicalRequest.Output (g := G) (fields := MdocRuntime.fields B) (Advice := MdocAdvice.Value)

variable (original : Fin binary.nPrivate → Bool) (remaining : Fin prime.remaining → N)
variable (tape : HonestRuntime.Tape binary prime binaryNodes)
variable (request : CanonicalRequest.Request shape binary.description.nPublic) (HM : Bytes → Digest)
variable (draw : C → RuntimeVerifier.RawSamples binary.description prime
  (backend binaryNodes binary.description.cells)
  (backend ConcreteSetup.primeNodes (CellLayout.Prime.cells prime.remaining prime.pads))
  (CompleteCanonicalVerifier.publicConfig binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg))

local notation "rootAt" => OracleHonestCanonical.root binary prime primePlan binaryNodes repr shape setup cfg original remaining tape HM
local notation "baseAt" => OracleHonestCanonical.writer binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM
local notation "samplers" => CompleteSimulator.samples binary prime primePlan binaryNodes repr shape setup cfg

def response (sample : Fin 361 → B) (frontend : Raw) (answer : C) :=
  CompleteResponse.respond binary.description prime binaryNodes ConcreteSetup.primeNodes Public
    (baseAt sample) (CanonicalRequest.hashPublic binary.description.nPublic)
    (CanonicalRuntime.decodePrimePublic binary.description prime P R repr shape setup
      (CompleteCanonicalVerifier.basePublic binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg) primeCount)
    draw (HonestRuntime.logical binary prime binaryNodes original remaining tape)
    (OracleHonestRuntime.tapeAt binary prime binaryNodes tape sample).backend frontend.state answer

def parse (sample : Fin 361 → B) (frontend : Raw) :=
  if inside : frontend.state.rank.val < (G).roles.length then
    RuntimeAdaptive.statementAt binary.description prime P R Public
      (CanonicalRequest.hashPublic binary.description.nPublic)
      (CanonicalRuntime.decodePrimePublic binary.description prime P R repr shape setup
        (CompleteCanonicalVerifier.basePublic binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg) primeCount)
      (CompleteTranscript.query (baseAt sample) frontend.state inside) frontend.state.past
  else none

def tree (sample : Fin 361 → B) : Tree Point (Digest × C) Pending (1+HonestTranscript.Mdoc.fuel binary prime primePlan) :=
  HonestTranscript.Mdoc.openingPrefix binary prime primePlan samplers (baseAt sample)
    (fun answer => (cfg.fingerprintBinary answer,cfg.fingerprintPrime answer))
    (FingerprintPrefix.context request (rootAt sample)) original remaining tape.frontend tape.selectors
    (response binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape request HM draw sample)

def asPending (sample : Fin 361 → B) (current : Pending) : Option Output := do
  let _data ← parse binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape request HM sample current.frontend
  let front := CompleteFrontendBody.rawBody binary prime primePlan (rootAt sample) current.frontend
  pure ⟨OracleResponse.fillBoth front
    (response binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape request HM draw sample
      current.frontend current.batch),fun _ => 0⟩

def active (sample : Fin 361 → B) (current : Pending) : Prop :=
  (asPending binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape request HM draw sample current).isSome

def input (sample : Fin 361 → B) (current : Pending) : Point :=
  HonestTranscript.Mdoc.openingInput binary prime primePlan samplers (baseAt sample)
    (FingerprintPrefix.context request (rootAt sample)) current

theorem response_parsed (sample : Fin 361 → B) (frontend : Raw) (answer : C)
    (data : Σ A : RuntimeVerifier.System binary.description prime (C := C), StatementData A First Second)
    (parsed : parse binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape request HM sample frontend = some data) :
    response binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape request HM draw sample frontend answer =
      CompleteVerifier.wireResponses binary.description prime binaryNodes ConcreteSetup.primeNodes Public
        (CompleteResponse.realResponses binary.description prime binaryNodes ConcreteSetup.primeNodes Public
          (HonestRuntime.logical binary prime binaryNodes original remaining tape) data.2.statement
          (RuntimeVerifier.batchingDecoder binary.description prime P R Public draw answer)
          (OracleHonestRuntime.tapeAt binary prime binaryNodes tape sample).backend) := by
  unfold parse at parsed
  split_ifs at parsed with inside
  · exact CompleteResponse.respond_parsed binary.description prime binaryNodes ConcreteSetup.primeNodes Public
      (baseAt sample) (CanonicalRequest.hashPublic binary.description.nPublic)
      (CanonicalRuntime.decodePrimePublic binary.description prime P R repr shape setup
        (CompleteCanonicalVerifier.basePublic binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg) primeCount)
      draw (HonestRuntime.logical binary prime binaryNodes original remaining tape)
      (OracleHonestRuntime.tapeAt binary prime binaryNodes tape sample).backend frontend.state answer inside data parsed

variable (H : QueryRuntime.Runtime.Point repr shape setup binary.description.nPublic → Digest × C)

theorem frontend_output (sample : Fin 361 → B) :
    ((tree binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape request HM draw sample).run H).1.frontend =
      OracleHonestCanonical.result binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM H sample := by
  rw [OracleHonestCanonical.result_run]
  unfold tree
  rw [HonestTranscript.Mdoc.openingPrefix_output]

theorem batch_output (sample : Fin 361 → B) :
    ((tree binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape request HM draw sample).run H).1.batch =
      (CompleteTranscript.step (baseAt sample) H
        (OracleHonestCanonical.result binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM H sample).state).1 := by
  rw [OracleHonestCanonical.result_run]
  unfold tree
  rw [HonestTranscript.Mdoc.openingPrefix_output]

theorem internal_fresh (sample : Fin 361 → B) :
    MerklePrequery.fresh
      (tree binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape request HM draw sample)
      (input binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM sample) H :=
  HonestTranscript.Mdoc.opening_fresh binary prime primePlan samplers (baseAt sample)
    (fun answer => (cfg.fingerprintBinary answer,cfg.fingerprintPrime answer))
    (FingerprintPrefix.context request (rootAt sample)) original remaining tape.frontend tape.selectors
    (response binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape request HM draw sample) H

theorem parse_atResult (sample : Fin 361 → B) (pivotOne : binary.basis 0 = 1)
    (hash : ∀ responses coin converted, FullCoupling.hashChecks binary prime primePlan
      samplers (baseAt sample) H (FingerprintPrefix.context request (rootAt sample))
      original responses coin converted) :
    parse binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape request HM sample
      (OracleHonestCanonical.result binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM H sample) =
      OracleHonestRuntime.statementAt binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
        original remaining tape request HM H sample := by
  let current := OracleHonestCanonical.result binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM H sample
  have inside : current.state.rank.val < (G).roles.length := by
    rw [OracleHonestCanonical.result_rank]
    exact (G).batchingIndex.isLt
  have past := History.query_past (Authentication := OpeningBody.Authentication G) (baseAt sample) H
    (FingerprintPrefix.context request (rootAt sample)) current.state inside
    (OracleHonestCanonical.result_good binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM H sample)
  have point := OracleHonestCanonical.batching_query binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata
    original remaining tape request HM H sample pivotOne hash
  unfold parse
  rw [dif_pos inside, past]
  unfold OracleHonestRuntime.statementAt CompleteCanonicalVerifier.statementAt
  exact congrArg (fun p : Point => RuntimeAdaptive.statementAt binary.description prime P R Public
    (CanonicalRequest.hashPublic binary.description.nPublic)
    (CanonicalRuntime.decodePrimePublic binary.description prime P R repr shape setup
      (CompleteCanonicalVerifier.basePublic binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg) primeCount)
    p (p.priorAnswers H)) point

theorem batch_atResult (sample : Fin 361 → B) (pivotOne : binary.basis 0 = 1)
    (hash : ∀ responses coin converted, FullCoupling.hashChecks binary prime primePlan
      samplers (baseAt sample) H (FingerprintPrefix.context request (rootAt sample))
      original responses coin converted) :
    ((tree binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape request HM draw sample).run H).1.batch =
      (H (CompleteCanonicalVerifier.batchingPoint binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg
        binaryCount metadata request
        (OracleHonestRuntime.frontend binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM H sample).body H)).2 := by
  rw [batch_output]
  have inside : (OracleHonestCanonical.result binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM H sample).state.rank.val < (G).roles.length := by
    rw [OracleHonestCanonical.result_rank]
    exact (G).batchingIndex.isLt
  rw [CompleteTranscript.step_query (baseAt sample) H _ inside]
  exact congrArg (fun point => (H point).2)
    (OracleHonestCanonical.batching_query binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata
      original remaining tape request HM H sample pivotOne hash)

theorem pending_output (sample : Fin 361 → B) (pivotOne : binary.basis 0 = 1)
    (hash : ∀ responses coin converted, FullCoupling.hashChecks binary prime primePlan
      samplers (baseAt sample) H (FingerprintPrefix.context request (rootAt sample))
      original responses coin converted) :
    asPending binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape request HM draw sample
      ((tree binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape request HM draw sample).run H).1 =
      OracleHonestRuntime.pending binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
        original remaining tape request HM H draw sample := by
  let current := OracleHonestCanonical.result binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM H sample
  have parsedEq := parse_atResult binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
    original remaining tape request HM H sample pivotOne hash
  unfold asPending
  rw [frontend_output,parsedEq]
  unfold OracleHonestRuntime.pending
  cases parsed : OracleHonestRuntime.statementAt binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
      original remaining tape request HM H sample with
  | none => simp only [Option.bind_eq_bind,Option.bind_none]
  | some data =>
    have localParsed : parse binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape request HM sample current = some data :=
      parsedEq.trans parsed
    simp only [Option.bind_eq_bind,Option.bind_some,Option.pure_def]
    rw [response_parsed binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
      original remaining tape request HM draw sample current _ data localParsed,
      batch_atResult binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
        original remaining tape request HM draw H sample pivotOne hash]
    rfl

theorem state_output (sample : Fin 361 → B) :
    ((tree binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape request HM draw sample).run H).1.state =
      OracleHonestCanonical.openingState binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM H sample
        (response binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape request HM draw sample
          ((tree binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape request HM draw sample).run H).1.frontend
          ((tree binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape request HM draw sample).run H).1.batch) := by
  unfold tree OracleHonestCanonical.openingState
  rw [HonestTranscript.Mdoc.openingPrefix_output, OracleHonestCanonical.result_run]

theorem input_output (sample : Fin 361 → B) (pivotOne : binary.basis 0 = 1)
    (hash : ∀ responses coin converted, FullCoupling.hashChecks binary prime primePlan
      samplers (baseAt sample) H (FingerprintPrefix.context request (rootAt sample))
      original responses coin converted) :
    let current := ((tree binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape request HM draw sample).run H).1
    input binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM sample current =
      ((CompleteCanonicalVerifier.encoding binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg
        binaryCount metadata request).encoding.chain cfg.initialLink).point
        ⟨OracleResponse.fillBoth (CompleteFrontendBody.rawBody binary prime primePlan (rootAt sample) current.frontend)
          (response binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape request HM draw sample current.frontend current.batch),fun _ => 0⟩
        H (G).openingIndex.val := by
  dsimp only
  have inside : ((tree binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape request HM draw sample).run H).1.state.rank.val < (G).roles.length := by
    rw [state_output,OracleHonestCanonical.opening_rank]
    exact (G).openingIndex.isLt
  unfold input HonestTranscript.Mdoc.openingInput
  rw [dif_pos inside]
  let responses := response binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape request HM draw sample
    ((tree binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape request HM draw sample).run H).1.frontend
    ((tree binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape request HM draw sample).run H).1.batch
  have stateSame := state_output binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape request HM draw H sample
  have expected := OracleHonestCanonical.opening_query binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata
    original remaining tape request HM H sample pivotOne hash responses
  change CompleteTranscript.query (Authentication := OpeningBody.Authentication G) (baseAt sample) _ _ = _
  have querySame : CompleteTranscript.query (Authentication := OpeningBody.Authentication G) (baseAt sample)
      ((tree binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape request HM draw sample).run H).1.state inside =
    CompleteTranscript.query (Authentication := OpeningBody.Authentication G) (baseAt sample)
      (OracleHonestCanonical.openingState binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata original remaining tape request HM H sample responses)
      (by rw [OracleHonestCanonical.opening_rank]; exact (G).openingIndex.isLt) := by
    exact query_congr (Auth := OpeningBody.Authentication G) (baseAt sample) stateSame _ _
  let endpoint := fun (raw : Raw) =>
    ((CompleteCanonicalVerifier.encoding binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg
      binaryCount metadata request).encoding.chain cfg.initialLink).point
      (⟨OracleResponse.fillBoth (CompleteFrontendBody.rawBody binary prime primePlan (rootAt sample) raw) responses,fun _ => 0⟩ : Output)
      H (G).openingIndex.val
  have endSame := congrArg endpoint
    (frontend_output binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining tape request HM draw H sample)
  exact querySame.trans (expected.trans endSame.symm)

end LfzkV2.Current.ZeroKnowledge.OracleHonestTree
