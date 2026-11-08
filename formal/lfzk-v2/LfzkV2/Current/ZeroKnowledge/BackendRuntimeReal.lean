import LfzkV2.Current.ZeroKnowledge.BackendRuntimeEncoding
import LfzkV2.Current.ZeroKnowledge.OracleHonestRefreshGames
import LfzkV2.Current.ZeroKnowledge.CompleteTerminalOpening

/-! Identify the real backend view with the actual complete honest proof
when its single opening answer is independently refreshed. The original
source tape, authentication and final seal are retained. -/

noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.BackendRuntimeReal
open Application ApplicationSetup RecursivePolygero ConcreteSetup Merkle Merkle.MH LigeroFamily
open Frontend BackendRuntime BackendRuntimeEncoding
open scoped Classical
set_option maxHeartbeats 300000
set_option maxRecDepth 8192
attribute [local irreducible] Merkle.MH.commitPass Merkle.RandomOracle.Tree.run

variable {B C Observed : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable [Fintype C] [DecidableEq Observed]
local notation "N" => Adapter.Mdoc.P
variable (binary : BinaryCircuit B) (prime : PrimePublic N 768)
variable (primePlan : FrontendSchedule.Plan N prime.circuit)
variable (binaryNodes : Fin 2792 ↪ B)
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
variable (primeCount : shape.primePublic = prime.nPublic)
variable (metadata : CanonicalRequest.Metadata (Advice := MdocAdvice.Value) (C := C) shape binary.description.nPublic)
local notation "G" => CompleteSimulation.geometry binary prime primePlan
local notation "Public" => CompleteCanonicalVerifier.publicConfig binary.description prime binaryNodes
  ConcreteSetup.primeNodes repr shape setup cfg
local notation "P" => ConcreteSetup.backend binaryNodes binary.description.cells
local notation "R" => ConcreteSetup.backend ConcreteSetup.primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)
local notation "First" => RuntimeVerifier.first binary.description prime P R Public
local notation "Second" => RuntimeVerifier.second binary.description prime P R Public
local notation "Point" => QueryRuntime.Runtime.Point repr shape setup binary.description.nPublic
local notation "Request" => CanonicalRequest.Request shape binary.description.nPublic
local notation "Output" => CanonicalRuntime.Output (Advice := MdocAdvice.Value) binary.description shape
local notation "Body" => Current.Body G (MdocRuntime.fields B) MdocAdvice.Value (OpeningBody.Authentication G)

variable {preM preT postM postT : ℕ}
variable (prior : Merkle.RandomOracle.TwoOracleTree Bytes Digest
  (QueryRuntime.Runtime.Point repr shape setup binary.description.nPublic) (Digest × C)
  (CanonicalRequest.Request shape binary.description.nPublic) preM preT)
variable (after : CanonicalRequest.Request shape binary.description.nPublic →
  Option (CanonicalRuntime.Output (Advice := MdocAdvice.Value) binary.description shape) →
  Merkle.RandomOracle.TwoOracleTree Bytes Digest
    (QueryRuntime.Runtime.Point repr shape setup binary.description.nPublic) (Digest × C) Observed postM postT)

variable (outside : Bytes → Digest)

attribute [local instance] BackendRuntime.requestFintype BackendRuntime.leafFintype
  BackendRuntime.frontCoinsFintype BackendRuntime.genericBackendMasksFintype
  BackendRuntime.backendMasksFintype BackendRuntime.merkleCoinsFintype BackendRuntime.coinsFintype

def honestTape
    (coin : BackendRuntime.PrivateCoins binary prime primePlan binaryNodes repr shape setup cfg prior after outside) :
    HonestRuntime.Tape binary prime binaryNodes :=
  ⟨coin.1.1.1,coin.1.1.2,coin.1.2,coin.2.2.1⟩

omit [DecidableEq Observed] [Fintype C] in
theorem real_columns (original : Fin binary.nPrivate → Bool) (remaining : Fin prime.remaining → N)
    (tape : HonestRuntime.Tape binary prime binaryNodes) :
    (fun i => MerkleRuntime.tupleLeaf (First).participant (Second).participant
      (MerkleBackend.realColumns (Backend.profileGeometry binaryNodes) (Backend.profileGeometry ConcreteSetup.primeNodes)
        (HonestRuntime.logical binary prime binaryNodes original remaining tape) tape.backend i)) =
      HonestRuntime.columns binary prime primePlan binaryNodes repr shape setup cfg original remaining tape := by
  funext i participant
  fin_cases participant <;> rfl

variable (original : CanonicalRequest.Request shape binary.description.nPublic → Fin binary.nPrivate → Bool)
variable (remaining : CanonicalRequest.Request shape binary.description.nPublic → Fin prime.remaining → Adapter.Mdoc.P)

def realLabels (original : Request → Fin binary.nPrivate → Bool)
    (remaining : Request → Fin prime.remaining → N) (H : Point → Digest × C)
    (coin : BackendRuntime.PrivateCoins binary prime primePlan binaryNodes repr shape setup cfg prior after outside) :=
  MerklePreparation.honestLabels
    (MerkleSimulation.nonceCodec (finiteCodec binary prime primePlan binaryNodes repr shape setup cfg prior after outside)) 2443
    (SHAObserverWindow.before SHAOracle.merkleDomain outside (codec binary prime primePlan binaryNodes repr shape setup cfg) prior after H)
    (BackendCompiled.realMessages (Backend.profileGeometry binaryNodes) (Backend.profileGeometry ConcreteSetup.primeNodes) id
      (BackendRuntime.cells binary prime primePlan binaryNodes repr shape setup original remaining) coin.1.1 coin.1.2)
    coin.2.2.1 coin.2.1

omit [DecidableEq Observed] in
theorem root_eq (H : Point → Digest × C)
    (coin : BackendRuntime.PrivateCoins binary prime primePlan binaryNodes repr shape setup cfg prior after outside) :
    let earlier := BackendRuntime.priorStateOf binary prime primePlan binaryNodes repr shape setup cfg prior after outside H (coin.1.2,coin.2)
    realLabels binary prime primePlan binaryNodes repr shape setup cfg prior after outside original remaining H coin ⟨2*2443-2,by decide⟩ =
      HonestRuntime.commitment binary prime primePlan binaryNodes repr shape setup cfg (original earlier.1) (remaining earlier.1)
        (expanded binary prime primePlan binaryNodes repr shape setup cfg prior after outside coin.2.1)
        (honestTape binary prime primePlan binaryNodes repr shape setup cfg prior after outside coin) := by
  let earlier := BackendRuntime.priorStateOf binary prime primePlan binaryNodes repr shape setup cfg prior after outside H (coin.1.2,coin.2)
  let tape := honestTape binary prime primePlan binaryNodes repr shape setup cfg prior after outside coin
  let columns := MerkleBackend.realColumns (Backend.profileGeometry binaryNodes) (Backend.profileGeometry ConcreteSetup.primeNodes)
    (BackendRuntime.cells binary prime primePlan binaryNodes repr shape setup original remaining coin.1.1 earlier) coin.1.2
  have value := committed_root binary prime primePlan binaryNodes repr shape setup cfg prior after outside coin.2.1 coin.2.2.1 columns
  have equal := real_columns binary prime primePlan binaryNodes repr shape setup cfg (original earlier.1) (remaining earlier.1) tape
  have rooted := congrArg (fun columns => root
    ((CompleteCanonicalVerifier.merkleCodec binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg).withOracle
      (expanded binary prime primePlan binaryNodes repr shape setup cfg prior after outside coin.2.1))
      2443 (fun i => (i,coin.2.2.1 i)) columns) equal
  exact value.trans rooted

omit [DecidableEq Observed] [Fintype C] in
theorem requested_commitment (request : Request) (original : Fin binary.nPrivate → Bool)
    (remaining : Fin prime.remaining → N) (tape : HonestRuntime.Tape binary prime binaryNodes) (HM : Bytes → Digest) :
    HonestRuntime.commitment
        (RequestedSimulator.requestedBinary binary prime primePlan shape request)
        (RequestedSimulator.requestedPrime binary prime primePlan shape primeCount request) primePlan binaryNodes repr shape setup
        (RequestedSimulator.configuration binary prime primePlan binaryNodes repr shape setup cfg primeCount request)
        original remaining HM (RequestedExperiment.honestTape binary prime primePlan binaryNodes shape primeCount request tape) =
      HonestRuntime.commitment binary prime primePlan binaryNodes repr shape setup cfg original remaining HM tape := rfl

omit [DecidableEq Observed] in
set_option maxHeartbeats 1800000 in
theorem front_result (H : Point → Digest × C)
    (coin : BackendRuntime.PrivateCoins binary prime primePlan binaryNodes repr shape setup cfg prior after outside) :
    let earlier := BackendRuntime.priorStateOf binary prime primePlan binaryNodes repr shape setup cfg prior after outside H (coin.1.2,coin.2)
    let labels := realLabels binary prime primePlan binaryNodes repr shape setup cfg prior after outside original remaining H coin
    let request := earlier.1
    let HM := expanded binary prime primePlan binaryNodes repr shape setup cfg prior after outside coin.2.1
    let tape := honestTape binary prime primePlan binaryNodes repr shape setup cfg prior after outside coin
    BackendRuntime.front binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata original remaining H
      coin.1.1 earlier labels =
      RequestedExperiment.frontendBody binary prime primePlan binaryNodes repr shape setup cfg
        binaryCount primeCount metadata request (original request) (remaining request) tape HM H := by
  dsimp only [RequestedExperiment.frontendBody]
  let earlier := BackendRuntime.priorStateOf binary prime primePlan binaryNodes repr shape setup cfg prior after outside H (coin.1.2,coin.2)
  let request := earlier.1
  let tape := honestTape binary prime primePlan binaryNodes repr shape setup cfg prior after outside coin
  let b := RequestedSimulator.requestedBinary binary prime primePlan shape request
  let p := RequestedSimulator.requestedPrime binary prime primePlan shape primeCount request
  let config := RequestedSimulator.configuration binary prime primePlan binaryNodes repr shape setup cfg primeCount request
  let source := RequestedExperiment.honestTape binary prime primePlan binaryNodes shape primeCount request tape
  let encode : Digest → Body := fun root => CompleteFrontendBody.rawBody b p primePlan root
    (HonestRuntime.frontendAtRoot b p primePlan binaryNodes repr shape setup config binaryCount metadata
      (original request) (remaining request) request root H source.frontend source.selectors)
  have roots := root_eq binary prime primePlan binaryNodes repr shape setup cfg prior after outside original remaining H coin
  have requested := requested_commitment binary prime primePlan binaryNodes repr shape setup cfg primeCount request
    (original request) (remaining request) tape
    (expanded binary prime primePlan binaryNodes repr shape setup cfg prior after outside coin.2.1)
  have equal := congrArg encode (roots.trans requested.symm)
  exact equal

variable (draw : C → RuntimeVerifier.RawSamples binary.description prime
  (ConcreteSetup.backend binaryNodes binary.description.cells)
  (ConcreteSetup.backend ConcreteSetup.primeNodes (CellLayout.Prime.cells prime.remaining prime.pads))
  (CompleteCanonicalVerifier.publicConfig binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg))

/-- The pending proof determines the one canonical opening boundary. -/
def refreshedKey (request : Request) (H : Point → Digest × C)
    (pending : CanonicalRequest.Output (g := G) (fields := MdocRuntime.fields B) (Advice := MdocAdvice.Value)) : Point :=
  let e := CompleteCanonicalVerifier.encoding binary.description prime binaryNodes ConcreteSetup.primeNodes
    repr shape setup cfg binaryCount metadata request
  (e.encoding.chain cfg.initialLink).point pending H (G).openingIndex.val

/-- Finish a fixed pending proof using one returned whole oracle answer.
The canonical key and completion callback are shared by the source and its
observation law, rather than reconstructed from a concrete proof body. -/
def refreshedCallback (original : Fin binary.nPrivate → Bool) (remaining : Fin prime.remaining → N)
    (tape : HonestRuntime.Tape binary prime binaryNodes) (sample : Fin 361 → B)
    (request : Request) (HM : Bytes → Digest) (H : Point → Digest × C) (answer : Digest × C)
    (pending : CanonicalRequest.Output (g := G) (fields := MdocRuntime.fields B) (Advice := MdocAdvice.Value)) :
    Output × (Point → Digest × C) :=
  let oracle := Function.update H
    (refreshedKey binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata request H pending) answer
  (OracleHonestRuntime.finish binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata
    original remaining tape request HM oracle sample pending,oracle)

/-- This is the actual honest pending computation on the base oracle,
followed by authentication and the ordinary final seal on the returned
oracle. A failed parse does not change the oracle. -/
def refreshedForRequest (original : Fin binary.nPrivate → Bool) (remaining : Fin prime.remaining → N)
    (tape : HonestRuntime.Tape binary prime binaryNodes) (sample : Fin 361 → B)
    (request : Request) (HM : Bytes → Digest) (H : Point → Digest × C) (answer : Digest × C) :
    Option (Output × (Point → Digest × C)) :=
  (OracleHonestRuntime.pending binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
    original remaining tape request HM H draw sample).map
    (refreshedCallback binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata
      original remaining tape sample request HM H answer)

omit [DecidableEq Observed] [Fintype C] in
set_option maxHeartbeats 1800000 in
theorem complete_pending (original : Fin binary.nPrivate → Bool) (remaining : Fin prime.remaining → N)
    (tape : HonestRuntime.Tape binary prime binaryNodes) (sample : Fin 361 → B)
    (request : Request) (HM : Bytes → Digest) (H : Point → Digest × C) (answer : Digest × C) :
    let privateTape := OracleHonestRuntime.tapeAt binary prime binaryNodes tape sample
    let early := (OracleHonestRuntime.frontend binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata
      original remaining tape request HM H sample).body
    let columns := MerkleBackend.realColumns (Backend.profileGeometry binaryNodes) (Backend.profileGeometry ConcreteSetup.primeNodes)
      (HonestRuntime.logical binary prime binaryNodes original remaining tape) privateTape.backend
    let statements := OracleHonestRuntime.statement binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
      original remaining tape request HM H sample
    let batch := CompleteCanonicalVerifier.batchingCoin binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg
      binaryCount metadata draw request early H
    CompleteObserver.complete binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg
      binaryCount primeCount metadata request (cfg.sample answer.2) early
      (CompleteResponse.realResponses binary.description prime binaryNodes ConcreteSetup.primeNodes Public
        (HonestRuntime.logical binary prime binaryNodes original remaining tape) statements batch privateTape.backend)
      (fun i => columns i.val)
      (CompleteObserverSimulation.opening binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg
        HM (cfg.sample answer.2) privateTape.nonces columns) H answer =
      refreshedForRequest binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata draw
        original remaining tape sample request HM H answer := by
  let privateTape := OracleHonestRuntime.tapeAt binary prime binaryNodes tape sample
  let early := (OracleHonestRuntime.frontend binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata
    original remaining tape request HM H sample).body
  let columns := MerkleBackend.realColumns (Backend.profileGeometry binaryNodes) (Backend.profileGeometry ConcreteSetup.primeNodes)
    (HonestRuntime.logical binary prime binaryNodes original remaining tape) privateTape.backend
  let opened := CompleteObserverSimulation.opening binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg
    HM (cfg.sample answer.2) privateTape.nonces columns
  have columnsEq := real_columns binary prime primePlan binaryNodes repr shape setup cfg original remaining privateTape
  have fixed : {early with commitment := opened.rt} = early := by
    have roots : opened.rt = early.commitment := by
      unfold opened CompleteObserverSimulation.opening
      change root _ 2443 _ (fun i => MerkleRuntime.tupleLeaf (First).participant (Second).participant (columns i)) = _
      rw [show (fun i => MerkleRuntime.tupleLeaf (First).participant (Second).participant (columns i)) =
        HonestRuntime.columns binary prime primePlan binaryNodes repr shape setup cfg original remaining privateTape from columnsEq]
      rfl
    exact CompleteTerminal.commitment_eq early opened.rt roots.symm
  let statements := OracleHonestRuntime.statement binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
    original remaining tape request HM H sample
  let batch := CompleteCanonicalVerifier.batchingCoin binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg
    binaryCount metadata draw request early H
  let responses := CompleteResponse.realResponses binary.description prime binaryNodes ConcreteSetup.primeNodes Public
    (HonestRuntime.logical binary prime binaryNodes original remaining tape) statements batch privateTape.backend
  let full := CompleteObserver.body binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg
    (cfg.sample answer.2) early responses (fun i => columns i.val) opened
  have parse := CompleteObserverSimulation.statementAt_body binary.description prime binaryNodes ConcreteSetup.primeNodes
    repr shape setup cfg binaryCount primeCount metadata request (cfg.sample answer.2) early responses
    (fun i => columns i.val) opened H
  rw [fixed] at parse
  have body := CompleteObserverSimulation.body_honest binary.description prime binaryNodes ConcreteSetup.primeNodes
    repr shape setup cfg HM (cfg.sample answer.2) privateTape.nonces columns early responses
  rw [fixed] at body
  cases parsed : OracleHonestRuntime.statementAt binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
      original remaining tape request HM H sample with
  | none =>
      have bad : CompleteCanonicalVerifier.statementAt binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg
          binaryCount primeCount metadata request full H = none := parse.trans parsed
      change (CompleteCanonicalVerifier.statementAt binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg
        binaryCount primeCount metadata request full H).bind (fun _ => some _) = _
      rw [bad]
      simp only [Option.bind_none,refreshedForRequest,OracleHonestRuntime.pending,parsed,Option.bind_eq_bind,Option.bind_none,Option.map_none]
  | some data =>
      have good : CompleteCanonicalVerifier.statementAt binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg
          binaryCount primeCount metadata request full H = some data := parse.trans parsed
      have statementEq : statements = data.2.statement := by
        simp only [statements,OracleHonestRuntime.statement,parsed,Option.map_some,Option.getD_some]
      let pending : CanonicalRequest.Output (g := G) (fields := MdocRuntime.fields B) (Advice := MdocAdvice.Value) :=
        ⟨HonestRuntime.responseBody binary prime primePlan early
          (CompleteVerifier.wireResponses binary.description prime binaryNodes ConcreteSetup.primeNodes Public responses),fun _ => 0⟩
      let e := CompleteCanonicalVerifier.encoding binary.description prime binaryNodes ConcreteSetup.primeNodes
        repr shape setup cfg binaryCount metadata request
      let oracle := Function.update H ((e.encoding.chain cfg.initialLink).point pending H (G).openingIndex.val) answer
      have selected : OracleHonestRuntime.pending binary prime primePlan binaryNodes repr shape setup cfg binaryCount primeCount metadata
          original remaining tape request HM H draw sample = some pending := by
        simp only [OracleHonestRuntime.pending,parsed,Option.bind_eq_bind,Option.bind_some,Option.pure_def]
        rw [← statementEq]
      have pendingBody : CompleteTerminal.fill pending.body full = full := by
        rw [show full = _ from body]
        rfl
      have binaryResponse : full.binaryBackend.response = pending.body.binaryBackend.response := by rfl
      have primeResponse : full.primeBackend.response = pending.body.primeBackend.response := by rfl
      have programmed := CompleteTerminalOpening.programAndFinalize_update repr shape setup binary.description.nPublic
        (CanonicalRuntime.binaryRequest binary.description prime P R repr shape setup
          (CompleteCanonicalVerifier.basePublic binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg) binaryCount)
        metadata request cfg.initialLink pending full binaryResponse primeResponse H answer
      rw [pendingBody] at programmed
      have openingAnswer : oracle ((e.encoding.chain cfg.initialLink).point pending oracle (G).openingIndex.val) = answer :=
        OracleProgramming.answer_at (e.encoding.chain cfg.initialLink) pending H (G).openingIndex answer
      have finished : OracleHonestRuntime.finish binary prime primePlan binaryNodes repr shape setup cfg binaryCount metadata
          original remaining tape request HM oracle sample pending = (⟨request,OracleProgramming.finalize e cfg.initialLink full oracle⟩ : Output) := by
        unfold OracleHonestRuntime.finish
        dsimp only
        rw [openingAnswer]
        rw [show full = _ from body]
        apply congrArg (fun value : Body => (⟨request,OracleProgramming.finalize e cfg.initialLink value oracle⟩ : Output))
        exact CompleteBody.fill_congr (First).participant (Second).participant cfg.binaryField cfg.primeField
          cfg.binaryRows cfg.primeRows cfg.openings _ (cfg.sample answer.2) privateTape.nonces _ _ columnsEq.symm
          pending.body early (by rfl) _ setup.jointContext _ _
      change (CompleteCanonicalVerifier.statementAt binary.description prime binaryNodes ConcreteSetup.primeNodes repr shape setup cfg
        binaryCount primeCount metadata request full H).bind (fun _ => some _) = _
      rw [good]
      simp only [Option.bind_some,refreshedForRequest,refreshedCallback,refreshedKey,selected,Option.map_some]
      rw [finished]
      exact congrArg (fun result => some ((⟨request,result.1⟩ : Output),result.2)) programmed

end LfzkV2.Current.ZeroKnowledge.BackendRuntimeReal
