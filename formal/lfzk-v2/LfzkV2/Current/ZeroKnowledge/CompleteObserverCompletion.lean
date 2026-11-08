import LfzkV2.Current.ZeroKnowledge.CompleteObserverSimulation

/-! Complete the public backend view with the actual parser, opening-answer
replacement and final seal. The small option lemma keeps parser failure and
the successful response selected by that same parser in one exact identity. -/

noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.CompleteObserverSimulation
open Application ApplicationSetup RecursivePolygero Merkle Merkle.MH LigeroFamily
open scoped Classical
set_option maxHeartbeats 1400000
set_option maxRecDepth 4096

variable {g : Geometry} {fields : Fields} {Advice C B : Type}
variable [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable {shared maskBits adviceBits : ℕ}
variable (binary : BinaryPublic B shared maskBits adviceBits)
local notation "N" => ZMod Adapter.Mdoc.primeOrder
variable (prime : PrimePublic N shared)
variable (binaryNodes : Fin 2792 ↪ B) (primeNodes : Fin 2792 ↪ N)
local notation "P" => ConcreteSetup.backend binaryNodes binary.cells
local notation "R" => ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)
variable (repr : ProofBodyCodec.Representations fields Advice)
variable (shape : WireBlocks.Shape g fields) (setup : FingerprintPrefix.Setup)
variable (cfg : RuntimeVerifier.Public (g := g) binary prime
  (ConcreteSetup.backend binaryNodes binary.cells)
  (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads))
  (fields := fields) (Advice := Advice)
  (Base := CanonicalRequest.Base repr shape setup binary.nPublic)
  (Key := FingerprintPrefix.Key binary.nPublic) (C := C) (Salt := Fin 2443 × MerkleNonce))
variable (binaryCount : shape.binaryPublic = binary.nPublic)
variable (primeCount : shape.primePublic = prime.nPublic)
variable (metadata : CanonicalRequest.Metadata (Advice := Advice) (C := C) shape binary.nPublic)
local notation "Cfg" => CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup cfg
local notation "First" => RuntimeVerifier.first binary prime P R Cfg
local notation "Second" => RuntimeVerifier.second binary prime P R Cfg
local notation "Body" => Current.Body g fields Advice (OpeningBody.Authentication g)
local notation "Point" => QueryRuntime.Runtime.Point repr shape setup binary.nPublic
local notation "Request" => CanonicalRequest.Request shape binary.nPublic
local notation "Output" => CanonicalRuntime.Output (Advice := Advice) binary shape

variable (draw : C → RuntimeVerifier.RawSamples binary prime
  (ConcreteSetup.backend binaryNodes binary.cells)
  (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads))
  (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup cfg))

def dummyResponse (request : CanonicalRequest.Request shape binary.nPublic)
    (HM : Bytes → Digest) (indices : Fin 84 ↪ Fin 2443) (nonces : Fin 2443 → MerkleNonce)
    (tape : CompleteBackend.Masks binaryNodes primeNodes binary.cells
      (CellLayout.Prime.cells prime.remaining prime.pads))
    (frontend : Body) (H : Point → Digest × C) :
    JointResponse.Response (First).participant (Second).participant :=
  let early := CompleteCanonicalVerifier.committedFrontend binary prime binaryNodes primeNodes repr shape setup cfg HM nonces tape frontend
  CompleteBackend.responses binaryNodes primeNodes binary.cells
    (CellLayout.Prime.cells prime.remaining prime.pads) cfg.countBinary cfg.countPrime
    (OrderedOpening.query indices)
    (statement binary prime binaryNodes primeNodes repr shape setup cfg binaryCount primeCount metadata request early H)
    (CompleteCanonicalVerifier.batchingCoin binary prime binaryNodes primeNodes repr shape setup cfg binaryCount metadata draw request early H) tape

private theorem selected_bind {A S T : Type} (o : Option A) (pick : A → S) (fallback : S)
    (left : S → T) (right : A → T) (same : ∀ a, left (pick a) = right a) :
    o.bind (fun _ => some (left ((o.map pick).getD fallback))) = o.bind (fun a => some (right a)) := by
  cases o with
  | none => rfl
  | some a => exact congrArg some (same a)

set_option maxHeartbeats 300000 in
theorem complete_dummy (request : CanonicalRequest.Request shape binary.nPublic)
    (HM : Bytes → Digest) (indices : Fin 84 ↪ Fin 2443) (nonces : Fin 2443 → MerkleNonce)
    (tape : CompleteBackend.Masks binaryNodes primeNodes binary.cells
      (CellLayout.Prime.cells prime.remaining prime.pads))
    (frontend : Body) (H : Point → Digest × C) (answer : Digest × C) :
    CompleteObserver.complete binary prime binaryNodes primeNodes repr shape setup cfg binaryCount primeCount metadata
      request indices frontend
      (dummyResponse binary prime binaryNodes primeNodes repr shape setup cfg binaryCount primeCount metadata draw request HM indices nonces tape frontend H)
      (fun i => MerkleBackend.simColumns (Backend.profileGeometry binaryNodes) (Backend.profileGeometry primeNodes) tape i.val)
      (opening binary prime binaryNodes primeNodes repr shape setup cfg HM indices nonces
        (MerkleBackend.simColumns (Backend.profileGeometry binaryNodes) (Backend.profileGeometry primeNodes) tape))
      H answer =
      CompleteCanonicalVerifier.complete binary prime binaryNodes primeNodes repr shape setup cfg binaryCount primeCount metadata draw
        request HM indices nonces tape frontend H answer := by
  have sameParse := statementAt_body binary prime binaryNodes primeNodes repr shape setup cfg binaryCount primeCount metadata
    request indices frontend
    (CompleteBackend.responses binaryNodes primeNodes binary.cells
      (CellLayout.Prime.cells prime.remaining prime.pads) cfg.countBinary cfg.countPrime
      (OrderedOpening.query indices)
      (statement binary prime binaryNodes primeNodes repr shape setup cfg binaryCount primeCount metadata request
        (CompleteCanonicalVerifier.committedFrontend binary prime binaryNodes primeNodes repr shape setup cfg HM nonces tape frontend) H)
      (CompleteCanonicalVerifier.batchingCoin binary prime binaryNodes primeNodes repr shape setup cfg binaryCount metadata draw request
        (CompleteCanonicalVerifier.committedFrontend binary prime binaryNodes primeNodes repr shape setup cfg HM nonces tape frontend) H) tape)
    (fun i => MerkleBackend.simColumns (Backend.profileGeometry binaryNodes) (Backend.profileGeometry primeNodes) tape i.val)
    (opening binary prime binaryNodes primeNodes repr shape setup cfg HM indices nonces
      (MerkleBackend.simColumns (Backend.profileGeometry binaryNodes) (Backend.profileGeometry primeNodes) tape)) H
  have sameRoot :
      {frontend with commitment := (opening binary prime binaryNodes primeNodes repr shape setup cfg HM indices nonces
        (MerkleBackend.simColumns (Backend.profileGeometry binaryNodes) (Backend.profileGeometry primeNodes) tape)).rt} =
      CompleteCanonicalVerifier.committedFrontend binary prime binaryNodes primeNodes repr shape setup cfg HM nonces tape frontend := by
    unfold opening CompleteCanonicalVerifier.committedFrontend
    erw [dummy_columns binary prime binaryNodes primeNodes repr shape setup cfg tape]
  rw [sameRoot] at sameParse
  let early := CompleteCanonicalVerifier.committedFrontend binary prime binaryNodes primeNodes repr shape setup cfg
    HM nonces tape frontend
  let batch := CompleteCanonicalVerifier.batchingCoin binary prime binaryNodes primeNodes repr shape setup cfg binaryCount metadata draw
    request early H
  let response := CompleteBackend.responses binaryNodes primeNodes binary.cells
    (CellLayout.Prime.cells prime.remaining prime.pads) cfg.countBinary cfg.countPrime (OrderedOpening.query indices)
    (statement binary prime binaryNodes primeNodes repr shape setup cfg binaryCount primeCount metadata request early H) batch tape
  let opened := opening binary prime binaryNodes primeNodes repr shape setup cfg HM indices nonces
    (MerkleBackend.simColumns (Backend.profileGeometry binaryNodes) (Backend.profileGeometry primeNodes) tape)
  let full := CompleteObserver.body binary prime binaryNodes primeNodes repr shape setup cfg indices frontend response
    (fun i => MerkleBackend.simColumns (Backend.profileGeometry binaryNodes) (Backend.profileGeometry primeNodes) tape i.val) opened
  let finish := fun body : Body =>
    let finalized := OracleProgramming.programAndFinalize
      (CompleteCanonicalVerifier.encoding binary prime binaryNodes primeNodes repr shape setup cfg binaryCount metadata request)
      cfg.initialLink body H g.openingIndex answer
    ((⟨request,finalized.1⟩ : Output),finalized.2)
  have swapped := congrArg (fun parsed => parsed.bind (fun _ => some (finish full))) sameParse
  change (CompleteCanonicalVerifier.statementAt binary prime binaryNodes primeNodes repr shape setup cfg
    binaryCount primeCount metadata request full H).bind (fun _ => some (finish full)) = _ at swapped
  change (CompleteCanonicalVerifier.statementAt binary prime binaryNodes primeNodes repr shape setup cfg
    binaryCount primeCount metadata request full H).bind (fun _ => some (finish full)) = _
  refine swapped.trans ?_
  exact selected_bind
    (CompleteCanonicalVerifier.statementAt binary prime binaryNodes primeNodes repr shape setup cfg binaryCount primeCount metadata request early H)
    (fun data => data.2.statement)
    (⟨fun _ _ _ _ => 0,fun _ => 0⟩,⟨fun _ _ _ _ => 0,fun _ => 0⟩)
    (fun st => finish (CompleteObserver.body binary prime binaryNodes primeNodes repr shape setup cfg indices frontend
      (CompleteBackend.responses binaryNodes primeNodes binary.cells
        (CellLayout.Prime.cells prime.remaining prime.pads) cfg.countBinary cfg.countPrime (OrderedOpening.query indices) st batch tape)
      (fun i => MerkleBackend.simColumns (Backend.profileGeometry binaryNodes) (Backend.profileGeometry primeNodes) tape i.val) opened))
    (fun data => CompleteCanonicalVerifier.simulate binary prime binaryNodes primeNodes repr shape setup cfg binaryCount metadata
      request HM indices nonces tape data batch frontend H answer)
    (fun data => congrArg finish (body_dummy binary prime binaryNodes primeNodes repr shape setup cfg HM indices nonces tape data.2.statement batch frontend))

end LfzkV2.Current.ZeroKnowledge.CompleteObserverSimulation
