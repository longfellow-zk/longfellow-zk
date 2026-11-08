import LfzkV2.Current.ZeroKnowledge.CompleteSimulationBody
import LfzkV2.Current.ZeroKnowledge.CompleteBody
import LfzkV2.Current.ZeroKnowledge.CompleteBackend
import LfzkV2.Current.RuntimeAdaptiveVerifier

/-! Actual current verifier acceptance of encoded zero-cell simulations.
The intermediate premises below are exact parser, wire-encoding and oracle
equalities. Backend arithmetic and Merkle acceptance are derived from the
public correction and the honest dummy commitment; neither is a supplied
acceptance/correctness certificate. The canonical frontend/finalization
constructors discharge the exact equalities at the complete protocol boundary. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.CompleteVerifier

open Application ApplicationSetup RecursivePolygero Merkle Merkle.MH LigeroFamily
open scoped Classical
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

variable {g : Geometry} {fields : Fields} {Advice Base Key C Enc Request : Type}
variable {B : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable {shared maskBits adviceBits : ℕ}
variable (binary : BinaryPublic B shared maskBits adviceBits)
local notation "N" => ZMod Adapter.Mdoc.primeOrder
variable (prime : PrimePublic N shared)
variable (binaryNodes : Fin 2792 ↪ B) (primeNodes : Fin 2792 ↪ N)
local notation "P" => ConcreteSetup.backend binaryNodes binary.cells
local notation "R" => ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)
variable (cfg : RuntimeVerifier.Public (g := g) binary prime
  (ConcreteSetup.backend binaryNodes binary.cells)
  (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads))
  (fields := fields) (Advice := Advice)
  (Base := Base) (Key := Key) (C := C) (Salt := Fin 2443 × MerkleNonce))
local notation "First" => RuntimeVerifier.first binary prime P R cfg
local notation "Second" => RuntimeVerifier.second binary prime P R cfg
local notation "Family" => RuntimeVerifier.Family binary prime P R cfg
local notation "Point" => RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice)
  (Base := Base) (Key := Key)
local notation "Output" => RuntimeAdaptive.Output (g := g) (fields := fields) (Advice := Advice)
  (Auth := OpeningBody.Authentication g) (Request := Request)
local notation "Data" => Σ A : RuntimeVerifier.System binary prime (C := C), StatementData A First Second

variable (earlier : Request → Replay.Encoding g fields Advice (OpeningBody.Authentication g) Key
  (Base × ProtocolWrites.Fresh g fields Advice) C)
variable (hashPublic : Key → Option (Fin binary.nPublic → Bool))
variable (decodePublic : Base → Option (Fin prime.nPublic → N))
variable (draw : C → RuntimeVerifier.RawSamples binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) cfg)
variable (codec : Codec (Fin 2443 × MerkleNonce) (RuntimeVerifier.Family binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) cfg).Leaf Digest Enc)

theorem simulatedBody_responses (HM : Enc → Digest) (indices : Fin 84 ↪ Fin 2443)
    (nonces : Fin 2443 → MerkleNonce)
    (tape : CompleteBackend.Masks binaryNodes primeNodes binary.cells
      (CellLayout.Prime.cells prime.remaining prime.pads))
    (statement : JointResponse.Statement (First).participant (Second).participant)
    (coin : JointResponse.Coin (First).participant (Second).participant)
    (frontend : Body g fields Advice (OpeningBody.Authentication g)) (context finalSeal : Digest) :
    RuntimeVerifier.responses binary prime P R cfg
      ⟨simulatedBody binary prime binaryNodes primeNodes cfg codec HM indices nonces tape statement coin frontend context,finalSeal⟩ =
      CompleteBackend.responses binaryNodes primeNodes binary.cells
        (CellLayout.Prime.cells prime.remaining prime.pads) cfg.countBinary cfg.countPrime
        (OrderedOpening.query indices) statement coin tape := by
  simp only [RuntimeVerifier.responses, BackendVerifier.responses, simulatedBody,
    CompleteBody.fill, wireResponses, Prod.eta, Equiv.apply_symm_apply]

theorem simulatedBody_raw (HM : Enc → Digest) (indices : Fin 84 ↪ Fin 2443)
    (nonces : Fin 2443 → MerkleNonce)
    (tape : CompleteBackend.Masks binaryNodes primeNodes binary.cells
      (CellLayout.Prime.cells prime.remaining prime.pads))
    (statement : JointResponse.Statement (First).participant (Second).participant)
    (coin : JointResponse.Coin (First).participant (Second).participant)
    (frontend : Body g fields Advice (OpeningBody.Authentication g)) (context finalSeal : Digest) :
    OpeningBody.raw (First).participant (Second).participant cfg.binaryField cfg.primeField
      cfg.binaryRows cfg.primeRows cfg.openings
      ⟨simulatedBody binary prime binaryNodes primeNodes cfg codec HM indices nonces tape statement coin frontend context,finalSeal⟩ =
      CompleteOpening.raw (codec.withOracle HM) (fun i nonce => (i,nonce)) indices nonces
        (dummyColumns binary prime binaryNodes primeNodes cfg tape) :=
  CompleteBody.raw_fill (First).participant (Second).participant cfg.binaryField cfg.primeField
    cfg.binaryRows cfg.primeRows cfg.openings (codec.withOracle HM) indices nonces
    (dummyColumns binary prime binaryNodes primeNodes cfg tape) _ _ context _ finalSeal

variable [Inhabited (RuntimeVerifier.Family binary prime (ConcreteSetup.backend binaryNodes binary.cells) (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) cfg).Leaf]

theorem acceptance_of_encoded_simulation
    (output : Output)
    (H : RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice) (Base := Base) (Key := Key) → Digest × C)
    (HM : Enc → Digest) (indices : Fin 84 ↪ Fin 2443)
    (nonces : Fin 2443 → MerkleNonce)
    (tape : CompleteBackend.Masks binaryNodes primeNodes binary.cells
      (CellLayout.Prime.cells prime.remaining prime.pads))
    (data : Data)
    (parsed :
      let e := RuntimeAdaptiveVerifier.encodings binary prime P R cfg earlier output.request
      let parent := BackendPath.parent e cfg.initialLink output.proof H g.batchingIndex
      RuntimeAdaptive.statementAt binary prime P R cfg hashPublic decodePublic
        parent.point (parent.point.priorAnswers H) = some data)
    (sampled :
      let e := RuntimeAdaptiveVerifier.encodings binary prime P R cfg earlier output.request
      cfg.sample (H ((e.chain cfg.initialLink).point output.proof H g.openingIndex.val)).2 = indices)
    (responsesEncoded :
      let e := RuntimeAdaptiveVerifier.encodings binary prime P R cfg earlier output.request
      let parent := BackendPath.parent e cfg.initialLink output.proof H g.batchingIndex
      let coin := RuntimeVerifier.batchingDecoder binary prime P R cfg draw (H parent.point).2
      RuntimeVerifier.responses binary prime P R cfg output.proof =
        CompleteBackend.responses binaryNodes primeNodes binary.cells
          (CellLayout.Prime.cells prime.remaining prime.pads) cfg.countBinary cfg.countPrime
          (OrderedOpening.query indices) data.2.statement coin tape)
    (rawEncoded :
      OpeningBody.raw (First).participant (Second).participant cfg.binaryField cfg.primeField
          cfg.binaryRows cfg.primeRows cfg.openings output.proof =
        CompleteOpening.raw (codec.withOracle HM) (fun i nonce => (i,nonce)) indices nonces
          ((RuntimeVerifier.Family binary prime P R cfg).columnsEquiv (CompleteBackend.familyOracle binaryNodes primeNodes binary.cells
            (CellLayout.Prime.cells prime.remaining prime.pads) cfg.countBinary cfg.countPrime tape)))
    (committed : output.proof.body.commitment =
      root (codec.withOracle HM) 2443 (fun i => (i,nonces i))
        ((RuntimeVerifier.Family binary prime P R cfg).columnsEquiv (CompleteBackend.familyOracle binaryNodes primeNodes binary.cells
          (CellLayout.Prime.cells prime.remaining prime.pads) cfg.countBinary cfg.countPrime tape)))
    (rootBound :
      let key := (RuntimeAdaptiveVerifier.encodings binary prime P R cfg earlier output.request).context output.proof
      cfg.root key = output.proof.body.commitment)
    (contextBound :
      let key := (RuntimeAdaptiveVerifier.encodings binary prime P R cfg earlier output.request).context output.proof
      output.proof.body.authentication.context = cfg.authenticationContext key)
    (saltBound :
      let key := (RuntimeAdaptiveVerifier.encodings binary prime P R cfg earlier output.request).context output.proof
      cfg.bindSalt key = fun i nonce => (i,nonce))
    (finalSeal : (H ((RuntimeAdaptiveVerifier.chain binary prime P R cfg earlier).finalSealPoint output H)).1 =
      output.proof.finalSeal) :
    RuntimeAdaptiveVerifier.verify binary prime P R cfg earlier hashPublic decodePublic draw codec HM output H = true := by
  letI : Inhabited (Joint.Pair.family (CompleteBackend.first binaryNodes binary.cells cfg.countBinary).participant
      (CompleteBackend.second primeNodes (CellLayout.Prime.cells prime.remaining prime.pads) cfg.countPrime).participant).Leaf :=
    inferInstanceAs (Inhabited (RuntimeVerifier.Family binary prime P R cfg).Leaf)
  let e := RuntimeAdaptiveVerifier.encodings binary prime P R cfg earlier output.request
  let parent := BackendPath.parent e cfg.initialLink output.proof H g.batchingIndex
  let coin := RuntimeVerifier.batchingDecoder binary prime P R cfg draw (H parent.point).2
  let columns := (RuntimeVerifier.Family binary prime P R cfg).columnsEquiv (CompleteBackend.familyOracle binaryNodes primeNodes binary.cells
    (CellLayout.Prime.cells prime.remaining prime.pads) cfg.countBinary cfg.countPrime tape)
  let claim := CompleteOpening.claim (codec.withOracle HM) (fun i nonce => (i,nonce)) indices nonces columns
  let decoded : RuntimeVerifier.Decoded binary prime P R cfg := {
    application := data.1
    statement := data.2
    claim := claim
    coin := coin
    query := OrderedOpening.query indices }
  apply (RuntimeAdaptiveVerifier.verify_true_iff binary prime P R cfg earlier hashPublic decodePublic draw codec HM output H).mpr
  refine ⟨decoded,?_,?_⟩
  · change Option.bind
      (RuntimeAdaptive.statementAt binary prime P R cfg hashPublic decodePublic parent.point (parent.point.priorAnswers H))
      (fun data => Option.bind
        (OrderedOpening.decode (cfg.bindSalt (e.context output.proof))
          (cfg.sample (H ((e.chain cfg.initialLink).point output.proof H g.openingIndex.val)).2)
          (OpeningBody.raw (First).participant (Second).participant cfg.binaryField cfg.primeField
            cfg.binaryRows cfg.primeRows cfg.openings output.proof))
        (fun claim => some ⟨data.1,data.2,claim,coin,
          OrderedOpening.query (cfg.sample (H ((e.chain cfg.initialLink).point output.proof H g.openingIndex.val)).2)⟩)) =
      some decoded
    have parse : RuntimeAdaptive.statementAt binary prime P R cfg hashPublic decodePublic
        parent.point (parent.point.priorAnswers H) = some data := parsed
    rw [parse]
    simp only [Option.bind_some]
    erw [sampled,rawEncoded,saltBound,CompleteOpening.decode_raw]
    rfl
  · change cfg.root (e.context output.proof) = output.proof.body.commitment ∧
      output.proof.body.authentication.context = cfg.authenticationContext (e.context output.proof) ∧
      ((RuntimeVerifier.Family binary prime P R cfg).compiler cfg.openingPositive).Accepts (codec.withOracle HM)
        ((Joint.Pair.statementEquiv _ _).symm data.2.statement) (cfg.root (e.context output.proof))
        ((Joint.Pair.coinEquiv _ _).symm coin)
        ((Joint.Pair.responseEquiv _ _).symm (RuntimeVerifier.responses binary prime P R cfg output.proof))
        (OrderedOpening.query indices) claim ∧ _
    refine ⟨rootBound,contextBound,?_,finalSeal⟩
    rw [rootBound,committed,responsesEncoded]
    exact CompleteBackend.compiled_verifies binaryNodes primeNodes binary.cells
      (CellLayout.Prime.cells prime.remaining prime.pads) cfg.countBinary cfg.countPrime
      (codec.withOracle HM) indices data.2.statement coin tape nonces

end LfzkV2.Current.ZeroKnowledge.CompleteVerifier
