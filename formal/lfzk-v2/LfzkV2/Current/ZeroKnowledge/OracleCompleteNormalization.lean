import LfzkV2.Current.ZeroKnowledge.OracleNormalization
import LfzkV2.Current.ZeroKnowledge.OracleResults
import LfzkV2.Current.ZeroKnowledge.CompleteCanonicalCompletion

/-! Canonical-coordinate normalization of the actual backend completion.
The public statement and batching answer are recomputed from the canonical
prefix. Both parser branches and the resulting programmed oracle are kept. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.OracleCompleteNormalization
open Application ApplicationSetup RecursivePolygero ConcreteSetup LigeroFamily
open scoped Classical
set_option maxHeartbeats 1000000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
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
local notation "Data" => Σ A : RuntimeVerifier.System binary prime (C := C), StatementData A First Second
local notation "Body" => Current.Body g fields Advice (OpeningBody.Authentication g)
local notation "Point" => QueryRuntime.Runtime.Point repr shape setup binary.nPublic
local notation "Output" => CanonicalRuntime.Output (Advice := Advice) binary shape
local notation "binaryRequest" => CanonicalRuntime.binaryRequest binary prime P R repr shape setup
  (CompleteCanonicalVerifier.basePublic binary prime binaryNodes primeNodes repr shape setup cfg) binaryCount
variable (bodyFits : ProofBodyBounds.bodyBound repr g ≤ CanonicalPrefix.maxLength)
variable (request : CanonicalRequest.Request shape binary.nPublic)
variable (H H' : QueryRuntime.Runtime.Point repr shape setup binary.nPublic → Digest × C)
variable (agree : OracleNormalization.Agree repr shape setup binary.nPublic H H')

omit [DecidableEq B] in
include agree bodyFits in
theorem batchingPoint_eq (frontend : Body) :
    CompleteCanonicalVerifier.batchingPoint binary prime binaryNodes primeNodes repr shape setup cfg binaryCount metadata request frontend H =
    CompleteCanonicalVerifier.batchingPoint binary prime binaryNodes primeNodes repr shape setup cfg binaryCount metadata request frontend H' := by
  unfold CompleteCanonicalVerifier.batchingPoint
  rw [BackendPath.parent_point,BackendPath.parent_point]
  exact OracleNormalization.point_eq repr shape setup binary.nPublic binaryRequest metadata request bodyFits cfg.initialLink
    ⟨frontend,fun _ => 0⟩ H H' agree g.batchingIndex.val (Nat.le_of_lt g.batchingIndex.isLt)

omit [DecidableEq B] in
include bodyFits in
theorem batchingPoint_canonical (frontend : Body) :
    QueryRuntime.Runtime.Canonical repr shape setup binary.nPublic
      (CompleteCanonicalVerifier.batchingPoint binary prime binaryNodes primeNodes repr shape setup cfg binaryCount metadata request frontend H) := by
  unfold CompleteCanonicalVerifier.batchingPoint
  rw [BackendPath.parent_point]
  exact OracleBytes.replay_canonical repr shape setup binary.nPublic binaryRequest metadata bodyFits request cfg.initialLink
    ⟨frontend,fun _ => 0⟩ H g.batchingIndex.val (Nat.le_of_lt g.batchingIndex.isLt)

include agree bodyFits in
theorem statement_eq (frontend : Body) :
    CompleteCanonicalVerifier.statementAt binary prime binaryNodes primeNodes repr shape setup cfg binaryCount primeCount metadata request frontend H =
    CompleteCanonicalVerifier.statementAt binary prime binaryNodes primeNodes repr shape setup cfg binaryCount primeCount metadata request frontend H' := by
  let point := CompleteCanonicalVerifier.batchingPoint binary prime binaryNodes primeNodes repr shape setup cfg binaryCount metadata request frontend H
  let decode := CanonicalRuntime.decodePrimePublic binary prime P R repr shape setup
    (CompleteCanonicalVerifier.basePublic binary prime binaryNodes primeNodes repr shape setup cfg) primeCount
  let read := fun p : Point => RuntimeAdaptive.statementAt binary prime P R Cfg
    (CanonicalRequest.hashPublic binary.nPublic) decode p (p.priorAnswers H')
  have prior := OracleNormalization.priorAnswers_eq repr shape setup binary.nPublic point
    (batchingPoint_canonical binary prime binaryNodes primeNodes repr shape setup cfg binaryCount metadata bodyFits request H frontend) H H' agree
  have points := batchingPoint_eq binary prime binaryNodes primeNodes repr shape setup cfg binaryCount metadata bodyFits request H H' agree frontend
  exact (congrArg (fun past => RuntimeAdaptive.statementAt binary prime P R Cfg
      (CanonicalRequest.hashPublic binary.nPublic) decode point past) prior).trans (congrArg read points)

variable (draw : C → RuntimeVerifier.RawSamples binary prime
  (ConcreteSetup.backend binaryNodes binary.cells)
  (ConcreteSetup.backend primeNodes (CellLayout.Prime.cells prime.remaining prime.pads))
  (CompleteCanonicalVerifier.publicConfig binary prime binaryNodes primeNodes repr shape setup cfg))

include agree bodyFits in
theorem batchingCoin_eq (frontend : Body) :
    CompleteCanonicalVerifier.batchingCoin binary prime binaryNodes primeNodes repr shape setup cfg binaryCount metadata draw request frontend H =
    CompleteCanonicalVerifier.batchingCoin binary prime binaryNodes primeNodes repr shape setup cfg binaryCount metadata draw request frontend H' := by
  have answers := (agree _ (batchingPoint_canonical binary prime binaryNodes primeNodes repr shape setup cfg binaryCount metadata bodyFits request H frontend)).trans
    (congrArg H' (batchingPoint_eq binary prime binaryNodes primeNodes repr shape setup cfg binaryCount metadata bodyFits request H H' agree frontend))
  exact congrArg (fun answer => RuntimeVerifier.batchingDecoder binary prime P R Cfg draw answer.2) answers

abbrev CompletionEq (first second : Option (Output × (Point → Digest × C))) : Prop :=
  OracleResults.SameCompletion
    {point | QueryRuntime.Runtime.Canonical repr shape setup binary.nPublic point} first second

include agree bodyFits in
theorem simulate_eq (HM : Bytes → Digest) (indices : Fin 84 ↪ Fin 2443) (nonces : Fin 2443 → MerkleNonce)
    (tape : CompleteBackend.Masks binaryNodes primeNodes binary.cells (CellLayout.Prime.cells prime.remaining prime.pads))
    (data : Data) (coin : JointResponse.Coin (First).participant (Second).participant)
    (frontend : Body) (answer : Digest × C) :
    (CompleteCanonicalVerifier.simulate binary prime binaryNodes primeNodes repr shape setup cfg binaryCount metadata request HM indices nonces tape data coin frontend H answer).1 =
      (CompleteCanonicalVerifier.simulate binary prime binaryNodes primeNodes repr shape setup cfg binaryCount metadata request HM indices nonces tape data coin frontend H' answer).1 ∧
    OracleNormalization.Agree repr shape setup binary.nPublic
      (CompleteCanonicalVerifier.simulate binary prime binaryNodes primeNodes repr shape setup cfg binaryCount metadata request HM indices nonces tape data coin frontend H answer).2
      (CompleteCanonicalVerifier.simulate binary prime binaryNodes primeNodes repr shape setup cfg binaryCount metadata request HM indices nonces tape data coin frontend H' answer).2 := by
  let full := CompleteCanonicalVerifier.body binary prime binaryNodes primeNodes repr shape setup cfg HM indices nonces tape data coin frontend
  have normalized := OracleNormalization.program_eq repr shape setup binary.nPublic binaryRequest metadata request bodyFits cfg.initialLink full H H' agree answer
  exact ⟨congrArg (fun proof => (⟨request,proof⟩ : Output)) normalized.1,normalized.2⟩

include agree bodyFits in
theorem complete_eq (HM : Bytes → Digest) (indices : Fin 84 ↪ Fin 2443) (nonces : Fin 2443 → MerkleNonce)
    (tape : CompleteBackend.Masks binaryNodes primeNodes binary.cells (CellLayout.Prime.cells prime.remaining prime.pads))
    (frontend : Body) (answer : Digest × C) :
    CompletionEq binary repr shape setup
      (CompleteCanonicalVerifier.complete binary prime binaryNodes primeNodes repr shape setup cfg binaryCount primeCount metadata draw request HM indices nonces tape frontend H answer)
      (CompleteCanonicalVerifier.complete binary prime binaryNodes primeNodes repr shape setup cfg binaryCount primeCount metadata draw request HM indices nonces tape frontend H' answer) := by
  let early := CompleteCanonicalVerifier.committedFrontend binary prime binaryNodes primeNodes repr shape setup cfg HM nonces tape frontend
  have statement := statement_eq binary prime binaryNodes primeNodes repr shape setup cfg binaryCount primeCount metadata bodyFits request H H' agree early
  have coins := batchingCoin_eq binary prime binaryNodes primeNodes repr shape setup cfg binaryCount metadata bodyFits request H H' agree draw early
  unfold CompleteCanonicalVerifier.complete
  dsimp only
  rw [statement]
  cases parsed : CompleteCanonicalVerifier.statementAt binary prime binaryNodes primeNodes repr shape setup cfg binaryCount primeCount metadata request early H' with
  | none =>
    simp only [Option.bind_eq_bind,Option.bind_none]
    exact .none _
  | some data =>
    simp only [Option.bind_eq_bind,Option.bind_some,Option.pure_def]
    rw [coins]
    have same := simulate_eq binary prime binaryNodes primeNodes repr shape setup cfg binaryCount metadata bodyFits request H H' agree HM indices nonces tape data
      (CompleteCanonicalVerifier.batchingCoin binary prime binaryNodes primeNodes repr shape setup cfg binaryCount metadata draw request early H') frontend answer
    exact .some same.1 (fun point canonical => same.2 point canonical)

end LfzkV2.Current.ZeroKnowledge.OracleCompleteNormalization
