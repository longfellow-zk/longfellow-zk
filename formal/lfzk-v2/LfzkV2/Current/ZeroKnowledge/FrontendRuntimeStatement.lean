import LfzkV2.Current.ZeroKnowledge.FrontendParserApplication
import LfzkV2.Current.ZeroKnowledge.FrontendStatementShape
import LfzkV2.Current.ZeroKnowledge.BackendStatement
import LfzkV2.Current.CanonicalRuntime

/-! Nonfailure of the actual mdoc statement reader. The configuration is
constructed here with the runtime's fixed field projections, advice decoder,
generator and row counts. None of these callbacks is an assumed equality
with an independently supplied verifier. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
namespace LfzkV2.Current.ZeroKnowledge.Frontend.RuntimeStatement
open SumcheckV2 ApplicationSetup ConcreteSetup
open scoped Classical
variable {B : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
local notation "P" => Adapter.Mdoc.P
variable (binary : BinaryCircuit B) (prime : PrimePublic P 768)
variable (primePlan : FrontendSchedule.Plan P prime.circuit) (binaryNodes : Fin 2792 ↪ B)
variable (scalars : MdocRuntime.Scalars B)
variable (inputFits : 768+prime.remaining+prime.pads < 2^64) (privateFits : binary.nPrivate < 2^64)

omit [Fintype B] [DecidableEq B] in
theorem degreeFits : binary.description.degree < 2^64 := by change (128 : ℕ) < 2^64; norm_num

variable (setup : FingerprintPrefix.Setup)

def configuration := MdocRuntime.configuration binary.description prime binary.plan primePlan binaryNodes scalars
  inputFits privateFits (degreeFits binary) setup (MdocRuntime.field_card binary.basis) (MdocRuntime.polynomialX binary.basis)

local notation "G" => MdocRuntime.geometry binary.description prime binary.plan primePlan
local notation "Shape" => MdocRuntime.shape binary.description prime binary.plan primePlan inputFits privateFits (degreeFits binary)
local notation "Repr" => MdocRuntime.representations scalars
local notation "Cfg" => configuration binary prime primePlan binaryNodes scalars inputFits privateFits setup
local notation "First" => ConcreteSetup.backend binaryNodes binary.description.cells
local notation "Second" => ConcreteSetup.backend ConcreteSetup.primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)

omit [Fintype B] [DecidableEq B] in
theorem binary_count : (MdocRuntime.shape binary.description prime binary.plan primePlan inputFits privateFits (degreeFits binary)).binaryPublic =
    binary.description.nPublic := rfl
omit [Fintype B] [DecidableEq B] in
theorem prime_count : (MdocRuntime.shape binary.description prime binary.plan primePlan inputFits privateFits (degreeFits binary)).primePublic =
    prime.nPublic := rfl

variable (metadata : CanonicalRequest.Metadata (Advice := MdocAdvice.Value)
  (C := MdocRuntime.Answer binary.description prime binary.plan primePlan binaryNodes)
  (MdocRuntime.shape binary.description prime binary.plan primePlan inputFits privateFits (degreeFits binary)) binary.nPublic)
variable (request : CanonicalRequest.Request
  (MdocRuntime.shape binary.description prime binary.plan primePlan inputFits privateFits (degreeFits binary)) binary.nPublic)
variable (proof : CanonicalRequest.Output (g := MdocRuntime.geometry binary.description prime binary.plan primePlan)
  (fields := MdocRuntime.fields B) (Advice := MdocAdvice.Value))
variable (H : QueryRuntime.Runtime.Point (MdocRuntime.representations scalars)
  (MdocRuntime.shape binary.description prime binary.plan primePlan inputFits privateFits (degreeFits binary)) setup binary.nPublic →
  Digest × MdocRuntime.Answer binary.description prime binary.plan primePlan binaryNodes)

local notation "Public" => CanonicalRuntime.wirePublic binary.description prime First Second Repr Shape setup Cfg
local notation "BinaryRequest" => CanonicalRuntime.binaryRequest binary.description prime First Second Repr Shape setup Cfg
  (binary_count binary prime primePlan inputFits privateFits)
local notation "PrimeCount" => prime_count binary prime primePlan inputFits privateFits
local notation "E" => CanonicalRequest.encoding Repr Shape setup binary.nPublic BinaryRequest metadata request
local notation "point" => TranscriptV2.Chain.point (Replay.Encoding.chain E (RuntimeVerifier.Public.initialLink Cfg))
  proof H (Fin.val (Geometry.batchingIndex G))
local notation "past" => Input.priorAnswers
  (TranscriptV2.Chain.point (Replay.Encoding.chain E (RuntimeVerifier.Public.initialLink Cfg))
    proof H (Fin.val (Geometry.batchingIndex G))) H

theorem success
    (primitive : Current.Adapter.Mdoc.generatorCheck (MdocRuntime.polynomialX binary.basis) = true)
    (trace : ∀ i, DualPacking.ArtinSchreier.traceF (F := B) (ZMod 2) (proof.body.packing.1 i) = 0) :
    ∃ result, RuntimeAdaptive.statementAt binary.description prime First Second Public
      (CanonicalRequest.hashPublic binary.nPublic)
      (CanonicalRuntime.decodePrimePublic binary.description prime First Second Repr Shape setup Cfg PrimeCount)
      point past = some result := by
  let samples := MdocRuntime.samples binary.description prime binary.plan primePlan binaryNodes
  let inputs := CanonicalRuntime.primeInputs binary.description prime First Second Repr Shape setup Cfg PrimeCount request
  have decoded := ParserApplication.decode_requested binary prime primePlan Repr Shape setup binary.nPublic BinaryRequest
    metadata request (RuntimeVerifier.Public.initialLink Cfg) proof H samples request.publicBits inputs primitive trace
  obtain ⟨system,hdecoded⟩ := decoded
  have primeStart : (G).primeStart ≤ (G).batchingIndex.val := by
    exact le_trans (Nat.le_add_right _ _) (ParserApplication.prime_window binary prime primePlan)
  have hbits := CanonicalRuntime.hashPublic_replay binary.description prime First Second Repr Shape setup Cfg
    (binary_count binary prime primePlan inputFits privateFits) metadata request (RuntimeVerifier.Public.initialLink Cfg)
    proof H (G).batchingIndex.val
  have hinputs := CanonicalRuntime.primePublic_replay binary.description prime First Second Repr Shape setup Cfg
    (binary_count binary prime primePlan inputFits privateFits) PrimeCount metadata request (RuntimeVerifier.Public.initialLink Cfg)
    proof H (G).batchingIndex.val (G).batchingIndex.isLt.le primeStart
  have application : RuntimeAdaptive.application binary.description prime First Second Public
      (CanonicalRequest.hashPublic binary.nPublic)
      (CanonicalRuntime.decodePrimePublic binary.description prime First Second Repr Shape setup Cfg PrimeCount)
      point past = some system := by
    rw [RequestedApplication.application_eq _ _ _ _ _ _ _ point past request.publicBits inputs hbits hinputs]
    exact hdecoded
  -- Fix the structural reader and its field maps before using the parse equation.
  have readerSpec := ApplicationPrefix.decodeChecked_spec
    (RuntimeAdaptive.binaryWithBits binary.description request.publicBits) (RuntimeAdaptive.primeWithInputs prime inputs)
    (MdocRuntime.field_card binary.basis) (MdocRuntime.polynomialX binary.basis) ParserApplication.quotient_bound
    (ParserApplication.packing_degree binary prime primePlan) id id samples.binary samples.binaryNonzero samples.prime samples.primeNonzero
    samples.conversion MdocAdvice.decode samples.fallback point past system
  obtain ⟨native,data,_,_,checked⟩ := readerSpec hdecoded
  let layout := BackendStatement.addresses (cellsB := binary.description.cells) (remaining := prime.remaining) (padsN := prime.pads)
    binaryNodes ConcreteSetup.primeNodes
  let fingerprint := (H (((E).chain (RuntimeVerifier.Public.initialLink Cfg)).point proof H 0)).2
  have coefficients := Parser.strictAnswer Repr Shape setup binary.nPublic BinaryRequest metadata request
    (RuntimeVerifier.Public.initialLink Cfg) proof H (G).batchingIndex.val (G).batchingIndex.isLt.le 0 (by
      have pos := (ParserApplication.positions binary prime primePlan).1
      simp only [ApplicationPrefix.rowBatchingIndex,Geometry.primeStart] at pos
      omega)
  have targets := Parser.read_fingerprints Repr Shape setup binary.nPublic BinaryRequest metadata request
    (RuntimeVerifier.Public.initialLink Cfg) proof H (G).batchingIndex.val (G).batchingIndex.isLt.le primeStart
  obtain ⟨statement,compiled⟩ := StatementShape.compile_success
    (RuntimeAdaptive.binaryWithBits binary.description request.publicBits) (RuntimeAdaptive.primeWithInputs prime inputs)
    native (MdocRuntime.field_card binary.basis) (MdocRuntime.polynomialX binary.basis) ParserApplication.quotient_bound data
    binary.plan (G) rfl (ParserApplication.packing_degree binary prime primePlan) First Second layout
    ((Cfg).fingerprintBinary fingerprint) ((Cfg).fingerprintPrime fingerprint) proof.body.fingerprints.1 proof.body.fingerprints.2
    system checked
  unfold RuntimeAdaptive.statementAt
  erw [application,BackendStatement.addresses_checked binaryNodes ConcreteSetup.primeNodes,coefficients,targets]
  refine ⟨⟨system,statement⟩,?_⟩
  simp only [Option.bind_eq_bind,Option.bind_some]
  erw [compiled]
  rfl

end LfzkV2.Current.ZeroKnowledge.Frontend.RuntimeStatement
