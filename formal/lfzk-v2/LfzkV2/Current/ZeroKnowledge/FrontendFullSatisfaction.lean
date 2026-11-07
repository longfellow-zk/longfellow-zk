import LfzkV2.Current.ZeroKnowledge.FrontendSimulationSystem
import LfzkV2.Current.ZeroKnowledge.FrontendHonestRunRows

/-! Reindexing the honest frontend coins preserves the complete public
statement, and that statement is true on the original physical cells.
Only ordinary signature/hash truth is supplied. Adapter correctness, input
packing, fingerprint equations, canonical parsing and the backend compiler
are all accounted for by the concrete runtime lemmas. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.Frontend.FullSatisfaction
open SumcheckV2 ApplicationSetup Application ConcreteSetup
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
variable {B C : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
local notation "P" => Adapter.Mdoc.P
variable (binary : BinaryCircuit B) (prime : PrimePublic P 768)
variable (primePlan : FrontendSchedule.Plan P prime.circuit)
variable (samples : ConcreteMetadata.Samples B C)
variable (shape : WireBlocks.Shape (CompleteSimulation.geometry binary prime primePlan) (MdocRuntime.fields B))
variable (repr : ProofBodyCodec.Representations (MdocRuntime.fields B) MdocAdvice.Value)
variable (setup : FingerprintPrefix.Setup) (defaultAdvice : MdocAdvice.Value) (publicCount : ℕ)
variable (binaryRequest : (Fin publicCount → Bool) → Fin shape.binaryPublic → B)
variable (metadata : CanonicalRequest.Metadata (Advice := MdocAdvice.Value) (C := C) shape publicCount)
variable (request : CanonicalRequest.Request shape publicCount) (root : Digest)
variable (H : CompleteSimulation.Point binary prime primePlan
  (Key := FingerprintPrefix.Key publicCount) (Base := CanonicalRequest.Base repr shape setup publicCount) → Digest × C)
variable (initial : Digest)
variable (original : Fin binary.nPrivate → Bool) (remaining : Fin prime.remaining → P)
variable (pivotOne : binary.basis 0 = 1)
local notation "G" => CompleteSimulation.geometry binary prime primePlan
local notation "W" => CompleteWire.canonicalBase shape defaultAdvice repr setup publicCount binaryRequest metadata request root
variable (hashAll : ∀ responses coin converted,
  FullCoupling.hashChecks binary prime primePlan samples
    (CompleteWire.canonicalBase shape defaultAdvice repr setup publicCount binaryRequest metadata request root) H
    (FingerprintPrefix.context request root) original responses coin converted)
variable (selection : C → WitnessSelection.Coins B binary.description.Original × WitnessSelection.Coins P prime.Original)
variable (tape : CompleteHonest.Tape binary prime) (masks : CompleteHonest.Masks (B := B))
local notation "coins" => FullCoupling.coupling binary prime primePlan samples W H (FingerprintPrefix.context request root)
  original remaining pivotOne hashAll selection (tape,masks)
local notation "result" => CompleteSimulation.simulate binary prime primePlan samples W H
  (FingerprintPrefix.context request root) coins
local notation "proof" => (Current.Proof.mk (CompleteFrontendBody.body binary prime primePlan root result) (fun _ => 0) :
  CanonicalRequest.Output (g := G) (fields := MdocRuntime.fields B) (Advice := MdocAdvice.Value))
local notation "point" => TranscriptV2.Chain.point
  (Replay.Encoding.chain (CanonicalRequest.encoding repr shape setup publicCount binaryRequest metadata request) initial)
  proof H (Fin.val (Geometry.batchingIndex G))

theorem compiled_satisfies (system)
    (decoded : ApplicationPrefix.decodeChecked binary.description prime (MdocRuntime.field_card binary.basis)
      (MdocRuntime.polynomialX binary.basis) ParserApplication.quotient_bound (ParserApplication.packing_degree binary prime primePlan)
      id id samples.binary samples.binaryNonzero samples.prime samples.primeNonzero samples.conversion MdocAdvice.decode
      samples.fallback point ((point).priorAnswers H) = some system)
    (binaryNodes : Fin 2792 ↪ B)
    (statement : StatementData system ((backend binaryNodes binary.description.cells).indexed ((G).affineRows .binary))
      ((backend ConcreteSetup.primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)).indexed ((G).affineRows .prime)))
    (compiled : StatementCompiler.compile (backend binaryNodes binary.description.cells)
      (backend ConcreteSetup.primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) system
      (BackendStatement.addresses binaryNodes ConcreteSetup.primeNodes) ((G).affineRows .binary) ((G).affineRows .prime)
      (selection (AnswerTape.pointLookup H samples.fallback point 0)).1
      (selection (AnswerTape.pointLookup H samples.fallback point 0)).2 (coins).fingerprints.1 (coins).fingerprints.2 = some statement)
    (signature : prime.circuit.Satisfies (CompleteHonest.primeInputs binary prime original remaining))
    (honestHash :
      let first := CompleteTranscript.step W H (CompleteTranscript.initial (FingerprintPrefix.context request root) samples.fallback)
      let raw := CompleteHonest.run binary prime primePlan samples W H selection (FingerprintPrefix.context request root)
        original remaining tape masks
      HonestAdapter.hashChecks binary prime primePlan samples W H
        (HonestRunRows.native binary prime primePlan samples W H first.2 raw) original tape) :
    statement.statement.1.Satisfies (Backend.logical (BackendCells.tableau
      (CompleteHonest.binaryCells binary prime original tape ((finTwoArrowEquiv B).symm masks.1)))) ∧
      statement.statement.2.Satisfies (Backend.logical (BackendCells.tableau
        (CompleteHonest.primeCells binary prime remaining tape ((finTwoArrowEquiv P).symm masks.2)))) := by
  have truth := HonestRunRows.run_rows binary prime primePlan samples W H selection (FingerprintPrefix.context request root)
    original remaining tape masks signature honestHash
  have view := FullCoupling.coupling_view binary prime primePlan samples W H (FingerprintPrefix.context request root)
    original remaining pivotOne hashAll selection tape masks
  generalize coinsEq : coins = publicCoins at *
  clear coinsEq
  dsimp only at truth
  rw [view] at truth
  apply SimulationSystem.compiled_satisfies binary prime primePlan samples shape repr setup defaultAdvice publicCount binaryRequest
    metadata request root H initial publicCoins system decoded binaryNodes selection statement compiled
    (CompleteHonest.binaryCells binary prime original tape ((finTwoArrowEquiv B).symm masks.1))
    (CompleteHonest.primeCells binary prime remaining tape ((finTwoArrowEquiv P).symm masks.2))
  · exact truth.2.1
  · exact truth.2.2

theorem statement_exists (binaryNodes : Fin 2792 ↪ B)
    (primitive : Current.Adapter.Mdoc.generatorCheck (MdocRuntime.polynomialX binary.basis) = true)
    (signature : prime.circuit.Satisfies (CompleteHonest.primeInputs binary prime original remaining))
    (honestHash :
      let first := CompleteTranscript.step W H (CompleteTranscript.initial (FingerprintPrefix.context request root) samples.fallback)
      let raw := CompleteHonest.run binary prime primePlan samples W H selection (FingerprintPrefix.context request root)
        original remaining tape masks
      HonestAdapter.hashChecks binary prime primePlan samples W H
        (HonestRunRows.native binary prime primePlan samples W H first.2 raw) original tape) :
    ∃ (system : RuntimeVerifier.System binary.description prime (C := C))
      (statement : StatementData system ((backend binaryNodes binary.description.cells).indexed ((G).affineRows .binary))
        ((backend ConcreteSetup.primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)).indexed ((G).affineRows .prime))),
      ApplicationPrefix.decodeChecked binary.description prime (MdocRuntime.field_card binary.basis)
        (MdocRuntime.polynomialX binary.basis) ParserApplication.quotient_bound (ParserApplication.packing_degree binary prime primePlan)
        id id samples.binary samples.binaryNonzero samples.prime samples.primeNonzero samples.conversion MdocAdvice.decode
        samples.fallback point ((point).priorAnswers H) = some system ∧
      StatementCompiler.compile (backend binaryNodes binary.description.cells)
        (backend ConcreteSetup.primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) system
        (BackendStatement.addresses binaryNodes ConcreteSetup.primeNodes) ((G).affineRows .binary) ((G).affineRows .prime)
        (selection (AnswerTape.pointLookup H samples.fallback point 0)).1
        (selection (AnswerTape.pointLookup H samples.fallback point 0)).2 (coins).fingerprints.1 (coins).fingerprints.2 = some statement ∧
      statement.statement.1.Satisfies (Backend.logical (BackendCells.tableau
        (CompleteHonest.binaryCells binary prime original tape ((finTwoArrowEquiv B).symm masks.1)))) ∧
      statement.statement.2.Satisfies (Backend.logical (BackendCells.tableau
        (CompleteHonest.primeCells binary prime remaining tape ((finTwoArrowEquiv P).symm masks.2)))) := by
  have trace : ∀ i, DualPacking.ArtinSchreier.traceF (F := B) (ZMod 2) ((proof).body.packing.1 i) = 0 := by
    intro i
    have zero := LinearMap.mem_ker.mp ((result).packing.1 i).property
    change algebraMap (ZMod 2) B (Algebra.trace (ZMod 2) B (((result).packing.1 i).val)) = 0
    rw [zero,map_zero]
  obtain ⟨system,decoded⟩ := ParserApplication.decode_success binary prime primePlan repr shape setup publicCount binaryRequest
    metadata request initial proof H samples primitive trace
  obtain ⟨primeData,data,_,_,checked⟩ := ApplicationPrefix.decodeChecked_spec binary.description prime
    (MdocRuntime.field_card binary.basis) (MdocRuntime.polynomialX binary.basis) ParserApplication.quotient_bound
    (ParserApplication.packing_degree binary prime primePlan) id id samples.binary samples.binaryNonzero samples.prime
    samples.primeNonzero samples.conversion MdocAdvice.decode samples.fallback point ((point).priorAnswers H) system decoded
  obtain ⟨statement,compiled⟩ := StatementShape.compile_success binary.description prime primeData (MdocRuntime.field_card binary.basis)
    (MdocRuntime.polynomialX binary.basis) ParserApplication.quotient_bound data binary.plan (G) rfl
    (ParserApplication.packing_degree binary prime primePlan) (backend binaryNodes binary.description.cells)
    (backend ConcreteSetup.primeNodes (CellLayout.Prime.cells prime.remaining prime.pads))
    (BackendStatement.addresses binaryNodes ConcreteSetup.primeNodes)
    (selection (AnswerTape.pointLookup H samples.fallback point 0)).1
    (selection (AnswerTape.pointLookup H samples.fallback point 0)).2 (coins).fingerprints.1 (coins).fingerprints.2 system checked
  exact ⟨system,statement,decoded,compiled,
    compiled_satisfies binary prime primePlan samples shape repr setup defaultAdvice publicCount binaryRequest metadata request root H
      initial original remaining pivotOne hashAll selection tape masks system decoded binaryNodes statement compiled signature honestHash⟩

end LfzkV2.Current.ZeroKnowledge.Frontend.FullSatisfaction
