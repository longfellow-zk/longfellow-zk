import LfzkV2.Current.ZeroKnowledge.FrontendSimulationParsed
import LfzkV2.Current.ZeroKnowledge.FrontendStatementShape
import LfzkV2.Current.ZeroKnowledge.BackendStatement

/-! Recover the complete canonical application statement from the public
frontend simulation. The parser, challenge coordinates, fingerprint query
and physical selector layouts all follow from the current runtime. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.Frontend.SimulationSystem
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
variable (initial : Digest) (coins : CompleteSimulation.Coins binary prime)
local notation "G" => CompleteSimulation.geometry binary prime primePlan
local notation "W" => CompleteWire.canonicalBase shape defaultAdvice repr setup publicCount binaryRequest metadata request root
local notation "selected" => CompleteSimulation.selectedState binary prime primePlan samples W H
  (FingerprintPrefix.context request root) coins.fingerprints
local notation "result" => CompleteSimulation.simulate binary prime primePlan samples W H
  (FingerprintPrefix.context request root) coins
local notation "native" => CompleteSimulation.primePrefix binary prime primePlan samples W H selected
  (simulateCircuit prime.circuit coins.prime)
local notation "converted" => CompleteSimulation.conversionPrefix binary prime primePlan samples W H native coins.mu
local notation "proof" => (Current.Proof.mk (CompleteFrontendBody.body binary prime primePlan root result) (fun _ => 0) :
  CanonicalRequest.Output (g := G) (fields := MdocRuntime.fields B) (Advice := MdocAdvice.Value))
local notation "point" => TranscriptV2.Chain.point
  (Replay.Encoding.chain (CanonicalRequest.encoding repr shape setup publicCount binaryRequest metadata request) initial)
  proof H (Fin.val (Geometry.batchingIndex G))

omit [DecidableEq B] in
theorem initial_answer :
    (CompleteTranscript.step W H (CompleteTranscript.initial (FingerprintPrefix.context request root) samples.fallback)).1 =
      AnswerTape.pointLookup H samples.fallback point 0 := by
  let first := CompleteTranscript.step W H (CompleteTranscript.initial (FingerprintPrefix.context request root) samples.fallback)
  have inside : 0 < (G).roles.length := by rw [SimulationWrites.capacity binary prime primePlan]; omega
  have through : AnswerTape.Extends samples.fallback first.2 (result).state :=
    (AnswerTape.bind_extends samples.fallback first.2 _).trans
      ((AnswerTape.readSetup_extends W H .prime (Equiv.refl P) samples.prime samples.primeNonzero samples.fallback
        primePlan prime.setup.plan (simulateCircuit prime.circuit coins.prime) selected false).trans
        (SimulationAnswers.prime_future binary prime primePlan samples W H (FingerprintPrefix.context request root) coins))
  have answer := AnswerTape.step_answer_into W H samples.fallback
    (CompleteTranscript.initial (FingerprintPrefix.context request root) samples.fallback) (result).state inside through
  rw [CanonicalSimulation.batching_tape binary prime primePlan samples shape repr setup defaultAdvice publicCount binaryRequest
    metadata request root H initial coins] at answer
  exact answer

omit [DecidableEq B] in
theorem binary_handoff_values (primeData : PrimeData prime C)
    (data : BinaryData binary.description primeData (MdocRuntime.generator binary.basis))
    (parsed : ApplicationPrefix.readBinary binary.description primeData (MdocRuntime.generator binary.basis)
      (ParserApplication.packing_degree binary prime primePlan) id id samples.binary samples.binaryNonzero
      samples.primeNonzero samples.conversion MdocAdvice.decode samples.fallback point ((point).priorAnswers H) = some data) :
    data.eta = (native).eta.val ∧ data.mu = coins.mu := by
  have spec := ApplicationPrefix.readBinary_spec (g := G) (fields := MdocRuntime.fields B) binary.description primeData (MdocRuntime.generator binary.basis)
    (ParserApplication.packing_degree binary prime primePlan) id id samples.binary samples.binaryNonzero
    samples.primeNonzero samples.conversion MdocAdvice.decode samples.fallback point ((point).priorAnswers H) data parsed
  simp only [Option.map_id] at spec
  obtain ⟨scale,hscale,eta⟩ := spec.2.1
  have scaleValue := SimulationParsed.strictAnswer_value H samples.fallback point _ scale hscale
  have values := SimulationParsed.challenge_values binary prime primePlan samples shape repr setup defaultAdvice publicCount
    binaryRequest metadata request root H initial coins
  have mu := Parser.read_mu repr shape setup publicCount binaryRequest metadata request initial proof H
    (G).batchingIndex.val (G).batchingIndex.isLt.le (ParserApplication.positions binary prime primePlan).2.2.1.le
  constructor
  · rw [eta,scaleValue]
    exact congrArg Subtype.val values.1.symm
  · exact Option.some.inj (spec.2.2.2.1.symm.trans mu)

theorem decoded_rows (system)
    (decoded : ApplicationPrefix.decodeChecked binary.description prime (MdocRuntime.field_card binary.basis)
      (MdocRuntime.polynomialX binary.basis) ParserApplication.quotient_bound (ParserApplication.packing_degree binary prime primePlan)
      id id samples.binary samples.binaryNonzero samples.prime samples.primeNonzero samples.conversion MdocAdvice.decode
      samples.fallback point ((point).priorAnswers H) = some system) :
    system.binary.rows = HonestRows.binaryRows binary prime primePlan samples W H native converted coins.advice
      (simulateCircuit binary.description.template coins.binary)
      (fun i => ((result).packing.1 i).val) (result).delta (result).packing.2 ∧
      system.primeRows = [(native).claim.row (native).eta.val coins.mu] ∧
      system.binaryLayout = CellLayout.selected binary.description.cells ∧
      system.primeLayout = CellLayout.Prime.layout prime.remaining prime.pads := by
  obtain ⟨primeData,data,parsedPrime,parsedBinary,checked⟩ := ApplicationPrefix.decodeChecked_spec (g := G) (fields := MdocRuntime.fields B) binary.description prime
    (MdocRuntime.field_card binary.basis) (MdocRuntime.polynomialX binary.basis) ParserApplication.quotient_bound
    (ParserApplication.packing_degree binary prime primePlan) id id samples.binary samples.binaryNonzero samples.prime
    samples.primeNonzero samples.conversion MdocAdvice.decode samples.fallback point ((point).priorAnswers H) system decoded
  have rowFields := StatementShape.decoded_rows binary.description prime primeData (MdocRuntime.field_card binary.basis)
    (MdocRuntime.polynomialX binary.basis) ParserApplication.quotient_bound data system checked
  have binaryRows := SimulationParsed.binary_frontend_rows binary prime primePlan samples shape repr setup defaultAdvice publicCount
    binaryRequest metadata request root H initial coins primeData parsedPrime data parsedBinary
  have claim := SimulationParsed.prime_claim binary prime primePlan samples shape repr setup defaultAdvice publicCount
    binaryRequest metadata request root H initial coins primeData parsedPrime
  have handoff := binary_handoff_values binary prime primePlan samples shape repr setup defaultAdvice publicCount
    binaryRequest metadata request root H initial coins primeData data parsedBinary
  refine ⟨rowFields.1.trans binaryRows,?_,rowFields.2.2.1,rowFields.2.2.2⟩
  rw [rowFields.2.1,claim,handoff.1,handoff.2]

theorem compiled_satisfies (system)
    (decoded : ApplicationPrefix.decodeChecked binary.description prime (MdocRuntime.field_card binary.basis)
      (MdocRuntime.polynomialX binary.basis) ParserApplication.quotient_bound (ParserApplication.packing_degree binary prime primePlan)
      id id samples.binary samples.binaryNonzero samples.prime samples.primeNonzero samples.conversion MdocAdvice.decode
      samples.fallback point ((point).priorAnswers H) = some system)
    (binaryNodes : Fin 2792 ↪ B)
    (selection : C → WitnessSelection.Coins B binary.description.Original × WitnessSelection.Coins P prime.Original)
    (statement : StatementData system ((backend binaryNodes binary.description.cells).indexed ((G).affineRows .binary))
      ((backend ConcreteSetup.primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)).indexed ((G).affineRows .prime)))
    (compiled : StatementCompiler.compile (backend binaryNodes binary.description.cells)
      (backend ConcreteSetup.primeNodes (CellLayout.Prime.cells prime.remaining prime.pads)) system
      (BackendStatement.addresses binaryNodes ConcreteSetup.primeNodes) ((G).affineRows .binary) ((G).affineRows .prime)
      (selection (AnswerTape.pointLookup H samples.fallback point 0)).1
      (selection (AnswerTape.pointLookup H samples.fallback point 0)).2 coins.fingerprints.1 coins.fingerprints.2 = some statement)
    (flatB : Fin (binary.description.cells+2) → B)
    (flatP : Fin (CellLayout.Prime.cells prime.remaining prime.pads+2) → P)
    (binaryRows : RowsHold
      (HonestRows.binaryRows binary prime primePlan samples W H native converted coins.advice
        (simulateCircuit binary.description.template coins.binary)
        (fun i => ((result).packing.1 i).val) (result).delta (result).packing.2 ++
        FingerprintRows.rows (fun i => CellLayout.selected binary.description.cells (.inl i))
          (fun i => CellLayout.selected binary.description.cells (.inr i))
          (selection (CompleteTranscript.step W H
            (CompleteTranscript.initial (FingerprintPrefix.context request root) samples.fallback)).1).1 coins.fingerprints.1) flatB)
    (primeRows : RowsHold ([(native).claim.row (native).eta.val coins.mu] ++
      FingerprintRows.rows (fun i => CellLayout.Prime.layout prime.remaining prime.pads (.inl i))
        (fun i => CellLayout.Prime.layout prime.remaining prime.pads (.inr i))
        (selection (CompleteTranscript.step W H
          (CompleteTranscript.initial (FingerprintPrefix.context request root) samples.fallback)).1).2 coins.fingerprints.2)
      (BackendCells.primeRead flatP)) :
    statement.statement.1.Satisfies (Backend.logical (BackendCells.tableau flatB)) ∧
      statement.statement.2.Satisfies (Backend.logical (BackendCells.tableau flatP)) := by
  have rowFields := decoded_rows binary prime primePlan samples shape repr setup defaultAdvice publicCount binaryRequest metadata
    request root H initial coins system decoded
  have first := initial_answer binary prime primePlan samples shape repr setup defaultAdvice publicCount binaryRequest metadata
    request root H initial coins
  apply BackendStatement.compile_satisfies binaryNodes ConcreteSetup.primeNodes system ((G).affineRows .binary) ((G).affineRows .prime)
    (selection (AnswerTape.pointLookup H samples.fallback point 0)).1
    (selection (AnswerTape.pointLookup H samples.fallback point 0)).2 coins.fingerprints.1 coins.fingerprints.2
    statement compiled flatB flatP
  · rw [rowFields.1,rowFields.2.2.1,← first]
    exact binaryRows
  · rw [rowFields.2.1,rowFields.2.2.2,← first]
    exact primeRows

end LfzkV2.Current.ZeroKnowledge.Frontend.SimulationSystem
