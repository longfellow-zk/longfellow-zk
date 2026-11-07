import LfzkV2.Current.ZeroKnowledge.FrontendSimulationMessages
import LfzkV2.Current.ZeroKnowledge.FrontendPayloadTransport
import LfzkV2.Current.ZeroKnowledge.FrontendParserApplication
import LfzkV2.Current.ZeroKnowledge.FrontendSimulationScalarAnswers

/-! The application parser recovers the simulator's actual payloads and
compiled frontend rows. These are conclusions about the ordinary canonical
reader, rather than equalities supplied to a simulator correctness premise. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.Frontend.SimulationParsed
open SumcheckV2 ApplicationSetup ConcreteSetup
open scoped Classical
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000

theorem strictAnswer_value {g : Geometry} {fields : Fields} {Advice Authentication Key Base C : Type}
    (H : CompleteTranscript.Point (g := g) (fields := fields) (Advice := Advice)
      (Authentication := Authentication) (Key := Key) (Base := Base) → Digest × C)
    (fallback : C)
    (point : CompleteTranscript.Point (g := g) (fields := fields) (Advice := Advice)
      (Authentication := Authentication) (Key := Key) (Base := Base))
    (index : ℕ) (value : C)
    (read : ApplicationPrefix.strictAnswer point (point.priorAnswers H) index = some value) :
    value = AnswerTape.pointLookup H fallback point index := by
  unfold ApplicationPrefix.strictAnswer at read
  split at read
  · rename_i inside
    simp only [AnswerTape.pointLookup,dif_pos inside]
    exact (Option.some.inj read).symm
  · contradiction

theorem strictAnswer_lookup {g : Geometry} {fields : Fields} {Advice Authentication Key Base C : Type}
    (H : CompleteTranscript.Point (g := g) (fields := fields) (Advice := Advice)
      (Authentication := Authentication) (Key := Key) (Base := Base) → Digest × C)
    (fallback : C)
    (point : CompleteTranscript.Point (g := g) (fields := fields) (Advice := Advice)
      (Authentication := Authentication) (Key := Key) (Base := Base))
    (index : ℕ) (inside : index < point.rank) :
    ApplicationPrefix.strictAnswer point (point.priorAnswers H) index =
      some (AnswerTape.pointLookup H fallback point index) := by
  simp only [ApplicationPrefix.strictAnswer,AnswerTape.pointLookup,dif_pos inside]

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
theorem prime_payload : Parser.payload proof .prime primePlan rfl = simulateCircuit prime.circuit coins.prime := by
  change (CompleteShape.bodyEquiv primePlan).symm
    (CompleteShape.bodyEquiv primePlan (simulateCircuit prime.circuit coins.prime)) = _
  exact (CompleteShape.bodyEquiv primePlan).symm_apply_apply _

omit [DecidableEq B] in
theorem binary_payload :
    let same := CompleteSimulation.generatedSame binary prime primePlan native converted coins.advice
    Parser.payload proof .binary (same.plan binary.plan) (same.frontend binary.plan).symm =
      CompleteShape.payloadEquiv same (simulateCircuit binary.description.template coins.binary) := by
  exact PayloadTransport.same_body binary.plan _ _

omit [DecidableEq B] in
theorem prime_frontend_rows (data : PrimeData prime C)
    (parsed : ApplicationPrefix.readPrime prime id samples.prime samples.primeNonzero samples.fallback point
      ((point).priorAnswers H) = some data) :
    data.frontend.rows = CompleteSimulation.primeRows prime (messagesFromSetup prime.circuit
      (readSetup (CompleteTranscript.reader .prime (Equiv.refl P) samples.prime samples.primeNonzero W H)
        primePlan prime.setup.plan (simulateCircuit prime.circuit coins.prime) selected false).1
      (simulateCircuit prime.circuit coins.prime)) := by
  have spec := ApplicationPrefix.readPrime_spec prime id samples.prime samples.primeNonzero samples.fallback
    point ((point).priorAnswers H) data parsed
  have wire := Parser.messages repr shape setup publicCount binaryRequest metadata request initial proof H
    .prime primePlan rfl (G).batchingIndex.val (G).batchingIndex.isLt.le
    (ParserApplication.prime_window binary prime primePlan)
  dsimp only [Parser.start] at wire
  rw [prime_payload binary prime primePlan samples shape repr setup defaultAdvice publicCount binaryRequest metadata
    request root H coins] at wire
  have payload : data.payload = simulateCircuit prime.circuit coins.prime :=
    Option.some.inj (spec.2.1.symm.trans wire)
  have messages := SimulationMessages.prime_messages binary prime primePlan samples shape repr setup defaultAdvice
    publicCount binaryRequest metadata request root H initial coins
  unfold PrimeData.frontend
  rw [spec.2.2.1,spec.2.2.2.1,spec.2.2.2.2.1,payload]
  symm
  simpa only [CompleteSimulation.primeRows,Frontend.Prime.rows,FrontendVerifier.PrimeSetup.prepare,
    FrontendVerifier.constraints,PrimePublic.setup,CellLayout.Prime.rows] using
    congrArg (CompleteSimulation.primeRows prime) messages

omit [DecidableEq B] in
theorem prime_claim (data : PrimeData prime C)
    (parsed : ApplicationPrefix.readPrime prime id samples.prime samples.primeNonzero samples.fallback point
      ((point).priorAnswers H) = some data) : data.claim = (native).claim := by
  have spec := ApplicationPrefix.readPrime_spec prime id samples.prime samples.primeNonzero samples.fallback
    point ((point).priorAnswers H) data parsed
  obtain ⟨batching,hbatching,rho⟩ := spec.2.2.2.2.2
  have batch := strictAnswer_value H samples.fallback point _ batching hbatching
  have first := (SimulationWrites.selected_properties binary prime primePlan samples W H
    (FingerprintPrefix.context request root) coins.fingerprints).1
  have fits : (selected).rank.val+HonestTranscript.circuitFuel primePlan false+2 ≤ (G).roles.length := by
    rw [first,SimulationWrites.capacity binary prime primePlan]
    omega
  have index : (selected).rank.val+HonestTranscript.circuitFuel primePlan false = ApplicationPrefix.rowBatchingIndex (G) := by
    rw [first,HonestTranscript.circuitFuel_roles primePlan .prime]
    rfl
  have values := SimulationScalarAnswers.prime_values binary prime primePlan samples W H selected (result).state
    (simulateCircuit prime.circuit coins.prime) fits
    (SimulationAnswers.native_future binary prime primePlan samples W H (FingerprintPrefix.context request root) coins)
  rw [CanonicalSimulation.batching_tape binary prime primePlan samples shape repr setup defaultAdvice publicCount
    binaryRequest metadata request root H initial coins,index,← batch] at values
  unfold PrimeData.claim
  rw [rho]
  erw [prime_frontend_rows binary prime primePlan samples shape repr setup defaultAdvice publicCount binaryRequest
    metadata request root H initial coins data parsed]
  exact values.1.symm

omit [DecidableEq B] in
theorem challenge_values :
    (native).eta = samples.primeNonzero (AnswerTape.pointLookup H samples.fallback point
      (ApplicationPrefix.rescalingIndex (G))) ∧
    (converted).alpha = samples.conversion (AnswerTape.pointLookup H samples.fallback point
      (ApplicationPrefix.conversionIndex (G))) ∧
    (result).delta = (fun i => samples.binary (AnswerTape.pointLookup H samples.fallback point
      (ApplicationPrefix.packingIndex (G))) i.val) := by
  have first := (SimulationWrites.selected_properties binary prime primePlan samples W H
    (FingerprintPrefix.context request root) coins.fingerprints).1
  have fits : (selected).rank.val+HonestTranscript.circuitFuel primePlan false+2 ≤ (G).roles.length := by
    rw [first,SimulationWrites.capacity binary prime primePlan]
    omega
  have batchIndex : (selected).rank.val+HonestTranscript.circuitFuel primePlan false = ApplicationPrefix.rowBatchingIndex (G) := by
    rw [first,HonestTranscript.circuitFuel_roles primePlan .prime]
    rfl
  have tape := CanonicalSimulation.batching_tape binary prime primePlan samples shape repr setup defaultAdvice publicCount
    binaryRequest metadata request root H initial coins
  have ranks := SimulationMessages.stage_ranks binary prime primePlan samples shape repr setup defaultAdvice publicCount
    binaryRequest metadata request root H coins
  have primeValues := SimulationScalarAnswers.prime_values binary prime primePlan samples W H selected (result).state
    (simulateCircuit prime.circuit coins.prime) fits
    (SimulationAnswers.native_future binary prime primePlan samples W H (FingerprintPrefix.context request root) coins)
  rw [tape,batchIndex] at primeValues
  have inside : (native).state.rank.val < (G).roles.length := by
    rw [ranks.2.1]
    exact ((ParserApplication.positions binary prime primePlan).2.2.1).trans (G).batchingIndex.isLt
  have conversion := SimulationScalarAnswers.conversion_values binary prime primePlan samples W H native coins.mu
    (result).state inside
    (SimulationAnswers.converted_future binary prime primePlan samples W H (FingerprintPrefix.context request root) coins)
  rw [tape,ranks.2.1] at conversion
  have packing := SimulationScalarAnswers.packing_values binary prime primePlan samples W H (FingerprintPrefix.context request root) coins
  dsimp only at packing
  rw [tape,ranks.2.2.2] at packing
  exact ⟨primeValues.2,conversion,packing⟩

omit [DecidableEq B] in
theorem binary_frontend_rows (primeData : PrimeData prime C)
    (parsedPrime : ApplicationPrefix.readPrime prime id samples.prime samples.primeNonzero samples.fallback point
      ((point).priorAnswers H) = some primeData)
    (data : BinaryData binary.description primeData (MdocRuntime.generator binary.basis))
    (parsed : ApplicationPrefix.readBinary binary.description primeData (MdocRuntime.generator binary.basis)
      (ParserApplication.packing_degree binary prime primePlan) id id samples.binary samples.binaryNonzero
      samples.primeNonzero samples.conversion MdocAdvice.decode samples.fallback point ((point).priorAnswers H) = some data) :
    data.frontend.rows = HonestRows.binaryRows binary prime primePlan samples W H native converted coins.advice
      (simulateCircuit binary.description.template coins.binary)
      (fun i => ((result).packing.1 i).val) (result).delta (result).packing.2 := by
  have values := challenge_values binary prime primePlan samples shape repr setup defaultAdvice publicCount binaryRequest
    metadata request root H initial coins
  have hclaim := prime_claim binary prime primePlan samples shape repr setup defaultAdvice publicCount binaryRequest
    metadata request root H initial coins primeData parsedPrime
  have messages := SimulationMessages.binary_messages binary prime primePlan samples shape repr setup defaultAdvice
    publicCount binaryRequest metadata request root H initial coins
  have bpayload : (result).binaryPayload = simulateCircuit binary.description.template coins.binary := rfl
  have hmu : (result).mu = coins.mu := rfl
  have hadvice : (result).advice = coins.advice := rfl
  have cmu : (converted).mu = coins.mu := rfl
  -- Keep the already computed stages opaque while transporting their
  -- public fields through the parser. Their defining equalities are rfl.
  generalize hresult : result = view at *
  generalize hconverted : converted = cv at *
  generalize hnative : native = n at *
  clear hresult hconverted hnative
  rcases n with ⟨claim,eta,primeState⟩
  rcases cv with ⟨mu,alpha,conversionState⟩
  dsimp only at hclaim cmu
  subst claim
  subst mu
  let n : CompleteSimulation.PrimePrefix binary prime primePlan
      (FingerprintPrefix.Key publicCount) (CanonicalRequest.Base repr shape setup publicCount) C :=
    ⟨primeData.claim,eta,primeState⟩
  let cv : CompleteSimulation.ConversionPrefix binary prime primePlan
      (FingerprintPrefix.Key publicCount) (CanonicalRequest.Base repr shape setup publicCount) C :=
    ⟨coins.mu,alpha,conversionState⟩
  let publicProof : CanonicalRequest.Output (g := G) (fields := MdocRuntime.fields B) (Advice := MdocAdvice.Value) :=
    ⟨CompleteFrontendBody.body binary prime primePlan root view,fun _ => 0⟩
  let publicPoint := ((CanonicalRequest.encoding repr shape setup publicCount binaryRequest metadata request).chain initial).point
    publicProof H (G).batchingIndex.val
  have rank := ((CanonicalRequest.encoding repr shape setup publicCount binaryRequest metadata request).chain initial).point_rank
    publicProof H (G).batchingIndex.isLt.le
  change publicPoint.rank = (G).batchingIndex.val at rank
  let powers := fun (tree : Fin 2) (i : Fin 1024) => MdocRuntime.generator binary.basis^
    ((cv.alpha tree).val*(Handoff.weights (maskBits := 256) primeData.claim.sharedWeights n.eta.val i)).val
  let targets := fun tree => MdocRuntime.generator binary.basis^((cv.alpha tree).val*coins.mu).val
  let same := binary.description.same_template powers (CompleteSimulation.generatorBase binary)
    (MdocAdvice.bits coins.advice) targets
  let plan := same.plan binary.plan
  have shapeEq : (G).binary = plan.frontend := (same.frontend binary.plan).symm
  have window := ParserApplication.binary_window binary prime primePlan _ plan shapeEq
  have wire := Parser.messages repr shape setup publicCount binaryRequest metadata request initial publicProof H
    .binary plan shapeEq (G).batchingIndex.val (G).batchingIndex.isLt.le window
  have payload : Parser.payload publicProof .binary plan shapeEq =
      CompleteShape.payloadEquiv same (simulateCircuit binary.description.template coins.binary) := by
    change (CompleteShape.bodyEquiv plan).symm
      (Eq.mp (congrArg (FrontendPayload B) shapeEq) (CompleteShape.bodyEquiv binary.plan view.binaryPayload)) = _
    rw [bpayload]
    exact PayloadTransport.same_body binary.plan same _
  rw [payload] at wire
  dsimp only [Parser.start] at wire
  have scale := strictAnswer_lookup H samples.fallback publicPoint (ApplicationPrefix.rescalingIndex (G))
    (by rw [rank]; exact (ParserApplication.positions binary prime primePlan).2.1)
  have conversion := strictAnswer_lookup H samples.fallback publicPoint (ApplicationPrefix.conversionIndex (G))
    (by rw [rank]; exact (ParserApplication.positions binary prime primePlan).2.2.1)
  have packing := strictAnswer_lookup H samples.fallback publicPoint (ApplicationPrefix.packingIndex (G))
    (by rw [rank]; exact (ParserApplication.positions binary prime primePlan).2.2.2)
  have mu := Parser.read_mu repr shape setup publicCount binaryRequest metadata request initial publicProof H
    (G).batchingIndex.val (G).batchingIndex.isLt.le (ParserApplication.positions binary prime primePlan).2.2.1.le
  have advice := Parser.read_advice repr shape setup publicCount binaryRequest metadata request initial publicProof H
    (G).batchingIndex.val (G).batchingIndex.isLt.le (by exact le_trans (Nat.le_add_right _ _) window)
  have U := Parser.read_packingU repr shape setup publicCount binaryRequest metadata request initial publicProof H
    (G).batchingIndex.val (G).batchingIndex.isLt.le (by change (128 : ℕ) ≠ 1; decide)
    (ParserApplication.positions binary prime primePlan).2.2.2.le
  have A := Parser.read_packingA repr shape setup publicCount binaryRequest metadata request initial publicProof H
    (G).batchingIndex.val (G).batchingIndex.isLt.le le_rfl
  change _ = some view.mu at mu
  rw [hmu] at mu
  change _ = some view.advice at advice
  rw [hadvice] at advice
  rw [ParserApplication.packing_pair binary prime primePlan publicProof] at U A
  unfold ApplicationPrefix.readBinary at parsed
  simp only [Option.map_id] at parsed
  erw [scale,conversion,mu,advice] at parsed
  simp only [Option.bind_eq_bind,Option.bind_some,MdocAdvice.decode] at parsed
  erw [U,packing,A] at parsed
  simp only [Option.bind_some,Option.map_some] at parsed
  erw [← values.1,← values.2.1] at parsed
  erw [if_pos (by erw [rank]; exact window),wire] at parsed
  simp only [Option.bind_some] at parsed
  cases Option.some.inj parsed
  unfold BinaryData.frontend BinaryData.setup FrontendVerifier.PackedSetup.prepare Frontend.Packed.rows FrontendVerifier.constraints
  dsimp only [BinaryData.powers,BinaryData.targets,publicProof,CompleteFrontendBody.body,CompleteFrontendBody.rawBody,
    CompleteSimulation.Result.raw,id_eq]
  erw [← values.2.2]
  symm
  exact congrArg
      (fun msg =>
        let circuit := CompleteSimulation.generatedCircuit binary prime primePlan n cv coins.advice
        let cs := (Linear.buildConstraints (circuit.proof msg 0)).getD ⟨[],zeroClaim⟩
        Linear.Packed.rows binary.description.packing cs binary.description.packedIndex
          (CellLayout.Binary.pad binary.description.words 128 binary.description.pads)
          (fun i => circuit.inputWeights msg 0 (binary.description.inputIndex (.inl i)))
          (Current.Adapter.Circuit.bitValue ∘ binary.publicBits)
          (fun i => circuit.inputWeights msg 0 (binary.description.inputIndex (.inr i)))
          (fun i => (view.packing.1 i).val) view.delta view.packing.2) messages

end LfzkV2.Current.ZeroKnowledge.Frontend.SimulationParsed
