import LfzkV2.Current.ZeroKnowledge.FrontendSimulationAnswers
import LfzkV2.Current.ZeroKnowledge.FrontendCompilerTransport
import LfzkV2.Current.ZeroKnowledge.FrontendHonestBinaryRows

/-! The public simulation's stateful sumcheck compiler sees the same answer
window as the canonical runtime. The frontend state and its consumed answers
are constructed by the protocol; no transcript-match or row-equivalence
certificate is supplied here. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.Frontend.SimulationMessages
open SumcheckV2 ApplicationSetup ConcreteSetup
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
theorem stage_ranks :
    (selected).rank.val = (G).primeStart ∧
      (native).state.rank.val = ApplicationPrefix.conversionIndex (G) ∧
      (converted).state.rank.val = (G).binaryStart ∧
      (CompleteSimulation.binaryReplay binary prime primePlan samples W H native converted coins.advice
        (simulateCircuit binary.description.template coins.binary)).2.rank.val = ApplicationPrefix.packingIndex (G) := by
  have first := SimulationWrites.selected_properties binary prime primePlan samples W H
    (FingerprintPrefix.context request root) coins.fingerprints
  have cap := SimulationWrites.capacity binary prime primePlan
  have middle := SimulationWrites.prime_properties binary prime primePlan samples W H selected
    (simulateCircuit prime.circuit coins.prime) (by rw [first.1,cap]; omega)
  have next := SimulationWrites.conversion_properties binary prime primePlan samples W H native coins.mu
    middle.2.2 (by rw [middle.1,first.1,cap]; omega)
  have last := SimulationWrites.binary_properties binary prime primePlan samples W H native converted coins.advice
    (simulateCircuit binary.description.template coins.binary) next.2.2 (by rw [next.1,middle.1,first.1,cap]; omega)
  refine ⟨first.1,?_,?_,?_⟩
  · rw [middle.1,first.1,HonestTranscript.circuitFuel_roles primePlan .prime]
    change 1+(primePlan.frontend.roles .prime).length+2 = 1+(primePlan.frontend.roles .prime).length+2
    rfl
  · rw [next.1,middle.1,first.1,HonestTranscript.circuitFuel_roles primePlan .prime]
    change 1+(primePlan.frontend.roles .prime).length+2+1 = (primePlan.frontend.roles .prime).length+4
    omega
  · rw [last.1,next.1,middle.1,first.1,HonestTranscript.circuitFuel_roles primePlan .prime,
      HonestTranscript.circuitFuel_roles binary.plan .binary]
    change 1+(primePlan.frontend.roles .prime).length+2+1+(binary.plan.frontend.roles .binary).length =
      (primePlan.frontend.roles .prime).length+4+(binary.plan.frontend.roles .binary).length
    omega

omit [DecidableEq B] in
theorem prime_messages :
    messagesFromSetup prime.circuit
      (readSetup (CompleteTranscript.reader .prime (Equiv.refl P) samples.prime samples.primeNonzero W H)
        primePlan prime.setup.plan (simulateCircuit prime.circuit coins.prime) selected false).1
      (simulateCircuit prime.circuit coins.prime) =
      FrontendReplay.read samples.prime samples.primeNonzero prime.circuit prime.setup.plan
        (simulateCircuit prime.circuit coins.prime)
        (ApplicationPrefix.frontendTape point ((point).priorAnswers H) samples.fallback (G).primeStart
          (FrontendReplay.slots prime.circuit)) := by
  have rank := (SimulationWrites.selected_properties binary prime primePlan samples W H
    (FingerprintPrefix.context request root) coins.fingerprints).1
  have fits : (selected).rank.val+HonestTranscript.circuitFuel primePlan false ≤ (G).roles.length := by
    rw [rank,SimulationWrites.capacity binary prime primePlan]
    omega
  have message := CompilerTransport.messages
    (g := G) (fields := MdocRuntime.fields B) (Authentication := OpeningBody.Authentication (G))
    .prime (Equiv.refl P) W H samples.prime samples.primeNonzero samples.fallback
    primePlan prime.setup.plan (simulateCircuit prime.circuit coins.prime) selected (result).state fits
    (SimulationAnswers.prime_future binary prime primePlan samples W H (FingerprintPrefix.context request root) coins)
  rw [CanonicalSimulation.batching_tape binary prime primePlan samples shape repr setup defaultAdvice publicCount
    binaryRequest metadata request root H initial coins,rank] at message
  exact message.trans (AnswerTape.frontend_read H samples.prime samples.primeNonzero samples.fallback prime.circuit
    prime.setup.plan (simulateCircuit prime.circuit coins.prime) point (G).primeStart).symm

omit [DecidableEq B] in
theorem binary_messages :
    let circuit := CompleteSimulation.generatedCircuit binary prime primePlan native converted coins.advice
    let payload := CompleteShape.payloadEquiv
      (CompleteSimulation.generatedSame binary prime primePlan native converted coins.advice)
      (simulateCircuit binary.description.template coins.binary)
    let ids := (binary.description.setup (CompleteSimulation.powers binary prime primePlan native converted)
      (CompleteSimulation.generatorBase binary) (MdocAdvice.bits coins.advice)
      (CompleteSimulation.targets binary prime primePlan converted)).plan
    messagesFromSetup circuit
      (CompleteSimulation.binaryReplay binary prime primePlan samples W H native converted coins.advice
        (simulateCircuit binary.description.template coins.binary)).1 payload =
      FrontendReplay.read samples.binary samples.binaryNonzero circuit ids payload
        (ApplicationPrefix.frontendTape point ((point).priorAnswers H) samples.fallback (G).binaryStart
          (FrontendReplay.slots circuit)) := by
  have rank : (CompleteSimulation.binaryStart binary prime primePlan converted coins.advice).rank.val = (G).binaryStart :=
    (stage_ranks binary prime primePlan samples shape repr setup defaultAdvice publicCount binaryRequest metadata request root H coins).2.2.1
  have fuel : HonestTranscript.circuitFuel
      (CompleteSimulation.generatedPlan binary prime primePlan native converted coins.advice) false =
        HonestTranscript.circuitFuel binary.plan false :=
    HonestTranscript.circuitFuel_same _ _ _
  have fits : (CompleteSimulation.binaryStart binary prime primePlan converted coins.advice).rank.val+
      HonestTranscript.circuitFuel (CompleteSimulation.generatedPlan binary prime primePlan native converted coins.advice) false ≤
        (G).roles.length := by
    rw [rank,fuel,SimulationWrites.capacity binary prime primePlan,HonestTranscript.circuitFuel_roles primePlan .prime]
    change (primePlan.frontend.roles .prime).length+4+HonestTranscript.circuitFuel binary.plan false ≤
      (primePlan.frontend.roles .prime).length+HonestTranscript.circuitFuel binary.plan false+7
    omega
  have message := CompilerTransport.messages
    (g := G) (fields := MdocRuntime.fields B) (Authentication := OpeningBody.Authentication (G))
    .binary (Equiv.refl B) W H samples.binary samples.binaryNonzero samples.fallback
    (CompleteSimulation.generatedPlan binary prime primePlan native converted coins.advice)
    (binary.description.setup _ _ _ _).plan
    (CompleteShape.payloadEquiv (CompleteSimulation.generatedSame binary prime primePlan native converted coins.advice)
      (simulateCircuit binary.description.template coins.binary))
    (CompleteSimulation.binaryStart binary prime primePlan converted coins.advice) (result).state fits
    (SimulationAnswers.binary_future binary prime primePlan samples W H (FingerprintPrefix.context request root) coins)
  rw [CanonicalSimulation.batching_tape binary prime primePlan samples shape repr setup defaultAdvice publicCount
    binaryRequest metadata request root H initial coins,rank] at message
  exact message.trans (AnswerTape.frontend_read H samples.binary samples.binaryNonzero samples.fallback
    (CompleteSimulation.generatedCircuit binary prime primePlan native converted coins.advice)
    (binary.description.setup _ _ _ _).plan
    (CompleteShape.payloadEquiv (CompleteSimulation.generatedSame binary prime primePlan native converted coins.advice)
      (simulateCircuit binary.description.template coins.binary)) point (G).binaryStart).symm

end LfzkV2.Current.ZeroKnowledge.Frontend.SimulationMessages
