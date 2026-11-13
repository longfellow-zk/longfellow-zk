import LfzkV2.Current.ZeroKnowledge.FrontendCanonicalState
import LfzkV2.Current.ZeroKnowledge.FrontendBodyState
import LfzkV2.Current.ZeroKnowledge.FrontendAnswerTape

/-! The public frontend simulator's next query is the canonical batching
query reconstructed from its complete frontend body. All prefix writes,
earlier answers and link feedback are derived, not supplied certificates. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.Frontend.CanonicalSimulation

open SumcheckV2 ApplicationSetup ConcreteSetup
open scoped Classical
set_option backward.isDefEq.respectTransparency false
variable {B C : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
local notation "P" => Adapter.Mdoc.P
variable (binary : BinaryCircuit B) (prime : PrimePublic P 768)
variable (primePlan : FrontendSchedule.Plan P prime.circuit)
variable (samples : ConcreteMetadata.Samples B C)
variable (shape : WireBlocks.Shape (MdocRuntime.geometry binary.description prime binary.plan primePlan) (MdocRuntime.fields B))
variable (repr : ProofBodyCodec.Representations (MdocRuntime.fields B) MdocAdvice.Value)
variable (setup : FingerprintPrefix.Setup) (defaultAdvice : MdocAdvice.Value)
variable (publicCount : ℕ)
variable (binaryRequest : (Fin publicCount → Bool) → Fin shape.binaryPublic → B)
variable (metadata : CanonicalRequest.Metadata (Advice := MdocAdvice.Value) (C := C) shape publicCount)
variable (request : CanonicalRequest.Request shape publicCount) (root : Digest)
variable (H : CompleteSimulation.Point binary prime primePlan
  (Key := FingerprintPrefix.Key publicCount) (Base := CanonicalRequest.Base repr shape setup publicCount) → Digest × C)

omit [DecidableEq B] in
theorem batching_query (initialLink : Digest) (coins : CompleteSimulation.Coins binary prime) :
    let base := CompleteWire.canonicalBase shape defaultAdvice repr setup publicCount binaryRequest metadata request root
    let result := CompleteSimulation.simulate binary prime primePlan samples base H
      (FingerprintPrefix.context request root) coins
    let proof : CanonicalRequest.Output (g := MdocRuntime.geometry binary.description prime binary.plan primePlan)
      (fields := MdocRuntime.fields B) (Advice := MdocAdvice.Value) :=
        ⟨CompleteFrontendBody.body binary prime primePlan root result,fun _ => 0⟩
    let inside : result.state.rank.val < (MdocRuntime.geometry binary.description prime binary.plan primePlan).roles.length := by
      rw [(SimulationWrites.simulate_properties binary prime primePlan samples base H _ coins).1]
      exact (MdocRuntime.geometry binary.description prime binary.plan primePlan).batchingIndex.isLt
    CompleteTranscript.query base result.state inside =
      ((CanonicalRequest.encoding repr shape setup publicCount binaryRequest metadata request).chain initialLink).point
        proof H (MdocRuntime.geometry binary.description prime binary.plan primePlan).batchingIndex.val := by
  let base := CompleteWire.canonicalBase shape defaultAdvice repr setup publicCount binaryRequest metadata request root
  let result := CompleteSimulation.simulate binary prime primePlan samples base H
    (FingerprintPrefix.context request root) coins
  let proof : CanonicalRequest.Output (g := MdocRuntime.geometry binary.description prime binary.plan primePlan)
      (fields := MdocRuntime.fields B) (Advice := MdocAdvice.Value) :=
    ⟨CompleteFrontendBody.body binary prime primePlan root result,fun _ => 0⟩
  have properties := SimulationWrites.simulate_properties binary prime primePlan samples base H
    (FingerprintPrefix.context request root) coins
  have inside : result.state.rank.val < (MdocRuntime.geometry binary.description prime binary.plan primePlan).roles.length := by
    rw [properties.1]
    exact (MdocRuntime.geometry binary.description prime binary.plan primePlan).batchingIndex.isLt
  have good := SimulationHistory.simulate_good binary prime primePlan samples base H (FingerprintPrefix.context request root) coins
  have written := BodyState.stored_writes binary prime primePlan samples base H root (FingerprintPrefix.context request root) coins
  have pending := BodyState.pending_write binary prime primePlan samples base H root (FingerprintPrefix.context request root) coins inside
  have same := CanonicalState.query_eq shape defaultAdvice repr setup publicCount binaryRequest metadata request
    proof H initialLink result.state inside good written pending
  exact same.trans (congrArg
    (fun n => ((CanonicalRequest.encoding repr shape setup publicCount binaryRequest metadata request).chain initialLink).point proof H n)
    properties.1)

omit [DecidableEq B] in
theorem batching_tape (initialLink : Digest) (coins : CompleteSimulation.Coins binary prime) :
    let base := CompleteWire.canonicalBase shape defaultAdvice repr setup publicCount binaryRequest metadata request root
    let result := CompleteSimulation.simulate binary prime primePlan samples base H
      (FingerprintPrefix.context request root) coins
    let proof : CanonicalRequest.Output (g := MdocRuntime.geometry binary.description prime binary.plan primePlan)
      (fields := MdocRuntime.fields B) (Advice := MdocAdvice.Value) :=
        ⟨CompleteFrontendBody.body binary prime primePlan root result,fun _ => 0⟩
    AnswerTape.lookup samples.fallback result.state = AnswerTape.pointLookup H samples.fallback
      (((CanonicalRequest.encoding repr shape setup publicCount binaryRequest metadata request).chain initialLink).point
        proof H (MdocRuntime.geometry binary.description prime binary.plan primePlan).batchingIndex.val) := by
  let base := CompleteWire.canonicalBase shape defaultAdvice repr setup publicCount binaryRequest metadata request root
  let result := CompleteSimulation.simulate binary prime primePlan samples base H
    (FingerprintPrefix.context request root) coins
  have properties := SimulationWrites.simulate_properties binary prime primePlan samples base H
    (FingerprintPrefix.context request root) coins
  have inside : result.state.rank.val < (MdocRuntime.geometry binary.description prime binary.plan primePlan).roles.length := by
    rw [properties.1]
    exact (MdocRuntime.geometry binary.description prime binary.plan primePlan).batchingIndex.isLt
  have good := SimulationHistory.simulate_good binary prime primePlan samples base H
    (FingerprintPrefix.context request root) coins
  have readback := AnswerTape.query_lookup base H samples.fallback
    (FingerprintPrefix.context request root) result.state inside good
  rw [batching_query binary prime primePlan samples shape repr setup defaultAdvice publicCount
    binaryRequest metadata request root H initialLink coins] at readback
  exact readback

end LfzkV2.Current.ZeroKnowledge.Frontend.CanonicalSimulation
