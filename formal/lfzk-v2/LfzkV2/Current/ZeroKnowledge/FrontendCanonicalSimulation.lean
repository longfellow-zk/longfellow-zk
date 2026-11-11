import LfzkV2.Current.ZeroKnowledge.FrontendBodyState
import LfzkV2.Current.ZeroKnowledge.FrontendAnswerTape
import LfzkV2.Current.ZeroKnowledge.FrontendOpeningState

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

omit [DecidableEq B] in
set_option maxHeartbeats 600000 in
theorem opening_query (initialLink : Digest) (coins : CompleteSimulation.Coins binary prime)
    (responses : Response (MdocRuntime.geometry binary.description prime binary.plan primePlan) B ×
      Response (MdocRuntime.geometry binary.description prime binary.plan primePlan) P) :
    let base := CompleteWire.canonicalBase shape defaultAdvice repr setup publicCount binaryRequest metadata request root
    let result := CompleteSimulation.simulate binary prime primePlan samples base H
      (FingerprintPrefix.context request root) coins
    let state := CompleteTranscript.bind (CompleteTranscript.step base H result.state).2
      (fun written => { written with responses := some responses })
    let proof : CanonicalRequest.Output (g := MdocRuntime.geometry binary.description prime binary.plan primePlan)
      (fields := MdocRuntime.fields B) (Advice := MdocAdvice.Value) :=
        ⟨OracleResponse.fillBoth (CompleteFrontendBody.body binary prime primePlan root result) responses,fun _ => 0⟩
    let inside : state.rank.val < (MdocRuntime.geometry binary.description prime binary.plan primePlan).roles.length := by
      change (CompleteTranscript.step base H result.state).2.rank.val < _
      rw [SimulationWrites.step_rank,
        (SimulationWrites.simulate_properties binary prime primePlan samples base H _ coins).1]
      have := (MdocRuntime.geometry binary.description prime binary.plan primePlan).batchingIndex_next
      omega
    CompleteTranscript.query base state inside =
      ((CanonicalRequest.encoding repr shape setup publicCount binaryRequest metadata request).chain initialLink).point
        proof H (MdocRuntime.geometry binary.description prime binary.plan primePlan).openingIndex.val := by
  let base := CompleteWire.canonicalBase shape defaultAdvice repr setup publicCount binaryRequest metadata request root
  let result := CompleteSimulation.simulate binary prime primePlan samples base H (FingerprintPrefix.context request root) coins
  let proof : CanonicalRequest.Output (g := MdocRuntime.geometry binary.description prime binary.plan primePlan)
      (fields := MdocRuntime.fields B) (Advice := MdocAdvice.Value) :=
    ⟨CompleteFrontendBody.body binary prime primePlan root result,fun _ => 0⟩
  have properties := SimulationWrites.simulate_properties binary prime primePlan samples base H
    (FingerprintPrefix.context request root) coins
  have firstInside : result.state.rank.val < (MdocRuntime.geometry binary.description prime binary.plan primePlan).roles.length :=
    properties.1.trans_lt (MdocRuntime.geometry binary.description prime binary.plan primePlan).batchingIndex.isLt
  have rank : result.state.rank.val+1 = (MdocRuntime.geometry binary.description prime binary.plan primePlan).openingIndex.val := by
    rw [properties.1]
    exact (MdocRuntime.geometry binary.description prime binary.plan primePlan).openingIndex_val.symm
  have opening := History.opening_properties result.state base H (FingerprintPrefix.context request root)
    proof.body responses rank
    (SimulationHistory.simulate_good binary prime primePlan samples base H _ coins)
    (BodyState.stored_writes binary prime primePlan samples base H root (FingerprintPrefix.context request root) coins)
    (BodyState.pending_write binary prime primePlan samples base H root (FingerprintPrefix.context request root) coins firstInside)
  let next := CompleteTranscript.bind (CompleteTranscript.step base H result.state).2
    (fun writes => { writes with responses := some responses })
  have inside : next.rank.val < (MdocRuntime.geometry binary.description prime binary.plan primePlan).roles.length :=
    opening.1.trans_lt (MdocRuntime.geometry binary.description prime binary.plan primePlan).openingIndex.isLt
  have same := CanonicalState.query_eq shape defaultAdvice repr setup publicCount binaryRequest metadata request
    (OracleResponse.proofBoth proof responses) H initialLink next inside opening.2.1 opening.2.2.1 (opening.2.2.2 inside)
  exact same.trans (congrArg
    (fun n => ((CanonicalRequest.encoding repr shape setup publicCount binaryRequest metadata request).chain initialLink).point
      (OracleResponse.proofBoth proof responses) H n) opening.1)

end LfzkV2.Current.ZeroKnowledge.Frontend.CanonicalSimulation
