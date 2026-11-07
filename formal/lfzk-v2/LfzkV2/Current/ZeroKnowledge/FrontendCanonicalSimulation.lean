import LfzkV2.Current.ZeroKnowledge.FrontendBodyState
import LfzkV2.Current.ZeroKnowledge.FrontendAnswerTape
import LfzkV2.Current.ZeroKnowledge.OracleResponse

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
variable (shape : WireBlocks.Shape (CompleteSimulation.geometry binary prime primePlan) (MdocRuntime.fields B))
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
    let proof : CanonicalRequest.Output (g := CompleteSimulation.geometry binary prime primePlan)
      (fields := MdocRuntime.fields B) (Advice := MdocAdvice.Value) :=
        ⟨CompleteFrontendBody.body binary prime primePlan root result,fun _ => 0⟩
    let inside : result.state.rank.val < (CompleteSimulation.geometry binary prime primePlan).roles.length := by
      rw [(SimulationWrites.simulate_properties binary prime primePlan samples base H _ coins).1]
      exact (CompleteSimulation.geometry binary prime primePlan).batchingIndex.isLt
    CompleteTranscript.query base result.state inside =
      ((CanonicalRequest.encoding repr shape setup publicCount binaryRequest metadata request).chain initialLink).point
        proof H (CompleteSimulation.geometry binary prime primePlan).batchingIndex.val := by
  let base := CompleteWire.canonicalBase shape defaultAdvice repr setup publicCount binaryRequest metadata request root
  let result := CompleteSimulation.simulate binary prime primePlan samples base H
    (FingerprintPrefix.context request root) coins
  let proof : CanonicalRequest.Output (g := CompleteSimulation.geometry binary prime primePlan)
      (fields := MdocRuntime.fields B) (Advice := MdocAdvice.Value) :=
    ⟨CompleteFrontendBody.body binary prime primePlan root result,fun _ => 0⟩
  have properties := SimulationWrites.simulate_properties binary prime primePlan samples base H
    (FingerprintPrefix.context request root) coins
  have inside : result.state.rank.val < (CompleteSimulation.geometry binary prime primePlan).roles.length := by
    rw [properties.1]
    exact (CompleteSimulation.geometry binary prime primePlan).batchingIndex.isLt
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
    let proof : CanonicalRequest.Output (g := CompleteSimulation.geometry binary prime primePlan)
      (fields := MdocRuntime.fields B) (Advice := MdocAdvice.Value) :=
        ⟨CompleteFrontendBody.body binary prime primePlan root result,fun _ => 0⟩
    AnswerTape.lookup samples.fallback result.state = AnswerTape.pointLookup H samples.fallback
      (((CanonicalRequest.encoding repr shape setup publicCount binaryRequest metadata request).chain initialLink).point
        proof H (CompleteSimulation.geometry binary prime primePlan).batchingIndex.val) := by
  let base := CompleteWire.canonicalBase shape defaultAdvice repr setup publicCount binaryRequest metadata request root
  let result := CompleteSimulation.simulate binary prime primePlan samples base H
    (FingerprintPrefix.context request root) coins
  have properties := SimulationWrites.simulate_properties binary prime primePlan samples base H
    (FingerprintPrefix.context request root) coins
  have inside : result.state.rank.val < (CompleteSimulation.geometry binary prime primePlan).roles.length := by
    rw [properties.1]
    exact (CompleteSimulation.geometry binary prime primePlan).batchingIndex.isLt
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
    (responses : Response (CompleteSimulation.geometry binary prime primePlan) B ×
      Response (CompleteSimulation.geometry binary prime primePlan) P) :
    let base := CompleteWire.canonicalBase shape defaultAdvice repr setup publicCount binaryRequest metadata request root
    let result := CompleteSimulation.simulate binary prime primePlan samples base H
      (FingerprintPrefix.context request root) coins
    let state := CompleteTranscript.bind (CompleteTranscript.step base H result.state).2
      (fun written => { written with responses := some responses })
    let proof : CanonicalRequest.Output (g := CompleteSimulation.geometry binary prime primePlan)
      (fields := MdocRuntime.fields B) (Advice := MdocAdvice.Value) :=
        ⟨OracleResponse.fillBoth (CompleteFrontendBody.body binary prime primePlan root result) responses,fun _ => 0⟩
    let inside : state.rank.val < (CompleteSimulation.geometry binary prime primePlan).roles.length := by
      change (CompleteTranscript.step base H result.state).2.rank.val < _
      rw [SimulationWrites.step_rank,
        (SimulationWrites.simulate_properties binary prime primePlan samples base H _ coins).1]
      have := (CompleteSimulation.geometry binary prime primePlan).batchingIndex_next
      omega
    CompleteTranscript.query base state inside =
      ((CanonicalRequest.encoding repr shape setup publicCount binaryRequest metadata request).chain initialLink).point
        proof H (CompleteSimulation.geometry binary prime primePlan).openingIndex.val := by
  let base := CompleteWire.canonicalBase shape defaultAdvice repr setup publicCount binaryRequest metadata request root
  let result := CompleteSimulation.simulate binary prime primePlan samples base H
    (FingerprintPrefix.context request root) coins
  let body := CompleteFrontendBody.body binary prime primePlan root result
  let state := CompleteTranscript.bind (CompleteTranscript.step base H result.state).2
    (fun written => { written with responses := some responses })
  let proof : CanonicalRequest.Output (g := CompleteSimulation.geometry binary prime primePlan)
      (fields := MdocRuntime.fields B) (Advice := MdocAdvice.Value) :=
    ⟨OracleResponse.fillBoth body responses,fun _ => 0⟩
  have properties := SimulationWrites.simulate_properties binary prime primePlan samples base H
    (FingerprintPrefix.context request root) coins
  have firstInside : result.state.rank.val < (CompleteSimulation.geometry binary prime primePlan).roles.length := by
    rw [properties.1]
    exact (CompleteSimulation.geometry binary prime primePlan).batchingIndex.isLt
  have next : state.rank.val = (CompleteSimulation.geometry binary prime primePlan).openingIndex.val := by
    change (CompleteTranscript.step base H result.state).2.rank.val = _
    rw [SimulationWrites.step_rank,properties.1,Nat.min_eq_right
      (Nat.le_of_lt (CompleteSimulation.geometry binary prime primePlan).batchingIndex_next)]
    exact (CompleteSimulation.geometry binary prime primePlan).openingIndex_val.symm
  have inside : state.rank.val < (CompleteSimulation.geometry binary prime primePlan).roles.length := by
    rw [next]
    exact (CompleteSimulation.geometry binary prime primePlan).openingIndex.isLt
  have good := History.bind_good base H (FingerprintPrefix.context request root)
    (CompleteTranscript.step base H result.state).2
    (fun written => { written with responses := some responses })
    (History.step_good base H (FingerprintPrefix.context request root) result.state
      (SimulationHistory.simulate_good binary prime primePlan samples base H _ coins))
  have oldWritten := BodyState.stored_writes binary prime primePlan samples base H root
    (FingerprintPrefix.context request root) coins
  have oldPending := BodyState.pending_write binary prime primePlan samples base H root
    (FingerprintPrefix.context request root) coins firstInside
  have untilOpening : result.state.rank.val < (CompleteSimulation.geometry binary prime primePlan).openingIndex.val :=
    properties.1.trans_lt (by rw [Geometry.openingIndex_val]; omega)
  have written : ∀ i, state.writes i = ProtocolWrites.fresh proof.body
      ⟨i.val,by have := i.isLt; have := state.rank.isLt; omega⟩ := by
    let Written (current : CompleteSimulation.State binary prime primePlan
        (Key := FingerprintPrefix.Key publicCount) (Base := CanonicalRequest.Base repr shape setup publicCount) (C := C)) : Prop :=
      ∀ i, current.writes i = ProtocolWrites.fresh proof.body
        ⟨i.val,by have := i.isLt; have := current.rank.isLt; omega⟩
    have advanced : Written (CompleteTranscript.bind
        (CompleteTranscript.advance base result.state firstInside
          (H (CompleteTranscript.query base result.state firstInside)))
        (fun written => { written with responses := some responses })) := by
      intro i
      change Fin.snoc (α := fun _ : Fin (result.state.rank.val+1) =>
        ProtocolWrites.Fresh (CompleteSimulation.geometry binary prime primePlan) (MdocRuntime.fields B) MdocAdvice.Value)
        result.state.writes result.state.pending i = _
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [Fin.snoc_last,oldPending]
        exact (OracleResponse.freshBoth_before body responses _
          (by
            change result.state.rank.val < (CompleteSimulation.geometry binary prime primePlan).openingIndex.val
            exact untilOpening)).symm
      · rw [Fin.snoc_castSucc,oldWritten]
        exact (OracleResponse.freshBoth_before body responses _
          (by
            change j.val < (CompleteSimulation.geometry binary prime primePlan).openingIndex.val
            exact j.isLt.trans untilOpening)).symm
    have actual := congrArg
      (fun pair => CompleteTranscript.bind pair.2 (fun written => { written with responses := some responses }))
      (CompleteTranscript.step_query base H result.state firstInside)
    exact (congrArg Written actual).mpr advanced
  have pending : state.pending = ProtocolWrites.fresh proof.body ⟨state.rank.val,inside⟩ := by
    have index : (⟨state.rank.val,inside⟩ : Fin
        (CompleteSimulation.geometry binary prime primePlan).roles.length) =
        (CompleteSimulation.geometry binary prime primePlan).openingIndex := Fin.ext next
    rw [index]
    have hp : (CompleteSimulation.geometry binary prime primePlan).openingIndex.val ≠
        (CompleteSimulation.geometry binary prime primePlan).primeStart := by
      have := (CompleteSimulation.geometry binary prime primePlan).roles_length
      have := (CompleteSimulation.geometry binary prime primePlan).openingIndex_last
      dsimp only [Geometry.primeStart]
      omega
    have hb : (CompleteSimulation.geometry binary prime primePlan).openingIndex.val ≠
        (CompleteSimulation.geometry binary prime primePlan).binaryStart := by
      have := (CompleteSimulation.geometry binary prime primePlan).roles_length
      have := (CompleteSimulation.geometry binary prime primePlan).openingIndex_last
      dsimp only [Geometry.binaryStart]
      omega
    dsimp only [state]
    rw [CompleteTranscript.step_query base H result.state firstInside]
    simp only [CompleteTranscript.bind,CompleteTranscript.advance,proof,OracleResponse.fillBoth,
      ProtocolWrites.fresh,Geometry.get_openingIndex,if_neg hp,if_neg hb,reduceCtorEq,if_false,if_true,
      ProtocolWrites.frontendMessages,Prod.eta]
  have same := CanonicalState.query_eq shape defaultAdvice repr setup publicCount binaryRequest metadata request
    proof H initialLink state inside good written pending
  exact same.trans (congrArg
    (fun n => ((CanonicalRequest.encoding repr shape setup publicCount binaryRequest metadata request).chain initialLink).point proof H n)
    next)

end LfzkV2.Current.ZeroKnowledge.Frontend.CanonicalSimulation
