import LfzkV2.Current.ZeroKnowledge.FrontendParser
import LfzkV2.Current.RuntimeAdaptive

/-! Canonical typed frontend bodies parse without an application-system
certificate. Public topology fixes both message windows, including every
challenge-generated adapter circuit. Trace and primitive-generator checks
remain the actual checks performed by the application decoder. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
namespace LfzkV2.Current.ZeroKnowledge.Frontend.ParserApplication
open SumcheckV2 ApplicationSetup ConcreteSetup
open scoped Classical
theorem quotient_bound : 2^10 ≤ Current.Adapter.Mdoc.quotientBound := by decide
variable {B C : Type} [Field B] [DecidableEq B] [Algebra (ZMod 2) B]
local notation "P" => Adapter.Mdoc.P
variable (binary : BinaryCircuit B) (prime : PrimePublic P 768)
variable (primePlan : FrontendSchedule.Plan P prime.circuit)
local notation "G" => MdocRuntime.geometry binary.description prime binary.plan primePlan
variable (repr : ProofBodyCodec.Representations (MdocRuntime.fields B) MdocAdvice.Value)
variable (shape : WireBlocks.Shape (MdocRuntime.geometry binary.description prime binary.plan primePlan) (MdocRuntime.fields B))
variable (setup : FingerprintPrefix.Setup) (publicCount : ℕ)
variable (binaryRequest : (Fin publicCount → Bool) → Fin shape.binaryPublic → MdocRuntime.fields B .binary)
variable (metadata : CanonicalRequest.Metadata (Advice := MdocAdvice.Value) (C := C) shape publicCount)
variable (request : CanonicalRequest.Request shape publicCount) (initial : Digest)
variable (proof : CanonicalRequest.Output (g := MdocRuntime.geometry binary.description prime binary.plan primePlan)
  (fields := MdocRuntime.fields B) (Advice := MdocAdvice.Value))
variable (H : QueryRuntime.Runtime.Point repr shape setup publicCount → Digest × C)
variable (samples : ConcreteMetadata.Samples B C)
local notation "E" => CanonicalRequest.encoding repr shape setup publicCount binaryRequest metadata request
local notation "point" => TranscriptV2.Chain.point (Replay.Encoding.chain E initial) proof H (Fin.val (Geometry.batchingIndex G))
local notation "past" => Input.priorAnswers
  (TranscriptV2.Chain.point (Replay.Encoding.chain E initial) proof H (Fin.val (Geometry.batchingIndex G))) H

omit [DecidableEq B] in
theorem positions :
    ApplicationPrefix.rowBatchingIndex (G) < (G).batchingIndex.val ∧
      ApplicationPrefix.rescalingIndex (G) < (G).batchingIndex.val ∧
      ApplicationPrefix.conversionIndex (G) < (G).batchingIndex.val ∧
      ApplicationPrefix.packingIndex (G) < (G).batchingIndex.val := by
  simp only [ApplicationPrefix.rowBatchingIndex,ApplicationPrefix.rescalingIndex,
    ApplicationPrefix.conversionIndex,ApplicationPrefix.packingIndex,Geometry.primeStart,
    Geometry.binaryStart,Geometry.batchingIndex_val,Geometry.backendPrefix,
    MdocRuntime.geometry,ConcreteSetup.geometry,BinaryCircuit.description,
    List.length_append,List.length_cons,List.length_nil,show (128 : ℕ) ≠ 1 by decide,if_false]
  repeat' constructor <;> omega

omit [DecidableEq B] in
theorem prime_window : (G).primeStart+FrontendReplay.slots prime.circuit ≤ (G).batchingIndex.val := by
  rw [primePlan.slots_eq_roles_length .prime]
  change (G).primeStart+((G).prime.roles .prime).length ≤ _
  exact (positions binary prime primePlan).1.le

omit [DecidableEq B] in
theorem binary_window {out input : ℕ} (circuit : Layered.Circuit B out input)
    (plan : FrontendSchedule.Plan B circuit) (same : (G).binary = plan.frontend) :
    (G).binaryStart+FrontendReplay.slots circuit ≤ (G).batchingIndex.val := by
  rw [plan.slots_eq_roles_length .binary,← same]
  exact (positions binary prime primePlan).2.2.2.le

omit [DecidableEq B] in
theorem prime_success : ∃ data,
    ApplicationPrefix.readPrime prime id samples.prime samples.primeNonzero samples.fallback point past = some data := by
  have messages := Parser.messages repr shape setup publicCount binaryRequest metadata request initial proof H
    .prime primePlan rfl (G).batchingIndex.val (G).batchingIndex.isLt.le (prime_window binary prime primePlan)
  have batch := Parser.strictAnswer repr shape setup publicCount binaryRequest metadata request initial proof H
    (G).batchingIndex.val (G).batchingIndex.isLt.le (ApplicationPrefix.rowBatchingIndex (G)) (positions binary prime primePlan).1
  have rank := ((E).chain initial).point_rank proof H (G).batchingIndex.isLt.le
  change Input.rank point = (G).batchingIndex.val at rank
  dsimp only [Parser.start] at messages
  unfold ApplicationPrefix.readPrime
  erw [if_pos (by erw [rank]; exact prime_window binary prime primePlan),messages,batch]
  exact ⟨_,rfl⟩

omit [DecidableEq B] in
theorem packing_pair : ProtocolWrites.packingPair proof.body = some proof.body.packing := rfl

omit [DecidableEq B] in
theorem packing_degree : (G).packingDegree = binary.description.degree := rfl

omit [DecidableEq B] in
theorem binary_success (native : PrimeData prime C) (generator : Bˣ) : ∃ data,
    ApplicationPrefix.readBinary binary.description native generator (packing_degree binary prime primePlan) id id samples.binary samples.binaryNonzero
      samples.primeNonzero samples.conversion MdocAdvice.decode samples.fallback point past = some data ∧
        data.U = proof.body.packing.1 := by
  let scale := (H (((E).chain initial).point proof H (ApplicationPrefix.rescalingIndex (G)))).2
  let conversion := (H (((E).chain initial).point proof H (ApplicationPrefix.conversionIndex (G)))).2
  let eta := (samples.primeNonzero scale).val
  let alpha := samples.conversion conversion
  let bodyMu : P := proof.body.mu
  let powers := fun (tree : Fin 2) (i : Fin 1024) => generator^((alpha tree).val*(Handoff.weights (maskBits := 256) native.claim.sharedWeights eta i)).val
  let targets := fun tree => generator^((alpha tree).val*bodyMu).val
  let same := binary.description.same_template powers (generator^(-(Current.Adapter.Mdoc.primeOrder : ℤ)))
    (MdocAdvice.bits proof.body.advice) targets
  let plan := same.plan binary.plan
  have shapeEq : (G).binary = plan.frontend := (same.frontend binary.plan).symm
  have window := binary_window binary prime primePlan _ plan shapeEq
  have messages := Parser.messages repr shape setup publicCount binaryRequest metadata request initial proof H
    .binary plan shapeEq (G).batchingIndex.val (G).batchingIndex.isLt.le window
  have rescale := Parser.strictAnswer repr shape setup publicCount binaryRequest metadata request initial proof H
    (G).batchingIndex.val (G).batchingIndex.isLt.le (ApplicationPrefix.rescalingIndex (G)) (positions binary prime primePlan).2.1
  have convert := Parser.strictAnswer repr shape setup publicCount binaryRequest metadata request initial proof H
    (G).batchingIndex.val (G).batchingIndex.isLt.le (ApplicationPrefix.conversionIndex (G)) (positions binary prime primePlan).2.2.1
  have packed := Parser.strictAnswer repr shape setup publicCount binaryRequest metadata request initial proof H
    (G).batchingIndex.val (G).batchingIndex.isLt.le (ApplicationPrefix.packingIndex (G)) (positions binary prime primePlan).2.2.2
  have mu := Parser.read_mu repr shape setup publicCount binaryRequest metadata request initial proof H
    (G).batchingIndex.val (G).batchingIndex.isLt.le (positions binary prime primePlan).2.2.1.le
  have advice := Parser.read_advice repr shape setup publicCount binaryRequest metadata request initial proof H
    (G).batchingIndex.val (G).batchingIndex.isLt.le (by
      exact le_trans (Nat.le_add_right _ _) window)
  have U := Parser.read_packingU repr shape setup publicCount binaryRequest metadata request initial proof H
    (G).batchingIndex.val (G).batchingIndex.isLt.le (by change (128 : ℕ) ≠ 1; decide) (positions binary prime primePlan).2.2.2.le
  have A := Parser.read_packingA repr shape setup publicCount binaryRequest metadata request initial proof H
    (G).batchingIndex.val (G).batchingIndex.isLt.le le_rfl
  rw [packing_pair binary prime primePlan proof] at U A
  have rank := ((E).chain initial).point_rank proof H (G).batchingIndex.isLt.le
  change Input.rank point = (G).batchingIndex.val at rank
  dsimp only [Parser.start] at messages
  unfold ApplicationPrefix.readBinary
  simp only [Option.map_id]
  erw [rescale,convert,mu,advice]
  simp only [Option.bind_eq_bind,Option.bind_some,MdocAdvice.decode]
  erw [U,packed,A]
  simp only [Option.bind_some,Option.map_some]
  erw [if_pos (by erw [rank]; exact window),messages]
  exact ⟨_,rfl,rfl⟩

variable [Fintype B]

theorem decode_success
    (primitive : Current.Adapter.Mdoc.generatorCheck (MdocRuntime.polynomialX binary.basis) = true)
    (trace : ∀ i, DualPacking.ArtinSchreier.traceF (F := B) (ZMod 2) (proof.body.packing.1 i) = 0) :
    ∃ system, ApplicationPrefix.decodeChecked binary.description prime (MdocRuntime.field_card binary.basis)
      (MdocRuntime.polynomialX binary.basis) quotient_bound (packing_degree binary prime primePlan) id id samples.binary samples.binaryNonzero
      samples.prime samples.primeNonzero samples.conversion MdocAdvice.decode samples.fallback point past = some system := by
  obtain ⟨native,hprime⟩ := prime_success binary prime primePlan repr shape setup publicCount binaryRequest metadata request initial proof H samples
  obtain ⟨data,hbinary,hU⟩ := binary_success binary prime primePlan repr shape setup publicCount binaryRequest metadata request initial proof H samples
    native (MdocRuntime.polynomialX binary.basis^Current.Adapter.Mdoc.generatorExponent)
  unfold ApplicationPrefix.decodeChecked
  erw [hprime]
  change ∃ system,
    (ApplicationPrefix.readBinary binary.description native (MdocRuntime.polynomialX binary.basis^Current.Adapter.Mdoc.generatorExponent)
      (packing_degree binary prime primePlan) id id samples.binary samples.binaryNonzero
      samples.primeNonzero samples.conversion MdocAdvice.decode samples.fallback point past).bind
      (fun data => ApplicationSetup.decodeChecked binary.description prime native (MdocRuntime.field_card binary.basis)
        (MdocRuntime.polynomialX binary.basis) quotient_bound data) = some system
  erw [hbinary]
  change ∃ system, ApplicationSetup.decodeChecked binary.description prime native (MdocRuntime.field_card binary.basis)
    (MdocRuntime.polynomialX binary.basis) quotient_bound data = some system
  unfold ApplicationSetup.decodeChecked
  erw [dif_pos primitive]
  unfold ApplicationSetup.decode
  erw [dif_pos (by rw [hU]; exact trace)]
  exact ⟨_,rfl⟩

theorem decode_requested (bits : Fin binary.nPublic → Bool) (inputs : Fin prime.nPublic → P)
    (primitive : Current.Adapter.Mdoc.generatorCheck (MdocRuntime.polynomialX binary.basis) = true)
    (trace : ∀ i, DualPacking.ArtinSchreier.traceF (F := B) (ZMod 2) (proof.body.packing.1 i) = 0) :
    ∃ system, ApplicationPrefix.decodeChecked (RuntimeAdaptive.binaryWithBits binary.description bits)
      (RuntimeAdaptive.primeWithInputs prime inputs) (MdocRuntime.field_card binary.basis)
      (MdocRuntime.polynomialX binary.basis) quotient_bound (packing_degree binary prime primePlan) id id
      samples.binary samples.binaryNonzero samples.prime samples.primeNonzero samples.conversion MdocAdvice.decode
      samples.fallback point past = some system :=
  decode_success { binary with publicBits := bits } (RuntimeAdaptive.primeWithInputs prime inputs)
    primePlan repr shape setup publicCount binaryRequest metadata request initial proof H samples primitive trace

end LfzkV2.Current.ZeroKnowledge.Frontend.ParserApplication
