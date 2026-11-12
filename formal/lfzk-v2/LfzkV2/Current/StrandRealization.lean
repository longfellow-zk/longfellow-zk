import LfzkV2.Current.StrandReplay
import LfzkV2.Current.StrandExecution
import LfzkV2.Current.StrandCutObservation
import LfzkV2.Current.StrandWindow
import LfzkV2.Current.StrandAcceptedPath

/-! The actual shared-SHA runtime as a transcript realization. Its physical
answer is a digest and one whole counter row. Reindexing the used role block
into ideal algebraic answers is separate from this exact execution transport. -/
noncomputable section
namespace LfzkV2.Current.StrandRealization
open Application ApplicationSetup CanonicalPrefix QueryRuntime
open Finset Merkle.RandomOracle TranscriptV2
open scoped Classical

variable {g : Geometry} {fields : Fields} {Advice C B Salt Enc : Type}
variable [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable [∀ side, Fintype (fields side)] [Fintype Advice]
variable {shared maskBits adviceBits k s n t blocks : ℕ}
local notation "N" => ZMod Adapter.Mdoc.primeOrder
variable (binary : BinaryPublic B shared maskBits adviceBits) (prime : PrimePublic N shared)
variable (P : FieldBackend B k s n t) (R : FieldBackend N k s n t)
variable (repr : ProofBodyCodec.Representations fields Advice)
variable (shape : WireBlocks.Shape g fields) (setup : FingerprintPrefix.Setup)
variable (cfg : RuntimeVerifier.Public (g := g) binary prime P R (fields := fields) (Advice := Advice)
  (Base := CanonicalRequest.Base repr shape setup binary.nPublic)
  (Key := FingerprintPrefix.Key binary.nPublic) (C := C) (Salt := Salt))
variable (binaryCount : shape.binaryPublic = binary.nPublic)
variable (metadata : CanonicalRequest.Metadata (Advice := Advice) (C := C) shape binary.nPublic)
variable (bodyFits : ProofBodyBounds.bodyBound repr g ≤ CanonicalPrefix.maxLength)
variable (fits : g.roles.length < 2^64)
variable (sample : QueryRuntime.Runtime.Point repr shape setup binary.nPublic →
  Tree Strand.Word Digest (Option C) blocks)
variable (primeCount : shape.primePublic = prime.nPublic)
variable (draw : C → RuntimeVerifier.RawSamples binary prime P R
  (CanonicalRuntime.wirePublic binary prime P R repr shape setup cfg))
variable [Inhabited Salt]
variable [Inhabited (RuntimeVerifier.Family binary prime P R
  (CanonicalRuntime.wirePublic binary prime P R repr shape setup cfg)).Leaf]
variable (codec : Merkle.Indexed.Codec Salt (RuntimeVerifier.Family binary prime P R
  (CanonicalRuntime.wirePublic binary prime P R repr shape setup cfg)).Leaf Digest Enc)
variable (merkleInput : Enc → Bytes)
variable {fuel : ℕ} (program : Tree Bytes Digest (CanonicalRuntime.Output (Advice := Advice) binary shape) fuel)

local notation "W" => CanonicalRuntime.wirePublic binary prime P R repr shape setup cfg
local notation "Earlier" => CanonicalRuntime.earlier binary prime P R repr shape setup cfg binaryCount metadata
local notation "M" => RuntimeAdaptiveVerifier.chain binary prime P R (W) (Earlier)
local notation "Value" => QueryRuntime.Runtime.Value repr shape setup binary.nPublic
local notation "Output" => CanonicalRuntime.Output (Advice := Advice) binary shape
local notation "bodyCodec" => ProofBodyCodec.codec repr g
local notation "schema" => StrandRuntime.Runtime.schema repr shape setup binary.nPublic
local notation "history" => StrandRuntime.history bodyCodec
local notation "ordinaryOracle" => TranscriptV2.StrandVerifier.oracle history sample cfg.fallback
local notation "fullReplay" => StrandAuthentication.replay binary prime P R (W) (Earlier) bodyCodec sample codec merkleInput

private def rootNode : Strand.OtherPoint := TranscriptV2.Strand.History.nodePoint (.root [])

/-- Cover every query branch and every canonical node, retaining one fixed
fallback address solely to make the finite address compiler total. -/
def other : Finset Strand.OtherPoint := by
  letI : Fintype Value := Fintype.ofInjective
    (QueryRuntime.Runtime.toPoint repr shape setup binary.nPublic)
    (QueryRuntime.Runtime.toPoint_injective repr shape setup binary.nPublic fits)
  exact insert rootNode (StrandWindow.support (schema) (program.bind fullReplay))

local notation "O" => other binary prime P R repr shape setup cfg binaryCount metadata fits sample codec merkleInput program
local notation "Node" => StrandWindow.Node (O)
local notation "Raw" => StrandWindow.Point (O)

def fallback : Node := ⟨rootNode,Finset.mem_insert_self _ _⟩
local notation "fallbackNode" => fallback binary prime P R repr shape setup cfg binaryCount metadata fits sample codec merkleInput program
local notation "decodeRaw" => StrandWindow.decode (O) fallbackNode
local notation "bytes" => StrandWindow.Node.bytes (other := O)
local notation "context" => QueryRuntime.Runtime.key repr shape setup binary.nPublic
local notation "Name" => StrandSearch.Name Node Value
local notation "Answer" => StrandCoupling.Sample Digest Strand.Word
local notation "compiled" => mapQueries decodeRaw program
local notation "compiledReplay" => fun output : Output => mapQueries decodeRaw (fullReplay output)
local notation "searchTree" => StrandReplay.search (schema) bytes compiled
local notation "resumeTree" => StrandReplay.resume (schema) bytes compiledReplay

/-- The finite raw table is the complete SHA marginal used by the program.
Its complement fallback cannot change a covered raw observation. -/
def rawSHA (G : Raw → Digest) : Bytes → Digest := G ∘ decodeRaw

/-- Erase finite address names once, at the execution boundary. The
original table, all extraction cuts and the verifier trace use physical
SHA inputs thereafter. No application proof needs a second view type. -/
def viewMap {Result : Type} (view : (Output × List (Raw × Digest)) ×
    (Result × List (Raw × Digest))) :
    Protocol.Execution.View Output Result (FingerprintPrefix.Key binary.nPublic) where
  original := (view.1.1,view.1.2.map fun qa => (StrandWindow.encode qa.1,qa.2))
  verifier := (view.2.1,view.2.2.map fun qa => (StrandWindow.encode qa.1,qa.2))
  cuts key := StrandCutObservation.byteCut (schema) bytes context key view.1.2

/-- Actual proof submission, all context cuts, and full verification trace. -/
def rawView (G : Raw → Digest) :=
  viewMap binary prime P R repr shape setup cfg binaryCount metadata fits sample codec merkleInput program
    ((compiled).run G,(compiledReplay ((compiled).run G).1).run G)

/-- Completion of the final cache supplies the one raw oracle used by
both the original search and the complete verifier replay. -/
def completion (H : Name → Answer) : Raw → Digest :=
  StrandCutObservation.completion (schema) bytes compiled compiledReplay H

/-- Grouping oracle answers changes probability coordinates only. It
returns the same raw execution observation; it does not construct another
verifier or another extraction view. -/
def observe (_ : (StrandReplay.Cut Node Output)) (H : Name → Answer) :=
  rawView binary prime P R repr shape setup cfg binaryCount metadata fits sample codec merkleInput program
    (completion binary prime P R repr shape setup cfg binaryCount metadata fits sample codec merkleInput program H)

local notation "completed" => completion binary prime P R repr shape setup cfg binaryCount metadata fits sample codec merkleInput program
local notation "SHAof" => rawSHA binary prime P R repr shape setup cfg binaryCount metadata fits sample codec merkleInput program
local notation "rawObservation" => rawView binary prime P R repr shape setup cfg binaryCount metadata fits sample codec merkleInput program
local notation "namedObservation" => observe binary prime P R repr shape setup cfg binaryCount metadata fits sample codec merkleInput program

theorem rawSHA_node (G : Raw → Digest) (raw : Node) :
    SHAof G raw.val.val = G (.inl raw) :=
  congrArg G (StrandWindow.decode_encode (O) fallbackNode (.inl raw))

theorem rawSHA_prf (G : Raw → Digest) (key : Strand.PrfKey) (counter : Strand.Word) :
    SHAof G (Strand.Input.prf key.1 key.2 counter).encode = G (.inr (key,counter)) :=
  congrArg G (StrandWindow.decode_encode (O) fallbackNode (.inr (key,counter)))

/-- This equality includes all cuts and the entire authentication trace.
Its raw completion is computed from the execution's own final cache. -/
theorem observe_source (H : Name → Answer) :
    rawObservation (completed H) = namedObservation ((searchTree).run H).1 H := rfl

private theorem compiled_output (G : Raw → Digest) :
    ((compiled).run G).1 = (program.run (SHAof G)).1 := by
  simp only [run_mapQueries,rawSHA]

/-- The finite address window covers both the original program and every
branch of its actual verifier continuation. This is address coverage only;
it does not charge the continuation to the adversary's query budget. -/
theorem input_represented (input : Bytes)
    (member : input ∈ OracleWindow.queries (program.bind fullReplay)) :
    StrandWindow.encode (decodeRaw input) = input := by
  apply StrandWindow.encode_decode (O) fallbackNode input
  intro point equal
  apply Finset.mem_insert_of_mem
  apply Finset.mem_union_left
  apply (StrandWindow.mem_complement _ point).mpr
  rwa [equal]

/-- Finite address restriction preserves the actual verifier continuation,
including every Merkle and final-seal query, on the submitted proof. -/
theorem replay_actual (G : Raw → Digest) :
    (((compiledReplay ((compiled).run G).1).run G).1,
      ((compiledReplay ((compiled).run G).1).run G).2.map (fun qa => (StrandWindow.encode qa.1,qa.2))) =
        (fullReplay (program.run (SHAof G)).1).run (SHAof G) := by
  rw [compiled_output binary prime P R repr shape setup cfg binaryCount metadata fits sample codec merkleInput program G,
    run_mapQueries]
  apply Prod.ext
  · rfl
  · simp only [List.map_map,Function.comp_def]
    have names : ∀ qa ∈ ((fullReplay (program.run (SHAof G)).1).run (SHAof G)).2,
        (StrandWindow.encode (decodeRaw qa.1),qa.2) = qa := by
      intro qa member
      have queried : qa.1 ∈ OracleWindow.queries (program.bind fullReplay) :=
        OracleWindow.trace_mem_queries (program.bind fullReplay) (SHAof G) qa (by
          rw [Tree.run_bind]
          exact List.mem_append_right _ member)
      have address := input_represented binary prime P R repr shape setup cfg binaryCount metadata
        fits sample codec merkleInput program qa.1 queried
      exact Prod.ext address rfl
    exact (List.map_congr_left names).trans (List.map_id _)

local notation "actualDecision" => StrandExecution.decision binary prime P R (W) (Earlier) bodyCodec sample codec merkleInput
  (CanonicalRequest.hashPublic binary.nPublic)
  (CanonicalRuntime.decodePrimePublic binary prime P R repr shape setup cfg primeCount) draw
local notation "actualVerify" => StrandVerifier.verify binary prime P R (W) (Earlier) bodyCodec sample
  (CanonicalRequest.hashPublic binary.nPublic)
  (CanonicalRuntime.decodePrimePublic binary prime P R repr shape setup cfg primeCount) draw codec

/-- The accepting predicate is exactly the existing verifier's decision,
not a relaxed semantic predicate on the reconstructed transcript. -/
theorem decision_actual (G : Raw → Digest) :
    actualDecision (rawObservation G) = actualVerify (SHAof G) merkleInput (program.run (SHAof G)).1 := by
  unfold rawView viewMap
  rw [replay_actual binary prime P R repr shape setup cfg binaryCount metadata fits sample codec merkleInput program G,
    compiled_output binary prime P R repr shape setup cfg binaryCount metadata fits sample codec merkleInput program G]
  exact StrandExecution.decision_actual binary prime P R (W) (Earlier) bodyCodec sample codec merkleInput
    (CanonicalRequest.hashPublic binary.nPublic)
    (CanonicalRuntime.decodePrimePublic binary prime P R repr shape setup cfg primeCount) draw _ _ _ _

def locate (value : Value) : Node := by
  letI : Fintype Value := Fintype.ofInjective
    (QueryRuntime.Runtime.toPoint repr shape setup binary.nPublic)
    (QueryRuntime.Runtime.toPoint_injective repr shape setup binary.nPublic fits)
  refine ⟨TranscriptV2.Strand.History.nodePoint ((schema).encode value),?_⟩
  apply Finset.mem_insert_of_mem
  apply Finset.mem_union_right
  exact StrandWindow.mem_canonical (schema) value

local notation "nodeOf" => locate binary prime P R repr shape setup cfg binaryCount metadata fits sample codec merkleInput program

/-- Locating a logical input preserves its actual strand bytes. This
supplies the deterministic codec identity used by Merkle-domain separation. -/
theorem locate_bytes (value : Value) :
    bytes (nodeOf value) = ((schema).encode value).input.encode := rfl

/-- Canonical runtime prefixes use their actual finite node names. Every
other raw name remains an auxiliary query under the codec's injective tag. -/
def queryCodec : ByteOracleTransport.Codec (QueryRuntime.Runtime.Point repr shape setup binary.nPublic) Name
    (QueryRuntime.Runtime.Canonical repr shape setup binary.nPublic) :=
  StrandRuntime.Runtime.pointCodec repr shape setup binary.nPublic fits nodeOf

local notation "names" => queryCodec binary prime P R repr shape setup cfg binaryCount metadata fits sample codec merkleInput program

theorem queryCodec_label (name : Name)
    (point : {point : QueryRuntime.Runtime.Point repr shape setup binary.nPublic //
      QueryRuntime.Runtime.Canonical repr shape setup binary.nPublic point})
    (decoded : (names).decode name = some point) :
    StrandCut.label context name = some point.val.context := by
  cases name with
  | inr _ => cases decoded
  | inl entry =>
      rcases entry with ⟨raw,value⟩
      cases value with
      | none => cases decoded
      | some value =>
          simp only [queryCodec,StrandRuntime.Runtime.pointCodec] at decoded
          split_ifs at decoded with same
          cases Option.some.inj decoded
          exact congrArg some (QueryRuntime.Runtime.toPoint_context repr shape setup binary.nPublic value).symm

/-- Reached points are obtained from the canonical runtime decoder. They
are not values or histories supplied by a prover or an execution record. -/
def path (_ : StrandReplay.Cut Node Output) (H : Name → Answer) (i : ℕ) : Name :=
  let SHA := SHAof (completed H)
  let value := StrandAcceptedPath.value binary prime P R repr shape setup cfg binaryCount metadata bodyFits fits sample
    (program.run SHA).1 SHA i
  .inl (nodeOf value,some value)

/-- Tagging the recovered named path gives the existing runtime's actual
replay inputs, including the final node. No path correspondence is assumed. -/
theorem tag_path (cut : StrandReplay.Cut Node Output) (H : Name → Answer) (index : ℕ)
    (within : index ≤ g.roles.length) :
    (names).tag (path binary prime P R repr shape setup cfg binaryCount metadata bodyFits fits sample codec merkleInput program cut H index) =
      .inl ((M).point (program.run (SHAof (completed H))).1 (ordinaryOracle (SHAof (completed H))) index) := by
  unfold path
  simp only [queryCodec,ByteOracleTransport.Codec.tag,StrandRuntime.Runtime.pointCodec,if_true]
  exact congrArg Sum.inl (StrandAcceptedPath.value_point binary prime P R repr shape setup cfg binaryCount metadata
    bodyFits fits sample _ _ index within)

/-- Only original collisions and missing original strand nodes are
exceptional. Seal validity restricts this event to proofs which could pass
finalization; the missing-query bound accounts for a guessed seal separately.
Fresh verifier-replay collisions are not excluded. -/
def rawException (G : Raw → Digest) : Prop :=
  let SHA := SHAof G
  let output := (program.run SHA).1
  StrandVerifier.finalSeal binary prime P R (W) (Earlier) bodyCodec sample output SHA = output.proof.finalSeal ∧
    (¬Merkle.MH.CollisionFree (program.run SHA).2 ∨
      ¬∀ i ≤ g.roles.length, Merkle.QueryTable.Known (program.run SHA).2
        (history ((M).point output (ordinaryOracle SHA) i)).input.encode)


/-- The named experiment uses exactly the same event on its own completed
execution; the probability transfer below uses observations, not an assumed
uniform distribution on all coordinates of that completion. -/
def exception (H : Name → Answer) : Prop :=
  rawException binary prime P R repr shape setup cfg binaryCount metadata fits
    sample codec merkleInput program (completed H)

/-- One auxiliary-query charge shares the original search budget. Verifier
replay contributes only to the explicit replay exception. -/
def speculation (H : Name → Answer) : ℚ :=
  DigestProjection.charge (StrandSearch.claims bytes) searchTree H

private theorem covers :
    StrandWindow.complement (OracleWindow.queries (program.bind fullReplay)) ⊆ (O) := by
  intro raw member
  exact Finset.mem_insert_of_mem (Finset.mem_union_left _ member)

private theorem covers_original :
    StrandWindow.complement (OracleWindow.queries program) ⊆ (O) := by
  intro raw member
  apply covers binary prime P R repr shape setup cfg binaryCount metadata fits sample codec merkleInput program
  apply (StrandWindow.mem_complement _ _).mpr
  exact OracleWindow.queries_bind_left program fullReplay ((StrandWindow.mem_complement _ _).mp member)

/-- The finite representation preserves the original query table itself,
including repeated queries and their order. -/
theorem original_actual (G : Raw → Digest) :
    (((compiled).run G).1,
      ((compiled).run G).2.map (fun qa => (StrandWindow.encode qa.1,qa.2))) =
        program.run (SHAof G) :=
  StrandWindow.decode_run (O) fallbackNode program
    (covers_original binary prime P R repr shape setup cfg binaryCount metadata fits
      sample codec merkleInput program) G

/-- The public observation is precisely the original raw execution and
the continuation that verifies its submitted proof. Finite address names
are confined to the transport proof above. -/
theorem rawView_actual (G : Raw → Digest) :
    rawObservation G =
      { original := program.run (SHAof G)
        verifier := (fullReplay (program.run (SHAof G)).1).run (SHAof G)
        cuts := (rawObservation G).cuts } := by
  apply Protocol.Execution.View.ext
  · exact original_actual binary prime P R repr shape setup cfg binaryCount metadata fits
      sample codec merkleInput program G
  · exact replay_actual binary prime P R repr shape setup cfg binaryCount metadata fits
      sample codec merkleInput program G
  · rfl

/-- Grouping preserves the original extraction cut, expressed in the same
physical byte addresses as the verifier's observation. -/
theorem observe_cut (H : Name → Answer) (key : FingerprintPrefix.Key binary.nPublic) :
    (namedObservation ((searchTree).run H).1 H).cuts key =
      (StrandCut.trace context searchTree H key).map (fun qa => (bytes qa.1,qa.2)) := by
  exact congrArg (List.map (fun qa : Node × Digest => (bytes qa.1,qa.2)))
    (StrandCutObservation.completion_cut (schema) bytes context compiled compiledReplay H key)

/-- Consumers use this one identity for the physical and grouped
experiments. They do not rebuild a verifier or decode a second execution. -/
theorem observe_actual (H : Name → Answer) :
    namedObservation ((searchTree).run H).1 H =
      { original := program.run (SHAof (completed H))
        verifier := (fullReplay (program.run (SHAof (completed H))).1).run (SHAof (completed H))
        cuts := fun key => (StrandCut.trace context searchTree H key).map (fun qa => (bytes qa.1,qa.2)) } := by
  rw [← observe_source,rawView_actual]
  congr 1
  funext key
  exact observe_cut binary prime P R repr shape setup cfg binaryCount metadata fits
    sample codec merkleInput program H key

/-- Decoding is a projection of the same execution that determines
acceptance. The extraction proof need not re-establish this correspondence. -/
theorem decoded_actual (G : Raw → Digest) :
    StrandExecution.decoded binary prime P R (W) (Earlier) bodyCodec sample
        (CanonicalRequest.hashPublic binary.nPublic)
        (CanonicalRuntime.decodePrimePublic binary prime P R repr shape setup cfg primeCount) draw
        (rawObservation G) =
      RuntimeAdaptiveVerifier.decode binary prime P R (W) (Earlier)
        (CanonicalRequest.hashPublic binary.nPublic)
        (CanonicalRuntime.decodePrimePublic binary prime P R repr shape setup cfg primeCount) draw
        (program.run (SHAof G)).1 (ordinaryOracle (SHAof G)) := by
  rw [rawView_actual]
  exact StrandExecution.decoded_actual binary prime P R (W) (Earlier) bodyCodec sample codec merkleInput
    (CanonicalRequest.hashPublic binary.nPublic)
    (CanonicalRuntime.decodePrimePublic binary prime P R repr shape setup cfg primeCount) draw _ _ _ _

/-- The exception is observable from the submitted proof, its original
query table, and the terminal verifier state and seal. Reading ancestors
from that terminal state does not perform any additional oracle query. -/
def observedException (original : Output × List (Bytes × Digest))
    (replayed : ((Output × (M).State) × Digest)) : Prop :=
  replayed.2 = original.1.proof.finalSeal ∧
    (¬Merkle.MH.CollisionFree original.2 ∨
      ¬∀ raw ∈ (history ((M).input replayed.1.2)).ancestors,
        Merkle.QueryTable.Known original.2 raw)

theorem rawException_observed (G : Raw → Digest) :
    rawException binary prime P R repr shape setup cfg binaryCount metadata fits
        sample codec merkleInput program G ↔
      observedException binary prime P R repr shape setup cfg binaryCount metadata
        (program.run (SHAof G)) ((fullReplay (program.run (SHAof G)).1).run (SHAof G)).1 := by
  rw [StrandAuthentication.replay_result]
  unfold rawException observedException
  apply and_congr Iff.rfl
  apply or_congr Iff.rfl
  apply not_congr
  constructor
  · intro known
    exact StrandRuntime.replay_ancestors bodyCodec (M) cfg.initialLink
      (fun _ => rfl) (fun _ => rfl) _ _ _ known g.roles.length le_rfl
  · intro known i within
    exact known _ (StrandRuntime.replay_node_mem bodyCodec (M) cfg.initialLink
      (fun _ => rfl) _ _ g.roles.length i le_rfl within)

/-- Exact transport of the original-query exception. The only observed
queries counted here are those in the submitted proof's original search;
verifier replay supplies the terminal state but never enlarges that table. -/
theorem exception_law :
    letI : Fintype Value := Fintype.ofInjective
      (QueryRuntime.Runtime.toPoint repr shape setup binary.nPublic)
      (QueryRuntime.Runtime.toPoint_injective repr shape setup binary.nPublic fits)
    letI : Fintype Name := inferInstance
    letI : Fintype Answer := inferInstance
    Bcs.FiniteProbability.density (rawException binary prime P R repr shape setup cfg
      binaryCount metadata fits sample codec merkleInput program) =
    Bcs.FiniteProbability.density (exception binary prime P R repr shape setup cfg
      binaryCount metadata fits sample codec merkleInput program) := by
  letI : Fintype Value := Fintype.ofInjective
    (QueryRuntime.Runtime.toPoint repr shape setup binary.nPublic)
    (QueryRuntime.Runtime.toPoint_injective repr shape setup binary.nPublic fits)
  letI : Fintype Name := inferInstance
  letI : Fintype Answer := inferInstance
  let event : (Output × List (Raw × Digest)) ×
      (((Output × (M).State) × Digest) × List (Raw × Digest)) → Prop :=
    fun view => observedException binary prime P R repr shape setup cfg binaryCount metadata
    (view.1.1,view.1.2.map (fun qa : Raw × Digest => (StrandWindow.encode qa.1,qa.2))) view.2.1
  have represented (G : Raw → Digest) :
      rawException binary prime P R repr shape setup cfg binaryCount metadata fits
          sample codec merkleInput program G ↔
        event ((compiled).run G,(compiledReplay ((compiled).run G).1).run G) := by
    dsimp only [event]
    rw [original_actual binary prime P R repr shape setup cfg binaryCount metadata fits
      sample codec merkleInput program G,
      congrArg Prod.fst (replay_actual binary prime P R repr shape setup cfg binaryCount metadata fits
        sample codec merkleInput program G)]
    exact rawException_observed binary prime P R repr shape setup cfg binaryCount metadata fits
      sample codec merkleInput program G
  exact (Bcs.FiniteProbability.density_congr represented).trans
    ((StrandCutObservation.completion_law (schema) bytes compiled compiledReplay event).trans
      (Bcs.FiniteProbability.density_congr (fun H => (represented (completed H)).symm)))

/-- Completing the final cache preserves every answer from both original
search and verifier replay. It supplies no new correspondence assumption. -/
theorem completion_matches (H : Name → Answer) :
    ((((searchTree).bind resumeTree).run H).1).1.2.Matches (completed H) := by
  unfold StrandReplay.resume
  simpa only [completion,StrandReplay.search] using
    (StrandCutObservation.completion_matches (schema) bytes compiled compiledReplay H)

/-- The completed physical execution exposes exactly its queried non-PRF
nodes. This supplies Merkle authentication visibility from actual replay,
while retaining the original byte inputs and their actual SHA answers. -/
theorem full_node_observations (H : Name → Answer) :
    (∀ raw logical answer,
      ((.inl (raw,logical),answer) : Name × Answer) ∈ (((searchTree).bind resumeTree).run H).2 →
      SHAof (completed H) raw.val.val = answer.1 ∧
        raw.val.val ∈ seen (program.bind fullReplay) (SHAof (completed H))) ∧
    (∀ address, address ∈ seen (program.bind fullReplay) (SHAof (completed H)) →
      Strand.decodePrf address = none →
      ∃ raw logical answer, raw.val.val = address ∧
        ((.inl (raw,logical),answer) : Name × Answer) ∈ (((searchTree).bind resumeTree).run H).2) := by
  let G := completed H
  have observations := StrandReplay.node_observations (schema) bytes compiled compiledReplay H G
    (completion_matches binary prime P R repr shape setup cfg binaryCount metadata fits sample codec merkleInput program H)
  constructor
  · intro raw logical answer member
    obtain ⟨same,present⟩ := observations.1 raw logical answer member
    refine ⟨(rawSHA_node binary prime P R repr shape setup cfg binaryCount metadata fits sample codec merkleInput program G raw).trans same,?_⟩
    exact StrandWindow.decode_seen (O) fallbackNode (program.bind fullReplay)
      (covers binary prime P R repr shape setup cfg binaryCount metadata fits sample codec merkleInput program) G (.inl raw)
      (by simpa only [mapQueries_bind] using present)
  · intro address member nonPrf
    obtain ⟨⟨input,digest⟩,present,same⟩ := List.mem_map.mp (List.mem_toFinset.mp member)
    change input = address at same
    subst input
    have supported : (⟨address,nonPrf⟩ : Strand.OtherPoint) ∈ (O) :=
      covers binary prime P R repr shape setup cfg binaryCount metadata fits sample codec merkleInput program
        ((StrandWindow.mem_complement _ _).mpr
          (OracleWindow.trace_mem_queries (program.bind fullReplay) (SHAof G) (address,digest) present))
    let raw : Node := ⟨⟨address,nonPrf⟩,supported⟩
    have named : (.inl raw : Raw) ∈ seen ((compiled).bind compiledReplay) G := by
      rw [← mapQueries_bind]
      simp only [seen,Bcs.TotalOracle.queried,run_mapQueries,List.map_map]
      apply List.mem_toFinset.mpr
      apply List.mem_map.mpr
      exact ⟨(address,digest),present,StrandWindow.decode_encode (O) fallbackNode (.inl raw)⟩
    obtain ⟨logical,answer,origin⟩ := observations.2 raw named
    exact ⟨raw,logical,answer,rfl,origin⟩

/-- Byte-level original node queries and their named sources agree in
both directions. Reserving a PRF row does not count as another node query. -/
theorem original_node_observations (H : Name → Answer) :
    (∀ raw logical answer,
      ((.inl (raw,logical),answer) : Name × Answer) ∈ ((searchTree).run H).2 →
      SHAof (completed H) (bytes raw) = answer.1 ∧ bytes raw ∈ seen program (SHAof (completed H))) ∧
    (∀ entry ∈ (program.run (SHAof (completed H))).2, Strand.decodePrf entry.1 = none →
      ∃ raw logical answer, (bytes raw,answer.1) = entry ∧
        ((.inl (raw,logical),answer) : Name × Answer) ∈ ((searchTree).run H).2) := by
  let G := completed H
  let SHA := SHAof G
  have agreement := StrandReplay.original_matches (schema) bytes compiled compiledReplay H G
    (completion_matches binary prime P R repr shape setup cfg binaryCount metadata fits sample codec merkleInput program H)
  have source := StrandSearch.searchState_source (schema) bytes (recordTrace compiled) StrandCoupling.Cache.empty [] H G agreement
  constructor
  · intro raw logical answer member
    refine ⟨(rawSHA_node binary prime P R repr shape setup cfg binaryCount metadata fits sample codec merkleInput program G raw).trans
      (source.2 raw logical answer member),?_⟩
    apply StrandWindow.decode_seen (O) fallbackNode program
      (covers_original binary prime P R repr shape setup cfg binaryCount metadata fits sample codec merkleInput program) G (.inl raw)
    simpa only [seen,List.mem_toFinset,Bcs.TotalOracle.queried,run_recordTrace] using
      StrandSearch.searchState_node_queried (schema) bytes (recordTrace compiled) StrandCoupling.Cache.empty [] H G agreement raw logical answer member
  · rintro ⟨address,digest⟩ present nonPrf
    have supported : (⟨address,nonPrf⟩ : Strand.OtherPoint) ∈ (O) :=
      covers_original binary prime P R repr shape setup cfg binaryCount metadata fits sample codec merkleInput program
        ((StrandWindow.mem_complement _ _).mpr
          (OracleWindow.trace_mem_queries program SHA (address,digest) present))
    let raw : Node := ⟨⟨address,nonPrf⟩,supported⟩
    have named : (.inl raw : Raw) ∈ seen compiled G := by
      rw [TranscriptV2.seen_mapQueries]
      exact Finset.mem_image.mpr ⟨address,List.mem_toFinset.mpr (List.mem_map_of_mem (f := Prod.fst) present),
        StrandWindow.decode_encode (O) fallbackNode (.inl raw)⟩
    obtain ⟨logical,answer,origin⟩ := StrandReplay.original_node_origin (schema) bytes compiled H G agreement raw named
    have agrees := (rawSHA_node binary prime P R repr shape setup cfg binaryCount metadata fits
      sample codec merkleInput program G raw).trans (source.2 raw logical answer origin)
    exact ⟨raw,logical,answer,Prod.ext rfl
      (agrees.symm.trans (Tree.trace_sound program SHA (address,digest) present).symm),origin⟩

/-- A node already queried by the original search retains its actual
digest when the verifier extends and finally completes that search cache. -/
theorem node_answer (H : Name → Answer) (raw : Node) (value : Option Value)
    (member : ((.inl (raw,value),H (.inl (raw,value))) : Name × Answer) ∈ ((searchTree).run H).2) :
    completed H (.inl raw) = (H (.inl (raw,value))).1 :=
  StrandReplay.node_answer (schema) bytes compiled compiledReplay H (completed H)
    (completion_matches binary prime P R repr shape setup cfg binaryCount metadata fits sample codec merkleInput program H)
    raw value _ member

/-- Finite addresses in the original search represent original byte
queries. No verifier replay query enters this collision scope. -/
theorem original_finite_collision_free (H : Name → Answer)
    (free : Merkle.MH.CollisionFree (program.run (SHAof (completed H))).2) :
    ∀ a, (.inl a : Raw) ∈ seen compiled (completed H) →
      ∀ b, (.inl b : Raw) ∈ seen compiled (completed H) →
        completed H (.inl a) = completed H (.inl b) → a = b := by
  intro a ha b hb same
  let SHA := SHAof (completed H)
  have knownA := StrandWindow.decode_seen (O) fallbackNode program
    (covers_original binary prime P R repr shape setup cfg binaryCount metadata fits sample codec merkleInput program)
    (completed H) (.inl a) ha
  have knownB := StrandWindow.decode_seen (O) fallbackNode program
    (covers_original binary prime P R repr shape setup cfg binaryCount metadata fits sample codec merkleInput program)
    (completed H) (.inl b) hb
  apply Subtype.ext
  apply Subtype.ext
  apply Merkle.QueryTable.equal_of_known (program.run SHA).2 SHA
    (fun qa member => (Tree.trace_sound program SHA qa member).symm) free a.val.val b.val.val
    ((Merkle.QueryTable.known_run_iff program SHA _).mpr knownA)
    ((Merkle.QueryTable.known_run_iff program SHA _).mpr knownB)
  exact (rawSHA_node binary prime P R repr shape setup cfg binaryCount metadata fits sample codec merkleInput program
    (completed H) a).trans (same.trans
      (rawSHA_node binary prime P R repr shape setup cfg binaryCount metadata fits sample codec merkleInput program (completed H) b).symm)

/-- Uniform raw tables and named grouped tables preserve the entire view,
including the precise extraction cut and the full authentication replay. -/
theorem observation_law :
    letI : Fintype Value := Fintype.ofInjective
      (QueryRuntime.Runtime.toPoint repr shape setup binary.nPublic)
      (QueryRuntime.Runtime.toPoint_injective repr shape setup binary.nPublic fits)
    letI : Fintype Name := inferInstance
    letI : Fintype Answer := inferInstance
    ∀ event : _ → Prop,
    Bcs.FiniteProbability.density (fun G : Raw → Digest => event (rawView binary prime P R repr shape setup cfg
      binaryCount metadata fits sample codec merkleInput program G)) =
    Bcs.FiniteProbability.density (fun H : Name → Answer => event (observe binary prime P R repr shape setup cfg
      binaryCount metadata fits sample codec merkleInput program ((searchTree).run H).1 H)) := by
  letI : Fintype Value := Fintype.ofInjective
    (QueryRuntime.Runtime.toPoint repr shape setup binary.nPublic)
    (QueryRuntime.Runtime.toPoint_injective repr shape setup binary.nPublic fits)
  letI : Fintype Name := inferInstance
  letI : Fintype Answer := inferInstance
  intro event
  exact StrandCutObservation.completion_law (schema) bytes compiled compiledReplay
    (fun view => event (viewMap binary prime P R repr shape setup cfg binaryCount metadata fits
      sample codec merkleInput program view))


end LfzkV2.Current.StrandRealization
