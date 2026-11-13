import LfzkV2.Current.StrandMerkleBounds
import LfzkV2.Current.StrandMerkleRealization
import LfzkV2.Current.Soundness.RecoveredPath
import LfzkV2.Current.StrandSearchBudget
import Bcs.FiniteProbability

/-! An accepted execution either supplies the ordered transcript and its
authenticated columns or exhibits a hash event. Both arguments use the
same original query log and the same extraction cut. -/
noncomputable section
namespace LfzkV2.Current.Soundness.Recovery
open Application ApplicationSetup CanonicalPrefix QueryRuntime
open Finset Merkle Merkle.Indexed Merkle.RandomOracle TranscriptV2 Bcs.FiniteProbability
open StrandMerkleMissingQueries
open scoped Classical

def hashCorrection (queries rounds columns : ℕ) : ℚ :=
  (((queries*(queries-1)/2 : ℕ) : ℚ) + rounds + Heap.heapDepth columns + 3)/2^256

variable {g : Geometry} {fields : Fields} {Advice C B : Type}
variable [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable [∀ side, Fintype (fields side)] [Fintype Advice]
variable {shared maskBits adviceBits k s n t blocks : ℕ}
variable [Inhabited (Fin n × MerkleNonce)]
local notation "N" => ZMod Adapter.Mdoc.primeOrder
variable (binary : BinaryPublic B shared maskBits adviceBits) (prime : PrimePublic N shared)
variable (P : FieldBackend B k s n t) (R : FieldBackend N k s n t)
variable (repr : ProofBodyCodec.Representations fields Advice)
variable (shape : WireBlocks.Shape g fields) (setup : FingerprintPrefix.Setup)
variable (cfg : RuntimeVerifier.Public (g := g) binary prime P R (fields := fields) (Advice := Advice)
  (Base := CanonicalRequest.Base repr shape setup binary.nPublic)
  (Key := FingerprintPrefix.Key binary.nPublic) (C := C) (Salt := Fin n × MerkleNonce))
variable (binaryCount : shape.binaryPublic = binary.nPublic)
variable (metadata : CanonicalRequest.Metadata (Advice := Advice) (C := C) shape binary.nPublic)
variable (fits : g.roles.length < 2^64) (columnsFit : n ≤ 2^64)
variable (sample : QueryRuntime.Runtime.Point repr shape setup binary.nPublic →
  Tree Strand.Word Digest (Option C) blocks)
variable (primeCount : shape.primePublic = prime.nPublic)
variable (draw : C → RuntimeVerifier.RawSamples binary prime P R
  (CanonicalRuntime.wirePublic binary prime P R repr shape setup cfg))
variable [leafDefault : Inhabited (Joint.Pair.family (P.indexed cfg.countBinary).participant
  (R.indexed cfg.countPrime).participant).Leaf]
local instance runtimeLeafInhabited : Inhabited (RuntimeVerifier.Family binary prime P R
    (CanonicalRuntime.wirePublic binary prime P R repr shape setup cfg)).Leaf := by
  change Inhabited (Joint.Pair.family (P.indexed cfg.countBinary).participant
    (R.indexed cfg.countPrime).participant).Leaf
  exact leafDefault
local notation "W" => CanonicalRuntime.wirePublic binary prime P R repr shape setup cfg
local notation "First" => FieldBackend.participant (RuntimeVerifier.first binary prime P R (W))
local notation "Second" => FieldBackend.participant (RuntimeVerifier.second binary prime P R (W))
local notation "codec" => MerkleWireCodec.codec (First) (Second) repr
  cfg.binaryField cfg.primeField setup.jointContext columnsFit
local notation "dec" => MerkleWireCodec.decoders (First) (Second) repr
  cfg.binaryField cfg.primeField setup.jointContext columnsFit
local notation "Output" => CanonicalRuntime.Output (Advice := Advice) binary shape
local notation "Earlier" => CanonicalRuntime.earlier binary prime P R repr shape setup cfg binaryCount metadata
local notation "E" => RuntimeAdaptiveVerifier.encodings binary prime P R (W) (Earlier)
local notation "bodyCodec" => ProofBodyCodec.codec repr g
local notation "history" => StrandRuntime.history bodyCodec
local notation "ordinary" => StrandVerifier.oracle binary prime P R (W) bodyCodec sample
local notation "hashPublic" => CanonicalRequest.hashPublic binary.nPublic
local notation "primePublic" => CanonicalRuntime.decodePrimePublic binary prime P R repr shape setup cfg primeCount
local notation "actualDecoded" => Protocol.Observation.decoded binary prime P R (W) (Earlier) bodyCodec sample
  hashPublic primePublic draw
local notation "decision" => Protocol.Observation.decision binary prime P R (W) (Earlier) bodyCodec sample (codec) id hashPublic primePublic draw
local notation "contextOf" => fun (output : Output) => Replay.Encoding.context
  (E (RuntimeAdaptive.Output.request output)) (RuntimeAdaptive.Output.proof output)
local notation "rootOf" => fun (output : Output) => RuntimeVerifier.Public.root (W) (contextOf output)
variable {fuel : ℕ} (program : Tree Bytes Digest (CanonicalRuntime.Output (Advice := Advice) binary shape) fuel)

local notation "O" => Soundness.OracleTransport.other binary prime P R repr shape setup cfg binaryCount metadata
  fits sample (codec) id program
local notation "Raw" => StrandWindow.Point (O)
local notation "Node" => StrandWindow.Node (O)
local notation "fallbackNode" => Soundness.OracleTransport.fallback binary prime P R repr shape setup cfg binaryCount metadata
  fits sample (codec) id program
local notation "decodeRaw" => StrandWindow.decode (O) fallbackNode
local notation "compiled" => mapQueries decodeRaw program
local notation "SHAof" => Soundness.OracleTransport.rawSHA binary prime P R repr shape setup cfg binaryCount metadata
  fits sample (codec) id program
local notation "rawView" => Soundness.OracleTransport.rawView binary prime P R repr shape setup cfg binaryCount metadata
  fits sample (codec) id program
local notation "rawException" => Soundness.OracleTransport.rawException binary prime P R repr shape setup cfg binaryCount metadata
  fits sample (codec) id program

variable {Result : Type}

/-- Disagreement uses the actual decoded opening and the fixed original cut. -/
def openingDisagrees (view : Protocol.Execution.View Output Result (FingerprintPrefix.Key binary.nPublic)) : Prop :=
  ∃ decoded, actualDecoded view = some decoded ∧
    ∃ column ∈ decoded.claim.I, messages (dec) (view.cuts (contextOf view.original.1))
      (rootOf view.original.1) n column ≠ decoded.claim.a column

/-- A prover query outside the cut hit the root or a child named in the cut. -/
def lateMerkleHit {Result : Type} (view : Protocol.Execution.View Output Result (FingerprintPrefix.Key binary.nPublic)) : Prop :=
  OriginalHit (codec) (dec) view.original.2 (view.cuts (contextOf view.original.1)) (rootOf view.original.1)

local notation "disagrees" => openingDisagrees binary prime P R repr shape setup cfg binaryCount metadata
  columnsFit sample primeCount draw
local notation "lateHit" => lateMerkleHit binary prime P R repr shape setup cfg binaryCount metadata columnsFit

variable (fallbackPath : SelectedPath (n := n) (Salt := Fin n × MerkleNonce)
  (M := (Joint.Pair.family (P.indexed cfg.countBinary).participant (R.indexed cfg.countPrime).participant).Leaf)
  (D := Digest) (Enc := Bytes))
variable (independent : CanonicalRequest.ChallengeIndependent shape binary.nPublic metadata)
variable (bindSalt : ∀ key column nonce, cfg.bindSalt key column nonce = (column,nonce))
local notation "M" => RuntimeAdaptiveVerifier.chain binary prime P R (W) (Earlier)

include independent bindSalt in
/-- The raw accepted disagreement event is covered by the existing one-path
argument. Its auxiliary fresh-hit witness stays in the raw experiment. -/
theorem opening_disagreement_cover (G : Raw → Digest) (accepted : decision (rawView G) = true)
    (good : ¬rawException G) (different : disagrees (rawView G)) :
    lateHit (rawView G) ∨
      StrandMerkleBounds.freshHit binary prime P R repr shape setup cfg binaryCount metadata fits
        columnsFit sample program fallbackPath G := by
  let result := (compiled).run G
  have actual := Soundness.OracleTransport.original_actual binary prime P R repr shape setup cfg binaryCount metadata fits
    sample (codec) id program G
  have outputEq : result.1 = (program.run (SHAof G)).1 := congrArg Prod.fst actual
  have traceEq : result.2.map (fun qa => (StrandWindow.encode qa.1,qa.2)) = (program.run (SHAof G)).2 :=
    congrArg Prod.snd actual
  rw [Soundness.OracleTransport.decision_actual binary prime P R repr shape setup cfg binaryCount metadata fits
    sample primeCount draw (codec) id program G] at accepted
  obtain ⟨decoded,decodedAt,checks⟩ := (StrandVerifier.verify_true_iff binary prime P R (W) (Earlier)
    bodyCodec sample hashPublic primePublic draw (codec) (SHAof G) id _).mp accepted
  have free : MH.CollisionFree (program.run (SHAof G)).2 := by
    by_contra collision
    exact good ⟨checks.2.2.2.2.1,Or.inl collision⟩
  have known : ∀ i ≤ g.roles.length, QueryTable.Known (program.run (SHAof G)).2
      (history ((M).point (program.run (SHAof G)).1 (ordinary (SHAof G)) i)).input.encode := by
    by_contra missing
    exact good ⟨checks.2.2.2.2.1,Or.inr missing⟩
  have viewDecoded := (Soundness.OracleTransport.decoded_actual binary prime P R repr shape setup cfg binaryCount metadata
    fits sample primeCount draw (codec) id program G).trans decodedAt
  obtain ⟨other,otherAt,column,opened,wrong⟩ := different
  have same := Option.some.inj (otherAt.symm.trans viewDecoded)
  subst other
  have indexed : Merkle.Indexed.Accepts ((codec).withOracle (SHAof G)) n (rootOf result.1)
      decoded.claim.I decoded.claim.a decoded.claim.pf := by
    rw [outputEq]
    exact checks.2.2.2.1.2.1
  have decodedResult : RuntimeAdaptiveVerifier.decode binary prime P R (W) (Earlier)
      hashPublic primePublic draw result.1 (ordinary (SHAof G)) = some decoded := by
    rwa [outputEq]
  have knownResult i (within : i ≤ g.openingIndex.val) :
      QueryTable.Known (result.2.map fun qa => (StrandWindow.encode qa.1,qa.2))
        (history ((M).point result.1 (ordinary (SHAof G)) i)).input.encode := by
    rw [traceEq,outputEq]
    exact known i (within.trans g.openingIndex.isLt.le)
  have covered := StrandMerkleBounds.accepted_cover binary prime P R repr shape setup cfg binaryCount metadata fits
    columnsFit sample program fallbackPath independent bindSalt primeCount draw G decoded decodedResult knownResult
    (by rw [traceEq]; exact free) indexed ⟨column,opened,wrong⟩
  exact covered

variable (bodyFits : ProofBodyBounds.bodyBound repr g ≤ CanonicalPrefix.maxLength)
local notation "schema" => StrandRuntime.Runtime.schema repr shape setup binary.nPublic
local notation "bytes" => StrandWindow.Node.bytes (other := O)
local notation "searchTree" => StrandReplay.search (schema) bytes compiled
local notation "Value" => QueryRuntime.Runtime.Value repr shape setup binary.nPublic
local notation "Name" => StrandSearch.Name Node Value
local notation "Answer" => StrandCoupling.Sample Digest Strand.Word
local notation "completed" => Soundness.OracleTransport.completion binary prime P R repr shape setup cfg binaryCount metadata
  fits sample (codec) id program
local notation "observe" => Soundness.OracleTransport.observe binary prime P R repr shape setup cfg binaryCount metadata
  fits sample (codec) id program
local notation "reached" => Soundness.OracleTransport.path binary prime P R repr shape setup cfg binaryCount metadata
  bodyFits fits sample (codec) id program
local notation "speculation" => Soundness.OracleTransport.speculation binary prime P R repr shape setup cfg binaryCount metadata
  fits sample (codec) id program

/-- The algebraic proof uses the ordered path, its physical challenge rows,
and agreement with extraction on every opened column. -/
def recovered (H : Name → Answer) : Prop :=
    let view := observe ((searchTree).run H).1 H
    let path := reached ((searchTree).run H).1 H
    let SHA := SHAof (completed H)
    Composition.PathQueries (rounds := g.roles.length) searchTree H path ∧
      (∀ i ≤ g.roles.length,
        let point := (M).point view.original.1 (ordinary SHA) i
        SHA (history point).input.encode = (H (path i)).1 ∧
          (fun counter => SHA (Strand.Input.prf (history point).id
            (SHA (history point).input.encode) counter).encode) = (H (path i)).2) ∧
      ¬disagrees view

local notation "recovers" => recovered binary prime P R repr shape setup cfg binaryCount metadata fits
  columnsFit sample primeCount draw program bodyFits

/-- The accepted path and opened columns are recovered together. The last
alternative is the observable disagreement covered by the raw fresh-hit
argument when there is no late prover hit. -/
theorem accepted_recovery_or_charge (H : Name → Answer)
    (accepted : decision (observe ((searchTree).run H).1 H) = true) :
    let view := observe ((searchTree).run H).1 H
    recovers H ∨ (rawException (completed H) ∨ 1 ≤ speculation H ∨ lateHit view ∨
      (disagrees view ∧ ¬rawException (completed H) ∧ ¬lateHit view)) := by
  dsimp only
  by_cases bad : rawException (completed H)
  · exact Or.inr (Or.inl bad)
  by_cases charged : 1 ≤ speculation H
  · exact Or.inr (Or.inr (Or.inl charged))
  by_cases late : lateHit (observe ((searchTree).run H).1 H)
  · exact Or.inr (Or.inr (Or.inr (Or.inl late)))
  by_cases different : disagrees (observe ((searchTree).run H).1 H)
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨different,bad,late⟩)))
  have path := (Soundness.OracleTransport.accepted_path_or_charge binary prime P R repr shape setup cfg binaryCount
    metadata bodyFits fits sample primeCount draw (codec) id program H accepted bad).resolve_right charged
  have rows := Soundness.OracleTransport.accepted_answers binary prime P R repr shape setup cfg binaryCount metadata
    bodyFits fits sample primeCount draw (codec) id program H accepted bad (lt_of_not_ge charged)
  have actual := congrArg (fun view => view.original.1)
    (Soundness.OracleTransport.observe_actual binary prime P R repr shape setup cfg binaryCount metadata fits
      sample (codec) id program H)
  exact Or.inl ⟨path,fun i within => by rw [actual]; exact rows i within,different⟩

local notation "observed" => fun H => observe (Prod.fst (Tree.run (searchTree) H)) H
local notation "originalException" => Soundness.OracleTransport.observedException
  binary prime P R repr shape setup cfg binaryCount metadata

/-- The verifier-side exceptions are determined by the common execution
view. The fresh Merkle witness is used only to bound the disagreement event. -/
def hashException (view : Protocol.Execution.View Output
    ((Output × TranscriptV2.Chain.State (M)) × Digest) (FingerprintPrefix.Key binary.nPublic)) : Prop :=
  originalException view.original view.verifier.1 ∨
    (decision view = true ∧ disagrees view ∧ ¬lateHit view)

local notation "hashBad" => hashException binary prime P R repr shape setup cfg binaryCount metadata
  columnsFit sample primeCount draw

private theorem rawException_view (G : Raw → Digest) :
    rawException G ↔ originalException (rawView G).original (rawView G).verifier.1 := by
  rw [Soundness.OracleTransport.rawView_actual binary prime P R repr shape setup cfg binaryCount metadata fits
    sample (codec) id program G]
  exact Soundness.OracleTransport.rawException_observed binary prime P R repr shape setup cfg binaryCount metadata fits
    sample (codec) id program G

variable {Q : ℕ} (queries : ∀ SHA : Bytes → Digest, (seen program SHA).card ≤ Q)

include bodyFits fallbackPath independent bindSalt queries in
/-- Both verifier-side exceptions have their raw probabilities. Only the
observable event is transported to the grouped experiment. -/
theorem hashException_ratio_le :
    letI : Fintype Value := Fintype.ofInjective
      (QueryRuntime.Runtime.toPoint repr shape setup binary.nPublic)
      (QueryRuntime.Runtime.toPoint_injective repr shape setup binary.nPublic fits)
    letI : Fintype Name := inferInstance
    letI : Fintype Answer := inferInstance
    density (fun H : Name → Answer => hashBad (observed H)) ≤
      Soundness.OracleBounds.delta Q g.roles.length + (Heap.heapDepth n+1 : ℚ)/2^256 := by
  letI : Fintype Value := Fintype.ofInjective
    (QueryRuntime.Runtime.toPoint repr shape setup binary.nPublic)
    (QueryRuntime.Runtime.toPoint_injective repr shape setup binary.nPublic fits)
  letI : Fintype Name := inferInstance
  letI : Fintype Answer := inferInstance
  rw [← Soundness.OracleTransport.observation_law binary prime P R repr shape setup cfg binaryCount metadata fits
    sample (codec) id program (hashBad)]
  let fresh := StrandMerkleBounds.freshHit binary prime P R repr shape setup cfg binaryCount metadata fits
    columnsFit sample program fallbackPath
  have cover (G : Raw → Digest) (bad : hashBad (rawView G)) : rawException G ∨ fresh G := by
    by_cases exception : rawException G
    · exact Or.inl exception
    have noOriginal := fun hit => exception ((rawException_view binary prime P R repr shape setup cfg binaryCount
      metadata fits columnsFit sample program G).mpr hit)
    obtain ⟨accepted,different,noLate⟩ := bad.resolve_left noOriginal
    exact Or.inr ((opening_disagreement_cover binary prime P R repr shape setup cfg binaryCount metadata fits
      columnsFit sample primeCount draw program fallbackPath independent bindSalt G accepted exception different).resolve_left noLate)
  have union := density_union_le (fun G : Raw → Digest => hashBad (rawView G))
    (fun i : Fin 2 => if i = 0 then rawException else fresh) (by
      intro G bad
      rcases cover G bad with exception | hit
      · exact ⟨0,by rw [if_pos (show (0 : Fin 2) = 0 by rfl)]; exact exception⟩
      · exact ⟨1,by simpa only [if_neg (show (1 : Fin 2) ≠ 0 by decide)] using hit⟩)
  rw [Fin.sum_univ_two,if_pos rfl,if_neg (show (1 : Fin 2) ≠ 0 by decide)] at union
  exact union.trans (add_le_add
    (Soundness.OracleBounds.raw_exception_ratio_le binary prime P R repr shape setup cfg binaryCount metadata
      bodyFits fits independent sample (codec) id program queries)
    (StrandMerkleBounds.freshHit_ratio_le binary prime P R repr shape setup cfg binaryCount metadata fits
      columnsFit sample program fallbackPath))

local notation "keyOf" => QueryRuntime.Runtime.key repr shape setup binary.nPublic
local notation "receiving" => DigestProjection.receivingCharge
  (StrandMerkleRealization.receives (codec) bytes)
  (StrandCommitment.claims MerkleWireCodec.nodeChildren keyOf FingerprintPrefix.Key.root ∘
    StrandMerkleRealization.byteName bytes) searchTree

/-- Late Merkle hits in the byte observation have a receiving query in
the original grouped search. Both sides use the same first-context cut. -/
theorem lateMerkleHit_charged (H : Name → Answer) (late : lateHit (observed H)) : 1 ≤ receiving H := by
  let view := observed H
  let SHA := SHAof (completed H)
  let key := contextOf view.original.1
  obtain ⟨input,digest,present,absent,merkle,target⟩ := late
  have original : view.original = program.run SHA := congrArg Protocol.Execution.View.original
    (Soundness.OracleTransport.observe_actual binary prime P R repr shape setup cfg binaryCount metadata fits
      sample (codec) id program H)
  have queried : (input,digest) ∈ (program.run SHA).2 := by rw [← original]; exact present
  have nonPrf : Strand.decodePrf input = none := by
    rcases merkle with ⟨leaf,encoded⟩ | ⟨index,children,encoded⟩
    · rw [encoded]
      exact StrandMerkleRealization.leaf_nonPrf (First) (Second) repr cfg.binaryField cfg.primeField
        setup.jointContext columnsFit leaf
    · rw [encoded]
      exact StrandMerkleRealization.node_nonPrf setup.jointContext index children
  have observations := Soundness.OracleTransport.original_node_observations binary prime P R repr shape setup cfg
    binaryCount metadata fits sample (codec) id program H
  obtain ⟨raw,logical,answer,entry,source⟩ := observations.2 (input,digest) queried nonPrf
  have receives : StrandMerkleRealization.receives (codec) bytes (.inl (raw,logical)) := by
    change IsMerkleInput (codec) (bytes raw)
    exact (congrArg (IsMerkleInput (codec)) (congrArg Prod.fst entry)).mpr merkle
  have cutEq := Soundness.OracleTransport.observe_cut binary prime P R repr shape setup cfg binaryCount metadata fits
    sample (codec) id program H key
  apply StrandMerkleRealization.wire_late_query_charged (First) (Second) repr cfg.binaryField cfg.primeField
    setup.jointContext columnsFit (schema) bytes keyOf FingerprintPrefix.Key.root compiled H SHA
    (fun raw logical answer member => (observations.1 raw logical answer member).1.symm)
    key raw logical answer source receives
  · rw [← cutEq,entry]
    exact absent
  · rw [← cutEq,show answer.1 = digest from congrArg Prod.snd entry]
    exact target

/-- These charges are paid by original queries and are independent of the
number of queries made during verifier replay. -/
def hashCharge (H : Name → Answer) : ℚ := speculation H + receiving H

local notation "charge" => hashCharge binary prime P R repr shape setup cfg binaryCount metadata fits
  columnsFit sample program

theorem hashCharge_nonneg (H : Name → Answer) : 0 ≤ charge H :=
  add_nonneg (DigestProjection.charge_nonneg _ _ _) (DigestProjection.receivingCharge_nonneg _ _ _ _)

/-- On the accepted path, recovery failure is either paid by an original
hash charge or falls in the observable exception. -/
theorem accepted_recovery_or_hash (H : Name → Answer) (accepted : decision (observed H) = true) :
    recovers H ∨ 1 ≤ charge H ∨ hashBad (observed H) := by
  rcases accepted_recovery_or_charge binary prime P R repr shape setup cfg binaryCount metadata fits
    columnsFit sample primeCount draw program bodyFits H accepted with ready | bad | speculative | late | fresh
  · exact Or.inl ready
  · exact Or.inr (Or.inr (Or.inl ((rawException_view binary prime P R repr shape setup cfg binaryCount metadata
      fits columnsFit sample program (completed H)).mp bad)))
  · exact Or.inr (Or.inl (speculative.trans (le_add_of_nonneg_right
      (DigestProjection.receivingCharge_nonneg _ _ _ _))))
  · have paid := lateMerkleHit_charged binary prime P R repr shape setup cfg binaryCount metadata fits
      columnsFit sample program H late
    exact Or.inr (Or.inl (paid.trans (le_add_of_nonneg_left (DigestProjection.charge_nonneg _ _ _))))
  · exact Or.inr (Or.inr (Or.inr ⟨accepted,fresh.1,fresh.2.2⟩))

include queries in
theorem grouped_budget (H : Name → Answer) : (seen searchTree H).card ≤ Q := by
  have agreement := StrandReplay.original_matches (schema) bytes compiled _ H (completed H)
    (Soundness.OracleTransport.completion_matches binary prime P R repr shape setup cfg binaryCount metadata fits
      sample (codec) id program H)
  exact (StrandReplay.search_card_le (schema) bytes compiled H (completed H) agreement).trans
    (Soundness.OracleBounds.compiled_budget binary prime P R repr shape setup cfg binaryCount metadata fits
      sample (codec) id program queries (completed H))

end LfzkV2.Current.Soundness.Recovery
