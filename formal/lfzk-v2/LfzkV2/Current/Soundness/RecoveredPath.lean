import LfzkV2.Current.Soundness.OracleTransport

/-! Recover accepted logical paths from the common raw execution view.
This layer proves order and challenge-row correspondence. Observation and
probability transport do not depend on these path-recovery arguments. -/
noncomputable section
namespace LfzkV2.Current.Soundness.OracleTransport
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

local notation "O" => other binary prime P R repr shape setup cfg binaryCount metadata fits sample codec merkleInput program
local notation "Node" => StrandWindow.Node (O)

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

local notation "completed" => completion binary prime P R repr shape setup cfg binaryCount metadata fits sample codec merkleInput program
local notation "SHAof" => rawSHA binary prime P R repr shape setup cfg binaryCount metadata fits sample codec merkleInput program
local notation "rawObservation" => rawView binary prime P R repr shape setup cfg binaryCount metadata fits sample codec merkleInput program
local notation "namedObservation" => observe binary prime P R repr shape setup cfg binaryCount metadata fits sample codec merkleInput program
local notation "nodeOf" => locate binary prime P R repr shape setup cfg binaryCount metadata fits sample codec merkleInput program
local notation "actualDecision" => Protocol.Observation.decision binary prime P R (W) (Earlier) bodyCodec sample codec merkleInput
  (CanonicalRequest.hashPublic binary.nPublic)
  (CanonicalRuntime.decodePrimePublic binary prime P R repr shape setup cfg primeCount) draw

/-- The original cache already fixes each queried node's entire PRF row.
Original collision freedom and the original speculative charge suffice;
fresh verifier answers require no collision-freedom hypothesis here. -/
theorem original_node_answers (H : Name → Answer)
    (free : Merkle.MH.CollisionFree (program.run (SHAof (completed H))).2)
    (uncharged : speculation binary prime P R repr shape setup cfg binaryCount metadata fits sample codec merkleInput program H < 1)
    (raw : Node) (value : Option Value)
    (member : ((.inl (raw,value),H (.inl (raw,value))) : Name × Answer) ∈ ((searchTree).run H).2) :
    let SHA := SHAof (completed H)
    let name : Name := .inl (raw,value)
    SHA raw.val.val = (H name).1 ∧
      (fun counter => SHA (Strand.Input.prf (Strand.nodeKey raw.val.val (SHA raw.val.val)).1 (SHA raw.val.val) counter).encode) = (H name).2 := by
  intro SHA name
  have agreement := StrandReplay.original_matches (schema) bytes compiled compiledReplay H (completed H)
    (completion_matches binary prime P R repr shape setup cfg binaryCount metadata fits sample codec merkleInput program H)
  have originalFree := original_finite_collision_free binary prime P R repr shape setup cfg binaryCount metadata fits
    sample codec merkleInput program H free
  have noGuess : ¬DigestProjection.Guess (StrandSearch.claims bytes) searchTree H := by
    intro guessed
    exact (not_le_of_gt uncharged) (DigestProjection.guess_charged _ _ _ guessed)
  have row := StrandSearch.node_stream (schema) bytes (recordTrace compiled) H (completed H) agreement
    (fun a ha b hb equal => originalFree a
      (by simpa only [seen,List.mem_toFinset,Bcs.TotalOracle.queried,run_recordTrace] using ha) b
      (by simpa only [seen,List.mem_toFinset,Bcs.TotalOracle.queried,run_recordTrace] using hb) equal)
    noGuess raw value (H name) member
  have digest : SHA raw.val.val = (H name).1 :=
    (rawSHA_node binary prime P R repr shape setup cfg binaryCount metadata fits sample codec merkleInput program (completed H) raw).trans
      (node_answer binary prime P R repr shape setup cfg binaryCount metadata fits sample codec merkleInput program H raw value member)
  refine ⟨digest,funext fun counter => ?_⟩
  rw [digest]
  exact (rawSHA_prf binary prime P R repr shape setup cfg binaryCount metadata fits sample codec merkleInput program
    (completed H) (StrandSearch.key bytes raw (H name).1) counter).trans (row counter)

/-- Raw original-path recovery lifts to the finite named realization with
the original query budget. The window encoding changes no query or answer. -/
theorem original_path_or_charge (H : Name → Answer)
    (free : Merkle.MH.CollisionFree (program.run (SHAof (completed H))).2)
    (known : ∀ i ≤ g.roles.length, Merkle.QueryTable.Known (program.run (SHAof (completed H))).2
      (history ((M).point (program.run (SHAof (completed H))).1 (ordinaryOracle (SHAof (completed H))) i)).input.encode) :
    Composition.PathQueries (rounds := g.roles.length) searchTree H
      (path binary prime P R repr shape setup cfg binaryCount metadata bodyFits fits sample codec merkleInput program
        ((searchTree).run H).1 H) ∨
      1 ≤ speculation binary prime P R repr shape setup cfg binaryCount metadata fits sample codec merkleInput program H := by
  let G := completed H
  let SHA := SHAof G
  let output := (program.run SHA).1
  let values := StrandAcceptedPath.value binary prime P R repr shape setup cfg binaryCount metadata bodyFits fits sample output SHA
  have agreement := StrandReplay.original_matches (schema) bytes compiled compiledReplay H G
    (completion_matches binary prime P R repr shape setup cfg binaryCount metadata fits sample codec merkleInput program H)
  have source := StrandSearch.searchState_source (schema) bytes (recordTrace compiled) StrandCoupling.Cache.empty [] H G agreement
  have named := StrandSearch.search_trace (schema) bytes (recordTrace compiled) H
  simp only [StrandSearch.search,Tree.run_map] at named
  have pathHistory i (within : i ≤ g.roles.length) :
      (schema).encode (values i) = history ((M).point output (ordinaryOracle SHA) i) :=
    StrandAcceptedPath.value_history binary prime P R repr shape setup cfg binaryCount metadata bodyFits fits sample output SHA i within
  have scope raw logical answer (member : ((.inl (raw,logical),answer) : Name × Answer) ∈ ((searchTree).run H).2) :
      Merkle.QueryTable.Known (program.run SHA).2 (bytes raw) := by
    apply (Merkle.QueryTable.known_run_iff program SHA _).mpr
    exact ((original_node_observations binary prime P R repr shape setup cfg binaryCount metadata fits
      sample codec merkleInput program H).1 raw logical answer member).2
  have visible i (within : i ≤ g.roles.length) : ∃ logical answer,
      ((.inl (nodeOf (values i),logical),answer) : Name × Answer) ∈ ((searchTree).run H).2 := by
    apply StrandReplay.original_node_origin (schema) bytes compiled H G agreement
    rw [TranscriptV2.seen_mapQueries]
    refine Finset.mem_image.mpr ⟨((schema).encode (values i)).input.encode,?_,?_⟩
    · rw [pathHistory i within]
      exact (Merkle.QueryTable.known_run_iff program SHA _).mp (known i within)
    · exact StrandWindow.decode_encode (O) fallbackNode (.inl (nodeOf (values i)))
  change Composition.PathQueries (rounds := g.roles.length) searchTree H
      (fun i => .inl (nodeOf (values i),some (values i))) ∨
    1 ≤ DigestProjection.charge (StrandSearch.claims bytes) searchTree H
  apply StrandRecognition.original_path_or_charge (schema) bytes searchTree H named SHA
    (fun raw logical answer member => (source.2 raw logical answer member).symm.trans
      (rawSHA_node binary prime P R repr shape setup cfg binaryCount metadata fits sample codec merkleInput program G raw).symm)
    (Merkle.QueryTable.Known (program.run SHA).2) scope
    (fun a ha b hb equal => Merkle.QueryTable.equal_of_known _ SHA
      (fun qa member => (Tree.trace_sound program SHA qa member).symm) free a b ha hb equal)
    (fun a b equal => Subtype.ext (Subtype.ext equal)) values nodeOf (fun _ => rfl) ?_ ?_ ?_ ?_ visible
  · intro i within
    rw [pathHistory i within]
    exact StrandRuntime.replay_consistent bodyCodec (M) cfg.initialLink (fun _ => rfl) (fun _ => rfl)
      (fun _ => rfl) sample cfg.fallback output SHA i within
  · intro i within
    rw [pathHistory i within,StrandRuntime.history_depth]
    have rank : ((M).point output (ordinaryOracle SHA) i).rank = i :=
      (M).point_rank output (ordinaryOracle SHA) within
    rw [rank]
    exact lt_of_le_of_lt within fits
  · rw [pathHistory 0 (Nat.zero_le _)]
    exact StrandRuntime.history_root bodyCodec _ ((M).point_rank output (ordinaryOracle SHA) (Nat.zero_le _))
  · intro i within
    rw [pathHistory (i+1) (by omega),pathHistory i within.le]
    obtain ⟨message,equal⟩ := StrandRuntime.history_parent bodyCodec cfg.initialLink _ _ ((M).point_parent output (ordinaryOracle SHA) within)
    exact ⟨_,message,equal⟩

/-- Original-path recovery supplies the exact physical node and PRF row
needed by the existing role normalization, without broad replay exceptions. -/
theorem original_answers (H : Name → Answer)
    (free : Merkle.MH.CollisionFree (program.run (SHAof (completed H))).2)
    (known : ∀ i ≤ g.roles.length, Merkle.QueryTable.Known (program.run (SHAof (completed H))).2
      (history ((M).point (program.run (SHAof (completed H))).1 (ordinaryOracle (SHAof (completed H))) i)).input.encode)
    (uncharged : speculation binary prime P R repr shape setup cfg binaryCount metadata fits sample codec merkleInput program H < 1)
    (index : ℕ) (within : index ≤ g.roles.length) :
    let SHA := SHAof (completed H)
    let point := (M).point (program.run SHA).1 (ordinaryOracle SHA) index
    let name := path binary prime P R repr shape setup cfg binaryCount metadata bodyFits fits sample codec merkleInput program
      ((searchTree).run H).1 H index
    SHA (history point).input.encode = (H name).1 ∧
      (fun counter => SHA (Strand.Input.prf (history point).id (SHA (history point).input.encode) counter).encode) = (H name).2 := by
  let SHA := SHAof (completed H)
  let output := (program.run SHA).1
  let point := (M).point output (ordinaryOracle SHA) index
  let value := StrandAcceptedPath.value binary prime P R repr shape setup cfg binaryCount metadata bodyFits fits sample output SHA index
  let name : Name := .inl (nodeOf value,some value)
  have queried : name ∈ seen searchTree H :=
    ((original_path_or_charge binary prime P R repr shape setup cfg binaryCount metadata bodyFits fits
      sample codec merkleInput program H free known).resolve_right (not_le_of_gt uncharged)).queried index within
  have member : (name,H name) ∈ ((searchTree).run H).2 := by
    obtain ⟨⟨address,answer⟩,present,equal⟩ := List.mem_map.mp (List.mem_toFinset.mp queried)
    change address = name at equal
    subst address
    have actual := Tree.trace_sound searchTree H (name,answer) present
    change answer = H name at actual
    simpa only [actual] using present
  have encoding : (nodeOf value).val.val = (history point).input.encode :=
    congrArg (fun h : Strand.History => h.input.encode)
      (StrandAcceptedPath.value_history binary prime P R repr shape setup cfg binaryCount metadata bodyFits fits sample output SHA index within)
  have answers := original_node_answers binary prime P R repr shape setup cfg binaryCount metadata fits sample codec merkleInput program
    H free uncharged (nodeOf value) (some value) member
  dsimp only at answers
  rw [encoding] at answers
  simpa only [path,Strand.nodeKey_encode _ (history point).valid,Strand.History.input_id] using answers

/-- Accepted proofs outside the explicit original-query event recover the
same fixed original cut used by the algebraic extractor. -/
theorem recovered_original (H : Name → Answer)
    (accepted : actualDecision (namedObservation ((searchTree).run H).1 H) = true)
    (good : ¬exception binary prime P R repr shape setup cfg binaryCount metadata fits sample codec merkleInput program H) :
    let SHA := SHAof (completed H)
    Merkle.MH.CollisionFree (program.run SHA).2 ∧
      ∀ i ≤ g.roles.length, Merkle.QueryTable.Known (program.run SHA).2
        (history ((M).point (program.run SHA).1 (ordinaryOracle SHA) i)).input.encode := by
  rw [← observe_source,decision_actual] at accepted
  obtain ⟨decoded,_,checks⟩ := (StrandVerifier.verify_true_iff binary prime P R (W) (Earlier)
    bodyCodec sample (CanonicalRequest.hashPublic binary.nPublic)
    (CanonicalRuntime.decodePrimePublic binary prime P R repr shape setup cfg primeCount)
    draw codec (SHAof (completed H)) merkleInput (program.run (SHAof (completed H))).1).mp accepted
  have excluded : ¬(¬Merkle.MH.CollisionFree (program.run (SHAof (completed H))).2 ∨
      ¬∀ i ≤ g.roles.length, Merkle.QueryTable.Known (program.run (SHAof (completed H))).2
        (history ((M).point (program.run (SHAof (completed H))).1 (ordinaryOracle (SHAof (completed H))) i)).input.encode) :=
    fun bad => good ⟨checks.2.2.2.2.1,bad⟩
  exact ⟨not_not.mp (fun bad => excluded (Or.inl bad)),not_not.mp (fun bad => excluded (Or.inr bad))⟩

theorem accepted_path_or_charge (H : Name → Answer)
    (accepted : actualDecision (namedObservation ((searchTree).run H).1 H) = true)
    (good : ¬exception binary prime P R repr shape setup cfg binaryCount metadata fits sample codec merkleInput program H) :
    Composition.PathQueries (rounds := g.roles.length) searchTree H
      (path binary prime P R repr shape setup cfg binaryCount metadata bodyFits fits sample codec merkleInput program
        ((searchTree).run H).1 H) ∨
      1 ≤ speculation binary prime P R repr shape setup cfg binaryCount metadata fits sample codec merkleInput program H := by
  obtain ⟨free,known⟩ := recovered_original binary prime P R repr shape setup cfg binaryCount metadata fits
    sample primeCount draw codec merkleInput program H accepted good
  exact original_path_or_charge binary prime P R repr shape setup cfg binaryCount metadata bodyFits fits
    sample codec merkleInput program H free known

theorem accepted_answers (H : Name → Answer)
    (accepted : actualDecision (namedObservation ((searchTree).run H).1 H) = true)
    (good : ¬exception binary prime P R repr shape setup cfg binaryCount metadata fits sample codec merkleInput program H)
    (uncharged : speculation binary prime P R repr shape setup cfg binaryCount metadata fits sample codec merkleInput program H < 1)
    (index : ℕ) (within : index ≤ g.roles.length) :
    let SHA := SHAof (completed H)
    let point := (M).point (program.run SHA).1 (ordinaryOracle SHA) index
    let name := path binary prime P R repr shape setup cfg binaryCount metadata bodyFits fits sample codec merkleInput program
      ((searchTree).run H).1 H index
    SHA (history point).input.encode = (H name).1 ∧
      (fun counter => SHA (Strand.Input.prf (history point).id (SHA (history point).input.encode) counter).encode) = (H name).2 := by
  obtain ⟨free,known⟩ := recovered_original binary prime P R repr shape setup cfg binaryCount metadata fits
    sample primeCount draw codec merkleInput program H accepted good
  exact original_answers binary prime P R repr shape setup cfg binaryCount metadata bodyFits fits
    sample codec merkleInput program H free known uncharged index within

include bodyFits in
/-- The accepted context is already queried during the original search.
Consequently authentication replay cannot enlarge its extraction cut. -/
theorem full_cut_eq (H : Name → Answer)
    (accepted : actualDecision (namedObservation ((searchTree).run H).1 H) = true)
    (good : ¬exception binary prime P R repr shape setup cfg binaryCount metadata fits sample codec merkleInput program H)
    (uncharged : speculation binary prime P R repr shape setup cfg binaryCount metadata fits sample codec merkleInput program H < 1) :
    let SHA := SHAof (completed H)
    let output := (program.run SHA).1
    let key := (RuntimeAdaptiveVerifier.encodings binary prime P R (W) (Earlier) output.request).context output.proof
    StrandCut.trace context ((searchTree).bind resumeTree) H key = StrandCut.trace context searchTree H key := by
  intro SHA output key
  let value := StrandAcceptedPath.value binary prime P R repr shape setup cfg binaryCount metadata bodyFits fits sample output SHA 0
  let name : Name := .inl (nodeOf value,some value)
  have queried : name ∈ seen searchTree H :=
    ((accepted_path_or_charge binary prime P R repr shape setup cfg binaryCount metadata bodyFits fits
      sample primeCount draw codec merkleInput program H accepted good).resolve_right (not_le_of_gt uncharged)).queried 0 (Nat.zero_le _)
  have label : StrandCut.label context name = some key := by
    change some (context value) = some key
    apply congrArg some
    calc
      context value = (QueryRuntime.Runtime.toPoint repr shape setup binary.nPublic value).context :=
        (QueryRuntime.Runtime.toPoint_context repr shape setup binary.nPublic value).symm
      _ = ((M).point output (ordinaryOracle SHA) 0).context :=
        congrArg Input.context (StrandAcceptedPath.value_point binary prime P R repr shape setup cfg binaryCount metadata
          bodyFits fits sample output SHA 0 (Nat.zero_le _))
      _ = key := by
        rw [RuntimeAdaptiveVerifier.point_eq]
        exact (RuntimeAdaptiveVerifier.encodings binary prime P R (W) (Earlier) output.request).point_context
          cfg.initialLink output.proof (ordinaryOracle SHA) 0
  unfold StrandCut.trace
  rw [beforeLabel_bind_of_queried (StrandCut.label context) (some key) searchTree resumeTree H ⟨name,queried,label⟩]

end LfzkV2.Current.Soundness.OracleTransport
