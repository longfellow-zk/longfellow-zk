import LfzkV2.Current.StrandVerifier
import LfzkV2.Current.RuntimeAdaptiveMerkle
import LfzkV2.Current.StrandSearch
import Merkle.Indexed.Execution
import Merkle.Indexed.Path

/-! The shared-SHA verifier's complete oracle use: ordinary transcript
replay, authentication of its one tuple opening, and the final PRF seal.
The authentication claim is reconstructed from that same replay and the
submitted proof. No separate decoded claim or execution certificate is used. -/
noncomputable section
namespace LfzkV2.Current.StrandAuthentication
open Application ApplicationSetup CanonicalPrefix
open Merkle Merkle.Indexed Merkle.RandomOracle
open Merkle.MH (OpeningClaim)
open TranscriptV2
open scoped Classical

section Check
variable {Leaf Salt Enc Out : Type} {n : ℕ}
variable (codec : Merkle.Indexed.Codec Salt Leaf Digest Enc)
variable (claimOf : Out → OpeningClaim n Salt Leaf Digest) (merkleInput : Enc → Bytes)

def check (out : Out) : Tree Enc Digest Unit (2*n) :=
  (Merkle.Indexed.check codec n (claimOf out).I (claimOf out).a (claimOf out).pf).map fun _ => ()

/-- These are the actual authentication hash calls, expressed as raw SHA
queries. The tuple check is shared by all participating fields. -/
def checkRaw (out : Out) : Tree Bytes Digest Unit (2*n) :=
  mapQueries merkleInput (check codec claimOf out)

theorem checkRaw_run (out : Out) (SHA : Bytes → Digest) :
    (checkRaw codec claimOf merkleInput out).run SHA =
      ((),((check codec claimOf out).run (SHA ∘ merkleInput)).2.map (fun qa => (merkleInput qa.1,qa.2))) := by
  rw [checkRaw,run_mapQueries]

/-- Every input in the mathematical indexed check is visible in replay. -/
theorem check_queries_visible (out : Out) (H : Enc → Digest) (input : Enc)
    (queried : input ∈ checkTraceQueries (codec.withOracle H) n
      (claimOf out).I (claimOf out).a (claimOf out).pf) :
    ∃ answer, (input,answer) ∈ ((check codec claimOf out).run H).2 := by
  obtain ⟨vertex,positive,within,atVertex⟩ := (mem_checkTraceQueries
    (codec.withOracle H) n (claimOf out).I (claimOf out).a (claimOf out).pf input).mp queried
  refine ⟨H input,?_⟩
  simpa only [check,Tree.run_map] using Merkle.Indexed.check_visible codec n (claimOf out).I
    (claimOf out).a (claimOf out).pf H vertex input positive within atVertex

theorem check_root_congr (out : Out) (H H' : Enc → Digest)
    (agree : ∀ qa ∈ ((check codec claimOf out).run H).2, H' qa.1 = qa.2) :
    checkValues (codec.withOracle H') n (claimOf out).I (claimOf out).a (claimOf out).pf 1 =
      checkValues (codec.withOracle H) n (claimOf out).I (claimOf out).a (claimOf out).pf 1 := by
  have same := Tree.run_congr_on_trace
    (Merkle.Indexed.check codec n (claimOf out).I (claimOf out).a (claimOf out).pf) H H'
    (by simpa only [check,Tree.run_map] using agree)
  have root := congrArg (fun result => result.1 1) same
  simpa only [Merkle.Indexed.check_run codec n (claimOf out).I (claimOf out).a
    (claimOf out).pf _ 1 (by decide)] using root

theorem checkRaw_root_congr (out : Out) (SHA SHA' : Bytes → Digest)
    (agree : ∀ qa ∈ ((checkRaw codec claimOf merkleInput out).run SHA).2, SHA' qa.1 = qa.2) :
    checkValues (codec.withOracle (SHA' ∘ merkleInput)) n (claimOf out).I (claimOf out).a (claimOf out).pf 1 =
      checkValues (codec.withOracle (SHA ∘ merkleInput)) n (claimOf out).I (claimOf out).a (claimOf out).pf 1 := by
  apply check_root_congr codec claimOf out
  intro qa member
  apply agree (merkleInput qa.1,qa.2)
  rw [checkRaw_run]
  exact List.mem_map.mpr ⟨qa,member,rfl⟩

theorem checkRaw_nonPrf_card (out : Out) (SHA : Bytes → Digest) :
    ((seen (checkRaw codec claimOf merkleInput out) SHA).filter
      (fun raw => Strand.decodePrf raw = none)).card ≤ 2*n :=
  (Finset.card_filter_le _ _).trans (seen_card_le _ _)

end Check

namespace Physical
variable {Point C Out : Type} {rounds blocks : ℕ}
variable (history : Point → Strand.History)
variable (sample : Point → Tree Strand.Word Digest (Option C) blocks) (fallback : C)
variable (model : Chain Point Digest C Out rounds)

/-- Every reached sampler's full raw trace is in ordinary replay, including
rejected draws. This is stronger than equality of its fallback-totalized value. -/
theorem round_trace_subset (output : Out) (SHA : Bytes → Digest) (i : Fin rounds) :
    ((TranscriptV2.StrandVerifier.readRound history sample fallback
      (model.point output (TranscriptV2.StrandVerifier.oracle history sample fallback SHA) i.val)).run SHA).2 ⊆
        ((TranscriptV2.StrandVerifier.replay history sample fallback model output).run SHA).2 := by
  rw [TranscriptV2.StrandVerifier.replay,expandQueries_run]
  intro qa member
  apply List.mem_flatMap.mpr
  refine ⟨(model.point output (TranscriptV2.StrandVerifier.oracle history sample fallback SHA) i.val,
    TranscriptV2.StrandVerifier.oracle history sample fallback SHA
      (model.point output (TranscriptV2.StrandVerifier.oracle history sample fallback SHA) i.val)),?_,member⟩
  rw [model.recompute_trace]
  exact List.mem_ofFn.mpr ⟨i,rfl⟩

theorem oracle_agree (output : Out) (SHA SHA' : Bytes → Digest)
    (agree : ∀ qa ∈ ((TranscriptV2.StrandVerifier.replay history sample fallback model output).run SHA).2,
      SHA' qa.1 = qa.2) (i : Fin rounds) :
    TranscriptV2.StrandVerifier.oracle history sample fallback SHA
        (model.point output (TranscriptV2.StrandVerifier.oracle history sample fallback SHA) i.val) =
      TranscriptV2.StrandVerifier.oracle history sample fallback SHA'
        (model.point output (TranscriptV2.StrandVerifier.oracle history sample fallback SHA) i.val) := by
  exact (congrArg Prod.fst (Tree.run_congr_on_trace _ SHA SHA'
    (fun qa member => agree qa (round_trace_subset history sample fallback model output SHA i member)))).symm

theorem sampled_agree (point : Point) (SHA SHA' : Bytes → Digest)
    (agree : ∀ qa ∈ ((TranscriptV2.StrandVerifier.readRound history sample fallback point).run SHA).2,
      SHA' qa.1 = qa.2) :
    TranscriptV2.StrandVerifier.sampled history sample SHA point ↔
      TranscriptV2.StrandVerifier.sampled history sample SHA' point := by
  have node : SHA' (history point).input.encode = SHA (history point).input.encode :=
    agree _ List.mem_cons_self
  have stream := Tree.run_congr_on_trace
    (TranscriptV2.StrandVerifier.stream (history point).id (SHA (history point).input.encode) (sample point)) SHA SHA'
    (by
      intro qa member
      apply agree qa
      simp only [TranscriptV2.StrandVerifier.readRound,Tree.run_query,Tree.run_map]
      exact List.mem_cons_of_mem _ member)
  have result := congrArg Prod.fst stream
  simp only [TranscriptV2.StrandVerifier.stream_run] at result
  unfold TranscriptV2.StrandVerifier.sampled
  rw [node,result]

theorem points_agree (output : Out) (SHA SHA' : Bytes → Digest)
    (agree : ∀ qa ∈ ((TranscriptV2.StrandVerifier.replay history sample fallback model output).run SHA).2,
      SHA' qa.1 = qa.2) (index : ℕ) (within : index ≤ rounds) :
    model.point output (TranscriptV2.StrandVerifier.oracle history sample fallback SHA) index =
      model.point output (TranscriptV2.StrandVerifier.oracle history sample fallback SHA') index := by
  apply congrArg model.input
  apply model.replay_congr_prefix
  intro i hi
  exact oracle_agree history sample fallback model output SHA SHA' agree ⟨i,by omega⟩

theorem path_sampled_agree (output : Out) (SHA SHA' : Bytes → Digest)
    (agree : ∀ qa ∈ ((TranscriptV2.StrandVerifier.replay history sample fallback model output).run SHA).2,
      SHA' qa.1 = qa.2) (i : Fin rounds) :
    TranscriptV2.StrandVerifier.sampled history sample SHA
        (model.point output (TranscriptV2.StrandVerifier.oracle history sample fallback SHA) i.val) ↔
      TranscriptV2.StrandVerifier.sampled history sample SHA'
        (model.point output (TranscriptV2.StrandVerifier.oracle history sample fallback SHA') i.val) := by
  rw [← points_agree history sample fallback model output SHA SHA' agree i.val (Nat.le_of_lt i.isLt)]
  exact sampled_agree history sample fallback _ SHA SHA'
    (fun qa member => agree qa (round_trace_subset history sample fallback model output SHA i member))

variable {authenticationBudget : ℕ}
variable (authentication : Out × model.State → Tree Bytes Digest Unit authenticationBudget)

def computedSeal (output : Out) (SHA : Bytes → Digest) : Digest :=
  SHA (Strand.Input.prf
    (history (model.finalSealPoint output
      (TranscriptV2.StrandVerifier.oracle history sample fallback SHA))).id
    (SHA (history (model.finalSealPoint output
      (TranscriptV2.StrandVerifier.oracle history sample fallback SHA))).input.encode) 0).encode

def authenticate (output : Out) :
    Tree Bytes Digest ((Out × model.State) × Digest) (2+authenticationBudget+(blocks+1)*rounds) :=
  (TranscriptV2.StrandVerifier.replay history sample fallback model output).bind fun annotated =>
    (authentication annotated).bind fun _ =>
      .query (history (model.input annotated.2)).input.encode fun node =>
        .query (Strand.Input.prf (history (model.input annotated.2)).id node 0).encode fun finalSeal =>
          .done (annotated,finalSeal)

theorem authenticate_result (output : Out) (SHA : Bytes → Digest) :
    ((authenticate history sample fallback model authentication output).run SHA).1 =
      ((output,model.replay output (TranscriptV2.StrandVerifier.oracle history sample fallback SHA) rounds),
        computedSeal history sample fallback model output SHA) := by
  simp only [authenticate,Tree.run_bind,TranscriptV2.StrandVerifier.replay_result,
    Tree.run_query,Tree.run_done,computedSeal]
  rfl

theorem authenticate_trace (output : Out) (SHA : Bytes → Digest) :
    ((authenticate history sample fallback model authentication output).run SHA).2 =
      ((TranscriptV2.StrandVerifier.replay history sample fallback model output).run SHA).2 ++
        (((authentication (output,model.replay output (TranscriptV2.StrandVerifier.oracle history sample fallback SHA) rounds)).run SHA).2 ++
          [((history (model.finalSealPoint output (TranscriptV2.StrandVerifier.oracle history sample fallback SHA))).input.encode,
              SHA (history (model.finalSealPoint output (TranscriptV2.StrandVerifier.oracle history sample fallback SHA))).input.encode),
           ((Strand.Input.prf (history (model.finalSealPoint output (TranscriptV2.StrandVerifier.oracle history sample fallback SHA))).id (SHA (history (model.finalSealPoint output (TranscriptV2.StrandVerifier.oracle history sample fallback SHA))).input.encode) 0).encode,
              computedSeal history sample fallback model output SHA)]) := by
  simp only [authenticate,Tree.run_bind,TranscriptV2.StrandVerifier.replay_result,
    Tree.run_query,Tree.run_done,computedSeal]
  rfl

theorem ordinary_trace_subset (output : Out) (SHA : Bytes → Digest) :
    ((TranscriptV2.StrandVerifier.replay history sample fallback model output).run SHA).2 ⊆
      ((authenticate history sample fallback model authentication output).run SHA).2 := by
  rw [authenticate_trace]
  exact fun _ member => List.mem_append_left _ member

theorem authentication_trace_subset (output : Out) (SHA : Bytes → Digest) :
    ((authentication (output,model.replay output (TranscriptV2.StrandVerifier.oracle history sample fallback SHA) rounds)).run SHA).2 ⊆
      ((authenticate history sample fallback model authentication output).run SHA).2 := by
  rw [authenticate_trace]
  intro qa member
  exact List.mem_append_right _ (List.mem_append_left _ member)

/-- The transcript-only final-node replay is a sub-observation of full
verification. Authentication is inserted before that same final node. -/
theorem beforeSeal_trace_subset (output : Out) (SHA : Bytes → Digest) :
    ((TranscriptV2.StrandVerifier.beforeSeal history sample fallback model output).run SHA).2 ⊆
      ((authenticate history sample fallback model authentication output).run SHA).2 := by
  intro qa member
  simp only [TranscriptV2.StrandVerifier.beforeSeal,Tree.run_bind,
    TranscriptV2.StrandVerifier.replay_result,Tree.run_query,Tree.run_done] at member
  rw [authenticate_trace]
  rcases List.mem_append.mp member with ordinary | finalNode
  · exact List.mem_append_left _ ordinary
  · exact List.mem_append_right _ (List.mem_append_right _ (List.mem_cons.mpr
      (Or.inl (List.mem_singleton.mp finalNode))))

/-- Ordinary nodes, the one shared authentication check and final node are
all counted. Counter-stream draws, including the final seal, are PRF calls. -/
theorem authenticate_nonPrf_card (output : Out) (SHA : Bytes → Digest) :
    ((seen (authenticate history sample fallback model authentication output) SHA).filter
      (fun raw => Strand.decodePrf raw = none)).card ≤ rounds+1+authenticationBudget := by
  -- Compare node sets with the existing transcript-only bound. The actual
  -- replay above executes authentication before its single final-node read.
  let before := TranscriptV2.StrandVerifier.beforeSeal history sample fallback model output
  let annotated := (output,model.replay output (TranscriptV2.StrandVerifier.oracle history sample fallback SHA) rounds)
  have subset : (seen (authenticate history sample fallback model authentication output) SHA).filter
        (fun raw => Strand.decodePrf raw = none) ⊆
      ((seen before SHA).filter (fun raw => Strand.decodePrf raw = none)) ∪
        ((seen (authentication annotated) SHA).filter (fun raw => Strand.decodePrf raw = none)) := by
    intro raw member
    obtain ⟨queried,nonPrf⟩ := Finset.mem_filter.mp member
    obtain ⟨⟨address,answer⟩,member,same⟩ := List.mem_map.mp (List.mem_toFinset.mp queried)
    change address = raw at same
    subst address
    rw [authenticate_trace] at member
    rcases List.mem_append.mp member with ordinaryQuery | later
    · apply Finset.mem_union_left
      apply Finset.mem_filter.mpr
      refine ⟨?_,nonPrf⟩
      apply List.mem_toFinset.mpr
      apply List.mem_map.mpr
      refine ⟨(raw,answer),?_,rfl⟩
      dsimp only [before]
      rw [TranscriptV2.StrandVerifier.beforeSeal,Tree.run_bind]
      exact List.mem_append_left _ ordinaryQuery
    · rcases List.mem_append.mp later with authenticationQuery | finalQuery
      · apply Finset.mem_union_right
        apply Finset.mem_filter.mpr
        exact ⟨List.mem_toFinset.mpr (List.mem_map.mpr ⟨(raw,answer),authenticationQuery,rfl⟩),nonPrf⟩
      · rcases List.mem_cons.mp finalQuery with node | sealQuery
        · have address := congrArg Prod.fst node
          change raw = _ at address
          subst raw
          apply Finset.mem_union_left
          apply Finset.mem_filter.mpr
          exact ⟨TranscriptV2.StrandVerifier.beforeSeal_nodes_visible history sample fallback model output SHA
            (Fin.last rounds),nonPrf⟩
        · have address := congrArg Prod.fst (List.mem_singleton.mp sealQuery)
          change raw = _ at address
          simp only [address,Strand.decodePrf_input] at nonPrf
          contradiction
  exact (Finset.card_le_card subset).trans ((Finset.card_union_le _ _).trans (Nat.add_le_add
    (TranscriptV2.StrandVerifier.beforeSeal_nonPrf_card history sample fallback model output SHA)
    ((Finset.card_filter_le _ _).trans (seen_card_le (authentication annotated) SHA))))

end Physical

section Completion
variable {T Value : Type} {fuel : ℕ}

/-- Completing unused raw SHA coordinates preserves the whole recorded
execution, not just its submitted proof. The cache's source theorem derives
this equality for arbitrary search and verifier query trees. -/
theorem named_completion_run (schema : Strand.History.Codec T) (program : Tree Bytes Digest Value fuel)
    (H : StrandSearch.Name Strand.OtherPoint T → StrandCoupling.Sample Digest Strand.Word)
    (SHA SHA' : Bytes → Digest)
    (cacheMatches : ((StrandSearch.searchState schema Subtype.val
      (recordTrace (mapQueries Strand.rawPoint program)) StrandCoupling.Cache.empty []).run H).1.1.2.Matches
        (SHA ∘ Strand.rawBytes))
    (cacheMatches' : ((StrandSearch.searchState schema Subtype.val
      (recordTrace (mapQueries Strand.rawPoint program)) StrandCoupling.Cache.empty []).run H).1.1.2.Matches
        (SHA' ∘ Strand.rawBytes)) : program.run SHA = program.run SHA' := by
  have first := (StrandSearch.searchState_source schema Subtype.val
    (recordTrace (mapQueries Strand.rawPoint program)) StrandCoupling.Cache.empty [] H
    (SHA ∘ Strand.rawBytes) cacheMatches).1
  have second := (StrandSearch.searchState_source schema Subtype.val
    (recordTrace (mapQueries Strand.rawPoint program)) StrandCoupling.Cache.empty [] H
    (SHA' ∘ Strand.rawBytes) cacheMatches').1
  simp only [run_recordTrace] at first second
  have source := first.trans second.symm
  rw [Strand.run_rawPoint,Strand.run_rawPoint] at source
  have raw := congrArg (fun result => (result.1,
    result.2.map (fun qa => (Strand.rawBytes qa.1,qa.2)))) source
  have roundtrip (xs : List (Bytes × Digest)) :
      (xs.map (fun qa => (Strand.rawPoint qa.1,qa.2))).map
        (fun qa => (Strand.rawBytes qa.1,qa.2)) = xs := by
    induction xs with
    | nil => rfl
    | cons qa rest ih => simp only [List.map_cons,Strand.rawBytes_point,ih,Prod.eta]
  change ((program.run SHA).1,_) = ((program.run SHA').1,_) at raw
  rw [roundtrip,roundtrip] at raw
  exact raw

end Completion

section Runtime
variable {g : Geometry} {fields : Fields} {Advice Key C B Salt Enc Request : Type}
variable [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable {shared maskBits adviceBits k s n t capacity blocks : ℕ}
local notation "N" => ZMod Adapter.Mdoc.primeOrder
variable (binary : BinaryPublic B shared maskBits adviceBits) (prime : PrimePublic N shared)
variable (P : FieldBackend B k s n t) (R : FieldBackend N k s n t)
variable (cfg : RuntimeVerifier.Public (g := g) binary prime P R (fields := fields) (Advice := Advice)
  (Base := BoundedBytes capacity) (Key := Key) (C := C) (Salt := Salt))
variable (earlier : Request → Replay.Encoding g fields Advice (RuntimeVerifier.Authentication (g := g)) Key
  (RuntimeVerifier.Block (g := g) (fields := fields) (Advice := Advice) (Base := BoundedBytes capacity)) C)
variable (bodyCodec : PrefixCodec (Body g fields Advice (RuntimeVerifier.Authentication (g := g))))
variable (sample : RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice)
  (Base := BoundedBytes capacity) (Key := Key) → Tree Strand.Word Digest (Option C) blocks)
variable [Inhabited Salt] [Inhabited (RuntimeVerifier.Family binary prime P R cfg).Leaf]
variable (codec : Merkle.Indexed.Codec Salt (RuntimeVerifier.Family binary prime P R cfg).Leaf Digest Enc)
variable (merkleInput : Enc → Bytes)
local notation "M" => RuntimeAdaptiveVerifier.chain binary prime P R cfg earlier
local notation "Output" => RuntimeAdaptiveVerifier.Output (g := g) (fields := fields)
  (Advice := Advice) (Request := Request)
local notation "Annotated" => RuntimeAdaptiveMerkle.Annotated (g := g) (fields := fields)
  (Advice := Advice) (Base := BoundedBytes capacity) (Key := Key) (C := C) (Request := Request)
local notation "history" => StrandRuntime.history bodyCodec
local notation "oracle" => StrandVerifier.oracle binary prime P R cfg bodyCodec sample
local notation "ordinary" => TranscriptV2.StrandVerifier.replay history sample cfg.fallback (M)
local notation "claims" => RuntimeAdaptiveMerkle.claimOf binary prime P R cfg
local notation "authentication" => checkRaw codec claims merkleInput

/-- Complete verification uses one transcript replay and one tuple opening.
Finalization follows authentication and hashes the actual complete body. -/
def replay (output : Output) :
    Tree Bytes Digest (Annotated × Digest) (2+2*n+(blocks+1)*g.roles.length) :=
  Physical.authenticate history sample cfg.fallback (M) authentication output

theorem replay_result (output : Output) (SHA : Bytes → Digest) :
    ((replay binary prime P R cfg earlier bodyCodec sample codec merkleInput output).run SHA).1 =
      ((output,(M).replay output (oracle SHA) g.roles.length),
        StrandVerifier.finalSeal binary prime P R cfg earlier bodyCodec sample output SHA) :=
  Physical.authenticate_result history sample cfg.fallback (M) authentication output SHA

theorem authentication_trace_subset (output : Output) (SHA : Bytes → Digest) :
    ((authentication (output,(M).replay output (oracle SHA) g.roles.length)).run SHA).2 ⊆
      ((replay binary prime P R cfg earlier bodyCodec sample codec merkleInput output).run SHA).2 :=
  Physical.authentication_trace_subset history sample cfg.fallback (M) authentication output SHA

theorem replay_nonPrf_card (output : Output) (SHA : Bytes → Digest) :
    ((seen (replay binary prime P R cfg earlier bodyCodec sample codec merkleInput output) SHA).filter
      (fun raw => Strand.decodePrf raw = none)).card ≤ g.roles.length+1+2*n :=
  Physical.authenticate_nonPrf_card history sample cfg.fallback (M) authentication output SHA

variable (hashPublic : Key → Option (Fin binary.nPublic → Bool))
variable (decodePublic : BoundedBytes capacity → Option (Fin prime.nPublic → N))
variable (draw : C → RuntimeVerifier.RawSamples binary prime P R cfg)
local notation "Point" => RuntimeVerifier.Point (g := g) (fields := fields) (Advice := Advice)
  (Base := BoundedBytes capacity) (Key := Key)

omit [Inhabited Salt] in
/-- Runtime decoding reads only the reached ordinary answers. This derives
its congruence directly from the existing decoder and predecessor replay. -/
theorem decode_congr (output : Output) (H H' : Point → Digest × C)
    (agree : ∀ i < g.roles.length, H ((M).point output H i) = H' ((M).point output H i)) :
    RuntimeAdaptiveVerifier.decode binary prime P R cfg earlier hashPublic decodePublic draw output H =
      RuntimeAdaptiveVerifier.decode binary prime P R cfg earlier hashPublic decodePublic draw output H' := by
  let e := RuntimeAdaptiveVerifier.encodings binary prime P R cfg earlier output.request
  have answers i (within : i < g.roles.length) :
      H ((e.chain cfg.initialLink).point output.proof H i) =
        H' ((e.chain cfg.initialLink).point output.proof H i) := by
    simpa only [RuntimeAdaptiveVerifier.point_eq] using agree i within
  have points i (within : i ≤ g.roles.length) :
      (e.chain cfg.initialLink).point output.proof H i =
        (e.chain cfg.initialLink).point output.proof H' i := by
    apply congrArg (e.chain cfg.initialLink).input
    exact (e.chain cfg.initialLink).replay_congr_prefix output.proof H H' i
      (fun j hj => answers j (by omega))
  let parent := BackendPath.parent e cfg.initialLink output.proof H g.batchingIndex
  have parentEq : parent = BackendPath.parent e cfg.initialLink output.proof H' g.batchingIndex := by
    apply BackendQueries.Parent.point_injective (Body := Body g fields Advice (RuntimeVerifier.Authentication (g := g)))
    rw [BackendPath.parent_point,BackendPath.parent_point]
    exact points _ (Nat.le_of_lt g.batchingIndex.isLt)
  have pastEq : parent.point.priorAnswers H = parent.point.priorAnswers H' := by
    funext i
    change (H (parent.point.priorPoints i)).2 = (H' (parent.point.priorPoints i)).2
    have prior : parent.point.priorPoints i = (e.chain cfg.initialLink).point output.proof H i.val := by
      have transport {first second : Point} (same : first = second) (j : Fin first.rank) :
          first.priorPoints j = second.priorPoints ⟨j.val,by rw [← same]; exact j.isLt⟩ := by
        cases same
        rfl
      have parentPoint := BackendPath.parent_point e cfg.initialLink output.proof H g.batchingIndex
      exact (transport parentPoint i).trans (e.point_priorPoints cfg.initialLink output.proof H
        g.batchingIndex.val (Nat.le_of_lt g.batchingIndex.isLt) ⟨i.val,i.isLt⟩)
    rw [prior]
    exact congrArg Prod.snd (answers i.val (i.isLt.trans g.batchingIndex.isLt))
  have batchingEq : (H parent.point).2 = (H' parent.point).2 := by
    rw [BackendPath.parent_point]
    exact congrArg Prod.snd (answers _ g.batchingIndex.isLt)
  have openingEq : (H ((e.chain cfg.initialLink).point output.proof H g.openingIndex.val)).2 =
      (H' ((e.chain cfg.initialLink).point output.proof H g.openingIndex.val)).2 :=
    congrArg Prod.snd (answers _ g.openingIndex.isLt)
  dsimp only [RuntimeAdaptiveVerifier.decode]
  rw [← parentEq,← points _ (Nat.le_of_lt g.openingIndex.isLt),← pastEq,← batchingEq,← openingEq]

theorem decode_raw_congr (output : Output) (SHA SHA' : Bytes → Digest)
    (agree : ∀ qa ∈ ((replay binary prime P R cfg earlier bodyCodec sample codec merkleInput output).run SHA).2,
      SHA' qa.1 = qa.2) :
    RuntimeAdaptiveVerifier.decode binary prime P R cfg earlier hashPublic decodePublic draw output
        (oracle SHA) =
      RuntimeAdaptiveVerifier.decode binary prime P R cfg earlier hashPublic decodePublic draw output
        (oracle SHA') := by
  apply decode_congr binary prime P R cfg earlier hashPublic decodePublic draw output
  intro index within
  exact Physical.oracle_agree history sample cfg.fallback (M) output SHA SHA'
    (fun qa member => agree qa
      (Physical.ordinary_trace_subset history sample cfg.fallback (M) authentication output SHA member))
    ⟨index,within⟩

/-- Every hash on an opened column's path occurs in the actual complete
verifier replay. Successful decoding identifies the authenticated claim;
no separate path supplied by the analysis is trusted. -/
theorem decoded_path_visible (output : Output) (SHA : Bytes → Digest)
    (decoded : RuntimeVerifier.Decoded binary prime P R cfg)
    (decodedAt : RuntimeAdaptiveVerifier.decode binary prime P R cfg earlier
      hashPublic decodePublic draw output (oracle SHA) = some decoded)
    (column : Fin n) (opened : column ∈ decoded.claim.I) (vertex : ℕ)
    (onPath : vertex ∈ Heap.pathOf n column) :
    let input := pathInput codec decoded.claim.I decoded.claim.a decoded.claim.pf column opened
      (SHA ∘ merkleInput) vertex
    (merkleInput input,SHA (merkleInput input)) ∈
      ((replay binary prime P R cfg earlier bodyCodec sample codec merkleInput output).run SHA).2 := by
  have claim := RuntimeAdaptiveMerkle.claimOf_replay binary prime P R cfg earlier
    hashPublic decodePublic draw output (oracle SHA) decoded decodedAt
  apply authentication_trace_subset binary prime P R cfg earlier bodyCodec sample codec merkleInput output SHA
  rw [checkRaw_run]
  apply List.mem_map.mpr
  refine ⟨(_,SHA (merkleInput _)),?_,rfl⟩
  simp only [check,Tree.run_map]
  rw [claim]
  exact Merkle.Indexed.pathInput_visible codec decoded.claim.I decoded.claim.a decoded.claim.pf
    column opened (SHA ∘ merkleInput) vertex onPath

theorem verify_congr (output : Output) (SHA SHA' : Bytes → Digest)
    (agree : ∀ qa ∈ ((replay binary prime P R cfg earlier bodyCodec sample codec merkleInput output).run SHA).2,
      SHA' qa.1 = qa.2) :
    StrandVerifier.verify binary prime P R cfg earlier bodyCodec sample hashPublic decodePublic draw codec
        SHA merkleInput output =
      StrandVerifier.verify binary prime P R cfg earlier bodyCodec sample hashPublic decodePublic draw codec
        SHA' merkleInput output := by
  have ordinaryAgree : ∀ qa ∈ ((ordinary output).run SHA).2, SHA' qa.1 = qa.2 :=
    fun qa member => agree qa (Physical.ordinary_trace_subset history sample cfg.fallback (M) authentication output SHA member)
  have decodedEq := decode_raw_congr binary prime P R cfg earlier bodyCodec sample codec merkleInput
    hashPublic decodePublic draw output SHA SHA' agree
  have sampledEq : StrandVerifier.samplersSucceeded binary prime P R cfg earlier bodyCodec sample output SHA ↔
      StrandVerifier.samplersSucceeded binary prime P R cfg earlier bodyCodec sample output SHA' := by
    unfold StrandVerifier.samplersSucceeded
    exact forall_congr' (fun i => Physical.path_sampled_agree history sample cfg.fallback (M) output SHA SHA' ordinaryAgree i)
  have resultEq := congrArg Prod.fst (Tree.run_congr_on_trace
    (replay binary prime P R cfg earlier bodyCodec sample codec merkleInput output) SHA SHA' agree)
  rw [replay_result,replay_result] at resultEq
  have sealEq := congrArg Prod.snd resultEq
  change StrandVerifier.finalSeal binary prime P R cfg earlier bodyCodec sample output SHA' =
    StrandVerifier.finalSeal binary prime P R cfg earlier bodyCodec sample output SHA at sealEq
  have checksEq (decoded : RuntimeVerifier.Decoded binary prime P R cfg)
      (decodedAtSHA : RuntimeAdaptiveVerifier.decode binary prime P R cfg earlier hashPublic decodePublic draw
        output (oracle SHA) = some decoded) :
      StrandVerifier.Checks binary prime P R cfg earlier bodyCodec sample codec SHA merkleInput output decoded ↔
        StrandVerifier.Checks binary prime P R cfg earlier bodyCodec sample codec SHA' merkleInput output decoded := by
    have claim := RuntimeAdaptiveMerkle.claimOf_replay binary prime P R cfg earlier hashPublic decodePublic draw
      output (oracle SHA) decoded decodedAtSHA
    have root := checkRaw_root_congr codec claims merkleInput
      (output,(M).replay output (oracle SHA) g.roles.length) SHA SHA'
      (fun qa member => agree qa (authentication_trace_subset binary prime P R cfg earlier bodyCodec sample codec
        merkleInput output SHA member))
    rw [claim] at root
    unfold StrandVerifier.Checks
    rw [sampledEq]
    simp only [Bcs.Compiler.AcceptsIndexed,Merkle.Indexed.Accepts]
    rw [root,sealEq]
  apply Bool.eq_iff_iff.mpr
  rw [StrandVerifier.verify_true_iff,StrandVerifier.verify_true_iff]
  constructor
  · rintro ⟨decoded,hd,hc⟩
    exact ⟨decoded,decodedEq.symm.trans hd,(checksEq decoded hd).mp hc⟩
  · rintro ⟨decoded,hd,hc⟩
    have original := decodedEq.trans hd
    exact ⟨decoded,original,(checksEq decoded original).mpr hc⟩

/-- Authentication replay contains the search output and every subsequent
verification query. Equal raw observations therefore preserve the actual
accepting decision for the same submitted proof. -/
theorem verify_after_search_congr {fuel : ℕ} (program : Tree Bytes Digest Output fuel)
    (SHA SHA' : Bytes → Digest)
    (same : (program.bind (replay binary prime P R cfg earlier bodyCodec sample codec merkleInput)).run SHA =
      (program.bind (replay binary prime P R cfg earlier bodyCodec sample codec merkleInput)).run SHA') :
    StrandVerifier.verify binary prime P R cfg earlier bodyCodec sample hashPublic decodePublic draw codec
        SHA merkleInput (program.run SHA).1 =
      StrandVerifier.verify binary prime P R cfg earlier bodyCodec sample hashPublic decodePublic draw codec
        SHA' merkleInput (program.run SHA').1 := by
  have agree : ∀ qa ∈ ((program.bind
      (replay binary prime P R cfg earlier bodyCodec sample codec merkleInput)).run SHA).2,
      SHA' qa.1 = qa.2 := by
    intro qa member
    exact (Tree.trace_sound _ SHA' qa (by rw [← same]; exact member)).symm
  have searchSame := congrArg Prod.fst (Tree.run_congr_on_trace program SHA SHA' (by
    intro qa member
    apply agree qa
    rw [Tree.run_bind]
    exact List.mem_append_left _ member))
  rw [searchSame]
  apply verify_congr binary prime P R cfg earlier bodyCodec sample codec merkleInput hashPublic decodePublic draw
  intro qa member
  apply agree qa
  rw [Tree.run_bind]
  exact List.mem_append_right _ (by simpa only [searchSame] using member)

/-- The accepted decision is determined by the named execution's completed
cache. No application-decoder or Merkle-agreement certificate is supplied. -/
theorem verify_cache_completion {T : Type} {fuel : ℕ} (schema : Strand.History.Codec T)
    (program : Tree Bytes Digest Output fuel)
    (H : StrandSearch.Name Strand.OtherPoint T → StrandCoupling.Sample Digest Strand.Word)
    (SHA SHA' : Bytes → Digest)
    (cacheMatches : ((StrandSearch.searchState schema Subtype.val
      (recordTrace (mapQueries Strand.rawPoint (program.bind
        (replay binary prime P R cfg earlier bodyCodec sample codec merkleInput))))
          StrandCoupling.Cache.empty []).run H).1.1.2.Matches (SHA ∘ Strand.rawBytes))
    (cacheMatches' : ((StrandSearch.searchState schema Subtype.val
      (recordTrace (mapQueries Strand.rawPoint (program.bind
        (replay binary prime P R cfg earlier bodyCodec sample codec merkleInput))))
          StrandCoupling.Cache.empty []).run H).1.1.2.Matches (SHA' ∘ Strand.rawBytes)) :
    StrandVerifier.verify binary prime P R cfg earlier bodyCodec sample hashPublic decodePublic draw codec
        SHA merkleInput (program.run SHA).1 =
      StrandVerifier.verify binary prime P R cfg earlier bodyCodec sample hashPublic decodePublic draw codec
        SHA' merkleInput (program.run SHA').1 := by
  apply verify_after_search_congr binary prime P R cfg earlier bodyCodec sample codec merkleInput
    hashPublic decodePublic draw program SHA SHA'
  exact named_completion_run schema _ H SHA SHA' cacheMatches cacheMatches'

end Runtime
end LfzkV2.Current.StrandAuthentication
