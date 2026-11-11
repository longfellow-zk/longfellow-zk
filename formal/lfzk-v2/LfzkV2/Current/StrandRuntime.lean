import LfzkV2.Current.QueryRuntime
import LfzkV2.Current.StrandQueryCodec
import LfzkV2.Current.StrandSearch
import TranscriptV2.StrandVerifierCoupling

/-! The strand parser uses the runtime's canonical packet schemas. Parsed
packets reconstruct the existing verifier caches and the same predecessor
relation; no serialization or independence law for redundant caches is needed. -/
noncomputable section
namespace LfzkV2.Current.StrandRuntime
open CanonicalPrefix QueryRuntime
open scoped Classical

section Generic
variable {Key Fresh Body : Type} {capacity : ℕ}
variable (bodyCodec : PrefixCodec Body) (context : Key)

private def historyFrom (roles : List Role) : (n : ℕ) → n ≤ roles.length →
    History Key (Block capacity Fresh) Digest n → Bytes → TranscriptV2.Strand.History
  | 0, _, _, message => .root message
  | n+1, within, previous, message =>
      .child (historyFrom roles n (by omega) previous.1
        (previous.2.1.1.bytes ++ StrandQueryCodec.roundFooter (roles.get ⟨n,by omega⟩).domain))
        previous.2.2 message

/-- The verifier's existing history determines the digest-linked node.
Only the current payload and one parent digest enter its wire encoding;
the full history here is proof metadata used to justify its interpretation. -/
def history {roles : List Role} : Input roles Key (Block capacity Fresh) Digest Body →
    TranscriptV2.Strand.History
  | .round i previous current => historyFrom roles i.val (by omega) previous
      (current.1.bytes ++ StrandQueryCodec.roundFooter (roles.get i).domain)
  | .finalSeal previous body => historyFrom roles roles.length le_rfl previous
      (StrandQueryCodec.finalFooter ++ frame (bodyCodec.encode body))

theorem history_length {roles : List Role} (point : Input roles Key (Block capacity Fresh) Digest Body) :
    (history bodyCodec point).ancestors.length = point.rank+1 := by
  have length (n : ℕ) (within : n ≤ roles.length)
      (previous : History Key (Block capacity Fresh) Digest n) (message : Bytes) :
      (historyFrom roles n within previous message).ancestors.length = n+1 := by
    induction n generalizing message with
    | zero => rfl
    | succ n ih =>
        simp only [historyFrom,TranscriptV2.Strand.History.ancestors,List.length_cons,ih]
  cases point <;> exact length _ _ _ _

theorem history_depth {roles : List Role} (point : Input roles Key (Block capacity Fresh) Digest Body) :
    (history bodyCodec point).depth = point.rank := by
  have length := history_length bodyCodec point
  rw [TranscriptV2.Strand.History.ancestors_length] at length
  exact Nat.add_right_cancel length

theorem history_root {roles : List Role} (point : Input roles Key (Block capacity Fresh) Digest Body)
    (first : point.rank = 0) : ∃ message, history bodyCodec point = .root message := by
  cases point with
  | round i previous current =>
      rcases i with ⟨n,within⟩
      change n = 0 at first
      subst n
      exact ⟨_,rfl⟩
  | finalSeal previous body =>
      have empty : roles = [] := List.eq_nil_of_length_eq_zero first
      subst roles
      exact ⟨_,rfl⟩

/-- The typed verifier's predecessor and link are exactly the parent and
digest in the strand serializer. Redundant caches add no hash input. -/
theorem history_parent {roles : List Role} (initial : Digest)
    (point earlier : Input roles Key (Block capacity Fresh) Digest Body)
    (previous : point.parent = some earlier) :
    ∃ message, history bodyCodec point =
      .child (history bodyCodec earlier) (point.claimed initial) message := by
  cases point with
  | round i past current =>
      rcases i with ⟨n,within⟩
      cases n with
      | zero => cases previous
      | succ n =>
          cases Option.some.inj previous
          exact ⟨_,rfl⟩
  | finalSeal past body =>
      cases roles with
      | nil => cases previous
      | cons role tail =>
          cases Option.some.inj previous
          exact ⟨_,rfl⟩

theorem history_prepend {roles : List Role} (role : Role) (block : Block capacity Fresh) (link : Digest)
    (point : Input roles Key (Block capacity Fresh) Digest Body) :
    history bodyCodec (prepend role block link point) =
      (history bodyCodec point).prepend (block.1.bytes ++ StrandQueryCodec.roundFooter role.domain) link := by
  have round (i : Fin roles.length) (past : History Key (Block capacity Fresh) Digest i.val)
      (current : Block capacity Fresh) :
      history bodyCodec (prepend role block link (.round i past current)) =
        (history bodyCodec (.round i past current)).prepend
          (block.1.bytes ++ StrandQueryCodec.roundFooter role.domain) link := by
    rcases i with ⟨n,within⟩
    induction n generalizing current with
    | zero => rfl
    | succ n ih =>
        change TranscriptV2.Strand.History.child
          (history bodyCodec (prepend role block link (.round ⟨n,by omega⟩ past.1 past.2.1))) past.2.2 _ =
            TranscriptV2.Strand.History.child
              ((history bodyCodec (.round ⟨n,by omega⟩ past.1 past.2.1)).prepend
                (block.1.bytes ++ StrandQueryCodec.roundFooter role.domain) link) past.2.2 _
        rw [ih]
        simp only [List.get_cons_succ]
  cases point with
  | round i past current => exact round i past current
  | finalSeal past body =>
      cases roles with
      | nil => rfl
      | cons previous tail =>
          change TranscriptV2.Strand.History.child
            (history bodyCodec (prepend role block link (.round ⟨tail.length,by simp⟩ past.1 past.2.1))) past.2.2 _ =
              TranscriptV2.Strand.History.child
                ((history bodyCodec (.round ⟨tail.length,by simp⟩ past.1 past.2.1)).prepend
                  (block.1.bytes ++ StrandQueryCodec.roundFooter role.domain) link) past.2.2 _
          rw [round]

/-- The raw verifier serializer and the online canonical parser use the
same node bytes. This derives their correspondence from the packet codecs. -/
theorem history_embed (packets : List (Packet Fresh capacity))
    (value : QueryCodec.Value bodyCodec (packets.map Packet.queryBlock)) :
    history bodyCodec (embed bodyCodec context packets value) =
      StrandQueryCodec.toHistory bodyCodec (packets.map Packet.queryBlock) value := by
  induction packets with
  | nil =>
      change TranscriptV2.Strand.History.root (StrandQueryCodec.finalFooter ++ frame (bodyCodec.encode value.val)) =
        TranscriptV2.Strand.History.root (StrandQueryCodec.finalFooter ++ bytes.encode ⟨bodyCodec.encode value.val,value.property⟩)
      rw [bytes_encode]
  | cons packet tail ih =>
      rcases value with ⟨value,next⟩
      cases next with
      | inl stop => rfl
      | inr next =>
          rcases next with ⟨link,next⟩
          simp only [List.map_cons,embed]
          rw [history_prepend,ih,StrandQueryCodec.history_continue]
          rfl

theorem history_reindex {first second : List Role} (equal : first = second)
    (point : Input first Key (Block capacity Fresh) Digest Body) :
    history bodyCodec (reindex equal point) = history bodyCodec point := by
  cases equal
  rfl

/-- The terminal message is exactly the encoder's canonical body. The
absorbing continuation contains only the preceding node's digest. -/
theorem history_final_input {roles : List Role}
    (past : History Key (Block capacity Fresh) Digest roles.length) (body : Body) :
    ∃ state, (history bodyCodec (Input.finalSeal (roles := roles) past body)).input.encode =
      TranscriptV2.StrandTranscript.finalNodeInput state (bodyCodec.encode body) := by
  cases roles with
  | nil => exact ⟨.root [],rfl⟩
  | cons role tail => exact ⟨TranscriptV2.Strand.continuation
      (history bodyCodec (Input.finalSeal (roles := role::tail) past body)).id past.2.2,rfl⟩

/-- Parsing a predecessor and then rebuilding its cache agrees with taking
the predecessor of the rebuilt verifier input. -/
theorem embed_parent (packets : List (Packet Fresh capacity))
    (value : QueryCodec.Value bodyCodec (packets.map Packet.queryBlock)) :
    (embed bodyCodec context packets value).parent =
      (StrandQueryCodec.parent bodyCodec (packets.map Packet.queryBlock) value).map
        (embed bodyCodec context packets) := by
  induction packets with
  | nil => rfl
  | cons packet tail ih =>
      rcases value with ⟨value,next⟩
      cases next with
      | inl stop => rfl
      | inr next =>
          rcases next with ⟨link,next⟩
          simp only [List.map_cons,embed,parent_prepend,ih,embed_context,StrandQueryCodec.parent]
          cases found : StrandQueryCodec.parent bodyCodec (tail.map Packet.queryBlock) next <;> rfl
end Generic

section Replay
open TranscriptV2

variable {Key Fresh Body C Out : Type} {capacity rounds blocks : ℕ} {roles : List Role}
variable (bodyCodec : PrefixCodec Body)
local notation "Point" => Input roles Key (Block capacity Fresh) Digest Body
variable (model : Chain (Input roles Key (Block capacity Fresh) Digest Body) Digest C Out rounds) (initial : Digest)
variable (ranks : ∀ point : Input roles Key (Block capacity Fresh) Digest Body, model.rank point = point.rank)
variable (parents : ∀ point : Input roles Key (Block capacity Fresh) Digest Body, model.parent point = point.parent)
variable (links : ∀ point : Input roles Key (Block capacity Fresh) Digest Body, model.claimed point = point.claimed initial)
variable (sample : Input roles Key (Block capacity Fresh) Digest Body →
  Merkle.RandomOracle.Tree Strand.Word Digest (Option C) blocks) (fallback : C)

local notation "oracleOf" => StrandVerifier.oracle (history bodyCodec) sample fallback

/-- The actual verifier replay, with its raw trace retained, consumes at
most one fresh sample per boundary and one for the final node. Online
history naming does not add samples or count each rejected PRF draw again. -/
theorem named_replay_length {T : Type} (schema : Strand.History.Codec T)
    (out : Out) (state : StrandCoupling.Cache Strand.OtherPoint Strand.PrfKey Digest Strand.Word)
    (past : List Strand.Entry)
    (H : StrandSearch.Name Strand.OtherPoint T → StrandCoupling.Sample Digest Strand.Word)
    (reserved : state.Reserved (StrandSearch.key Subtype.val)) :
    ((StrandSearch.searchState schema Subtype.val
      (mapQueries Strand.rawPoint (recordTrace (StrandVerifier.beforeSeal (history bodyCodec) sample fallback model out)))
      state past).run H).2.length ≤ rounds+1 := by
  apply StrandSearch.searchState_length schema Subtype.val _ state past H
  intro answers
  rw [StrandCoupling.eagerState_recordTrace_queries]
  exact StrandVerifier.Coupling.beforeSeal_length (history bodyCodec) sample fallback model out state answers reserved

include ranks parents links in
/-- Raw replay supplies every stored parent digest. Consistency is a
consequence of the runtime transitions and node reads, not a certificate. -/
theorem replay_consistent (out : Out) (G : Strand.Oracle) (n : ℕ) (within : n ≤ rounds) :
    (history bodyCodec (model.point out (oracleOf G) n)).Consistent G := by
  induction n with
  | zero =>
      have rank : (model.point out (oracleOf G) 0).rank = 0 :=
        (ranks _).symm.trans (model.point_rank out (oracleOf G) (Nat.zero_le _))
      obtain ⟨message,equal⟩ := history_root bodyCodec _ rank
      rw [equal]
      trivial
  | succ n ih =>
      have parent := model.point_parent out (oracleOf G) (by omega : n < rounds)
      rw [parents] at parent
      obtain ⟨message,equal⟩ := history_parent bodyCodec initial _ _ parent
      rw [equal]
      refine ⟨ih (by omega),?_⟩
      have answer := model.point_link out (oracleOf G) (by omega : n < rounds)
      rw [links] at answer
      rw [answer]
      exact StrandVerifier.oracle_node (history bodyCodec) sample fallback G _

include parents initial in
/-- Every earlier reached node occurs in the terminal history. This is a
property of replay's predecessor relation, independent of hash collisions. -/
theorem replay_node_mem (out : Out) (oracle : Point → Digest × C)
    (n j : ℕ) (within : n ≤ rounds) (earlier : j ≤ n) :
    (history bodyCodec (model.point out oracle j)).input.encode ∈
      (history bodyCodec (model.point out oracle n)).ancestors := by
  induction n with
  | zero =>
      have zero : j = 0 := by omega
      subst j
      exact Strand.History.mem_ancestors _
  | succ n ih =>
      by_cases current : j = n+1
      · subst j; exact Strand.History.mem_ancestors _
      · have parent := model.point_parent out oracle (by omega : n < rounds)
        rw [parents] at parent
        obtain ⟨message,equal⟩ := history_parent bodyCodec initial _ _ parent
        rw [equal]
        exact List.mem_cons_of_mem _ (ih (by omega) (by omega))

include ranks parents initial in
/-- Ancestor recovery stays inside the reached path. Its collision scope
never includes an unqueried or counterfactual transcript history. -/
theorem replay_ancestors (out : Out) (oracle : Point → Digest × C) (scope : Bytes → Prop)
    (visible : ∀ i ≤ rounds, scope (history bodyCodec (model.point out oracle i)).input.encode)
    (n : ℕ) (within : n ≤ rounds) :
    ∀ raw ∈ (history bodyCodec (model.point out oracle n)).ancestors, scope raw := by
  induction n with
  | zero =>
      have rank : (model.point out oracle 0).rank = 0 :=
        (ranks _).symm.trans (model.point_rank out oracle (Nat.zero_le _))
      obtain ⟨message,equal⟩ := history_root bodyCodec _ rank
      intro raw member
      rw [equal] at member
      have same := List.mem_singleton.mp member
      rw [same,← equal]
      exact visible 0 (Nat.zero_le _)
  | succ n ih =>
      have parent := model.point_parent out oracle (by omega : n < rounds)
      rw [parents] at parent
      obtain ⟨message,equal⟩ := history_parent bodyCodec initial _ _ parent
      intro raw member
      rw [equal] at member
      rcases List.mem_cons.mp member with current | earlier
      · rw [current,← equal]
        exact visible (n+1) within
      · exact ih (by omega) raw earlier

include ranks parents links in
/-- Different reached boundaries have different digests outside collisions
on actual verifier queries. This discharges final-seal freshness without a
serialized round counter or an assumption about the adversary's query order. -/
theorem replay_digest_injective (out : Out) (G : Strand.Oracle)
    (collisionFree : ∀ a ∈ seen (StrandVerifier.beforeSeal (history bodyCodec) sample fallback model out) G,
      Strand.decodePrf a = none →
      ∀ b ∈ seen (StrandVerifier.beforeSeal (history bodyCodec) sample fallback model out) G,
      Strand.decodePrf b = none →
      G a = G b → a = b) :
    Function.Injective (fun i : Fin (rounds+1) => G (history bodyCodec (model.point out (oracleOf G) i.val)).input.encode) := by
  let scope := fun raw => raw ∈ seen (StrandVerifier.beforeSeal (history bodyCodec) sample fallback model out) G ∧
    Strand.decodePrf raw = none
  have visible i (within : i ≤ rounds) : scope (history bodyCodec (model.point out (oracleOf G) i)).input.encode :=
    ⟨StrandVerifier.beforeSeal_nodes_visible (history bodyCodec) sample fallback model out G ⟨i,by omega⟩,
      (Strand.History.nodePoint (history bodyCodec (model.point out (oracleOf G) i))).property⟩
  have ancestors := replay_ancestors bodyCodec model initial ranks parents out (oracleOf G) scope visible
  have actual := replay_consistent bodyCodec model initial ranks parents links sample fallback out G
  intro i j same
  have hi : i.val ≤ rounds := by have := i.isLt; omega
  have hj : j.val ≤ rounds := by have := j.isLt; omega
  have input := collisionFree _ (visible i.val hi).1 (visible i.val hi).2
    _ (visible j.val hj).1 (visible j.val hj).2 same
  have equal := Strand.History.erasure_injective G _ _ (actual i.val hi) (actual j.val hj)
    (fun a ha b hb => collisionFree a (ancestors i.val hi a ha).1 (ancestors i.val hi a ha).2
      b (ancestors j.val hj b hb).1 (ancestors j.val hj b hb).2) input
  have count := congrArg (fun value : Strand.History => value.ancestors.length) equal
  rw [history_length,history_length,← ranks,← ranks,model.point_rank out (oracleOf G) hi,model.point_rank out (oracleOf G) hj] at count
  exact Fin.ext (Nat.add_right_cancel count)

include ranks in
/-- The final PRF address is different from every earlier sampler address
because its strand id is the next position. Hash collisions do not affect
this syntactic fact; the bound rules out counter wrap, as Rust does. -/
theorem replay_seal_fresh (out : Out) (G : Strand.Oracle) (fits : rounds < 2^64) :
    (StrandVerifier.sealModel (history bodyCodec) model).point
        ((StrandVerifier.beforeSeal (history bodyCodec) sample fallback model out).run G).1 G ∉
      seen (StrandVerifier.beforeSeal (history bodyCodec) sample fallback model out) G := by
  have position (i : ℕ) (within : i ≤ rounds) :
      (history bodyCodec (model.point out (oracleOf G) i)).id.val = i := by
    have depth : (history bodyCodec (model.point out (oracleOf G) i)).depth = i := by
      rw [history_depth,← ranks,model.point_rank out (oracleOf G) within]
    rw [Strand.History.id_val _ (by rw [depth]; omega),depth]
  apply StrandVerifier.seal_fresh (history bodyCodec) sample fallback model out G
  intro i same
  have equal := congrArg Fin.val same
  change (history bodyCodec (model.point out (oracleOf G) i.val)).id.val =
    (history bodyCodec (model.point out (oracleOf G) rounds)).id.val at equal
  rw [position i.val (by omega),position rounds le_rfl] at equal
  exact (Nat.ne_of_lt i.isLt) equal

include ranks in
/-- An accepted final seal forces the original raw prover's PRF query,
except for the separately bounded seal guess. Verifier replay cannot
supply that query: its preceding queries have different node or PRF ids. -/
theorem seal_required {fuel : ℕ} (search : Merkle.RandomOracle.Tree Bytes Digest Out fuel)
    (G : Strand.Oracle) (fits : rounds < 2^64)
    (unguessed : ¬StrandSealCharging.Guess (StrandVerifier.sealModel (history bodyCodec) model)
      (search.bind (StrandVerifier.beforeSeal (history bodyCodec) sample fallback model)) G)
    (valid : StrandVerifier.sealValid (history bodyCodec) sample fallback model (search.run G).1 G) :
    (StrandVerifier.sealModel (history bodyCodec) model).point
      ((search.bind (StrandVerifier.beforeSeal (history bodyCodec) sample fallback model)).run G).1 G ∈ seen search G := by
  let finish := StrandVerifier.beforeSeal (history bodyCodec) sample fallback model
  apply StrandSealCharging.required_before_replay (StrandVerifier.sealModel (history bodyCodec) model) search finish G unguessed
  · change G ((StrandVerifier.sealModel (history bodyCodec) model).point ((search.bind finish).run G).1 G) = _
    rw [Merkle.RandomOracle.Tree.run_bind]
    have result := StrandVerifier.beforeSeal_result (history bodyCodec) sample fallback model (search.run G).1 G
    simpa only [finish,StrandVerifier.sealValid,StrandVerifier.sealModel,result] using valid
  · simpa only [Merkle.RandomOracle.Tree.run_bind] using
      replay_seal_fresh bodyCodec model ranks sample fallback (search.run G).1 G fits

end Replay

section CompleteBody
variable {g : Geometry} {fields : Fields} {Advice Authentication Key Fresh C : Type} {capacity : ℕ}
variable (bodyCodec : PrefixCodec (Current.Body g fields Advice Authentication))
variable (encoding : Replay.Encoding g fields Advice Authentication Key (Block capacity Fresh) C)

/-- The existing complete-proof replay owns the body used by the strand
seal. A caller cannot replace it with a separately chosen final message. -/
theorem complete_body_node (initial : Digest) (proof : Replay.Output g fields Advice Authentication)
    (H : Replay.Point g fields Advice Authentication Key (Block capacity Fresh) → Digest × C) :
    ∃ state, (history bodyCodec ((encoding.chain initial).finalSealPoint proof H)).input.encode =
      TranscriptV2.StrandTranscript.finalNodeInput state (bodyCodec.encode proof.body) := by
  obtain ⟨past,equal⟩ := encoding.finalSealPoint_body initial proof H
  rw [equal]
  exact history_final_input bodyCodec past proof.body

end CompleteBody

namespace Runtime
variable {g : Geometry} {fields : Fields} {Advice : Type}
variable (repr : ProofBodyCodec.Representations fields Advice)
variable (shape : WireBlocks.Shape g fields) (setup : FingerprintPrefix.Setup) (publicCount : ℕ)

local notation "Value" => QueryRuntime.Runtime.Value repr shape setup publicCount
local notation "Point" => QueryRuntime.Runtime.Point repr shape setup publicCount
local notation "bodyCodec" => ProofBodyCodec.codec repr g
local notation "blocks" => QueryRuntime.Runtime.blocks repr shape setup publicCount
local notation "toPoint" => QueryRuntime.Runtime.toPoint repr shape setup publicCount

/-- This is instantiated with the existing first-fingerprint packet and
every role-local runtime packet, including the complete canonical proof body. -/
def schema : TranscriptV2.Strand.History.Codec Value := StrandQueryCodec.schema bodyCodec blocks

/-- The actual runtime serializer is the same encoding recognized by the
online decoder. No assumption about arbitrary cache serialization is needed. -/
theorem toPoint_history (value : Value) :
    StrandRuntime.history bodyCodec (toPoint value) = (schema repr shape setup publicCount).encode value := by
  unfold QueryRuntime.Runtime.toPoint
  rw [history_reindex,history_embed]
  rfl

theorem parent_key (value earlier : Value)
    (previous : StrandQueryCodec.parent bodyCodec blocks value = some earlier) :
    QueryRuntime.Runtime.key repr shape setup publicCount value =
      QueryRuntime.Runtime.key repr shape setup publicCount earlier :=
  StrandQueryCodec.parent_first bodyCodec _ _ value earlier previous

/-- The parent relation consumed by the existing algebraic failure cover is
exactly the one obtained by dropping the last strand node. -/
theorem toPoint_parent (value earlier : Value)
    (previous : StrandQueryCodec.parent bodyCodec blocks value = some earlier) :
    (toPoint value).parent = some (toPoint earlier) := by
  dsimp only [QueryRuntime.Runtime.Value,QueryRuntime.Runtime.blocks] at value earlier previous
  unfold QueryRuntime.Runtime.toPoint
  rw [reindex_parent,embed_parent,previous,Option.map_some,Option.map_some,
    parent_key repr shape setup publicCount value earlier previous]

theorem history_parent (value earlier : Value)
    (previous : StrandQueryCodec.parent bodyCodec blocks value = some earlier) :
    ∃ digest message, (schema repr shape setup publicCount).encode value =
      .child ((schema repr shape setup publicCount).encode earlier) digest message :=
  StrandQueryCodec.history_parent bodyCodec blocks value earlier previous

/-- Parsed packet values and canonical runtime points are the same finite
objects. The verifier's redundant caches add no independent coordinates. -/
def valuesEquiv (fits : g.roles.length < 2^64) :
    Value ≃ {point : Point // QueryRuntime.Runtime.Canonical repr shape setup publicCount point} :=
  Equiv.ofInjective toPoint (QueryRuntime.Runtime.toPoint_injective repr shape setup publicCount fits)

theorem valuesEquiv_apply (fits : g.roles.length < 2^64) (value : Value) :
    ((valuesEquiv repr shape setup publicCount fits) value).val = toPoint value := rfl

theorem valuesEquiv_symm (fits : g.roles.length < 2^64)
    (point : {point : Point // QueryRuntime.Runtime.Canonical repr shape setup publicCount point}) :
    toPoint ((valuesEquiv repr shape setup publicCount fits).symm point) = point.val := by
  have same := congrArg Subtype.val ((valuesEquiv repr shape setup publicCount fits).apply_symm_apply point)
  rw [valuesEquiv_apply] at same
  exact same

variable {P : Type}

/-- Give each canonical verifier input its one ordinary name in the
renamed search. All speculative and malformed names remain in the complement. -/
def pointCodec (fits : g.roles.length < 2^64) (locate : Value → P) :
    ByteOracleTransport.Codec Point (StrandSearch.Name P Value)
      (QueryRuntime.Runtime.Canonical repr shape setup publicCount) where
  encode point :=
    let value := (valuesEquiv repr shape setup publicCount fits).symm point
    .inl (locate value,some value)
  decode
    | .inl (point,some value) =>
        if point = locate value then some ((valuesEquiv repr shape setup publicCount fits) value) else none
    | _ => none
  decode_encode point := by simp only [Equiv.apply_symm_apply,if_true]
  encode_decode raw point found := by
    cases raw with
    | inr _ => cases found
    | inl raw =>
        rcases raw with ⟨raw,value⟩
        cases value with
        | none => cases found
        | some value =>
            change (if raw = locate value then some ((valuesEquiv repr shape setup publicCount fits) value)
              else none) = some point at found
            by_cases equal : raw = locate value
            · rw [if_pos equal] at found
              cases Option.some.inj found
              simp only [Equiv.symm_apply_apply,equal]
            · rw [if_neg equal] at found
              contradiction

/-- Merkle preimages start with ASCII `p`, whereas every canonical
strand node starts with type word one. Even a forged logical annotation
cannot make these raw bytes spend an ordinary protocol-query allowance. -/
theorem pointCodec_merkle_auxiliary (fits : g.roles.length < 2^64) (locate : Value → P)
    (bytes : P → Bytes)
    (located : ∀ value, bytes (locate value) = ((schema repr shape setup publicCount).encode value).input.encode)
    (raw : P) (value : Option Value) (merkle : (bytes raw).head? = some 112) :
    (pointCodec repr shape setup publicCount fits locate).decode (.inl (raw,value)) = none := by
  cases value with
  | none => rfl
  | some value =>
      have different : raw ≠ locate value := by
        intro same
        rw [same,located value] at merkle
        have first : (((schema repr shape setup publicCount).encode value).input.encode).head? = some 1 := by
          cases (schema repr shape setup publicCount).encode value <;> rfl
        rw [first] at merkle
        exact (by decide : (1 : TranscriptV2.Framing.Byte) ≠ 112) (Option.some.inj merkle)
      simp only [pointCodec,if_neg different]

/-- Every ordinary name actually emitted by online decoding is in this
canonical image. The raw-byte equality follows from parsing, not a promise
about how a caller constructed its cache. -/
theorem pointCodec_ordinary (fits : g.roles.length < 2^64) (locate : Value → P)
    (bytes : P → Bytes) (injective : Function.Injective bytes)
    (located : ∀ value, bytes (locate value) = ((schema repr shape setup publicCount).encode value).input.encode)
    (past : List TranscriptV2.Strand.Entry) (raw : P) (value : Value)
    (parsed : StrandSearch.decode (schema repr shape setup publicCount) bytes past raw = some value) :
    ((pointCodec repr shape setup publicCount fits locate).decode (.inl (raw,some value))).map Subtype.val =
      some (toPoint value) := by
  have same : raw = locate value := injective
    ((StrandSearch.decode_erases (schema repr shape setup publicCount) bytes past raw value parsed).symm.trans
      (located value).symm)
  simp only [pointCodec,if_pos same,Option.map_some,valuesEquiv]
  rfl

end Runtime
end LfzkV2.Current.StrandRuntime
