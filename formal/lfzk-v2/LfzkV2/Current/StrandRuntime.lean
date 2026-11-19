import LfzkV2.Current.QueryPacket
import LfzkV2.Current.Replay
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
variable (wire : NodeWire) (bodyCodec : WholeCodec Body) (context : Key)

private def historyFrom (roles : List Role) : (n : ℕ) → n ≤ roles.length →
    History Key (Block capacity Fresh) Digest n → Bytes → TranscriptV2.Strand.History
  | 0, _, _, message => .root message
  | n+1, within, previous, message =>
      .child (historyFrom roles n (by omega) previous.1
        (previous.2.1.1.bytes ++ wire.terminator (roles.get ⟨n,by omega⟩).domain))
        previous.2.2 message

/-- The verifier's existing history determines the digest-linked node.
Only the current payload and one parent digest enter its wire encoding;
the full history here is proof metadata used to justify its interpretation. -/
def history {roles : List Role} : Input roles Key (Block capacity Fresh) Digest Body →
    TranscriptV2.Strand.History
  | .round i previous current => historyFrom wire roles i.val (by omega) previous
      (current.1.bytes ++ wire.terminator (roles.get i).domain)
  | .finalSeal previous body => historyFrom wire roles roles.length le_rfl previous
      (wire.sealFrame (bodyCodec.encode body))

theorem history_length {roles : List Role} (point : Input roles Key (Block capacity Fresh) Digest Body) :
    (history wire bodyCodec point).ancestors.length = point.rank+1 := by
  have length (n : ℕ) (within : n ≤ roles.length)
      (previous : History Key (Block capacity Fresh) Digest n) (message : Bytes) :
      (historyFrom wire roles n within previous message).ancestors.length = n+1 := by
    induction n generalizing message with
    | zero => rfl
    | succ n ih =>
        simp only [historyFrom,TranscriptV2.Strand.History.ancestors,List.length_cons,ih]
  cases point <;> exact length _ _ _ _

theorem history_depth {roles : List Role} (point : Input roles Key (Block capacity Fresh) Digest Body) :
    (history wire bodyCodec point).depth = point.rank := by
  have length := history_length wire bodyCodec point
  rw [TranscriptV2.Strand.History.ancestors_length] at length
  exact Nat.add_right_cancel length

theorem history_root {roles : List Role} (point : Input roles Key (Block capacity Fresh) Digest Body)
    (first : point.rank = 0) : ∃ message, history wire bodyCodec point = .root message := by
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
    ∃ message, history wire bodyCodec point =
      .child (history wire bodyCodec earlier) (point.claimed initial) message := by
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
    history wire bodyCodec (prepend role block link point) =
      (history wire bodyCodec point).prepend (block.1.bytes ++ wire.terminator role.domain) link := by
  have round (i : Fin roles.length) (past : History Key (Block capacity Fresh) Digest i.val)
      (current : Block capacity Fresh) :
      history wire bodyCodec (prepend role block link (.round i past current)) =
        (history wire bodyCodec (.round i past current)).prepend
          (block.1.bytes ++ wire.terminator role.domain) link := by
    rcases i with ⟨n,within⟩
    induction n generalizing current with
    | zero => rfl
    | succ n ih =>
        change TranscriptV2.Strand.History.child
          (history wire bodyCodec (prepend role block link (.round ⟨n,by omega⟩ past.1 past.2.1))) past.2.2 _ =
            TranscriptV2.Strand.History.child
              ((history wire bodyCodec (.round ⟨n,by omega⟩ past.1 past.2.1)).prepend
                (block.1.bytes ++ wire.terminator role.domain) link) past.2.2 _
        rw [ih]
        simp only [List.get_cons_succ]
  cases point with
  | round i past current => exact round i past current
  | finalSeal past body =>
      cases roles with
      | nil => rfl
      | cons previous tail =>
          change TranscriptV2.Strand.History.child
            (history wire bodyCodec (prepend role block link (.round ⟨tail.length,by simp⟩ past.1 past.2.1))) past.2.2 _ =
              TranscriptV2.Strand.History.child
                ((history wire bodyCodec (.round ⟨tail.length,by simp⟩ past.1 past.2.1)).prepend
                  (block.1.bytes ++ wire.terminator role.domain) link) past.2.2 _
          rw [round]

/-- The raw verifier serializer and the online canonical parser use the
same node bytes. This derives their correspondence from the packet codecs. -/
theorem history_embed (packets : List (Packet Fresh capacity))
    (value : QueryCodec.Value bodyCodec (packets.map Packet.queryBlock)) :
    history wire bodyCodec (embed bodyCodec context packets value) =
      StrandQueryCodec.toHistory wire bodyCodec (packets.map Packet.queryBlock) value := by
  induction packets with
  | nil =>
      change TranscriptV2.Strand.History.root (wire.sealFrame (bodyCodec.encode value.val)) =
        TranscriptV2.Strand.History.root (wire.sealCodec.encode ⟨bodyCodec.encode value.val,value.property⟩)
      rw [wire.sealCodec_encode]
  | cons packet tail ih =>
      rcases value with ⟨value,next⟩
      cases next with
      | inl stop => rfl
      | inr next =>
          rcases next with ⟨link,next⟩
          simp only [List.map_cons,embed]
          rw [history_prepend,ih,StrandQueryCodec.history_continue wire]
          rfl

theorem history_reindex {first second : List Role} (equal : first = second)
    (point : Input first Key (Block capacity Fresh) Digest Body) :
    history wire bodyCodec (reindex equal point) = history wire bodyCodec point := by
  cases equal
  rfl

/-- The terminal message is exactly the sealed canonical body. The
absorbing continuation contains only the preceding node's digest. -/
theorem history_seal_input {roles : List Role}
    (past : History Key (Block capacity Fresh) Digest roles.length) (body : Body) :
    ∃ state : TranscriptV2.Strand.Absorbing,
      (history wire bodyCodec (Input.finalSeal (roles := roles) past body)).input.encode =
        (state.write (wire.sealFrame (bodyCodec.encode body))).input.encode := by
  cases roles with
  | nil => exact ⟨.root [],rfl⟩
  | cons role tail => exact ⟨TranscriptV2.Strand.continuation
      (history wire bodyCodec (Input.finalSeal (roles := role::tail) past body)).id past.2.2,rfl⟩

/-- The seal is the final node of `TranscriptV2.StrandTranscript` under the
wire's seal frame. -/
theorem history_final_input {roles : List Role}
    (past : History Key (Block capacity Fresh) Digest roles.length) (body : Body) :
    ∃ state, (history wire bodyCodec (Input.finalSeal (roles := roles) past body)).input.encode =
      TranscriptV2.StrandTranscript.sealNodeInput wire.sealFrame state (bodyCodec.encode body) :=
  history_seal_input wire bodyCodec past body

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
variable (wire : NodeWire) (bodyCodec : WholeCodec Body)
local notation "Point" => Input roles Key (Block capacity Fresh) Digest Body
variable (model : Chain (Input roles Key (Block capacity Fresh) Digest Body) Digest C Out rounds) (initial : Digest)
variable (ranks : ∀ point : Input roles Key (Block capacity Fresh) Digest Body, model.rank point = point.rank)
variable (parents : ∀ point : Input roles Key (Block capacity Fresh) Digest Body, model.parent point = point.parent)
variable (links : ∀ point : Input roles Key (Block capacity Fresh) Digest Body, model.claimed point = point.claimed initial)
variable (sample : Input roles Key (Block capacity Fresh) Digest Body →
  Merkle.RandomOracle.Tree Strand.Word Digest (Option C) blocks) (fallback : C)

local notation "oracleOf" => StrandVerifier.oracle (history wire bodyCodec) sample fallback

include ranks parents links in
/-- Raw replay supplies every stored parent digest. Consistency is a
consequence of the runtime transitions and node reads, not a certificate. -/
theorem replay_consistent (out : Out) (G : Strand.Oracle) (n : ℕ) (within : n ≤ rounds) :
    (history wire bodyCodec (model.point out (oracleOf G) n)).Consistent G := by
  induction n with
  | zero =>
      have rank : (model.point out (oracleOf G) 0).rank = 0 :=
        (ranks _).symm.trans (model.point_rank out (oracleOf G) (Nat.zero_le _))
      obtain ⟨message,equal⟩ := history_root wire bodyCodec _ rank
      rw [equal]
      trivial
  | succ n ih =>
      have parent := model.point_parent out (oracleOf G) (by omega : n < rounds)
      rw [parents] at parent
      obtain ⟨message,equal⟩ := history_parent wire bodyCodec initial _ _ parent
      rw [equal]
      refine ⟨ih (by omega),?_⟩
      have answer := model.point_link out (oracleOf G) (by omega : n < rounds)
      rw [links] at answer
      rw [answer]
      exact StrandVerifier.oracle_node (history wire bodyCodec) sample fallback G _

include parents initial in
/-- Every earlier reached node occurs in the terminal history. This is a
property of replay's predecessor relation, independent of hash collisions. -/
theorem replay_node_mem (out : Out) (oracle : Point → Digest × C)
    (n j : ℕ) (within : n ≤ rounds) (earlier : j ≤ n) :
    (history wire bodyCodec (model.point out oracle j)).input.encode ∈
      (history wire bodyCodec (model.point out oracle n)).ancestors := by
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
        obtain ⟨message,equal⟩ := history_parent wire bodyCodec initial _ _ parent
        rw [equal]
        exact List.mem_cons_of_mem _ (ih (by omega) (by omega))

include ranks parents initial in
/-- Ancestor recovery stays inside the reached path. Its collision scope
never includes an unqueried or counterfactual transcript history. -/
theorem replay_ancestors (out : Out) (oracle : Point → Digest × C) (scope : Bytes → Prop)
    (visible : ∀ i ≤ rounds, scope (history wire bodyCodec (model.point out oracle i)).input.encode)
    (n : ℕ) (within : n ≤ rounds) :
    ∀ raw ∈ (history wire bodyCodec (model.point out oracle n)).ancestors, scope raw := by
  induction n with
  | zero =>
      have rank : (model.point out oracle 0).rank = 0 :=
        (ranks _).symm.trans (model.point_rank out oracle (Nat.zero_le _))
      obtain ⟨message,equal⟩ := history_root wire bodyCodec _ rank
      intro raw member
      rw [equal] at member
      have same := List.mem_singleton.mp member
      rw [same,← equal]
      exact visible 0 (Nat.zero_le _)
  | succ n ih =>
      have parent := model.point_parent out oracle (by omega : n < rounds)
      rw [parents] at parent
      obtain ⟨message,equal⟩ := history_parent wire bodyCodec initial _ _ parent
      intro raw member
      rw [equal] at member
      rcases List.mem_cons.mp member with current | earlier
      · rw [current,← equal]
        exact visible (n+1) within
      · exact ih (by omega) raw earlier

include ranks in
/-- The final PRF address is different from every earlier sampler address
because its strand id is the next position. Hash collisions do not affect
this syntactic fact; the bound rules out counter wrap, as Rust does. -/
theorem replay_seal_fresh (out : Out) (G : Strand.Oracle) (fits : rounds < 2^64) :
    (StrandVerifier.sealModel (history wire bodyCodec) model).point
        ((StrandVerifier.beforeSeal (history wire bodyCodec) sample fallback model out).run G).1 G ∉
      seen (StrandVerifier.beforeSeal (history wire bodyCodec) sample fallback model out) G := by
  have position (i : ℕ) (within : i ≤ rounds) :
      (history wire bodyCodec (model.point out (oracleOf G) i)).id.val = i := by
    have depth : (history wire bodyCodec (model.point out (oracleOf G) i)).depth = i := by
      rw [history_depth,← ranks,model.point_rank out (oracleOf G) within]
    rw [Strand.History.id_val _ (by rw [depth]; omega),depth]
  apply StrandVerifier.seal_fresh (history wire bodyCodec) sample fallback model out G
  intro i same
  have equal := congrArg Fin.val same
  change (history wire bodyCodec (model.point out (oracleOf G) i.val)).id.val =
    (history wire bodyCodec (model.point out (oracleOf G) rounds)).id.val at equal
  rw [position i.val (by omega),position rounds le_rfl] at equal
  exact (Nat.ne_of_lt i.isLt) equal

include ranks in
/-- An accepted final seal forces the original raw prover's PRF query,
except for the separately bounded seal guess. Verifier replay cannot
supply that query: its preceding queries have different node or PRF ids. -/
theorem seal_required {fuel : ℕ} (search : Merkle.RandomOracle.Tree Bytes Digest Out fuel)
    (G : Strand.Oracle) (fits : rounds < 2^64)
    (unguessed : ¬StrandSealCharging.Guess (StrandVerifier.sealModel (history wire bodyCodec) model)
      (search.bind (StrandVerifier.beforeSeal (history wire bodyCodec) sample fallback model)) G)
    (valid : StrandVerifier.sealValid (history wire bodyCodec) sample fallback model (search.run G).1 G) :
    (StrandVerifier.sealModel (history wire bodyCodec) model).point
      ((search.bind (StrandVerifier.beforeSeal (history wire bodyCodec) sample fallback model)).run G).1 G ∈ seen search G := by
  let finish := StrandVerifier.beforeSeal (history wire bodyCodec) sample fallback model
  apply StrandSealCharging.required_before_replay (StrandVerifier.sealModel (history wire bodyCodec) model) search finish G unguessed
  · change G ((StrandVerifier.sealModel (history wire bodyCodec) model).point ((search.bind finish).run G).1 G) = _
    rw [Merkle.RandomOracle.Tree.run_bind]
    have result := StrandVerifier.beforeSeal_result (history wire bodyCodec) sample fallback model (search.run G).1 G
    simpa only [finish,StrandVerifier.sealValid,StrandVerifier.sealModel,result] using valid
  · simpa only [Merkle.RandomOracle.Tree.run_bind] using
      replay_seal_fresh wire bodyCodec model ranks sample fallback (search.run G).1 G fits

end Replay

section CompleteBody
variable {g : Geometry} {fields : Fields} {Advice Authentication Key Fresh C : Type} {capacity : ℕ}
variable (wire : NodeWire) (bodyCodec : WholeCodec (Current.Body g fields Advice Authentication))
variable (encoding : Replay.Encoding g fields Advice Authentication Key (Block capacity Fresh) C)

/-- The existing complete-proof replay owns the body used by the strand
seal. A caller cannot replace it with a separately chosen final message. -/
theorem complete_body_node (initial : Digest) (proof : Replay.Output g fields Advice Authentication)
    (H : Replay.Point g fields Advice Authentication Key (Block capacity Fresh) → Digest × C) :
    ∃ state, (history wire bodyCodec ((encoding.chain initial).finalSealPoint proof H)).input.encode =
      TranscriptV2.StrandTranscript.sealNodeInput wire.sealFrame state (bodyCodec.encode proof.body) := by
  obtain ⟨past,equal⟩ := encoding.finalSealPoint_body initial proof H
  rw [equal]
  exact history_final_input wire bodyCodec past proof.body

end CompleteBody

end LfzkV2.Current.StrandRuntime
