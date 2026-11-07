import LfzkV2.Current.CanonicalReplay

/-! Canonical physical transcript prefixes retain canonical ancestors.
This is a parser property, independent of arithmetic correctness or verifier
acceptance. It supplies the canonical-coordinate restriction needed when a
raw-byte oracle is transported to the finite typed transcript oracle. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.OracleCanonicalAncestors
open CanonicalPrefix QueryRuntime
open scoped Classical
set_option maxHeartbeats 800000
set_option maxRecDepth 4096
variable {Key Fresh Body : Type} {capacity : ℕ}

private theorem prepend_context {roles : List Role} (role : Role)
    (block : Block capacity Fresh) (link : Digest)
    (point : Input roles Key (Block capacity Fresh) Digest Body) :
    (prepend role block link point).context = point.context := by
  have rounds : ∀ n (bound : n < roles.length) (history : History Key (Block capacity Fresh) Digest n) (current : Block capacity Fresh),
      (prepend role block link (.round ⟨n,bound⟩ history current : Input roles Key (Block capacity Fresh) Digest Body)).context =
        Input.historyContext n history := by
    intro n
    induction n with
    | zero => intros; rfl
    | succ n ih =>
      intro bound history current
      exact ih (by omega) history.1 history.2.1
  have finals : ∀ (tail : List Role) (history : History Key (Block capacity Fresh) Digest tail.length) (body : Body),
      (prepend role block link (.finalSeal history body : Input tail Key (Block capacity Fresh) Digest Body)).context =
        Input.historyContext tail.length history := by
    intro tail
    induction tail with
    | nil => intros; rfl
    | cons previous tail ih =>
      intro history body
      exact ih history.1 body
  cases point with
  | round i history current => exact rounds i.val i.isLt history current
  | finalSeal history body => exact finals roles history body

private theorem parent_prepend {roles : List Role} (role : Role)
    (block : Block capacity Fresh) (link : Digest)
    (point : Input roles Key (Block capacity Fresh) Digest Body) :
    (prepend role block link point).parent =
      match point.parent with
      | none => some (.round ⟨0,by simp⟩ point.context block)
      | some previous => some (prepend role block link previous) := by
  cases point with
  | round i history current =>
    rcases i with ⟨n,bound⟩
    cases n <;> rfl
  | finalSeal history body => cases roles <;> rfl

private theorem embed_context (bodyCodec : PrefixCodec Body) (context : Key)
    (packets : List (Packet Fresh capacity))
    (value : QueryCodec.Value bodyCodec (packets.map Packet.queryBlock)) :
    (embed bodyCodec context packets value).context = context := by
  induction packets with
  | nil => rfl
  | cons packet tail ih =>
    rcases value with ⟨value,stop | ⟨link,remaining⟩⟩
    · rfl
    · exact (prepend_context packet.role (packet.block value) link _).trans (ih remaining)

private theorem embed_parent (bodyCodec : PrefixCodec Body) (context : Key)
    (packets : List (Packet Fresh capacity))
    (value : QueryCodec.Value bodyCodec (packets.map Packet.queryBlock))
    (previous : Input (packets.map Packet.role) Key (Block capacity Fresh) Digest Body)
    (present : (embed bodyCodec context packets value).parent = some previous) :
    ∃ earlier : QueryCodec.Value bodyCodec (packets.map Packet.queryBlock),
      embed bodyCodec context packets earlier = previous := by
  induction packets with
  | nil => cases present
  | cons packet tail ih =>
    rcases value with ⟨value,stop | ⟨link,remaining⟩⟩
    · cases present
    · change (prepend packet.role (packet.block value) link (embed bodyCodec context tail remaining)).parent = some previous at present
      rw [parent_prepend] at present
      cases parent : (embed bodyCodec context tail remaining).parent with
      | none =>
        rw [parent] at present
        refine ⟨(value,.inl ()),?_⟩
        have same := Option.some.inj present
        exact (congrArg (fun key => Input.round (roles := (packet::tail).map Packet.role) (Body := Body)
          ⟨0,by simp⟩ key (packet.block value)) (embed_context bodyCodec context tail remaining)).symm.trans same
      | some older =>
        rw [parent] at present
        obtain ⟨earlier,same⟩ := ih remaining older parent
        refine ⟨(value,.inr (link,earlier)),?_⟩
        exact (congrArg (prepend packet.role (packet.block value) link) same).trans (Option.some.inj present)

private theorem embed_cons_parent (bodyCodec : PrefixCodec Body) (context : Key)
    (packet : Packet Fresh capacity) (tail : List (Packet Fresh capacity))
    (value : QueryCodec.Value bodyCodec ((packet::tail).map Packet.queryBlock))
    (previous : Input ((packet::tail).map Packet.role) Key (Block capacity Fresh) Digest Body)
    (present : (embed bodyCodec context (packet::tail) value).parent = some previous) :
    ∃ earlier : QueryCodec.Value bodyCodec ((packet::tail).map Packet.queryBlock),
      earlier.1 = value.1 ∧ embed bodyCodec context (packet::tail) earlier = previous := by
  rcases value with ⟨value,stop | ⟨link,remaining⟩⟩
  · cases present
  · change (prepend packet.role (packet.block value) link (embed bodyCodec context tail remaining)).parent = some previous at present
    rw [parent_prepend] at present
    cases parent : (embed bodyCodec context tail remaining).parent with
    | none =>
      rw [parent] at present
      refine ⟨(value,.inl ()),rfl,?_⟩
      exact (congrArg (fun key => Input.round (roles := (packet::tail).map Packet.role) (Body := Body)
        ⟨0,by simp⟩ key (packet.block value)) (embed_context bodyCodec context tail remaining)).symm.trans (Option.some.inj present)
    | some older =>
      rw [parent] at present
      obtain ⟨earlier,same⟩ := embed_parent bodyCodec context tail remaining older parent
      exact ⟨(value,.inr (link,earlier)),rfl,
        (congrArg (prepend packet.role (packet.block value) link) same).trans (Option.some.inj present)⟩

private theorem prior_closed {roles : List Role} {Context Block Link Body : Type}
    (property : Input roles Context Block Link Body → Prop)
    (closed : ∀ point previous, property point → point.parent = some previous → property previous)
    (point : Input roles Context Block Link Body) (good : property point) :
    ∀ i, property (point.priorPoints i) := by
  have go : ∀ n (point : Input roles Context Block Link Body), point.rank = n → property point →
      ∀ i, property (point.priorPoints i) := by
    intro n
    induction n with
    | zero =>
      intro current rank good i
      have := i.isLt
      omega
    | succ n ih =>
      intro current rank good i
      cases current with
      | round index history block =>
        rcases index with ⟨value,bound⟩
        change value = n+1 at rank
        subst value
        let previous : Input roles Context Block Link Body := .round ⟨n,by omega⟩ history.1 history.2.1
        have prior : property previous := closed _ previous good rfl
        refine Fin.lastCases ?_ (fun j => ?_) i
        · simpa only [Input.priorPoints,Input.historyPoints,Fin.snoc_last] using prior
        · simpa only [Input.priorPoints,Input.historyPoints,Fin.snoc_castSucc] using ih previous rfl prior j
      | finalSeal history body =>
        cases roles with
        | nil => exact Fin.elim0 i
        | cons role tail =>
          have size : tail.length = n := by
            change tail.length+1 = n+1 at rank
            omega
          subst n
          let previous : Input (role::tail) Context Block Link Body := .round ⟨tail.length,by simp⟩ history.1 history.2.1
          have prior : property previous := closed _ previous good rfl
          refine Fin.lastCases ?_ (fun j => ?_) i
          · simpa only [Input.priorPoints,List.length_cons,Input.historyPoints,Fin.snoc_last] using prior
          · simpa only [Input.priorPoints,List.length_cons,Input.historyPoints,Fin.snoc_castSucc] using ih previous rfl prior j
  exact go point.rank point rfl good

section Runtime
variable {g : Geometry} {fields : Fields} {Advice : Type}
variable [∀ side, Fintype (fields side)] [Fintype Advice]
variable (repr : ProofBodyCodec.Representations fields Advice)
variable (shape : WireBlocks.Shape g fields) (setup : FingerprintPrefix.Setup) (publicCount : ℕ)

theorem canonical_parent
    (point previous : QueryRuntime.Runtime.Point repr shape setup publicCount)
    (canonical : QueryRuntime.Runtime.Canonical repr shape setup publicCount point)
    (parent : point.parent = some previous) :
    QueryRuntime.Runtime.Canonical repr shape setup publicCount previous := by
  obtain ⟨value,rfl⟩ := canonical
  unfold QueryRuntime.Runtime.toPoint at parent
  rw [CanonicalReplay.reindex_parent] at parent
  obtain ⟨older,present,same⟩ := Option.map_eq_some_iff.mp parent
  obtain ⟨earlier,head,matched⟩ := embed_cons_parent (ProofBodyCodec.codec repr g)
    (QueryRuntime.Runtime.key repr shape setup publicCount value)
    (QueryRuntime.Runtime.first repr shape setup publicCount)
    (List.ofFn (QueryRuntime.Runtime.ordinary repr shape setup publicCount)).tail value older present
  let selected : QueryRuntime.Runtime.Value repr shape setup publicCount := earlier
  have selected_eq : embed (ProofBodyCodec.codec repr g)
      (QueryRuntime.Runtime.key repr shape setup publicCount value)
      (QueryRuntime.Runtime.packets repr shape setup publicCount) selected = older := matched
  refine ⟨selected,?_⟩
  have key : QueryRuntime.Runtime.key repr shape setup publicCount selected =
      QueryRuntime.Runtime.key repr shape setup publicCount value := head
  have context_eq := congrArg (fun key => embed (ProofBodyCodec.codec repr g) key
    (QueryRuntime.Runtime.packets repr shape setup publicCount) selected) key
  exact (congrArg (reindex (QueryRuntime.Runtime.roles_eq repr shape setup publicCount))
    (context_eq.trans selected_eq)).trans same

theorem canonical_priorPoints (point : QueryRuntime.Runtime.Point repr shape setup publicCount)
    (canonical : QueryRuntime.Runtime.Canonical repr shape setup publicCount point) (i : Fin point.rank) :
    QueryRuntime.Runtime.Canonical repr shape setup publicCount (point.priorPoints i) :=
  prior_closed (QueryRuntime.Runtime.Canonical repr shape setup publicCount)
    (fun current previous good parent => canonical_parent repr shape setup publicCount current previous good parent)
    point canonical i

end Runtime

end LfzkV2.Current.ZeroKnowledge.OracleCanonicalAncestors
