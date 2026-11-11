import TranscriptV2.StrandCausality
import TranscriptV2.StrandOracle

/-! Numbered digest-linked nodes unfold to full histories using the query table,
not hash inversion. The serialized id is the history depth; the parser checks
the successor relation and rejects overflow. Erasure is injective on consistent histories except
for a collision among their actually recorded ancestor inputs. -/
namespace TranscriptV2.Strand
open Framing

inductive History where
  | root (message : Bytes)
  | child (parent : History) (digest : Digest) (message : Bytes)

def History.depth : History → ℕ
  | .root _ => 0
  | .child parent .. => parent.depth+1

/-- Finite encoding of a position. Runtime histories and parsed histories are
bounded below 2^64; arbitrary proof-side histories need not satisfy that bound. -/
def History.id (history : History) : Word :=
  ⟨history.depth % 2^64,Nat.mod_lt _ (by decide)⟩

theorem History.id_val (history : History) (fits : history.depth < 2^64) :
    history.id.val = history.depth := Nat.mod_eq_of_lt fits

/-- Root payload followed by the ordered one-parent continuation payloads.
This is proof-side history recovery; these ancestor bytes are not rehashed. -/
def History.spine : History → Bytes × List (Digest × Bytes)
  | .root message => (message,[])
  | .child parent digest message => (parent.spine.1,parent.spine.2 ++ [(digest,message)])

def History.ofSpine (root : Bytes) (rest : List (Digest × Bytes)) : History :=
  rest.foldl (fun parent step => .child parent step.1 step.2) (.root root)

theorem History.ofSpine_spine (history : History) :
    ofSpine history.spine.1 history.spine.2 = history := by
  induction history with
  | root message => rfl
  | child parent digest message ih =>
      simp only [spine,ofSpine,List.foldl_append,List.foldl_cons,List.foldl_nil]
      exact congrArg (fun past => History.child past digest message) ih

theorem History.spine_ofSpine (root : Bytes) (rest : List (Digest × Bytes)) :
    (ofSpine root rest).spine = (root,rest) := by
  have append (history : History) (steps : List (Digest × Bytes)) :
      (steps.foldl (fun parent step => History.child parent step.1 step.2) history).spine =
        (history.spine.1,history.spine.2 ++ steps) := by
    induction steps generalizing history with
    | nil => simp only [List.foldl_nil,List.append_nil,Prod.eta]
    | cons step rest ih =>
        simp only [List.foldl_cons,ih,spine,List.append_assoc,List.singleton_append]
  exact append (.root root) rest

/-- Prepend one completed node to a full history. This operation is used
only to describe parsed history; the wire continuation contains its digest. -/
def History.prepend (message : Bytes) (digest : Digest) : History → History
  | .root next => .child (.root message) digest next
  | .child parent link next => .child (prepend message digest parent) link next

theorem History.prepend_ofSpine (message : Bytes) (digest : Digest)
    (root : Bytes) (rest : List (Digest × Bytes)) :
    prepend message digest (ofSpine root rest) = ofSpine message ((digest,root)::rest) := by
  have commute (history : History) (steps : List (Digest × Bytes)) :
      prepend message digest (steps.foldl (fun parent step => History.child parent step.1 step.2) history) =
        steps.foldl (fun parent step => History.child parent step.1 step.2) (prepend message digest history) := by
    induction steps generalizing history with
    | nil => rfl
    | cons step rest ih => exact ih (.child history step.1 step.2)
  exact commute (.root root) rest

def History.input : History → Input
  | .root message => .root message
  | .child parent digest message => .node (History.child parent digest message).id [digest] message

@[simp] theorem History.input_id (history : History) : history.input.id = history.id := by
  cases history <;> rfl

@[simp] theorem History.valid (history : History) : history.input.Valid := by
  cases history with
  | root _ => trivial
  | child _ _ _ => exact ⟨List.cons_ne_nil _ _,by change 1 < 2^32; decide⟩

theorem History.input_ne_prf (history : History) (id : Word) (digest : Digest) (counter : Word) :
    history.input.encode ≠ (Input.prf id digest counter).encode := by
  cases history with
  | root message => exact Ne.symm (Input.prf_ne_root id digest counter message)
  | child past parent message => exact Ne.symm (Input.prf_ne_node id digest counter _ [parent] message)

/-- A history is a node-domain address, regardless of its hash output. -/
def History.nodePoint (history : History) : OtherPoint := ⟨history.input.encode,by
  cases found : decodePrf history.input.encode with
  | none => rfl
  | some point => exact False.elim (history.input_ne_prf point.1.1 point.1.2 point.2
      (decodePrf_sound history.input.encode point found))⟩

@[simp] theorem History.nodeKey (history : History) (digest : Digest) :
    nodeKey history.nodePoint.val digest = (history.id,digest) := by
  rw [nodePoint,nodeKey_encode history.input history.valid,history.input_id]

def History.ancestors (history : History) : List Bytes :=
  history.input.encode :: match history with
    | .root _ => []
    | .child parent _ _ => parent.ancestors

@[simp] theorem History.ancestors_length (history : History) :
    history.ancestors.length = history.depth+1 := by
  induction history with
  | root _ => rfl
  | child parent digest message ih =>
      simp only [ancestors,List.length_cons,depth,ih]

@[simp] theorem History.mem_ancestors (history : History) :
    history.input.encode ∈ history.ancestors := by
  cases history <;> exact List.mem_cons_self

def History.Consistent (H : Oracle) : History → Prop
  | .root _ => True
  | .child parent digest _ => parent.Consistent H ∧ digest = H parent.input.encode

/-- Only the two finite ancestor paths need be collision-free. There is no
impossible global injectivity premise on a fixed-width hash function. -/
theorem History.erasure_injective (H : Oracle) (first second : History)
    (hfirst : first.Consistent H) (hsecond : second.Consistent H)
    (nocollision : ∀ a ∈ first.ancestors, ∀ b ∈ second.ancestors, H a = H b → a = b)
    (encoded : first.input.encode = second.input.encode) : first = second := by
  induction first generalizing second with
  | root message =>
      cases second with
      | root other =>
          have hi := Input.encode_injective (History.valid _) (History.valid _) encoded
          exact congrArg History.root (Input.root.inj hi)
      | child parent digest other =>
          have hi := Input.encode_injective (History.valid _) (History.valid _) encoded
          cases hi
  | child parent digest message ih =>
      cases second with
      | root other =>
          have hi := Input.encode_injective (History.valid _) (History.valid _) encoded
          cases hi
      | child other otherDigest otherMessage =>
          have hi := Input.encode_injective (History.valid _) (History.valid _) encoded
          have hparts := Input.node.inj hi
          have hd : digest = otherDigest := (List.cons.inj hparts.2.1).1
          have hm : message = otherMessage := hparts.2.2
          have hpa : parent.input.encode ∈ (History.child parent digest message).ancestors :=
            List.mem_cons_of_mem _ (History.mem_ancestors parent)
          have hpb : other.input.encode ∈ (History.child other otherDigest otherMessage).ancestors :=
            List.mem_cons_of_mem _ (History.mem_ancestors other)
          have hp : parent.input.encode = other.input.encode :=
            nocollision _ hpa _ hpb (hfirst.2.symm.trans (hd.trans hsecond.2))
          have he := ih other hfirst.1 hsecond.1 (by
            intro a ha b hb hab
            exact nocollision a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb) hab) hp
          cases he
          cases hd
          cases hm
          rfl

structure Entry where
  history : History
  digest : Digest

/-- A table stores already obtained answers. Resolving a digest never makes
an additional oracle query and never reads an unqueried oracle coordinate. -/
def resolve (table : List Entry) (digest : Digest) : Option History :=
  (table.find? fun entry => decide (entry.digest = digest)).map Entry.history

theorem resolve_sound (table : List Entry) (digest : Digest) (parent : History)
    (h : resolve table digest = some parent) :
    ∃ entry ∈ table, entry.history = parent ∧ entry.digest = digest := by
  unfold resolve at h
  obtain ⟨entry,he,hparent⟩ := Option.map_eq_some_iff.mp h
  exact ⟨entry,List.mem_of_find?_eq_some he,hparent,of_decide_eq_true (List.find?_some (p := fun e : Entry => decide (e.digest = digest)) he)⟩

/-- An already resolved parent never changes when more query answers are
recorded. The decoder therefore needs only its current prefix table. -/
theorem resolve_append (table later : List Entry) (digest : Digest) (parent : History)
    (h : resolve table digest = some parent) : resolve (table ++ later) digest = some parent := by
  obtain ⟨entry,hfind,hparent⟩ := Option.map_eq_some_iff.mp h
  unfold resolve
  rw [List.find?_append,hfind]
  change some entry.history = some parent
  exact congrArg some hparent

/-- Existence of a matching entry suffices when every matching entry names
the same history. The collision argument establishes that agreement; the
decoder itself simply uses the first match. -/
theorem resolve_complete (table : List Entry) (digest : Digest) (parent : History)
    (known : ∃ entry ∈ table, entry.digest = digest)
    (agree : ∀ entry ∈ table, entry.digest = digest → entry.history = parent) :
    resolve table digest = some parent := by
  cases found : table.find? (fun entry => decide (entry.digest = digest)) with
  | none =>
      obtain ⟨entry,member,same⟩ := known
      exact (List.find?_eq_none.mp found entry member (by simp only [same,decide_true])).elim
  | some entry =>
      have same := of_decide_eq_true
        (List.find?_some (p := fun e : Entry => decide (e.digest = digest)) found)
      simp only [resolve,found,Option.map_some,agree entry (List.mem_of_find?_eq_some found) same]

/-- Parse the raw one-parent node by resolving its named digest in the
already queried table. Other SHA domains and arbitrary unresolved parents
are not silently interpreted as a valid protocol history. -/
def unfoldInput (table : List Entry) : Input → Option History
  | .root message => some (.root message)
  | .node id [digest] message =>
      ((resolve table digest).filter fun parent =>
        decide (parent.depth+1 < 2^64 ∧ id = (History.child parent digest message).id)).map
          fun parent => .child parent digest message
  | _ => none

def unfoldNode (table : List Entry) (raw : Bytes) : Option History :=
  Input.decode raw >>= unfoldInput table

theorem unfoldInput_erases (table : List Entry) (input : Input) (history : History)
    (h : unfoldInput table input = some history) : history.input = input := by
  cases input with
  | prf _ _ _ => cases h
  | root message => cases Option.some.inj h; rfl
  | node id parents message =>
      cases parents with
      | nil => cases h
      | cons digest rest =>
          cases rest with
          | cons _ _ => cases h
          | nil =>
              obtain ⟨parent,checked,hh⟩ := Option.map_eq_some_iff.mp h
              cases hh
              obtain ⟨_,valid⟩ := Option.filter_eq_some_iff.mp checked
              have equal := (of_decide_eq_true valid).2
              simp only [History.input,equal]

theorem unfoldNode_erases (table : List Entry) (raw : Bytes) (history : History)
    (h : unfoldNode table raw = some history) : raw = history.input.encode := by
  obtain ⟨input,hd,hh⟩ := Option.bind_eq_some_iff.mp h
  rw [unfoldInput_erases table input history hh]
  exact (Input.decode_sound raw input hd).2

/-- Resolving a child records an actual earlier parent entry, not just a
matching digest value supplied by the caller. -/
theorem unfoldNode_parent (table : List Entry) (raw : Bytes) (parent : History)
    (digest : Digest) (message : Bytes)
    (found : unfoldNode table raw = some (.child parent digest message)) :
    ∃ entry ∈ table, entry.history = parent ∧ entry.digest = digest := by
  have encoded := unfoldNode_erases table raw (.child parent digest message) found
  rw [encoded] at found
  have decoded := Input.decode_encode (.node (History.child parent digest message).id [digest] message)
    ⟨List.cons_ne_nil _ _,by change 1 < 2^32; decide⟩
  simp only [unfoldNode,History.input,decoded] at found
  obtain ⟨known,checked,equal⟩ := Option.map_eq_some_iff.mp found
  have resolved := (Option.filter_eq_some_iff.mp checked).1
  have same : known = parent := (History.child.inj equal).1
  subst known
  exact resolve_sound table digest parent resolved

/-- The source table's consistency is an inductive invariant of executed
queries. Resolving a parent therefore preserves the very same SHA function. -/
theorem unfoldInput_consistent (table : List Entry) (H : Oracle)
    (sound : ∀ entry ∈ table,
      entry.history.Consistent H ∧ entry.digest = H entry.history.input.encode)
    (input : Input) (history : History) (h : unfoldInput table input = some history) :
    history.Consistent H := by
  cases input with
  | prf _ _ _ => cases h
  | root message => cases Option.some.inj h; trivial
  | node id parents message =>
      cases parents with
      | nil => cases h
      | cons digest rest =>
          cases rest with
          | cons _ _ => cases h
          | nil =>
              obtain ⟨parent,checked,hh⟩ := Option.map_eq_some_iff.mp h
              have hresolve := (Option.filter_eq_some_iff.mp checked).1
              cases hh
              obtain ⟨entry,he,hparent,hdigest⟩ := resolve_sound table digest parent hresolve
              have hs := sound entry he
              exact ⟨hparent ▸ hs.1,hdigest.symm.trans (hparent ▸ hs.2)⟩

theorem unfoldNode_consistent (table : List Entry) (H : Oracle)
    (sound : ∀ entry ∈ table,
      entry.history.Consistent H ∧ entry.digest = H entry.history.input.encode)
    (raw : Bytes) (history : History) (h : unfoldNode table raw = some history) :
    history.Consistent H := by
  obtain ⟨input,_,hi⟩ := Option.bind_eq_some_iff.mp h
  exact unfoldInput_consistent table H sound input history hi

/-- Updating the byte decoder after an actual node query stores only an
already parsed history and the returned digest. Unresolved inputs stay in
the auxiliary SHA domain until a parent guess is detected. -/
def record (table : List Entry) (raw : Bytes) (answer : Digest) : List Entry :=
  match unfoldNode table raw with
  | none => table
  | some history => table ++ [⟨history,answer⟩]

theorem record_subset (table : List Entry) (raw : Bytes) (answer : Digest) :
    table ⊆ record table raw answer := by
  intro entry member
  unfold record
  split
  · exact member
  · exact List.mem_append_left _ member

theorem record_sound (table : List Entry) (H : Oracle)
    (sound : ∀ entry ∈ table,
      entry.history.Consistent H ∧ entry.digest = H entry.history.input.encode)
    (raw : Bytes) : ∀ entry ∈ record table raw (H raw),
      entry.history.Consistent H ∧ entry.digest = H entry.history.input.encode := by
  cases hnode : unfoldNode table raw with
  | none => simpa only [record,hnode] using sound
  | some history =>
      intro entry he
      simp only [record,hnode,List.mem_append,List.mem_singleton] at he
      rcases he with hold | rfl
      · exact sound entry hold
      · refine ⟨unfoldNode_consistent table H sound raw history hnode,?_⟩
        exact congrArg H (unfoldNode_erases table raw history hnode)

theorem resolve_record_stable (table : List Entry) (raw : Bytes) (answer digest : Digest)
    (parent : History) (h : resolve table digest = some parent) :
    resolve (record table raw answer) digest = some parent := by
  unfold record
  split
  next hnode => exact h
  next history hnode => exact resolve_append table [⟨history,answer⟩] digest parent h

/-- Every ancestor used by a recovered history is itself a registered node.
Thus the later collision correction concerns queried inputs only. -/
def Closed (table : List Entry) : Prop :=
  ∀ entry ∈ table, ∀ raw ∈ entry.history.ancestors,
    ∃ known ∈ table, raw = known.history.input.encode

@[simp] theorem closed_nil : Closed [] := by
  intro entry he
  cases he

private theorem unfoldInput_past (table : List Entry) (closed : Closed table)
    (input : Input) (history : History) (h : unfoldInput table input = some history) :
    ∀ raw ∈ history.ancestors, raw = history.input.encode ∨
      ∃ known ∈ table, raw = known.history.input.encode := by
  cases input with
  | prf _ _ _ => cases h
  | root message =>
      cases Option.some.inj h
      intro raw hr
      simp only [History.ancestors,List.mem_cons,List.not_mem_nil,or_false] at hr
      exact Or.inl hr
  | node id parents message =>
      cases parents with
      | nil => cases h
      | cons digest rest =>
          cases rest with
          | cons _ _ => cases h
          | nil =>
              obtain ⟨parent,hresolve,hh⟩ := Option.map_eq_some_iff.mp h
              obtain ⟨hresolve,_⟩ := Option.filter_eq_some_iff.mp hresolve
              cases hh
              intro raw hr
              rcases List.mem_cons.mp hr with hself | hpast
              · exact Or.inl hself
              · obtain ⟨entry,he,hparent,_⟩ := resolve_sound table digest parent hresolve
                have past := closed entry he
                rw [hparent] at past
                exact Or.inr (past raw hpast)

/-- Every ancestor of a decoded node is either that node or an earlier
registered query. This keeps collision hypotheses restricted to real inputs. -/
theorem unfoldNode_past (table : List Entry) (closed : Closed table)
    (raw : Bytes) (history : History) (found : unfoldNode table raw = some history) :
    ∀ point ∈ history.ancestors, point = raw ∨
      ∃ known ∈ table, point = known.history.input.encode := by
  obtain ⟨input,_,parsed⟩ := Option.bind_eq_some_iff.mp found
  intro point member
  rcases unfoldInput_past table closed input history parsed point member with current | earlier
  · exact Or.inl (current.trans (unfoldNode_erases table raw history found).symm)
  · exact Or.inr earlier

theorem record_closed (table : List Entry) (closed : Closed table) (raw : Bytes) (answer : Digest) :
    Closed (record table raw answer) := by
  cases hnode : unfoldNode table raw with
  | none => simpa only [record,hnode] using closed
  | some history =>
      intro entry he point hp
      simp only [record,hnode,List.mem_append,List.mem_singleton] at he
      rcases he with hold | rfl
      · obtain ⟨known,hknown,hpoint⟩ := closed entry hold point hp
        refine ⟨known,?_,hpoint⟩
        simp only [record,hnode,List.mem_append]
        exact Or.inl hknown
      · obtain ⟨input,_,hi⟩ := Option.bind_eq_some_iff.mp hnode
        rcases unfoldInput_past table closed input history hi point hp with hself | hpast
        · refine ⟨⟨history,answer⟩,?_,hself⟩
          simp only [record,hnode,List.mem_append,List.mem_singleton,or_true]
        · obtain ⟨known,hknown,hpoint⟩ := hpast
          refine ⟨known,?_,hpoint⟩
          simp only [record,hnode,List.mem_append]
          exact Or.inl hknown

/-- A canonical protocol schema for full histories. The parsed value contains
only serialized data; derived verifier caches can be reconstructed afterward. -/
structure History.Codec (T : Type) where
  encode : T → History
  decode : History → Option T
  inverse : ∀ value, decode (encode value) = some value
  canonical : ∀ history value, decode history = some value → encode value = history

theorem History.Codec.encode_injective {T : Type} (codec : History.Codec T) :
    Function.Injective codec.encode := by
  intro first second equal
  have decoded := congrArg codec.decode equal
  simpa only [codec.inverse,Option.some.injEq] using decoded

end TranscriptV2.Strand
