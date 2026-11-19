import LfzkV2.Current.QueryCodec
import LfzkV2.Current.ProtocolWrites

/-! Role packets and the logical runtime inputs they build, independent of
any one transcript format. A packet is a role schema with its deterministic
cache; `embed` assembles the verifier's logical input from parsed packet
values, whose strand history `StrandRuntime` serializes. A transcript
`Format` supplies the packets; `TaggedFormat` is the deployed one. -/
noncomputable section
namespace LfzkV2.Current.QueryRuntime
open CanonicalPrefix
open scoped Classical

section Generic
variable {Key Fresh Body : Type} {capacity : ℕ}

abbrev Block (capacity : ℕ) (Fresh : Type) := BoundedBytes capacity × Fresh

/-- A public role schema and its deterministic cache. The capacity bound is
on the whole block, so it may exceed the u64 bound on one bytes operation. -/
structure Packet (Fresh : Type) (capacity : ℕ) where
  Data : Type
  codec : PrefixCodec Data
  role : Role
  cache : Data → Fresh
  bounded : ∀ value, (codec.encode value).length ≤ capacity

namespace Packet
variable (packet : Packet Fresh capacity)

def queryBlock : QueryCodec.Block := ⟨packet.Data,packet.codec,packet.role.domain⟩

def block (value : packet.Data) : Block capacity Fresh :=
  (⟨packet.codec.encode value,packet.bounded value⟩,packet.cache value)

@[simp] theorem block_bytes (value : packet.Data) :
    (packet.block value).1.bytes = packet.codec.encode value := rfl

end Packet

private def prependHistory (block : Block capacity Fresh) (link : Digest) :
    (n : ℕ) → History Key (Block capacity Fresh) Digest n →
      History Key (Block capacity Fresh) Digest (n+1)
  | 0, context => (context,block,link)
  | n+1, history => (prependHistory block link n history.1,history.2)

/-- Insert one actual earlier boundary, preserving all later blocks and
their links. This operation changes no messages or challenge boundaries. -/
def prepend {roles : List Role} (role : Role) (block : Block capacity Fresh) (link : Digest) :
    Input roles Key (Block capacity Fresh) Digest Body →
      Input (role :: roles) Key (Block capacity Fresh) Digest Body
  | .round i history current =>
      .round ⟨i.val+1,by simpa only [List.length_cons] using Nat.add_lt_add_right i.isLt 1⟩
        (prependHistory block link i.val history) current
  | .finalSeal history body => .finalSeal (prependHistory block link roles.length history) body

/-- Build the existing logical runtime input directly from parsed packets.
Links are the actual supplied feedback values, not fresh serialized fields. -/
def embed (bodyCodec : WholeCodec Body) (context : Key) :
    (packets : List (Packet Fresh capacity)) →
      QueryCodec.Value bodyCodec (packets.map Packet.queryBlock) →
        Input (packets.map Packet.role) Key (Block capacity Fresh) Digest Body
  | [], body => .finalSeal context body.val
  | packet :: tail, (value,.inl _) => .round ⟨0,by simp⟩ context (packet.block value)
  | packet :: tail, (value,.inr (link,next)) =>
      prepend packet.role (packet.block value) link (embed bodyCodec context tail next)

private theorem prependHistory_context (block : Block capacity Fresh) (link : Digest)
    (n : ℕ) (history : History Key (Block capacity Fresh) Digest n) :
    Input.historyContext (n+1) (prependHistory block link n history) =
      Input.historyContext n history := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih history.1

theorem prepend_context {roles : List Role} (role : Role) (block : Block capacity Fresh)
    (link : Digest) (point : Input roles Key (Block capacity Fresh) Digest Body) :
    (prepend role block link point).context = point.context := by
  cases point <;> exact prependHistory_context block link _ _

/-- Prepending a boundary preserves every later predecessor. A point that
was first now has precisely the newly inserted boundary as its parent. -/
theorem parent_prepend {roles : List Role} (role : Role) (block : Block capacity Fresh)
    (link : Digest) (point : Input roles Key (Block capacity Fresh) Digest Body) :
    (prepend role block link point).parent =
      match point.parent with
      | none => some (.round ⟨0,by simp⟩ point.context block)
      | some earlier => some (prepend role block link earlier) := by
  have previous (n : ℕ) (hn : n ≤ roles.length)
      (history : History Key (Block capacity Fresh) Digest n) :
      Input.previous (roles := role::roles) (Body := Body) (n+1) (by simp only [List.length_cons]; omega)
          (prependHistory block link n history) =
        match Input.previous (roles := roles) (Body := Body) n hn history with
        | none => some (.round ⟨0,by simp⟩ (Input.historyContext n history) block)
        | some earlier => some (prepend role block link earlier) := by
    cases n <;> rfl
  cases point with
  | round i history current => exact previous i.val (by omega) history
  | finalSeal history body => exact previous roles.length (by rfl) history

theorem embed_context (bodyCodec : WholeCodec Body) (context : Key)
    (packets : List (Packet Fresh capacity))
    (value : QueryCodec.Value bodyCodec (packets.map Packet.queryBlock)) :
    (embed bodyCodec context packets value).context = context := by
  induction packets with
  | nil => rfl
  | cons packet tail ih =>
      rcases value with ⟨value,next⟩
      cases next with
      | inl _ => rfl
      | inr continuation =>
          rcases continuation with ⟨link,next⟩
          exact (prepend_context packet.role (packet.block value) link _).trans (ih next)

/-- Changing only the proof that a parsed schema has the public schedule
changes neither bytes nor the logical context. -/
def reindex {first second : List Role} (h : first = second)
    (point : Input first Key (Block capacity Fresh) Digest Body) :
    Input second Key (Block capacity Fresh) Digest Body := h ▸ point

theorem reindex_context {first second : List Role} (h : first = second)
    (point : Input first Key (Block capacity Fresh) Digest Body) :
    (reindex h point).context = point.context := by cases h; rfl

theorem reindex_parent {first second : List Role} (h : first = second)
    (point : Input first Key (Block capacity Fresh) Digest Body) :
    (reindex h point).parent = point.parent.map (reindex h) := by
  cases h
  change point.parent = point.parent.map id
  simp only [Option.map_id,id_eq]

end Generic

end LfzkV2.Current.QueryRuntime
