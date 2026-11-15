import LfzkV2.Current.QueryCodec
import LfzkV2.Current.ProtocolWrites

/-! Role packets and the logical runtime inputs they build, independent of
any one transcript format. A packet is a role schema with its deterministic
cache; `embed` assembles the verifier's logical input from parsed packet
values, and `bytes` is the earlier chained-transcript preimage (not the
numbered-strand runtime, which `StrandRuntime` models). A transcript
`Format` supplies the packets; `QueryRuntime.Runtime` is the deployed one. -/
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

/-- History bytes contain only actual writes, role footers and link
feedback. The logical context is already part of the first block. -/
def historyBytes (roles : List Role) (counter : ℕ) (fits : counter+roles.length < 2^64) :
    (n : ℕ) → n ≤ roles.length → History Key (Block capacity Fresh) Digest n → Bytes
  | 0, _, _ => []
  | n+1, hn, history =>
      historyBytes roles counter fits n (by omega) history.1 ++ history.2.1.1.bytes ++
        roundFooter (roles.get ⟨n,by omega⟩).domain ⟨counter+n,by omega⟩ ++
        feedback.encode history.2.2

/-- The oracle preimage under the earlier chained transcript (not the
numbered-strand runtime). It deliberately ignores redundant logical caches.
Canonicality below reconstructs and checks those caches. -/
def bytes (bodyCodec : PrefixCodec Body) (roles : List Role) (counter : ℕ)
    (fits : counter+roles.length < 2^64) :
    Input roles Key (Block capacity Fresh) Digest Body → Bytes
  | .round i history block =>
      historyBytes roles counter fits i.val (by omega) history ++ block.1.bytes ++
        roundFooter (roles.get i).domain ⟨counter+i.val,by omega⟩
  | .finalSeal history body =>
      historyBytes roles counter fits roles.length (by rfl) history ++
        finalFooter ⟨counter+roles.length,fits⟩ ++ frame (bodyCodec.encode body)

private theorem historyBytes_prepend (roles : List Role) (role : Role) (counter : ℕ)
    (fits : counter+(role::roles).length < 2^64) (block : Block capacity Fresh) (link : Digest)
    (n : ℕ) (hn : n ≤ roles.length) (history : History Key (Block capacity Fresh) Digest n) :
    historyBytes (role::roles) counter fits (n+1) (by simp only [List.length_cons]; omega)
        (prependHistory block link n history) =
      block.1.bytes ++ roundFooter role.domain ⟨counter,by simp only [List.length_cons] at fits; omega⟩ ++
        feedback.encode link ++
        historyBytes roles (counter+1) (by simp only [List.length_cons] at fits; omega) n hn history := by
  induction n with
  | zero => simp [historyBytes,prependHistory]
  | succ n ih =>
      conv_lhs => rw [historyBytes]; simp only [prependHistory]
      conv_rhs => rw [historyBytes]
      rw [ih (by omega) history.1]
      simp only [List.get_cons_succ]
      have he : counter+(n+1) = (counter+1)+n := by omega
      simp only [he,List.append_assoc]

theorem bytes_prepend (bodyCodec : PrefixCodec Body) (roles : List Role) (role : Role)
    (counter : ℕ) (fits : counter+(role::roles).length < 2^64)
    (block : Block capacity Fresh) (link : Digest)
    (point : Input roles Key (Block capacity Fresh) Digest Body) :
    bytes bodyCodec (role::roles) counter fits (prepend role block link point) =
      block.1.bytes ++ roundFooter role.domain ⟨counter,by simp only [List.length_cons] at fits; omega⟩ ++
        feedback.encode link ++
        bytes bodyCodec roles (counter+1) (by simp only [List.length_cons] at fits; omega) point := by
  cases point with
  | round i history current =>
      simp only [prepend,bytes]
      rw [historyBytes_prepend roles role counter fits block link i.val (by omega) history]
      have he : counter+(i.val+1) = (counter+1)+i.val := by omega
      simp only [List.get_cons_succ,he,List.append_assoc]
  | finalSeal history body =>
      simp only [prepend,bytes,List.length_cons]
      rw [historyBytes_prepend roles role counter fits block link roles.length (by rfl) history]
      have he : counter+(roles.length+1) = (counter+1)+roles.length := by omega
      simp only [he,List.append_assoc]

/-- Build the existing logical runtime input directly from parsed packets.
Links are the actual supplied feedback values, not fresh serialized fields. -/
def embed (bodyCodec : PrefixCodec Body) (context : Key) :
    (packets : List (Packet Fresh capacity)) →
      QueryCodec.Value bodyCodec (packets.map Packet.queryBlock) →
        Input (packets.map Packet.role) Key (Block capacity Fresh) Digest Body
  | [], body => .finalSeal context body.val
  | packet :: tail, (value,.inl _) => .round ⟨0,by simp⟩ context (packet.block value)
  | packet :: tail, (value,.inr (link,next)) =>
      prepend packet.role (packet.block value) link (embed bodyCodec context tail next)

/-- The byte projection is derived from the component codecs. No
injectivity assumption about arbitrary runtime points is needed. -/
theorem bytes_embed (bodyCodec : PrefixCodec Body) (context : Key)
    (packets : List (Packet Fresh capacity)) (counter : ℕ)
    (fits : counter+(packets.map Packet.role).length < 2^64)
    (value : QueryCodec.Value bodyCodec (packets.map Packet.queryBlock)) :
    bytes bodyCodec (packets.map Packet.role) counter fits (embed bodyCodec context packets value) =
      QueryCodec.encode bodyCodec (packets.map Packet.queryBlock) counter
        (by simpa only [List.length_map] using fits) value := by
  induction packets generalizing counter with
  | nil =>
      simp only [List.map_nil,embed,bytes,historyBytes,List.nil_append,
        QueryCodec.encode_nil,List.length_nil,Nat.add_zero]
  | cons packet tail ih =>
      rcases value with ⟨value,next⟩
      cases next with
      | inl stop =>
          cases stop
          simp only [List.map_cons]
          rw [QueryCodec.encode_stop]
          simp only [embed,bytes,historyBytes,List.nil_append,
            List.get_eq_getElem,List.getElem_cons_zero,Packet.block_bytes,
            Nat.add_zero,Packet.queryBlock]
      | inr continuation =>
          rcases continuation with ⟨link,next⟩
          simp only [List.map_cons]
          rw [QueryCodec.encode_continue]
          simp only [embed,bytes_prepend]
          rw [ih]
          simp only [Packet.queryBlock,Packet.block_bytes,List.append_assoc]

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

theorem embed_context (bodyCodec : PrefixCodec Body) (context : Key)
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

theorem bytes_reindex (bodyCodec : PrefixCodec Body) {first second : List Role}
    (h : first = second) (counter : ℕ) (fits : counter+second.length < 2^64)
    (point : Input first Key (Block capacity Fresh) Digest Body) :
    bytes bodyCodec second counter fits (reindex h point) =
      bytes bodyCodec first counter (by simpa only [h] using fits) point := by
  cases h
  rfl

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
