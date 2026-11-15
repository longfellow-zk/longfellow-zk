import LfzkV2.Current.QueryPacket
import LfzkV2.Current.FingerprintPrefix
import LfzkV2.Current.WireBlockBounds

/-! Canonical byte queries of the earlier chained transcript, embedded in
logical inputs. The base retains the complete writes at a boundary and the
fresh component is only a parsed cache. The initial key is recovered from
the first block; it is not serialized a second time. Malformed logical cache
aliases lie outside the canonical image and cannot acquire the same byte query.

These byte layouts (u64 round counters and `boundary-output` feedback links)
are not what the Rust runtime hashes. The runtime uses numbered SHA-256
strands, whose preimages are modeled by `TranscriptV2.Strand` and
`StrandQueryCodec`; the endpoints use those. Current modules import this one
for its logical types (`Block`, `Input`). -/
noncomputable section
namespace LfzkV2.Current.QueryRuntime
open CanonicalPrefix
open scoped Classical

namespace Runtime
variable {g : Geometry} {fields : Fields} {Advice : Type}
variable (repr : ProofBodyCodec.Representations fields Advice)
variable (shape : WireBlocks.Shape g fields) (setup : FingerprintPrefix.Setup) (publicCount : ℕ)

/-- Structural bounds for the initial and ordinary packets determine the
capacity. This affects only a logical type, adding no padding or serialized length. -/
def capacity : ℕ :=
  max (FingerprintPrefix.blockBound setup publicCount) (WireBlocks.blockBound shape repr)

abbrev Fresh := ProtocolWrites.Fresh g fields Advice
abbrev Key := FingerprintPrefix.Key publicCount
abbrev Body := Current.Body g fields Advice (OpeningBody.Authentication g)

def first : Packet (Fresh (g := g) (fields := fields) (Advice := Advice))
    (capacity repr shape setup publicCount) where
  Data := Key publicCount
  codec := FingerprintPrefix.codec setup publicCount
  role := .fingerprint
  cache _ := {}
  bounded value := (FingerprintPrefix.encode_length_le setup publicCount value).trans (le_max_left _ _)

def ordinary (i : Fin g.roles.length) :
    Packet (Fresh (g := g) (fields := fields) (Advice := Advice)) (capacity repr shape setup publicCount) where
  Data := WireBlocks.Data (Advice := Advice) shape i
  codec := WireBlocks.codec repr shape i
  role := g.roles.get i
  cache := WireBlocks.cache shape i
  bounded value := (WireBlocks.encode_length_le shape repr i value).trans (le_max_right _ _)

/-- The special first packet replaces only the fingerprint block. All
later packets use the role-local parser at their actual public counter. -/
def packets : List (Packet (Fresh (g := g) (fields := fields) (Advice := Advice))
    (capacity repr shape setup publicCount)) :=
  first repr shape setup publicCount ::
    (List.ofFn (ordinary repr shape setup publicCount)).tail

theorem roles_eq : (packets repr shape setup publicCount).map Packet.role = g.roles := by
  have hordinary : (List.ofFn (ordinary repr shape setup publicCount)).map Packet.role = g.roles := by
    rw [List.map_ofFn]
    exact List.ofFn_get g.roles
  simp only [packets,List.map_cons,first,List.map_tail,hordinary]
  have hhead : Role.fingerprint :: g.roles.tail = g.roles := by
    rw [g.roles_eq]
    simp only [List.cons_append,List.tail_cons]
  exact hhead

def blocks : List QueryCodec.Block := (packets repr shape setup publicCount).map Packet.queryBlock

abbrev Value := QueryCodec.Value (ProofBodyCodec.codec repr g).whole (blocks repr shape setup publicCount)

abbrev Point := Replay.Point g fields Advice (OpeningBody.Authentication g)
  (Key publicCount) (Block (capacity repr shape setup publicCount)
    (Fresh (g := g) (fields := fields) (Advice := Advice)))

def key (value : Value repr shape setup publicCount) : Key publicCount := value.1

/-- Parse the key from the initial bytes and reconstruct all later caches.
The erased whole-query encoding contains no separate context field. -/
def toPoint (value : Value repr shape setup publicCount) : Point repr shape setup publicCount :=
  reindex (roles_eq repr shape setup publicCount)
    (embed (ProofBodyCodec.codec repr g).whole (key repr shape setup publicCount value)
      (packets repr shape setup publicCount) value)

def pointBytes (fits : g.roles.length < 2^64) : Point repr shape setup publicCount → Bytes :=
  bytes (ProofBodyCodec.codec repr g) g.roles 0 (by simpa only [Nat.zero_add] using fits)

theorem blocks_length : (blocks repr shape setup publicCount).length = g.roles.length := by
  simpa only [blocks,List.length_map] using congrArg List.length (roles_eq repr shape setup publicCount)

theorem toPoint_bytes (fits : g.roles.length < 2^64) (value : Value repr shape setup publicCount) :
    pointBytes repr shape setup publicCount fits (toPoint repr shape setup publicCount value) =
      QueryCodec.encode (ProofBodyCodec.codec repr g) (blocks repr shape setup publicCount) 0
        (by simpa only [Nat.zero_add,blocks_length] using fits) value := by
  unfold pointBytes toPoint
  rw [bytes_reindex]
  exact bytes_embed _ _ _ _ _ _

theorem toPoint_context (value : Value repr shape setup publicCount) :
    (toPoint repr shape setup publicCount value).context = key repr shape setup publicCount value := by
  rw [toPoint,reindex_context,embed_context]

theorem toPoint_injective (fits : g.roles.length < 2^64) :
    Function.Injective (toPoint repr shape setup publicCount) :=
  QueryCodec.pointMap_injective (ProofBodyCodec.codec repr g) (blocks repr shape setup publicCount) 0
    (by simpa only [Nat.zero_add,blocks_length] using fits)
    (toPoint repr shape setup publicCount) (pointBytes repr shape setup publicCount fits)
    (toPoint_bytes repr shape setup publicCount fits)

/-- A runtime point is canonical precisely when its complete physical
prefix parses and reproduces its context and every fresh cache. -/
def Canonical (point : Point repr shape setup publicCount) : Prop :=
  ∃ value, toPoint repr shape setup publicCount value = point

def codec (fits : g.roles.length < 2^64) :
    ByteOracleTransport.Codec (Point repr shape setup publicCount) Bytes
      (Canonical repr shape setup publicCount) :=
  QueryCodec.intoCodec (ProofBodyCodec.codec repr g) (blocks repr shape setup publicCount) 0
    (by simpa only [Nat.zero_add,blocks_length] using fits)
    (toPoint repr shape setup publicCount) (pointBytes repr shape setup publicCount fits)
    (toPoint_bytes repr shape setup publicCount fits)

end Runtime

end LfzkV2.Current.QueryRuntime
