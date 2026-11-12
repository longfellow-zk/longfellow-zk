import LfzkV2.Current.CanonicalPrefix
import Merkle.Indexed.Codec
import Merkle.Indexed.Independence

/-! Concrete preimages of the current joint SHA-256 column tree. The joint
layout digest is a fixed public parameter. Leaf and node inputs use the raw
concatenations in `rust/runtime/v2/merkle/src/hash.rs`; transcript-operation
tags are not part of these hash inputs. Executable role inverses are constructed from the
canonical scalar representations, rather than supplied as assumptions. -/
noncomputable section
namespace LfzkV2.Current.MerkleWireCodec
open Merkle Merkle.Indexed
open TranscriptV2.Framing (FieldCodec encodeLE)
open scoped Classical

abbrev Salt (columns : ℕ) := Fin columns × MerkleNonce

def leafDomain : Bytes := CanonicalPrefix.utf8 "polygero/joint/leaf/v1"
def nodeDomain : Bytes := CanonicalPrefix.utf8 "polygero/joint/node/v1"

theorem leafDomain_length : leafDomain.length = 22 := by decide
theorem nodeDomain_length : nodeDomain.length = 22 := by decide
theorem domains_ne : leafDomain ≠ nodeDomain := by decide

variable {k s n t : ℕ}
variable (P R : Joint.Participant k s n t)

/-- Physical rows are `u, m, witness[0..nw), fstar`. The only transport
uses the checked fact that current participants have no quadratic rows. -/
def participantLeafEquiv (P : Joint.Participant k s n t) :
    (Fin (P.backend.nw+3) → P.Carrier) ≃ P.Leaf :=
  (OpeningBody.leafEquiv P.Carrier P.backend.nw).trans (Equiv.cast (by
    change RecursivePolygero.MerkleCompiler.Leaf P.Carrier P.backend.nw 0 =
      RecursivePolygero.MerkleCompiler.Leaf P.Carrier P.backend.nw P.backend.nq
    rw [P.linearOnly]))

def tupleLeafEquiv : (P.Leaf × R.Leaf) ≃ (Joint.Pair.family P R).Leaf :=
  (piFinTwoEquiv (fun i : Fin 2 => ((Joint.Pair.family P R).participant i).Leaf)).symm

def physicalLeafEquiv :
    ((Fin (P.backend.nw+3) → P.Carrier) × (Fin (R.backend.nw+3) → R.Carrier)) ≃
      (Joint.Pair.family P R).Leaf :=
  ((participantLeafEquiv P).prodCongr (participantLeafEquiv R)).trans (tupleLeafEquiv P R)

variable {fields : Fields} {Advice : Type}
variable (repr : ProofBodyCodec.Representations fields Advice)
variable (binary : fields .binary ≃ P.Carrier) (prime : fields .prime ≃ R.Carrier)
variable (context : Digest) (columnsFit : n ≤ 2^64)

def physical : PrefixCodec
    ((Fin (P.backend.nw+3) → P.Carrier) × (Fin (R.backend.nw+3) → R.Carrier)) :=
  (PrefixCodec.vector ((PrefixCodec.field repr.binary).equiv binary) (P.backend.nw+3)).pair
    (PrefixCodec.vector ((PrefixCodec.field repr.prime).equiv prime) (R.backend.nw+3))

def leaf : PrefixCodec (Salt n × (Joint.Pair.family P R).Leaf) :=
  (((PrefixCodec.unsigned 8 n (by simpa only [show 256^8 = 2^64 by decide] using columnsFit)).pair
    ProofBodyCodec.nonce).pair ((physical P R repr binary prime).equiv (physicalLeafEquiv P R))).prefixed
      (leafDomain ++ List.ofFn context)

def node (context : Digest) (index : ℕ) : PrefixCodec (Digest × Digest) :=
  (ProofBodyCodec.digest.pair ProofBodyCodec.digest).prefixed (nodeDomain ++ List.ofFn context ++ encodeLE 8 index)

def codec : Codec (Salt n) (Joint.Pair.family P R).Leaf Digest Bytes where
  leafEnc := (leaf P R repr binary prime context columnsFit).encode
  nodeEnc index := (node context index).encode

/-- A recognized input consumes its entire byte string. Context, column
index and nonce are retained in the same-role leaf preimage. -/
def decoders : RoleDecoders (codec P R repr binary prime context columnsFit) where
  leafDec := CanonicalPrefix.readWhole (leaf P R repr binary prime context columnsFit)
  nodeDec index := CanonicalPrefix.readWhole (node context index)
  leaf_roundTrip := CanonicalPrefix.readWhole_encode _
  node_roundTrip index := CanonicalPrefix.readWhole_encode (node context index)
  leaf_sound bytes value h := (CanonicalPrefix.readWhole_canonical _ bytes value h).symm
  node_sound index bytes value h := (CanonicalPrefix.readWhole_canonical (node context index) bytes value h).symm

theorem codec_inj : (codec P R repr binary prime context columnsFit).Inj :=
  (decoders P R repr binary prime context columnsFit).inj

/-- The public heap coordinate is included in the salted leaf input. The
wire opening itself still stores only its existing 32-byte nonce. -/
def bindSalt {Key : Type} (_key : Key) (column : Fin n) (nonce : MerkleNonce) : Salt n := (column,nonce)

theorem leaf_encode (value : Salt n × (Joint.Pair.family P R).Leaf) :
    (codec P R repr binary prime context columnsFit).leafEnc value =
      leafDomain ++ List.ofFn context ++ encodeLE 8 value.1.1.val ++ List.ofFn value.1.2 ++
        (physical P R repr binary prime).encode ((physicalLeafEquiv P R).symm value.2) := by
  simp only [codec,leaf,PrefixCodec.prefixed,PrefixCodec.equiv,PrefixCodec.pair,PrefixCodec.marker,
    PrefixCodec.unsigned,Equiv.coe_fn_symm_mk,ProofBodyCodec.nonce,PrefixCodec.bytes_encode,List.append_assoc]

theorem node_encode (index : ℕ) (value : Digest × Digest) :
    (codec P R repr binary prime context columnsFit).nodeEnc index value =
      nodeDomain ++ List.ofFn context ++ encodeLE 8 index ++ List.ofFn value.1 ++ List.ofFn value.2 := by
  simp only [codec,node,PrefixCodec.prefixed,PrefixCodec.equiv,PrefixCodec.pair,PrefixCodec.marker,
    Equiv.coe_fn_symm_mk,ProofBodyCodec.digest,PrefixCodec.bytes_encode,List.append_assoc]

/-- A proof-only projection of the two child labels. Authentication still
checks the expected index and context with `decoders`; this projection merely
bounds the targets named by an arbitrary raw query. It may count two extra
labels for a malformed query, which only enlarges the soundness event. -/
def nodeChildren (raw : Bytes) : Option (Digest × Digest) :=
  if raw.head? = some (112 : TranscriptV2.Framing.Byte) then
    CanonicalPrefix.readWhole (ProofBodyCodec.digest.pair ProofBodyCodec.digest)
      (raw.drop (nodeDomain.length + 32 + 8))
  else none

theorem nodeChildren_encode (index : ℕ) (value : Digest × Digest) :
    nodeChildren ((codec P R repr binary prime context columnsFit).nodeEnc index value) = some value := by
  unfold nodeChildren
  rw [if_pos (by rw [node_encode]; rfl)]
  let headerBytes := nodeDomain ++ List.ofFn context ++ encodeLE 8 index
  have length : headerBytes.length = nodeDomain.length + 32 + 8 := by
    simp only [headerBytes,List.length_append,List.length_ofFn,
      TranscriptV2.Framing.encodeLE_length]
  change CanonicalPrefix.readWhole (ProofBodyCodec.digest.pair ProofBodyCodec.digest)
    (((node context index).encode value).drop (nodeDomain.length + 32 + 8)) = some value
  change CanonicalPrefix.readWhole (ProofBodyCodec.digest.pair ProofBodyCodec.digest)
    ((headerBytes ++ (ProofBodyCodec.digest.pair ProofBodyCodec.digest).encode value).drop
      (nodeDomain.length + 32 + 8)) = some value
  rw [← length,List.drop_left]
  exact CanonicalPrefix.readWhole_encode _ value

/-- Supplying the heap index to the real decoder does not introduce more
than the same two child labels in the query-budget calculation. -/
theorem nodeChildren_of_decoded (index : ℕ) (raw : Bytes) (value : Digest × Digest)
    (decoded : (decoders P R repr binary prime context columnsFit).nodeDec index raw = some value) :
    nodeChildren raw = some value := by
  rw [← (decoders P R repr binary prime context columnsFit).node_sound index raw value decoded]
  exact nodeChildren_encode P R repr binary prime context columnsFit index value

/-- Different live heap positions have different inputs even when all their
child digests coincide. The bound is the checked u64 wire-index range. -/
theorem node_positions_ne (first second : ℕ)
    (firstFits : first < 2^64) (secondFits : second < 2^64) (different : first ≠ second)
    (left right : Digest × Digest) :
    (codec P R repr binary prime context columnsFit).nodeEnc first left ≠
      (codec P R repr binary prime context columnsFit).nodeEnc second right := by
  intro same
  rw [node_encode,node_encode] at same
  simp only [List.append_assoc] at same
  have suffix := List.append_cancel_left (List.append_cancel_left same)
  have parsed := congrArg (TranscriptV2.Framing.readLE 8) suffix
  rw [TranscriptV2.Framing.readLE_encode_append 8 first _ (by
    simpa only [show 256^8 = 2^64 by decide] using firstFits),
    TranscriptV2.Framing.readLE_encode_append 8 second _ (by
    simpa only [show 256^8 = 2^64 by decide] using secondFits)] at parsed
  exact different (congrArg Prod.fst (Option.some.inj parsed))

theorem leaf_positions_ne (first second : Fin n) (different : first ≠ second)
    (leftNonce rightNonce : MerkleNonce) (left right : (Joint.Pair.family P R).Leaf) :
    (codec P R repr binary prime context columnsFit).leafEnc ((first,leftNonce),left) ≠
      (codec P R repr binary prime context columnsFit).leafEnc ((second,rightNonce),right) := by
  intro same
  have values := (codec_inj P R repr binary prime context columnsFit).leaf same
  exact different (congrArg (fun value => value.1.1) values)

/-- The actual raw scalar traversal is binary before prime, without
separators between fixed-width rows. No row is omitted from the tuple. -/
theorem leaf_encode_physical (column : Fin n) (nonce : MerkleNonce)
    (binaryRows : Fin (P.backend.nw+3) → P.Carrier)
    (primeRows : Fin (R.backend.nw+3) → R.Carrier) :
    (codec P R repr binary prime context columnsFit).leafEnc
        ((column,nonce),physicalLeafEquiv P R (binaryRows,primeRows)) =
      leafDomain ++ List.ofFn context ++ encodeLE 8 column.val ++ List.ofFn nonce ++
        (List.ofFn binaryRows).flatMap (fun value => repr.binary.encode (binary.symm value)) ++
        (List.ofFn primeRows).flatMap (fun value => repr.prime.encode (prime.symm value)) := by
  rw [leaf_encode,Equiv.symm_apply_apply]
  simp only [physical,PrefixCodec.pair,PrefixCodec.vector_encode,PrefixCodec.equiv,PrefixCodec.field,
    List.append_assoc]

/-- The two literal domains differ before any context bytes are read. -/
theorem role_ranges_disjoint (index : ℕ) (sm : Salt n × (Joint.Pair.family P R).Leaf) (dd : Digest × Digest) :
    (codec P R repr binary prime context columnsFit).leafEnc sm ≠
      (codec P R repr binary prime context columnsFit).nodeEnc index dd := by
  intro h
  have hp := congrArg (List.take 22) h
  rw [leaf_encode,node_encode] at hp
  have hl (tail : Bytes) : List.take 22 (leafDomain ++ tail) = leafDomain := by
    rw [← leafDomain_length]
    simp only [List.take_left]
  have hn (tail : Bytes) : List.take 22 (nodeDomain ++ tail) = nodeDomain := by
    rw [← nodeDomain_length]
    simp only [List.take_left]
  simp only [List.append_assoc,hl,hn] at hp
  exact domains_ne hp

/-- The independence proof uses exactly the tags and heap indices present
in Rust's hash preimages. No assumption that SHA outputs are distinct enters. -/
theorem separated : Merkle.Indexed.Separated
    (codec P R repr binary prime context columnsFit) n where
  leaf_node := role_ranges_disjoint P R repr binary prime context columnsFit
  nodes first second _ firstBound _ secondBound different left right :=
    node_positions_ne P R repr binary prime context columnsFit first second
      (lt_of_lt_of_le firstBound columnsFit) (lt_of_lt_of_le secondBound columnsFit)
      different left right

/-- OpeningBody's explicit physical decoder is the very same leaf map used
here; there is no arbitrary finite row enumeration in this codec. -/
theorem participantLeaf_eq {g : Geometry} (side : Side)
    (field : fields side → P.Carrier) (hrows : g.dataRows side = P.backend.nw)
    (values : Fin (g.dataRows side+3) → fields side) :
    OpeningBody.participantLeaf P side field hrows values =
      participantLeafEquiv P (fun i => field (values (Fin.cast (by rw [hrows]) i))) := rfl

end LfzkV2.Current.MerkleWireCodec
