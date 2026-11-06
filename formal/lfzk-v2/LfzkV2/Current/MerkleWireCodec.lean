import LfzkV2.Current.OpeningBody
import LfzkV2.Current.CanonicalPrefix
import Merkle.Extraction

/-! Concrete preimages of the current joint SHA-256 column tree. The joint
layout digest is a fixed public parameter. Leaf and node inputs use the raw
concatenations in `polygero/hash.rs`; transcript-operation tags are not part
of these hash inputs. Executable role inverses are constructed from the
canonical scalar representations, rather than supplied as assumptions. -/
noncomputable section
namespace LfzkV2.Current.MerkleWireCodec
open Merkle Merkle.MH
open TranscriptV2.Framing (FieldCodec encodeLE)
open scoped Classical

abbrev Salt (columns : ℕ) := Fin columns × Digest

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
    ProofBodyCodec.digest).pair ((physical P R repr binary prime).equiv (physicalLeafEquiv P R))).prefixed
      (leafDomain ++ List.ofFn context)

def node (context : Digest) : PrefixCodec (Digest × Digest) :=
  (ProofBodyCodec.digest.pair ProofBodyCodec.digest).prefixed (nodeDomain ++ List.ofFn context)

def codec : Codec (Salt n) (Joint.Pair.family P R).Leaf Digest Bytes where
  leafEnc := (leaf P R repr binary prime context columnsFit).encode
  nodeEnc := (node context).encode

/-- A recognized input consumes its entire byte string. Context, column
index and nonce are retained in the same-role leaf preimage. -/
def decoders : RoleDecoders (codec P R repr binary prime context columnsFit) where
  leafDec := CanonicalPrefix.readWhole (leaf P R repr binary prime context columnsFit)
  nodeDec := CanonicalPrefix.readWhole (node context)
  leaf_roundTrip := CanonicalPrefix.readWhole_encode _
  node_roundTrip := CanonicalPrefix.readWhole_encode _
  leaf_sound bytes value h := (CanonicalPrefix.readWhole_canonical _ bytes value h).symm
  node_sound bytes value h := (CanonicalPrefix.readWhole_canonical _ bytes value h).symm

theorem codec_inj : (codec P R repr binary prime context columnsFit).Inj :=
  (decoders P R repr binary prime context columnsFit).inj

/-- The public heap coordinate is included in the salted leaf input. The
wire opening itself still stores only its existing 32-byte nonce. -/
def bindSalt {Key : Type} (_key : Key) (column : Fin n) (nonce : Digest) : Salt n := (column,nonce)

theorem leaf_encode (value : Salt n × (Joint.Pair.family P R).Leaf) :
    (codec P R repr binary prime context columnsFit).leafEnc value =
      leafDomain ++ List.ofFn context ++ encodeLE 8 value.1.1.val ++ List.ofFn value.1.2 ++
        (physical P R repr binary prime).encode ((physicalLeafEquiv P R).symm value.2) := by
  simp only [codec,leaf,PrefixCodec.prefixed,PrefixCodec.equiv,PrefixCodec.pair,PrefixCodec.marker,
    PrefixCodec.unsigned,Equiv.coe_fn_symm_mk,ProofBodyCodec.digest,PrefixCodec.bytes_encode,List.append_assoc]

theorem node_encode (value : Digest × Digest) :
    (codec P R repr binary prime context columnsFit).nodeEnc value =
      nodeDomain ++ List.ofFn context ++ List.ofFn value.1 ++ List.ofFn value.2 := by
  simp only [codec,node,PrefixCodec.prefixed,PrefixCodec.equiv,PrefixCodec.pair,PrefixCodec.marker,
    Equiv.coe_fn_symm_mk,ProofBodyCodec.digest,PrefixCodec.bytes_encode,List.append_assoc]

/-- The actual raw scalar traversal is binary before prime, without
separators between fixed-width rows. No row is omitted from the tuple. -/
theorem leaf_encode_physical (column : Fin n) (nonce : Digest)
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
theorem role_ranges_disjoint (sm : Salt n × (Joint.Pair.family P R).Leaf) (dd : Digest × Digest) :
    (codec P R repr binary prime context columnsFit).leafEnc sm ≠
      (codec P R repr binary prime context columnsFit).nodeEnc dd := by
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

/-- OpeningBody's explicit physical decoder is the very same leaf map used
here; there is no arbitrary finite row enumeration in this codec. -/
theorem participantLeaf_eq {g : Geometry} (side : Side)
    (field : fields side → P.Carrier) (hrows : g.dataRows side = P.backend.nw)
    (values : Fin (g.dataRows side+3) → fields side) :
    OpeningBody.participantLeaf P side field hrows values =
      participantLeafEquiv P (fun i => field (values (Fin.cast (by rw [hrows]) i))) := rfl

end LfzkV2.Current.MerkleWireCodec
