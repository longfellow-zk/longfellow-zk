import LfzkV2.Current.CanonicalPrefix

/-! The first mdoc boundary contains the public presentation bits, participant
layouts and joint root. Later prime-field public inputs are deliberately absent
from its key. The same bytes occur at every accepted replay of this context.
The duplicate root written by witness selection is checked by the parser. -/
noncomputable section
namespace LfzkV2.Current.FingerprintPrefix
open CanonicalPrefix (frame utf8)
open TranscriptV2.Framing (Byte encodeLE)
open scoped Classical

abbrev Word := Fin (2^64)

/-- Fixed trusted circuit and field layout. These values are the existing
bind-only metadata; no additional identifier is inserted in the transcript. -/
structure Setup where
  combinedHash : Digest
  hashCircuit : Digest
  hashTemplate : Digest
  primeCircuit : Digest
  packingDescriptor : BoundedBytes CanonicalPrefix.maxLength
  privateInputs : Word
  padCells : Word
  layerWidths : List Word
  shared : Word
  jointContext : Digest
  binaryField : BoundedBytes CanonicalPrefix.maxLength
  primeField : BoundedBytes CanonicalPrefix.maxLength
  binaryCells : Word
  primeCells : Word

/-- Only the early public data and commitment identify the extraction cut.
Neither the issuer public values nor a complete proof are part of this key. -/
structure Key (publicCount : ℕ) where
  session : BoundedBytes CanonicalPrefix.maxLength
  publicBits : Fin publicCount → Bool
  root : Digest

instance (publicCount : ℕ) : Fintype (Key publicCount) := by
  apply Fintype.ofInjective (fun key : Key publicCount => (key.session,key.publicBits,key.root))
  intro a b h
  cases a
  cases b
  cases h
  rfl

private def boolData : Fin 2 ≃ Bool where
  toFun value := decide (value.val = 1)
  invFun value := if value then 1 else 0
  left_inv value := by fin_cases value <;> rfl
  right_inv value := by cases value <;> rfl

private def bit : PrefixCodec Bool :=
  (PrefixCodec.unsigned 1 2 (by decide)).equiv boolData

private def bits (count : ℕ) : PrefixCodec (Fin count → Bool) :=
  (PrefixCodec.vector bit count).prefixed ([0] ++ encodeLE 8 count)

private def suffixed {A : Type} (codec : PrefixCodec A) (suffix : Bytes) : PrefixCodec A :=
  (codec.pair (PrefixCodec.marker suffix)).equiv {
    toFun := Prod.fst
    invFun value := (value,())
    left_inv value := by rcases value with ⟨value,⟨⟩⟩; rfl
    right_inv _ := rfl }

private def digestFrame (digest : Digest) : Bytes := frame (List.ofFn digest)
private def wordFrame (word : Word) : Bytes := frame (encodeLE 8 word.val)
private def constantWord (word : ℕ) : Bytes := frame (encodeLE 8 word)

/-- The statement marker follows session initialization and precedes the
canonical byte vector of public presentation bits. -/
def beforePublic (setup : Setup) : Bytes :=
  frame (utf8 "mdoc/adapter/statement/v1") ++ digestFrame setup.combinedHash

/-- Packing/layout binding, binary template, prime shared-prefix binding,
then the shared Polygero root envelope, in the actual runtime order. -/
def beforeRoot (setup : Setup) : Bytes :=
  frame (utf8 "longfellow/v2/packing-commitment/v1") ++ digestFrame setup.hashCircuit ++
  frame setup.packingDescriptor.bytes ++ wordFrame setup.privateInputs ++ wordFrame setup.padCells ++
  frame (utf8 "mdoc/adapter/shared-binary/v1") ++ digestFrame setup.hashTemplate ++
  setup.layerWidths.flatMap wordFrame ++
  frame (utf8 "native-shared-prefix/joint/v1") ++ digestFrame setup.primeCircuit ++ wordFrame setup.shared ++
  frame (utf8 "polygero/joint/root/v1") ++ digestFrame setup.jointContext

def beforeRepeatedRoot (setup : Setup) : Bytes :=
  frame (utf8 "longfellow/witness-selection/v1") ++ digestFrame setup.jointContext

/-- Both ordered fields describe their original cells and two dedicated
fingerprint masks before the one coefficient answer is sampled. -/
def afterRoot (setup : Setup) : Bytes :=
  constantWord 2 ++ frame setup.binaryField.bytes ++ wordFrame setup.binaryCells ++ constantWord 2 ++
  frame setup.primeField.bytes ++ wordFrame setup.primeCells ++ constantWord 2

private abbrev Data (publicCount : ℕ) :=
  BoundedBytes CanonicalPrefix.maxLength × (Fin publicCount → Bool) × Digest × Digest

private def dataCodec (setup : Setup) (publicCount : ℕ) : PrefixCodec (Data publicCount) :=
  CanonicalPrefix.session.pair ((bits publicCount).prefixed (beforePublic setup) |>.pair
    ((CanonicalPrefix.framedDigest.prefixed (beforeRoot setup)).pair
      (suffixed (CanonicalPrefix.framedDigest.prefixed (beforeRepeatedRoot setup)) (afterRoot setup))))

private def keyData (publicCount : ℕ) :
    {value : Data publicCount // value.2.2.1 = value.2.2.2} ≃ Key publicCount where
  toFun value := ⟨value.val.1,value.val.2.1,value.val.2.2.1⟩
  invFun value := ⟨(value.session,value.publicBits,value.root,value.root),rfl⟩
  left_inv value := by
    rcases value with ⟨⟨session,publicBits,root,repeated⟩,h⟩
    change root = repeated at h
    subst repeated
    rfl
  right_inv value := by cases value; rfl

/-- This is the existing first block, excluding only its round footer.
All fixed metadata is checked; both serialized root copies must agree. -/
def codec (setup : Setup) (publicCount : ℕ) : PrefixCodec (Key publicCount) :=
  ((dataCodec setup publicCount).restrict (fun value => value.2.2.1 = value.2.2.2)).equiv
    (keyData publicCount)

theorem codec_encode (setup : Setup) (publicCount : ℕ) (key : Key publicCount) :
    (codec setup publicCount).encode key =
      CanonicalPrefix.session.encode key.session ++
      (beforePublic setup ++ (bits publicCount).encode key.publicBits) ++
      (beforeRoot setup ++ CanonicalPrefix.framedDigest.encode key.root) ++
      (beforeRepeatedRoot setup ++ CanonicalPrefix.framedDigest.encode key.root) ++ afterRoot setup := by
  simp only [codec,dataCodec,PrefixCodec.equiv,PrefixCodec.restrict,PrefixCodec.pair,
    PrefixCodec.prefixed,PrefixCodec.marker,suffixed,keyData,Equiv.coe_fn_symm_mk,List.append_assoc]

def read (setup : Setup) (publicCount : ℕ) : Bytes → Option (Key publicCount) :=
  CanonicalPrefix.readWhole (codec setup publicCount)

theorem read_encode (setup : Setup) (publicCount : ℕ) (key : Key publicCount) :
    read setup publicCount ((codec setup publicCount).encode key) = some key :=
  CanonicalPrefix.readWhole_encode _ _

theorem read_canonical (setup : Setup) (publicCount : ℕ) (input : Bytes) (key : Key publicCount)
    (h : read setup publicCount input = some key) : input = (codec setup publicCount).encode key :=
  CanonicalPrefix.readWhole_canonical _ _ _ h

/-- Requests may contain later public values, but the initial context is
computed from the early projection alone. This permits shared early prefixes. -/
structure Request (publicCount primeCount : ℕ) (Prime : Type) where
  session : BoundedBytes CanonicalPrefix.maxLength
  publicBits : Fin publicCount → Bool
  primeInputs : Fin primeCount → Prime

def context {publicCount primeCount : ℕ} {Prime : Type}
    (request : Request publicCount primeCount Prime) (root : Digest) : Key publicCount :=
  ⟨request.session,request.publicBits,root⟩

theorem public_readback {publicCount primeCount : ℕ} {Prime : Type}
    (setup : Setup) (request : Request publicCount primeCount Prime) (root : Digest) :
    (read setup publicCount ((codec setup publicCount).encode (context request root))).map Key.publicBits =
      some request.publicBits := by
  rw [read_encode]
  rfl

theorem context_independent_of_prime {publicCount primeCount : ℕ} {Prime : Type}
    (request : Request publicCount primeCount Prime) (inputs : Fin primeCount → Prime) (root : Digest) :
    context {request with primeInputs := inputs} root = context request root := rfl

/-- Structural capacity for the complete initial block. Session bytes are
bounded once; public counts and fixed metadata determine every other size.
The bound is only an ambient type size, and appends no bytes to the transcript. -/
def blockBound (setup : Setup) (publicCount : ℕ) : ℕ :=
  (frame CanonicalPrefix.sessionDomain).length+9+CanonicalPrefix.maxLength +
    (beforePublic setup).length+9+publicCount +
    (beforeRoot setup).length+41 + (beforeRepeatedRoot setup).length+41 + (afterRoot setup).length

private theorem bits_length (count : ℕ) (value : Fin count → Bool) :
    ((bits count).encode value).length = 9+count := by
  change (([0] ++ encodeLE 8 count) ++ (PrefixCodec.vector bit count).encode value).length = _
  rw [List.length_append,PrefixCodec.vector_length bit 1 (by
    intro v
    change (encodeLE 1 _).length = 1
    exact TranscriptV2.Framing.encodeLE_length _ _)]
  simp only [List.length_append,List.length_singleton,TranscriptV2.Framing.encodeLE_length,Nat.mul_one]

theorem encode_length_le (setup : Setup) (publicCount : ℕ) (key : Key publicCount) :
    ((codec setup publicCount).encode key).length ≤ blockBound setup publicCount := by
  rw [codec_encode]
  simp only [List.length_append,CanonicalPrefix.session_length,bits_length,
    CanonicalPrefix.framedDigest_length]
  have h := key.session.bound
  unfold blockBound
  omega

def blockBytes (setup : Setup) (publicCount : ℕ) (key : Key publicCount) :
    BoundedBytes (blockBound setup publicCount) :=
  ⟨(codec setup publicCount).encode key,encode_length_le setup publicCount key⟩

end LfzkV2.Current.FingerprintPrefix
