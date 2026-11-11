import LfzkV2.Current.QueryCodec
import LfzkV2.Current.ProtocolWrites

/-! Existing writes between ordinary v2 boundaries. The public schema fixes
the field at each scalar/slice position; the writer adds no field tag. Every
bound metadata value remains in the parsed packet, while `Fresh` is a derived
cache. The initial fingerprint block, including session initialization and
the application request, is assembled separately. -/
noncomputable section
namespace LfzkV2.Current.WireBlocks
open TranscriptV2.Framing (Byte FieldCodec encodeLE)
open CanonicalPrefix
open SumcheckV2 Layered.Replay
open scoped Classical

abbrev Word := Fin (2^64)

/-- Counts are fixed by the public circuit/layout. They are not redundant
lengths in the proof. Packing binds its cell counts, not its derived coefficients. -/
structure Shape (g : Geometry) (fields : Fields) where
  binaryPublic : ℕ
  primePublic : ℕ
  primeInputs : ℕ
  sharedBits : ℕ
  packingInputs : ℕ
  binary128Packing : Bool
  zero : (side : Side) → fields side
  sliceFits : ∀ count ∈ [primeInputs,sharedBits+1,packingInputs,g.packingDegree,
      g.rowDimension+g.maskingDegree,2*g.rowDimension], count < 2^64

private def followed {A : Type} (codec : PrefixCodec A) (suffix : Bytes) : PrefixCodec A :=
  (codec.pair (PrefixCodec.marker suffix)).equiv {
    toFun := Prod.fst
    invFun value := (value,())
    left_inv value := by rcases value with ⟨value,⟨⟩⟩; rfl
    right_inv _ := rfl }

theorem followed_encode {A : Type} (codec : PrefixCodec A) (suffix : Bytes) (value : A) :
    (followed codec suffix).encode value = codec.encode value ++ suffix := rfl

def bytesDomain (text : String) : Bytes := frame (utf8 text)

/-- `write_bytes(&word.to_le_bytes())`: the payload is eight bytes, not a
raw u64 inserted between transcript operations. -/
def word : PrefixCodec Word :=
  (PrefixCodec.unsigned 8 (2^64) (by decide)).prefixed ([0] ++ encodeLE 8 8)

theorem word_encode (value : Word) : word.encode value = frame (encodeLE 8 value.val) := by
  simp only [word,PrefixCodec.prefixed,PrefixCodec.equiv,PrefixCodec.pair,PrefixCodec.marker,
    PrefixCodec.unsigned,Equiv.coe_fn_symm_mk,frame,TranscriptV2.Framing.encodeLE_length]

def scalar {F : Type} (field : FieldCodec F) : PrefixCodec F :=
  (PrefixCodec.field field).prefixed [1]

theorem scalar_encode {F : Type} (field : FieldCodec F) (value : F) :
    (scalar field).encode value = [1] ++ field.encode value := rfl

def slice {F : Type} (field : FieldCodec F) (count : ℕ) : PrefixCodec (Fin count → F) :=
  (PrefixCodec.vector (PrefixCodec.field field) count).prefixed ([2] ++ encodeLE 8 count)

theorem slice_encode {F : Type} (field : FieldCodec F) (count : ℕ) (values : Fin count → F) :
    (slice field count).encode values = [2] ++ encodeLE 8 count ++
      (List.ofFn values).flatMap field.encode := by
  simp only [slice,PrefixCodec.prefixed,PrefixCodec.equiv,PrefixCodec.pair,PrefixCodec.marker,
    Equiv.coe_fn_symm_mk,PrefixCodec.vector_encode,PrefixCodec.field]

/-- Two-element slices are still one slice operation, unlike the two
individually written sumcheck coefficients. -/
def pairSlice {F : Type} (field : FieldCodec F) : PrefixCodec (F × F) :=
  ((PrefixCodec.field field).pair (PrefixCodec.field field)).prefixed ([2] ++ encodeLE 8 2)

def fieldCodec {fields : Fields} {Advice : Type}
    (repr : ProofBodyCodec.Representations fields Advice) : (side : Side) → FieldCodec (fields side)
  | .binary => repr.binary
  | .prime => repr.prime

variable {g : Geometry} {fields : Fields} {Advice : Type}
variable (repr : ProofBodyCodec.Representations fields Advice) (shape : Shape g fields)

abbrev CircuitStatement (fields : Fields) (side : Side) (count : ℕ) :=
  Digest × (Fin count → fields side)

/-- Circuit ID, individually framed public scalars, and the field's zero
output claim. The ID fixes their count in the runtime's trusted circuit. -/
def statement (side : Side) (count : ℕ) : PrefixCodec (CircuitStatement fields side count) :=
  followed (framedDigest.pair (PrefixCodec.vector (scalar (fieldCodec repr side)) count))
    ([1] ++ (fieldCodec repr side).encode (shape.zero side))

abbrev CircuitSchedule (count : ℕ) := Fin count → Digest × Word

def schedule (count : ℕ) : PrefixCodec (CircuitSchedule count) :=
  (PrefixCodec.vector (framedDigest.pair word) count).prefixed
    (bytesDomain "layered-sumcheck/circuits/v1" ++ frame (encodeLE 8 count))

/-- Generated instances have no circuit ID. Their trusted template and
layout were bound before commitment; only fixed depths enter this schedule. -/
abbrev DerivedSchedule (count : ℕ) := Fin count → Word

def derivedSchedule (count : ℕ) : PrefixCodec (DerivedSchedule count) :=
  (PrefixCodec.vector (word.prefixed (bytesDomain "layered-sumcheck/derived-circuit/v1")) count).prefixed
    (bytesDomain "layered-sumcheck/circuits/v1" ++ frame (encodeLE 8 count))

abbrev PrimeStart (fields : Fields) (publicCount : ℕ) :=
  Fingerprints fields × (CircuitStatement fields .prime publicCount × CircuitSchedule 1)

def primeStart : PrefixCodec (PrimeStart fields shape.primePublic) :=
  (((pairSlice repr.binary).pair (pairSlice repr.prime)).pair
    ((statement repr shape .prime shape.primePublic).pair (schedule 1))).prefixed
      (bytesDomain "longfellow/witness-selection/responses/v1")

abbrev BinaryStart (fields : Fields) (Advice : Type) (publicCount : ℕ) :=
  Advice × (CircuitStatement fields .binary publicCount × DerivedSchedule 2)

/-- Bind advice and the ordinary hash statement. The generated adapter
has neither a separate instance ID nor a repeated public-input statement. -/
def binaryStart : PrefixCodec (BinaryStart fields Advice shape.binaryPublic) :=
  (repr.advice.prefixed (bytesDomain "p256-adapter/masked-quotient-bits/v1" ++
    [0] ++ encodeLE 8 repr.adviceWidth)).pair
      ((statement repr shape .binary shape.binaryPublic).pair (derivedSchedule 2))

inductive Start where
  | none | prime | binary
  deriving DecidableEq

def startAt (g : Geometry) (i : Fin g.roles.length) : Start :=
  if i.val = g.primeStart then .prime else if i.val = g.binaryStart then .binary else .none

def StartData : Start → Type
  | .none => Unit
  | .prime => PrimeStart fields shape.primePublic
  | .binary => BinaryStart fields Advice shape.binaryPublic

def startCodec : (start : Start) → PrefixCodec (StartData (Advice := Advice) shape start)
  | .none => PrefixCodec.unit
  | .prime => primeStart repr shape
  | .binary => binaryStart repr shape

def startCache : (start : Start) → StartData (Advice := Advice) shape start → ProtocolWrites.Fresh g fields Advice
  | .none, _ => {}
  | .prime, value => { fingerprints := some value.1 }
  | .binary, value => { advice := some value.1 }

def PackingHeader : Type :=
  if shape.binary128Packing then BoundedBytes maxLength else BoundedBytes maxLength × BoundedBytes maxLength

/-- The optimized binary profile writes a four-byte basis ID (`u32`),
whereas the generic profile writes its descriptor before the statement. -/
def packingHeader : PrefixCodec (PackingHeader shape) :=
  if h : shape.binary128Packing then by
    simpa [PackingHeader,h] using
      (followed CanonicalPrefix.bytes (frame (encodeLE 4 2))).prefixed
        (bytesDomain "longfellow/dual-packing128/trace-zero/v1")
  else by
    simpa [PackingHeader,h] using
      (CanonicalPrefix.bytes.pair CanonicalPrefix.bytes).prefixed
        (bytesDomain "longfellow/dual-packing/generic/trace-zero/v1")

/-- Caller-supplied statement bytes and the logical input/auxiliary cell counts.
The source coefficients and RHS are reconstructed from the earlier frontend
messages and oracle answers; they are not additional transcript writes. -/
abbrev PackingStatement (shape : Shape g fields) := PackingHeader shape × (Word × Word)

def packingStatement : PrefixCodec (PackingStatement shape) :=
  (packingHeader shape).pair (word.pair word)

abbrev SourceStatement := Digest × (Digest × Word)

def sourceStatement : PrefixCodec SourceStatement := framedDigest.pair (framedDigest.pair word)

def PackingA (g : Geometry) (fields : Fields) : Type := if g.packingDegree = 1 then Unit else fields .binary

def packingA : PrefixCodec (PackingA g fields) :=
  if h : g.packingDegree = 1 then by simpa only [PackingA,h,↓reduceIte] using PrefixCodec.unit
  else by
    simpa only [PackingA,h,↓reduceIte] using
      (scalar repr.binary).prefixed (bytesDomain (if shape.binary128Packing then "trace-zero128/A" else "trace-zero/A"))

/-- Role data retains all metadata as well as actual body messages. The
fingerprint constructor is not exported as an ordinary block codec. -/
def RoleData : Role → Type
  | .fingerprint => Unit
  | .inputAssertions .. | .assertions .. => Word
  | .sumcheck side .. => fields side × fields side
  | .terminal side .. => fields side
  | .combine side .. => fields side × fields side
  | .rowBatching => Unit
  | .rescaling => Unit
  | .conversion => fields .prime
  | .packing => PackingStatement shape × (Fin g.packingDegree → fields .binary)
  | .batching => PackingA g fields × (SourceStatement × SourceStatement)
  | .opening => Response g (fields .binary) × Response g (fields .prime)

def response (side : Side) : PrefixCodec (Response g (fields side)) :=
  ((slice (fieldCodec repr side) (g.rowDimension+g.maskingDegree)).pair
    (slice (fieldCodec repr side) (2*g.rowDimension))).equiv {
      toFun value := ⟨value.1,value.2⟩
      invFun value := (value.h,value.z)
      left_inv _ := rfl
      right_inv value := by cases value; rfl }

def roleCodec : (role : Role) → PrefixCodec (RoleData shape role)
  | .fingerprint => PrefixCodec.unit
  | .inputAssertions .. | .assertions .. => word
  | .sumcheck side .. => (scalar (fieldCodec repr side)).pair (scalar (fieldCodec repr side))
  | .terminal side .. => scalar (fieldCodec repr side)
  | .combine side .. => pairSlice (fieldCodec repr side)
  | .rowBatching => PrefixCodec.marker
      (bytesDomain "native-masked-sumcheck/all-linear-rows/v1" ++ bytesDomain "all-linear-rows")
  | .rescaling => PrefixCodec.marker (bytesDomain "native-shared-prefix/nonzero-rescaling/v2")
  | .conversion => followed
      ((scalar repr.prime).prefixed (bytesDomain "native-shared-prefix/masked-opening/v2"))
      (bytesDomain "p256-adapter/two-independent-full-field-rescalings/v3")
  | .packing => (packingStatement shape).pair (slice repr.binary g.packingDegree)
  | .batching => (packingA repr shape).pair (sourceStatement.pair sourceStatement)
  | .opening => (response repr .binary).pair (response repr .prime)

private def packingACache (value : PackingA g fields) : Option (fields .binary) :=
  if h : g.packingDegree = 1 then none else
    some (by simpa only [PackingA,h,↓reduceIte] using value)

def roleCache : (role : Role) → RoleData shape role → ProtocolWrites.Fresh g fields Advice
  | .sumcheck side .., value => { frontend := Function.update (fun _ => .empty) side (.round ⟨value.1,value.2⟩) }
  | .terminal side .., value => { frontend := Function.update (fun _ => .empty) side (.cross value) }
  | .combine side .., value => { frontend := Function.update (fun _ => .empty) side (.claims value.1 value.2) }
  | .conversion, value => { mu := some value }
  | .packing, value => { packingU := some value.2 }
  | .batching, value => { packingA := packingACache value.1 }
  | .opening, value => { responses := some value }
  | _, _ => {}

abbrev Data (i : Fin g.roles.length) :=
  StartData (Advice := Advice) shape (startAt g i) × RoleData shape (g.roles.get i)

def codec (i : Fin g.roles.length) : PrefixCodec (Data (Advice := Advice) shape i) :=
  (startCodec repr shape (startAt g i)).pair (roleCodec repr shape (g.roles.get i))

/-- The cache includes only writes observable at this actual role. Public
metadata stays in the base bytes; derived instance IDs are absent. -/
def cache (i : Fin g.roles.length) (value : Data (Advice := Advice) shape i) : ProtocolWrites.Fresh g fields Advice :=
  let start := startCache shape (startAt g i) value.1
  let role : ProtocolWrites.Fresh g fields Advice := roleCache shape (g.roles.get i) value.2
  { fingerprints := start.fingerprints, advice := start.advice, mu := role.mu,
    packingU := role.packingU, packingA := role.packingA,
    frontend := role.frontend, responses := role.responses }

/-- Complete role-local parsing. Ignored suffixes cannot be used to change
the byte transcript while keeping its cached writes unchanged. -/
def parse (i : Fin g.roles.length) (bytes : Bytes) : Option (Data (Advice := Advice) shape i) :=
  readWhole (codec repr shape i) bytes

def parseCache (i : Fin g.roles.length) (bytes : Bytes) : Option (ProtocolWrites.Fresh g fields Advice) :=
  (parse repr shape i bytes).map (cache shape i)

theorem parse_encode (i : Fin g.roles.length) (value : Data (Advice := Advice) shape i) :
    parse repr shape i ((codec repr shape i).encode value) = some value := readWhole_encode _ value

theorem parse_canonical (i : Fin g.roles.length) (bytes : Bytes) (value : Data (Advice := Advice) shape i)
    (h : parse repr shape i bytes = some value) : bytes = (codec repr shape i).encode value :=
  readWhole_canonical _ bytes value h

theorem parseCache_encode (i : Fin g.roles.length) (value : Data (Advice := Advice) shape i) :
    parseCache repr shape i ((codec repr shape i).encode value) = some (cache shape i value) := by
  simp only [parseCache,parse_encode,Option.map_some]

theorem parseCache_some_iff (i : Fin g.roles.length) (bytes : Bytes) (fresh : ProtocolWrites.Fresh g fields Advice) :
    parseCache repr shape i bytes = some fresh ↔
      ∃ value : Data (Advice := Advice) shape i, bytes = (codec repr shape i).encode value ∧ cache shape i value = fresh := by
  constructor
  · intro h
    obtain ⟨value,hvalue,hcache⟩ := Option.map_eq_some_iff.mp h
    exact ⟨value,parse_canonical repr shape i bytes value hvalue,hcache⟩
  · rintro ⟨value,rfl,rfl⟩
    exact parseCache_encode repr shape i value

/-- Only ordinary blocks are exposed to the whole-query parser. Block zero
must use the separate complete initial-prefix/context codec. -/
def block (i : Fin g.roles.length) (_ordinary : g.roles.get i ≠ .fingerprint) : QueryCodec.Block where
  Data := Data (Advice := Advice) shape i
  codec := codec repr shape i
  domain := (g.roles.get i).domain

end LfzkV2.Current.WireBlocks
