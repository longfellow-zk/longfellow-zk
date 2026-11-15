import LfzkV2.Current.Format
import LfzkV2.Current.TaggedCodec
import LfzkV2.Current.WireBlocks
import LfzkV2.Current.ProofBodyBounds

/-! The deployed transcript format, `TaggedFormat`: the tagged node grammar
of `rust/src/runtime/v2/transcript/DESIGN.md` (transcript I5 to I7) and the
mdoc proof body of `rust/src/runtime/v2/proto/DESIGN.md`.

- Node 0 is the statement: the statement message with the session, the
  setup's circuit, layout and geometry messages, both `PublicInputs`
  messages and the `Commitment`. It is the key, so it binds the public
  values of both circuits before the first draw.
- Each later node is the prover messages written since the previous draw,
  every message a u64 tag and its typed values (`TaggedCodec`). No setup
  constant, circuit identifier, domain label or derived value is written
  after node 0.
- A node ends with the u64 `ROUND` terminator; the last node is the `Seal`
  message, whose one value is the whole proof body, then `SEAL`.
- The body is `MDA7`, the prover messages in physical order and the joint
  opening, its frontier the rest of the body, with no count; the complete
  proof is the body and its 32-byte seal block (`complete`).

The setup's statement constants are bytes fixed by the trusted circuits
(`Setup`); the format reads none of them back. -/
noncomputable section
namespace LfzkV2.Current.TaggedFormat
open CanonicalPrefix TaggedCodec QueryRuntime
open TranscriptV2.Framing (FieldCodec encodeLE)
open SumcheckV2
open scoped Classical

/-! ## Registry -/

/-- Message tags (`rust/src/runtime/v2/proto/tags.rs`). -/
def publicInputsTag : ℕ := 21
def commitmentTag : ℕ := 32
def fingerprintTag : ℕ := 33
def roundTag : ℕ := 48
def crossTag : ℕ := 49
def claimsTag : ℕ := 50
def splitTag : ℕ := 64
def quotientsTag : ℕ := 65
def packingUTag : ℕ := 80
def packingATag : ℕ := 81
def responseTag : ℕ := 96
def sealTag : ℕ := 112

/-- The registry's field IDs of the two mdoc fields: GF(2^128) and P-256. -/
def fieldId : Side → ℕ
  | .binary => 4
  | .prime => 1

/-- `ROUND` and `SEAL` (transcript I7). -/
def round : Bytes := word 0
def «seal» : Bytes := word 1

/-! ## Node wire -/

private def followed {A : Type} (codec : PrefixCodec A) (suffix : Bytes) : PrefixCodec A :=
  (codec.pair (PrefixCodec.marker suffix)).equiv {
    toFun := Prod.fst
    invFun value := (value,())
    left_inv value := by rcases value with ⟨value,⟨⟩⟩; rfl
    right_inv _ := rfl }

/-- Every boundary ends with `ROUND`; the seal node is the `Seal` message,
its one `Bytes` value the whole body, then `SEAL`. -/
def wire : NodeWire where
  terminator _ := round
  sealFrame body := word sealTag ++ (word 0 ++ word body.length ++ body) ++ «seal»
  sealCodec := followed (tagged sealTag bytesValue) «seal»
  sealCodec_encode body := by
    change word sealTag ++ bytesValue.encode body ++ «seal» = _
    rw [bytesValue_encode]

theorem wire_sealFrame (body : Bytes) :
    wire.sealFrame body = word sealTag ++ word 0 ++ word body.length ++ body ++ «seal» := by
  simp only [wire,List.append_assoc]

theorem wire_terminator (domain : Domain) : wire.terminator domain = word 0 := rfl

/-! ## Node 0: the statement -/

/-- The trusted setup constants the statement absorbs: the statement
message's tag and leading values before the session, the values and
messages after it up to the public inputs, and the joint commitment context
of the Merkle hashes (which no node absorbs). -/
structure Setup where
  head : Bytes
  constants : Bytes
  jointContext : Digest

/-- The first node's key: the request and the commitment root. -/
structure Key (publicCount primeCount : ℕ) (Prime : Type) where
  session : BoundedBytes maxLength
  publicBits : Fin publicCount → Bool
  primeInputs : Fin primeCount → Prime
  root : Digest

instance (publicCount primeCount : ℕ) (Prime : Type) [Fintype Prime] :
    Fintype (Key publicCount primeCount Prime) := by
  apply Fintype.ofInjective (fun key : Key publicCount primeCount Prime =>
    (key.session,key.publicBits,key.primeInputs,key.root))
  intro a b h
  cases a
  cases b
  cases h
  rfl

variable {Prime : Type}

private def bitData : Fin 2 ≃ Bool where
  toFun value := decide (value.val = 1)
  invFun value := if value then 1 else 0
  left_inv value := by fin_cases value <;> rfl
  right_inv value := by cases value <;> rfl

/-- A public bit as a GF(2^128) element: the canonical 16-byte encoding of
0 or 1. -/
def bit : PrefixCodec Bool := (PrefixCodec.unsigned 16 2 (by decide)).equiv bitData

theorem bit_length (value : Bool) : (bit.encode value).length = 16 :=
  TranscriptV2.Framing.encodeLE_length _ _

private def keyData (publicCount primeCount : ℕ) (Prime : Type) :
    (BoundedBytes maxLength × ((Fin publicCount → Bool) × ((Fin primeCount → Prime) × Digest))) ≃
      Key publicCount primeCount Prime where
  toFun value := ⟨value.1,value.2.1,value.2.2.1,value.2.2.2⟩
  invFun key := (key.session,key.publicBits,key.primeInputs,key.root)
  left_inv _ := rfl
  right_inv key := by cases key; rfl

/-- The session inside the statement message, the setup constants, the hash
circuit's public bits, the signature circuit's public inputs and the root. -/
def first (setup : Setup) (prime : FieldCodec Prime) (publicCount primeCount : ℕ) :
    PrefixCodec (Key publicCount primeCount Prime) :=
  ((bytesValue.prefixed setup.head).pair
    (((tagged publicInputsTag (elementsOf (fieldId .binary) bit publicCount)).prefixed setup.constants).pair
      ((tagged publicInputsTag (elements (fieldId .prime) prime primeCount)).pair
        (tagged commitmentTag digestValue)))).equiv (keyData publicCount primeCount Prime)

theorem first_encode (setup : Setup) (prime : FieldCodec Prime) (publicCount primeCount : ℕ)
    (key : Key publicCount primeCount Prime) :
    (first setup prime publicCount primeCount).encode key =
      setup.head ++ bytesValue.encode key.session ++ setup.constants ++
      word publicInputsTag ++ (elementsOf (fieldId .binary) bit publicCount).encode key.publicBits ++
      word publicInputsTag ++ (elements (fieldId .prime) prime primeCount).encode key.primeInputs ++
      word commitmentTag ++ digestValue.encode key.root := by
  simp only [first,tagged,PrefixCodec.equiv,PrefixCodec.pair,PrefixCodec.prefixed,PrefixCodec.marker,
    keyData,Equiv.coe_fn_symm_mk,List.append_assoc]

def firstBound (setup : Setup) (prime : FieldCodec Prime) (publicCount primeCount : ℕ) : ℕ :=
  setup.head.length+(16+maxLength)+setup.constants.length+(32+publicCount*16)+
    (32+primeCount*prime.width)+56

theorem first_length_le (setup : Setup) (prime : FieldCodec Prime) (publicCount primeCount : ℕ)
    (key : Key publicCount primeCount Prime) :
    ((first setup prime publicCount primeCount).encode key).length ≤
      firstBound setup prime publicCount primeCount := by
  rw [first_encode,bytesValue_encode]
  simp only [List.length_append,word_length,elementsOf_length _ bit 16 bit_length,elements_length,
    digestValue_length]
  have := key.session.bound
  unfold firstBound
  omega

/-! ## Later nodes: the prover messages of each boundary -/

section Packets
variable {g : Geometry} {fields : Fields} {Advice : Type}
variable (repr : ProofBodyCodec.Representations fields Advice)

def fieldCodec : (side : Side) → FieldCodec (fields side)
  | .binary => repr.binary
  | .prime => repr.prime

/-- Messages written at a frontend's first boundary, before its first draw:
both fields' fingerprint responses before the signature circuit, the masked
quotients before the hash circuit. -/
def StartData (fields : Fields) (Advice : Type) : WireBlocks.Start → Type
  | .none => Unit
  | .prime => Fingerprints fields
  | .binary => Advice

def startCodec : (start : WireBlocks.Start) → PrefixCodec (StartData fields Advice start)
  | .none => PrefixCodec.unit
  | .prime => (tagged fingerprintTag (elementPair (fieldId .binary) repr.binary)).pair
      (tagged fingerprintTag (elementPair (fieldId .prime) repr.prime))
  | .binary => tagged quotientsTag repr.adviceWrites

def startCache : (start : WireBlocks.Start) → StartData fields Advice start → ProtocolWrites.Fresh g fields Advice
  | .none, _ => {}
  | .prime, value => { fingerprints := some value }
  | .binary, value => { advice := some value }

/-- The prover message of each role. Assertion and row-batching roles
write none. -/
def RoleData (g : Geometry) (fields : Fields) : Role → Type
  | .fingerprint => Unit
  | .inputAssertions .. | .assertions .. => Unit
  | .sumcheck side .. => fields side × fields side
  | .terminal side .. => fields side
  | .combine side .. => fields side × fields side
  | .rowBatching => Unit
  | .conversion => fields .prime
  | .packing => Fin g.packingDegree → fields .binary
  | .batching => WireBlocks.PackingA g fields
  | .opening => Response g (fields .binary) × Response g (fields .prime)

private def responseData (g : Geometry) (F : Type) :
    ((Fin (g.rowDimension+g.maskingDegree) → F) × (Fin (2*g.rowDimension) → F)) ≃ Response g F where
  toFun value := ⟨value.1,value.2⟩
  invFun value := (value.h,value.z)
  left_inv _ := rfl
  right_inv value := by cases value; rfl

/-- `PolygeroResponse`: H on the first k+s nodes, then Z on the first 2k. -/
def response (side : Side) : PrefixCodec (Response g (fields side)) :=
  tagged responseTag (((elements (fieldId side) (fieldCodec repr side) (g.rowDimension+g.maskingDegree)).pair
    (elements (fieldId side) (fieldCodec repr side) (2*g.rowDimension))).equiv (responseData g (fields side)))

def packingA : PrefixCodec (WireBlocks.PackingA g fields) :=
  if h : g.packingDegree = 1 then by simpa only [WireBlocks.PackingA,h,↓reduceIte] using PrefixCodec.unit
  else by
    simpa only [WireBlocks.PackingA,h,↓reduceIte] using
      tagged packingATag (element (fieldId .binary) repr.binary)

def roleCodec : (role : Role) → PrefixCodec (RoleData g fields role)
  | .fingerprint => PrefixCodec.unit
  | .inputAssertions .. => PrefixCodec.unit
  | .assertions .. => PrefixCodec.unit
  | .sumcheck side .. => tagged roundTag (elementPair (fieldId side) (fieldCodec repr side))
  | .terminal side .. => tagged crossTag (element (fieldId side) (fieldCodec repr side))
  | .combine side .. => tagged claimsTag (elementPair (fieldId side) (fieldCodec repr side))
  | .rowBatching => PrefixCodec.unit
  | .conversion => tagged splitTag (element (fieldId .prime) repr.prime)
  | .packing => tagged packingUTag (elements (fieldId .binary) repr.binary g.packingDegree)
  | .batching => packingA repr
  | .opening => (response repr .binary).pair (response repr .prime)

private def packingACache (value : WireBlocks.PackingA g fields) : Option (fields .binary) :=
  if h : g.packingDegree = 1 then none else
    some (by simpa only [WireBlocks.PackingA,h,↓reduceIte] using value)

def roleCache : (role : Role) → RoleData g fields role → ProtocolWrites.Fresh g fields Advice
  | .sumcheck side .., value => { frontend := Function.update (fun _ => .empty) side (.round ⟨value.1,value.2⟩) }
  | .terminal side .., value => { frontend := Function.update (fun _ => .empty) side (.cross value) }
  | .combine side .., value => { frontend := Function.update (fun _ => .empty) side (.claims value.1 value.2) }
  | .conversion, value => { mu := some value }
  | .packing, value => { packingU := some value }
  | .batching, value => { packingA := packingACache value }
  | .opening, value => { responses := some value }
  | _, _ => {}

abbrev Data (i : Fin g.roles.length) :=
  StartData fields Advice (WireBlocks.startAt g i) × RoleData g fields (g.roles.get i)

def codec (i : Fin g.roles.length) : PrefixCodec (Data (fields := fields) (Advice := Advice) i) :=
  (startCodec repr (WireBlocks.startAt g i)).pair (roleCodec repr (g.roles.get i))

def cache (i : Fin g.roles.length) (value : Data (fields := fields) (Advice := Advice) i) : ProtocolWrites.Fresh g fields Advice :=
  let start : ProtocolWrites.Fresh g fields Advice := startCache (WireBlocks.startAt g i) value.1
  let role : ProtocolWrites.Fresh g fields Advice := roleCache (g.roles.get i) value.2
  { fingerprints := start.fingerprints, advice := start.advice, mu := role.mu,
    packingU := role.packingU, packingA := role.packingA,
    frontend := role.frontend, responses := role.responses }

/-! ### Sizes -/

def startLength : WireBlocks.Start → ℕ
  | .none => 0
  | .prime => (32+2*repr.binary.width)+(32+2*repr.prime.width)
  | .binary => 8+repr.adviceWritesWidth

def responseLength (g : Geometry) (side : Side) : ℕ :=
  8+((24+(g.rowDimension+g.maskingDegree)*(fieldCodec repr side).width)+
    (24+(2*g.rowDimension)*(fieldCodec repr side).width))

def roleLength (g : Geometry) : Role → ℕ
  | .sumcheck side .. => 32+2*(fieldCodec repr side).width
  | .terminal side .. => 32+(fieldCodec repr side).width
  | .combine side .. => 32+2*(fieldCodec repr side).width
  | .conversion => 32+repr.prime.width
  | .packing => 32+g.packingDegree*repr.binary.width
  | .batching => if g.packingDegree = 1 then 0 else 32+repr.binary.width
  | .opening => responseLength repr g .binary+responseLength repr g .prime
  | _ => 0

theorem startCodec_length (start : WireBlocks.Start) (value : StartData fields Advice start) :
    ((startCodec repr start).encode value).length = startLength repr start := by
  cases start with
  | none => rfl
  | prime =>
      change ((tagged fingerprintTag (elementPair (fieldId .binary) repr.binary)).encode value.1 ++
        (tagged fingerprintTag (elementPair (fieldId .prime) repr.prime)).encode value.2).length = _
      simp only [List.length_append,tagged_length,elementPair_length,startLength]
      omega
  | binary =>
      change ((tagged quotientsTag repr.adviceWrites).encode value).length = _
      rw [tagged_length,repr.adviceWritesLength]
      rfl

private theorem cast_length {A B : Type} (h : A = B) (codec : PrefixCodec A) (width : ℕ)
    (hlen : ∀ value, (codec.encode value).length = width) (value : B) :
    ((cast (congrArg PrefixCodec h) codec).encode value).length = width := by
  cases h
  exact hlen value

theorem packingA_length (value : WireBlocks.PackingA g fields) :
    ((packingA repr).encode value).length = roleLength repr g .batching := by
  by_cases h : g.packingDegree = 1
  · simp only [packingA,h,↓reduceDIte,roleLength,↓reduceIte]
    exact cast_length (by simp only [WireBlocks.PackingA,h,↓reduceIte]) PrefixCodec.unit 0 (fun _ => rfl) value
  · simp only [packingA,h,↓reduceDIte,roleLength,↓reduceIte]
    exact cast_length (by simp only [WireBlocks.PackingA,h,↓reduceIte])
      (tagged packingATag (element (fieldId .binary) repr.binary)) (32+repr.binary.width) (by
        intro value
        rw [tagged_length,element_length]
        omega) value

theorem response_length (side : Side) (value : Response g (fields side)) :
    ((response repr side).encode value).length = responseLength repr g side := by
  change (word responseTag ++ ((elements (fieldId side) (fieldCodec repr side) _).encode value.h ++
    (elements (fieldId side) (fieldCodec repr side) _).encode value.z)).length = _
  simp only [List.length_append,word_length,elements_length,responseLength]

theorem roleCodec_length (role : Role) (value : RoleData g fields role) :
    ((roleCodec repr role).encode value).length = roleLength repr g role := by
  cases role with
  | sumcheck side stage round =>
      change ((tagged roundTag (elementPair (fieldId side) (fieldCodec repr side))).encode value).length = _
      rw [tagged_length,elementPair_length]
      simp only [roleLength]
      omega
  | terminal side stage =>
      change ((tagged crossTag (element (fieldId side) (fieldCodec repr side))).encode value).length = _
      rw [tagged_length,element_length]
      simp only [roleLength]
      omega
  | combine side stage entries fragments last =>
      change ((tagged claimsTag (elementPair (fieldId side) (fieldCodec repr side))).encode value).length = _
      rw [tagged_length,elementPair_length]
      simp only [roleLength]
      omega
  | conversion =>
      change ((tagged splitTag (element (fieldId .prime) repr.prime)).encode value).length = _
      rw [tagged_length,element_length]
      simp only [roleLength]
      omega
  | packing =>
      change ((tagged packingUTag (elements (fieldId .binary) repr.binary g.packingDegree)).encode value).length = _
      rw [tagged_length,elements_length]
      simp only [roleLength]
      omega
  | batching => exact packingA_length repr value
  | opening =>
      change ((response repr .binary).encode value.1 ++ (response repr .prime).encode value.2).length = _
      rw [List.length_append,response_length,response_length]
      rfl
  | fingerprint => rfl
  | inputAssertions => rfl
  | assertions => rfl
  | rowBatching => rfl

def dataLength (i : Fin g.roles.length) : ℕ :=
  startLength repr (WireBlocks.startAt g i)+roleLength repr g (g.roles.get i)

theorem codec_length (i : Fin g.roles.length) (value : Data (fields := fields) (Advice := Advice) i) :
    ((codec repr i).encode value).length = dataLength repr i := by
  change ((startCodec repr _).encode value.1 ++ (roleCodec repr _).encode value.2).length = _
  rw [List.length_append,startCodec_length,roleCodec_length]
  rfl

/-- An ambient bound on every later node; it adds no bytes. -/
def laterBound (g : Geometry) : ℕ := Finset.univ.sup fun i : Fin g.roles.length => dataLength (g := g) repr i

theorem codec_length_le (i : Fin g.roles.length) (value : Data (fields := fields) (Advice := Advice) i) :
    ((codec repr i).encode value).length ≤ laterBound repr g := by
  rw [codec_length]
  exact Finset.le_sup (f := fun i : Fin g.roles.length => dataLength (g := g) repr i) (Finset.mem_univ i)

/-! ### Data from the body and from the fresh writes -/

def startFromBody {Auth : Type} (body : Body g fields Advice Auth) :
    (start : WireBlocks.Start) → StartData fields Advice start
  | .none => ()
  | .prime => body.fingerprints
  | .binary => body.advice

private def packingValues {Auth : Type} (body : Body g fields Advice Auth) (h : g.packingDegree ≠ 1) :
    (Fin g.packingDegree → fields .binary) × fields .binary := by
  simpa only [PackingPayload,h,↓reduceIte] using body.packing

def roleFromBody {Auth : Type} (body : Body g fields Advice Auth) :
    (role : Role) → WireBlocks.ValidRole g role → RoleData g fields role
  | .fingerprint, _ => ()
  | .inputAssertions .., _ => ()
  | .assertions .., _ => ()
  | .sumcheck side stage round, valid =>
      let hs := valid.choose
      ((body.frontend side) ⟨stage,hs⟩).coefficients ⟨round,valid.choose_spec⟩
  | .terminal side stage, valid => ((body.frontend side) ⟨stage,valid⟩).cross
  | .combine side stage .., valid => ((body.frontend side) ⟨stage,valid⟩).claims
  | .rowBatching, _ => ()
  | .conversion, _ => body.mu
  | .packing, valid => (packingValues body valid).1
  | .batching, _ => if h : g.packingDegree = 1 then
      (by simpa only [RoleData,WireBlocks.PackingA,h,↓reduceIte] using ()) else
      (by simpa only [RoleData,WireBlocks.PackingA,h,↓reduceIte] using (packingValues body h).2)
  | .opening, _ => (body.binaryBackend.response,body.primeBackend.response)

def fromBody {Auth : Type} (i : Fin g.roles.length) (body : Body g fields Advice Auth) :
    Data (fields := fields) (Advice := Advice) i :=
  (startFromBody body (WireBlocks.startAt g i), roleFromBody body (g.roles.get i) (WireBlocks.role_valid g i))

private def roleBodyCache {Auth : Type} (body : Body g fields Advice Auth) (role : Role) :
    ProtocolWrites.Fresh g fields Advice where
  mu := if role = .conversion then some body.mu else none
  packingU := if role = .packing then (ProtocolWrites.packingPair body).map Prod.fst else none
  packingA := if role = .batching then (ProtocolWrites.packingPair body).map Prod.snd else none
  frontend := ProtocolWrites.frontendMessages body role
  responses := if role = .opening then some (body.binaryBackend.response,body.primeBackend.response) else none

private theorem roleFromBody_cache {Auth : Type} (body : Body g fields Advice Auth) (role : Role)
    (valid : WireBlocks.ValidRole g role) :
    roleCache (Advice := Advice) role (roleFromBody body role valid) = roleBodyCache body role := by
  cases role with
  | sumcheck side stage round =>
      simp only [roleFromBody,roleCache,roleBodyCache,ProtocolWrites.frontendMessages,
        ProtocolWrites.stageMessage,dif_pos valid.choose,ProtocolWrites.layerMessage,dif_pos valid.choose_spec]
      rfl
  | terminal side stage =>
      have hs : stage < (g.frontend side).stages.length := valid
      simp [roleFromBody,roleCache,roleBodyCache,ProtocolWrites.frontendMessages,
        ProtocolWrites.stageMessage,ProtocolWrites.layerMessage,hs]
  | combine side stage entries fragments last =>
      have hs : stage < (g.frontend side).stages.length := valid
      simp [roleFromBody,roleCache,roleBodyCache,ProtocolWrites.frontendMessages,
        ProtocolWrites.stageMessage,ProtocolWrites.layerMessage,hs]
  | packing =>
      change g.packingDegree ≠ 1 at valid
      simp [roleFromBody,roleCache,roleBodyCache,ProtocolWrites.frontendMessages,
        ProtocolWrites.packingPair,packingValues,valid]
  | batching =>
      have ha : (roleCache (Advice := Advice) .batching (roleFromBody body .batching valid)).packingA =
          (ProtocolWrites.packingPair body).map Prod.snd := by
        by_cases he : g.packingDegree = 1
        · simp [roleCache,packingACache,he,ProtocolWrites.packingPair]
        · simp [roleCache,packingACache,he,roleFromBody,ProtocolWrites.packingPair,packingValues]
          exact (cast_cast _ _ _).trans (cast_eq _ _)
      exact congrArg (fun value : Option (fields .binary) =>
        ({ packingA := value } : ProtocolWrites.Fresh g fields Advice)) ha
  | _ => rfl

private def startBodyCache {Auth : Type} (body : Body g fields Advice Auth) :
    WireBlocks.Start → ProtocolWrites.Fresh g fields Advice
  | .none => {}
  | .prime => { fingerprints := some body.fingerprints }
  | .binary => { advice := some body.advice }

private theorem startFromBody_cache {Auth : Type} (body : Body g fields Advice Auth) (start : WireBlocks.Start) :
    startCache (g := g) start (startFromBody body start) = startBodyCache body start := by
  cases start <;> rfl

/-- Each node's cache is the body's fresh writes at its boundary. -/
theorem fromBody_cache {Auth : Type} (i : Fin g.roles.length) (body : Body g fields Advice Auth) :
    cache i (fromBody i body) = ProtocolWrites.fresh body i := by
  unfold cache fromBody
  rw [roleFromBody_cache,startFromBody_cache]
  have hne : g.primeStart ≠ g.binaryStart := by
    dsimp only [Geometry.binaryStart,Geometry.primeStart]
    omega
  by_cases hp : i.val = g.primeStart
  · simp [WireBlocks.startAt,hp,startBodyCache,ProtocolWrites.fresh,roleBodyCache,hne]
  · by_cases hb : i.val = g.binaryStart
    · simp [WireBlocks.startAt,hb,startBodyCache,ProtocolWrites.fresh,roleBodyCache,Ne.symm hne]
    · simp [WireBlocks.startAt,hp,hb,startBodyCache,ProtocolWrites.fresh,roleBodyCache]

section Fresh
variable (shape : WireBlocks.Shape g fields) [Inhabited Advice]

def polynomial {E : Type} (zero : E) : Layered.Replay.Message E → E × E
  | .round p => (p.c0,p.c1)
  | _ => (zero,zero)

def cross {E : Type} (zero : E) : Layered.Replay.Message E → E
  | .cross x => x
  | _ => zero

def claims {E : Type} (zero : E) : Layered.Replay.Message E → E × E
  | .claims a b => (a,b)
  | _ => (zero,zero)

/-- A node's messages from its fresh writes alone, with public defaults
only off the honest image. The simulator writes these. -/
def startFromFresh (fresh : ProtocolWrites.Fresh g fields Advice) :
    (start : WireBlocks.Start) → StartData fields Advice start
  | .none => ()
  | .prime => fresh.fingerprints.getD ((shape.zero .binary,shape.zero .binary),
      (shape.zero .prime,shape.zero .prime))
  | .binary => fresh.advice.getD default

def roleFromFresh (fresh : ProtocolWrites.Fresh g fields Advice) : (role : Role) → RoleData g fields role
  | .fingerprint => ()
  | .inputAssertions .. => ()
  | .assertions .. => ()
  | .sumcheck side .. => polynomial (shape.zero side) (fresh.frontend side)
  | .terminal side .. => cross (shape.zero side) (fresh.frontend side)
  | .combine side .. => claims (shape.zero side) (fresh.frontend side)
  | .rowBatching => ()
  | .conversion => fresh.mu.getD (shape.zero .prime)
  | .packing => fresh.packingU.getD (fun _ => shape.zero .binary)
  | .batching =>
      if h : g.packingDegree = 1 then (by simpa only [RoleData,WireBlocks.PackingA,h,↓reduceIte] using ())
      else (by simpa only [RoleData,WireBlocks.PackingA,h,↓reduceIte] using fresh.packingA.getD (shape.zero .binary))
  | .opening => fresh.responses.getD
      (⟨fun _ => shape.zero .binary,fun _ => shape.zero .binary⟩,
       ⟨fun _ => shape.zero .prime,fun _ => shape.zero .prime⟩)

def fromFresh (i : Fin g.roles.length) (fresh : ProtocolWrites.Fresh g fields Advice) : Data (fields := fields) (Advice := Advice) i :=
  (startFromFresh shape fresh (WireBlocks.startAt g i), roleFromFresh shape fresh (g.roles.get i))

private theorem startFromFresh_body_for {Auth : Type} (body : Body g fields Advice Auth) (i : Fin g.roles.length)
    (start : WireBlocks.Start) (hs : WireBlocks.startAt g i = start) :
    startFromFresh shape (ProtocolWrites.fresh body i) start = startFromBody body start := by
  cases start with
  | none => rfl
  | prime =>
      have hp : i.val = g.primeStart := by
        unfold WireBlocks.startAt at hs
        split_ifs at hs
        simp_all
      simp [startFromFresh,startFromBody,ProtocolWrites.fresh,hp]
  | binary =>
      have hb : i.val = g.binaryStart := by
        unfold WireBlocks.startAt at hs
        split_ifs at hs
        simp_all
      simp [startFromFresh,startFromBody,ProtocolWrites.fresh,hb]

omit [Inhabited Advice] in
private theorem roleFromFresh_body_for {Auth : Type} (body : Body g fields Advice Auth) (i : Fin g.roles.length)
    (role : Role) (hr : g.roles.get i = role) (valid : WireBlocks.ValidRole g role) :
    roleFromFresh shape (ProtocolWrites.fresh body i) role = roleFromBody body role valid := by
  simp only [List.get_eq_getElem] at hr
  cases role with
  | sumcheck side stage round =>
      obtain ⟨hs,hn⟩ := valid
      simp only [List.get_eq_getElem] at hn
      simp [roleFromFresh,roleFromBody,ProtocolWrites.fresh,hr,
        ProtocolWrites.frontendMessages,ProtocolWrites.stageMessage,ProtocolWrites.layerMessage,
        hs,hn,Body.frontend,polynomial]
  | terminal side stage =>
      change stage < (g.frontend side).stages.length at valid
      simp [roleFromFresh,roleFromBody,ProtocolWrites.fresh,hr,
        ProtocolWrites.frontendMessages,ProtocolWrites.stageMessage,ProtocolWrites.layerMessage,valid,cross]
  | combine side stage entries fragments last =>
      change stage < (g.frontend side).stages.length at valid
      simp [roleFromFresh,roleFromBody,ProtocolWrites.fresh,hr,
        ProtocolWrites.frontendMessages,ProtocolWrites.stageMessage,ProtocolWrites.layerMessage,valid,claims]
  | packing =>
      change g.packingDegree ≠ 1 at valid
      simp [roleFromFresh,roleFromBody,ProtocolWrites.fresh,hr,ProtocolWrites.packingPair,valid]
      rfl
  | batching =>
      by_cases hd : g.packingDegree = 1 <;>
        simp [roleFromFresh,roleFromBody,ProtocolWrites.fresh,hr,ProtocolWrites.packingPair,hd]
      rfl
  | _ => simp [roleFromFresh,roleFromBody,ProtocolWrites.fresh,hr]

/-- On the honest image the fresh writes determine the node's messages. -/
theorem fromFresh_body {Auth : Type} (body : Body g fields Advice Auth) (i : Fin g.roles.length) :
    fromFresh shape i (ProtocolWrites.fresh body i) = fromBody i body :=
  Prod.ext (startFromFresh_body_for shape body i _ rfl)
    (roleFromFresh_body_for shape body i _ rfl (WireBlocks.role_valid g i))

end Fresh

/-! ### The opening node -/

abbrev Responses (g : Geometry) (fields : Fields) :=
  Response g (fields .binary) × Response g (fields .prime)

theorem startAt_opening : WireBlocks.startAt g g.openingIndex = .none := by
  have hlength := g.roles_length
  have hlast := g.openingIndex_last
  have hp : g.openingIndex.val ≠ g.primeStart := by
    dsimp only [Geometry.primeStart]
    omega
  have hb : g.openingIndex.val ≠ g.binaryStart := by
    dsimp only [Geometry.binaryStart]
    omega
  simp only [WireBlocks.startAt,if_neg hp,if_neg hb]

private def noneValue (start : WireBlocks.Start) (h : start = .none) : StartData fields Advice start := by
  cases h
  exact ()

private def responseValue (role : Role) (h : role = .opening) (responses : Responses g fields) :
    RoleData g fields role := by
  cases h
  exact responses

def openingData (responses : Responses g fields) : Data (fields := fields) (Advice := Advice) g.openingIndex :=
  (noneValue _ startAt_opening,responseValue _ g.get_openingIndex responses)

private theorem noneValue_cache (start : WireBlocks.Start) (h : start = .none) :
    startCache (g := g) (Advice := Advice) start (noneValue (fields := fields) start h) = {} := by
  cases h
  rfl

private theorem responseValue_cache (role : Role) (h : role = .opening) (responses : Responses g fields) :
    roleCache (Advice := Advice) role (responseValue role h responses) = { responses := some responses } := by
  cases h
  rfl

theorem openingData_cache (responses : Responses g fields) :
    cache (Advice := Advice) g.openingIndex (openingData responses) = { responses := some responses } := by
  unfold cache openingData
  rw [noneValue_cache,responseValue_cache]

private theorem startFromBody_none {Auth : Type} (body : Body g fields Advice Auth)
    (start : WireBlocks.Start) (h : start = .none) : startFromBody body start = noneValue start h := by
  cases h
  rfl

private theorem roleFromBody_opening {Auth : Type} (body : Body g fields Advice Auth)
    (role : Role) (h : role = .opening) (valid : WireBlocks.ValidRole g role) :
    roleFromBody body role valid = responseValue role h (body.binaryBackend.response,body.primeBackend.response) := by
  cases h
  rfl

theorem fromBody_opening {Auth : Type} (body : Body g fields Advice Auth) :
    fromBody g.openingIndex body = openingData (body.binaryBackend.response,body.primeBackend.response) :=
  Prod.ext (startFromBody_none body _ startAt_opening) (roleFromBody_opening body _ g.get_openingIndex _)

end Packets

/-! ## The proof body -/

section Body
variable {g : Geometry} {fields : Fields} {Advice : Type}
variable (repr : ProofBodyCodec.Representations fields Advice)

private abbrev Front (g : Geometry) (fields : Fields) (Advice : Type) :=
  Digest × (Fingerprints fields × (FrontendPayload (fields .prime) g.prime × (fields .prime × (Advice ×
    (FrontendPayload (fields .binary) g.binary × PackingPayload (fields .binary) g.packingDegree)))))

private abbrev Rows (g : Geometry) (fields : Fields) (side : Side) :=
  Fin (g.dataRows side+3) → Fin g.openings → fields side

private abbrev Back (g : Geometry) (fields : Fields) :=
  (Response g (fields .binary) × Response g (fields .prime)) ×
    ((Rows g fields .binary × Rows g fields .prime) × (Fin g.openings → MerkleNonce))

/-- The root, both fingerprint responses, the signature circuit's sumcheck,
mu, the masked quotients, the hash circuit's sumcheck and packing. -/
def front (repr : ProofBodyCodec.Representations fields Advice) (g : Geometry) :
    PrefixCodec (Front g fields Advice) :=
  let b := PrefixCodec.field repr.binary
  let p := PrefixCodec.field repr.prime
  ProofBodyCodec.digest.pair (((b.pair b).pair (p.pair p)).pair ((ProofBodyCodec.frontend p g.prime).pair
    (p.pair (repr.advice.pair ((ProofBodyCodec.frontend b g.binary).pair (ProofBodyCodec.packing b g.packingDegree))))))

def rows {F : Type} (field : PrefixCodec F) (g : Geometry) (count : ℕ) :
    PrefixCodec (Fin count → Fin g.openings → F) :=
  PrefixCodec.vector (PrefixCodec.vector field g.openings) count

/-- Both responses, both fields' opened rows, then the nonces. -/
def back (repr : ProofBodyCodec.Representations fields Advice) (g : Geometry) : PrefixCodec (Back g fields) :=
  let b := PrefixCodec.field repr.binary
  let p := PrefixCodec.field repr.prime
  ((ProofBodyCodec.response b g).pair (ProofBodyCodec.response p g)).pair
    (((rows b g (g.dataRows .binary+3)).pair (rows p g (g.dataRows .prime+3))).pair
      (PrefixCodec.vector ProofBodyCodec.nonce g.openings))

private def bodyData (g : Geometry) (fields : Fields) (Advice : Type) :
    ((Front g fields Advice × Back g fields) × Whole.Digests (OpeningBody.frontierCapacity g)) ≃
      FormatBody g fields Advice where
  toFun value :=
    let (commitment,fingerprints,prime,mu,advice,binary,packing) := value.1.1
    let ((binaryResponse,primeResponse),(binaryRows,primeRows),nonce) := value.1.2
    { commitment := commitment, fingerprints := fingerprints, mu := mu, advice := advice
      binary := binary, prime := prime, packing := packing
      binaryBackend := ⟨binaryResponse,binaryRows⟩, primeBackend := ⟨primeResponse,primeRows⟩
      authentication := { nonce := nonce, frontierLength := value.2.1, frontier := value.2.2 } }
  invFun value :=
    (((value.commitment,value.fingerprints,value.prime,value.mu,value.advice,value.binary,value.packing),
      (value.binaryBackend.response,value.primeBackend.response),
      (value.binaryBackend.rows,value.primeBackend.rows),value.authentication.nonce),
      ⟨value.authentication.frontierLength,value.authentication.frontier⟩)
  left_inv value := by
    rcases value with ⟨⟨⟨root,fingerprints,prime,mu,advice,binary,packing⟩,⟨hb,hp⟩,⟨rb,rp⟩,nonce⟩,⟨length,path⟩⟩
    rfl
  right_inv value := by
    rcases value with ⟨commitment,fingerprints,mu,advice,binary,prime,packing,⟨hb,rb⟩,⟨hp,rp⟩,⟨nonce,length,path⟩⟩
    rfl

/-- `MDA7` and the composed body; its frontier is the rest of the body. -/
def body (repr : ProofBodyCodec.Representations fields Advice) (g : Geometry) :
    WholeCodec (FormatBody g fields Advice) :=
  Whole.prefixed (Whole.equiv (Whole.andThen ((front repr g).pair (back repr g))
    (Whole.digests (OpeningBody.frontierCapacity g))) (bodyData g fields Advice)) ProofBodyCodec.mda7

theorem body_encode (value : FormatBody g fields Advice) :
    (body repr g).encode value =
      ProofBodyCodec.mda7 ++ ProofBodyCodec.digest.encode value.commitment ++
      repr.binary.encode value.fingerprints.1.1 ++ repr.binary.encode value.fingerprints.1.2 ++
      repr.prime.encode value.fingerprints.2.1 ++ repr.prime.encode value.fingerprints.2.2 ++
      (ProofBodyCodec.frontend (PrefixCodec.field repr.prime) g.prime).encode value.prime ++
      repr.prime.encode value.mu ++ repr.advice.encode value.advice ++
      (ProofBodyCodec.frontend (PrefixCodec.field repr.binary) g.binary).encode value.binary ++
      (ProofBodyCodec.packing (PrefixCodec.field repr.binary) g.packingDegree).encode value.packing ++
      (ProofBodyCodec.response (PrefixCodec.field repr.binary) g).encode value.binaryBackend.response ++
      (ProofBodyCodec.response (PrefixCodec.field repr.prime) g).encode value.primeBackend.response ++
      (rows (PrefixCodec.field repr.binary) g (g.dataRows .binary+3)).encode value.binaryBackend.rows ++
      (rows (PrefixCodec.field repr.prime) g (g.dataRows .prime+3)).encode value.primeBackend.rows ++
      (PrefixCodec.vector ProofBodyCodec.nonce g.openings).encode value.authentication.nonce ++
      Whole.digestsEncode (OpeningBody.frontierCapacity g)
        ⟨value.authentication.frontierLength,value.authentication.frontier⟩ := by
  simp only [body,Whole.prefixed_encode,Whole.equiv_encode,Whole.andThen_encode,front,back,
    PrefixCodec.pair,PrefixCodec.field,bodyData,Equiv.coe_fn_symm_mk,List.append_assoc]
  rfl

private theorem rows_length {F : Type} (field : PrefixCodec F) (width : ℕ)
    (hlen : ∀ value, (field.encode value).length = width) (count : ℕ) (value : Fin count → Fin g.openings → F) :
    ((rows field g count).encode value).length = count*g.openings*width := by
  rw [rows,PrefixCodec.vector_length _ (g.openings*width) (PrefixCodec.vector_length field width hlen g.openings)]
  ring

theorem body_length_le (value : FormatBody g fields Advice) :
    ((body repr g).encode value).length ≤ ProofBodyBounds.bodyBound repr g := by
  have hb : ∀ v, ((PrefixCodec.field repr.binary).encode v).length = 16 :=
    fun v => (repr.binary.length v).trans repr.binaryWidth
  have hp : ∀ v, ((PrefixCodec.field repr.prime).encode v).length = 32 :=
    fun v => (repr.prime.length v).trans repr.primeWidth
  rw [body_encode]
  simp only [List.length_append,ProofBodyBounds.digest_length,repr.binary.length,repr.prime.length,
    repr.binaryWidth,repr.primeWidth,repr.adviceLength,
    ProofBodyBounds.frontend_length _ 16 hb,ProofBodyBounds.frontend_length _ 32 hp,
    ProofBodyBounds.packing_length _ 16 hb,ProofBodyBounds.response_length _ 16 hb,
    ProofBodyBounds.response_length _ 32 hp,rows_length _ 16 hb,rows_length _ 32 hp,
    PrefixCodec.vector_length _ merkleNonceBytes ProofBodyBounds.nonce_length,Whole.digests_length,
    ProofBodyCodec.mda7,List.length_cons,List.length_nil]
  have hfrontier := value.authentication.frontierLength.isLt
  unfold ProofBodyBounds.bodyBound merkleNonceBytes
  split_ifs <;> nlinarith

private def proofData (g : Geometry) (fields : Fields) (Advice : Type) :
    FormatBody g fields Advice × Digest ≃ Proof g fields Advice (OpeningBody.Authentication g) where
  toFun value := ⟨value.1,value.2⟩
  invFun proof := (proof.body,proof.finalSeal)
  left_inv _ := rfl
  right_inv proof := by cases proof; rfl

/-- The complete proof: the body, then its 32-byte seal block. It depends
on no setup value. -/
def complete (repr : ProofBodyCodec.Representations fields Advice) (g : Geometry) :
    WholeCodec (Proof g fields Advice (OpeningBody.Authentication g)) :=
  withSeal (body repr g) (proofData g fields Advice)

end Body

/-! ## The format -/

section Format
variable {g : Geometry} {fields : Fields} {Advice : Type}
variable (repr : ProofBodyCodec.Representations fields Advice) (shape : WireBlocks.Shape g fields)
variable (setup : Setup) (publicCount : ℕ)

def capacity : ℕ := max (firstBound setup repr.prime publicCount shape.primePublic) (laterBound repr g)

def ordinary (i : Fin g.roles.length) :
    Packet (ProtocolWrites.Fresh g fields Advice) (capacity repr shape setup publicCount) where
  Data := Data (fields := fields) (Advice := Advice) i
  codec := codec repr i
  role := g.roles.get i
  cache := cache i
  bounded value := (codec_length_le repr i value).trans (le_max_right _ _)

private theorem roles_eq : Role.fingerprint ::
    (List.ofFn (ordinary repr shape setup publicCount)).tail.map Packet.role = g.roles := by
  have hordinary : (List.ofFn (ordinary repr shape setup publicCount)).map Packet.role = g.roles := by
    rw [List.map_ofFn]
    exact List.ofFn_get g.roles
  rw [List.map_tail,hordinary]
  rw [g.roles_eq]
  simp only [List.cons_append,List.tail_cons]

private theorem later_get (i : Fin g.roles.length) (h : i.val-1 <
      (List.ofFn (ordinary repr shape setup publicCount)).tail.length) (hi : i.val ≠ 0) :
    (List.ofFn (ordinary repr shape setup publicCount)).tail.get ⟨i.val-1,h⟩ =
      ordinary repr shape setup publicCount i := by
  simp only [List.get_eq_getElem,List.getElem_tail,List.getElem_ofFn]
  congr 1
  ext
  simp only
  omega

private theorem packet_block_cast {Fresh : Type} {capacity : ℕ} {first second : Packet Fresh capacity}
    (h : first = second) (value : first.Data) : second.block (h ▸ value) = first.block value := by
  cases h
  rfl

abbrev Request := PublicRequest publicCount shape.primePublic (fields .prime)
abbrev Base := BoundedBytes (capacity repr shape setup publicCount)

def context (request : Request (fields := fields) shape publicCount) (root : Digest) :
    Key publicCount shape.primePublic (fields .prime) :=
  ⟨request.session,request.publicBits,request.primeInputs,root⟩

def firstBase (key : Key publicCount shape.primePublic (fields .prime)) : Base repr shape setup publicCount :=
  ⟨(first setup repr.prime publicCount shape.primePublic).encode key,
    (first_length_le setup repr.prime publicCount shape.primePublic key).trans (le_max_left _ _)⟩

/-- The node at boundary `i`: the statement, or the prover messages of the
fresh writes there. -/
def node [Inhabited Advice] (request : Request (fields := fields) shape publicCount) (root : Digest) (i : Fin g.roles.length)
    (fresh : ProtocolWrites.Fresh g fields Advice) : Base repr shape setup publicCount :=
  if i.val = 0 then firstBase repr shape setup publicCount (context shape publicCount request root)
  else ((ordinary repr shape setup publicCount i).block (fromFresh shape i fresh)).1

def block [Inhabited Advice] (request : Request (fields := fields) shape publicCount) (body : FormatBody g fields Advice)
    (i : Fin g.roles.length) : Block (capacity repr shape setup publicCount) (ProtocolWrites.Fresh g fields Advice) :=
  (node repr shape setup publicCount request body.commitment i (ProtocolWrites.fresh body i),
    ProtocolWrites.fresh body i)

private theorem fresh_zero (body : FormatBody g fields Advice) (i : Fin g.roles.length) (hi : i.val = 0) :
    ProtocolWrites.fresh body i = {} := by
  have hp : i.val ≠ g.primeStart := by simp only [hi,Geometry.primeStart]; omega
  have hb : i.val ≠ g.binaryStart := by simp only [hi,Geometry.binaryStart]; omega
  have hr : g.roles.get i = .fingerprint := by simp [List.get_eq_getElem,g.roles_eq,hi]
  simp only [ProtocolWrites.fresh,hp,hb,if_false,hr,reduceCtorEq,ProtocolWrites.frontendMessages]

theorem block_pos [Inhabited Advice] (request : Request (fields := fields) shape publicCount) (body : FormatBody g fields Advice)
    (i : Fin g.roles.length) (hi : i.val ≠ 0) :
    block repr shape setup publicCount request body i =
      (ordinary repr shape setup publicCount i).block (fromBody i body) := by
  apply Prod.ext
  · simp only [block,node,if_neg hi,fromFresh_body]
  · exact (fromBody_cache i body).symm

def openingBase (responses : Responses g fields) : Base repr shape setup publicCount :=
  ((ordinary repr shape setup publicCount g.openingIndex).block (openingData responses)).1

def primeIndex (g : Geometry) : Fin g.roles.length :=
  ⟨0,by have := g.roles_length; omega⟩

def decodePrimePublic (base : Base repr shape setup publicCount) : Option (Fin shape.primePublic → fields .prime) :=
  (readWhole (first setup repr.prime publicCount shape.primePublic) base.bytes).map Key.primeInputs

/-- The deployed format. -/
@[reducible] def format [Fintype (fields .prime)] [Inhabited Advice] : Format g fields Advice publicCount where
  wire := wire
  Key := Key publicCount shape.primePublic (fields .prime)
  keyFintype := inferInstance
  capacity := capacity repr shape setup publicCount
  first := first setup repr.prime publicCount shape.primePublic
  first_bounded key := (first_length_le setup repr.prime publicCount shape.primePublic key).trans (le_max_left _ _)
  later := (List.ofFn (ordinary repr shape setup publicCount)).tail
  roles_eq := roles_eq repr shape setup publicCount
  body := body repr g
  scalars := repr
  binaryPublic := shape.binaryPublic
  primePublic := shape.primePublic
  context := context shape publicCount
  root := Key.root
  root_context _ _ := rfl
  hashPublic key := some key.publicBits
  hashPublic_context _ _ := rfl
  jointContext := setup.jointContext
  openingBase := openingBase repr shape setup publicCount
  primeIndex := primeIndex g
  primeIndex_le := Nat.zero_le _
  decodePrimePublic := decodePrimePublic repr shape setup publicCount
  Metadata _ := Unit
  block _ _ request body i _ := block repr shape setup publicCount request body i
  block_zero _ _ request body i _ hi := by
    simp only [block,node,if_pos hi,fresh_zero body i hi]
    rfl
  block_fresh _ _ _ _ _ _ := rfl
  block_opening _ _ request body _ := by
    have hi : g.openingIndex.val ≠ 0 := by
      have h := g.openingIndex_last
      have hlength := g.roles_length
      omega
    rw [block_pos repr shape setup publicCount request body _ hi,fromBody_opening]
    exact Prod.ext rfl (openingData_cache _)
  block_prime _ _ request body i _ hi := by
    subst hi
    simp only [block,node,primeIndex,↓reduceIte,decodePrimePublic,firstBase,readWhole_encode,Option.map_some]
    rfl
  block_independent _ _ _ _ _ _ _ _ := rfl
  block_later _ _ request body i _ hi :=
    ⟨(later_get repr shape setup publicCount i _ hi).symm ▸ fromBody i body,
      (block_pos repr shape setup publicCount request body i hi).trans (packet_block_cast _ _).symm⟩
  bodyBound := ProofBodyBounds.bodyBound repr g
  body_bound := body_length_le repr
  node _ _ request root i writes _ := node repr shape setup publicCount request root i (writes (Fin.last i.val))
  block_node _ _ _ _ _ _ := rfl

end Format
end LfzkV2.Current.TaggedFormat
