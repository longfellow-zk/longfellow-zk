import LfzkV2.Current.StrandRuntime
import LfzkV2.Current.PublicRequest
import LfzkV2.Current.BodyEncoding
import LfzkV2.Current.BackendBody

/-! A transcript format: everything the soundness, extraction and
zero-knowledge development needs to know about the bytes that a proof's
strand nodes absorb, and nothing else. A format fixes

- the node wire: round terminators and the seal frame (`NodeWire`);
- the first node's key (what the commitment cut binds) and its codec;
- the role packets of the later nodes, each a canonical codec with the
  typed messages it writes (`Packet.cache`);
- the proof body codec;
- how a request and body produce each node (`block`), with the readback of
  the request's public values (`hashPublic`, `decodePrimePublic`), and the
  opening packet (`openingBase`).

The laws are local: each is a property of one codec or one node. The
history codec (`Format.schema`, `Format.history_codec`) and the replay
identities below are derived from them once, for every format. The deployed
format is `LegacyFormat`. -/
noncomputable section
namespace LfzkV2.Current
open CanonicalPrefix QueryRuntime
open scoped Classical

/-- The proof body, with the current opening authentication. -/
abbrev FormatBody (g : Geometry) (fields : Fields) (Advice : Type) :=
  Body g fields Advice (OpeningBody.Authentication g)

structure Format (g : Geometry) (fields : Fields) (Advice : Type) (publicCount : ℕ) where
  /-- Node closing bytes: the round terminator and the seal frame. -/
  wire : NodeWire
  /-- What the first node binds: the statement prefix and commitment. -/
  Key : Type
  keyFintype : Fintype Key
  /-- An ambient bound on one node payload; it adds no bytes. -/
  capacity : ℕ
  first : PrefixCodec Key
  first_bounded : ∀ key, (first.encode key).length ≤ capacity
  /-- The role packets after the first node, in schedule order. -/
  later : List (Packet (ProtocolWrites.Fresh g fields Advice) capacity)
  roles_eq : Role.fingerprint :: later.map Packet.role = g.roles
  body : PrefixCodec (FormatBody g fields Advice)
  /-- The public input counts of the hash and signature circuits. -/
  binaryPublic : ℕ
  primePublic : ℕ
  /-- The first node's key for a request and commitment root. -/
  context : PublicRequest publicCount primePublic (fields .prime) → Digest → Key
  root : Key → Digest
  root_context : ∀ request digest, root (context request digest) = digest
  /-- The hash circuit's public bits, read back from the first node. -/
  hashPublic : Key → Option (Fin publicCount → Bool)
  hashPublic_context : ∀ request digest, hashPublic (context request digest) = some request.publicBits
  /-- The joint Polygero context of the opening authentication. -/
  jointContext : Digest
  /-- The opening node's bytes for the H/Z responses. -/
  openingBase : Response g (fields .binary) × Response g (fields .prime) → BoundedBytes capacity
  /-- The signature circuit's public inputs, read back from the node at
  `g.primeStart`. -/
  decodePrimePublic : BoundedBytes capacity → Option (Fin primePublic → fields .prime)
  /-- Setup values absorbed at a boundary (none in a format whose statement
  absorbs all setup once). -/
  Metadata : Fin g.roles.length → Type
  /-- The node at boundary `i` for a request and body, given the request's
  binary public inputs, the metadata and the earlier challenge answers. -/
  block : {C : Type} → ((Fin publicCount → Bool) → Fin binaryPublic → fields .binary) →
    ((request : PublicRequest publicCount primePublic (fields .prime)) → (i : Fin g.roles.length) →
      (Fin (i.val+1) → ProtocolWrites.Fresh g fields Advice) → (Fin i.val → C) → Metadata i) →
    PublicRequest publicCount primePublic (fields .prime) → FormatBody g fields Advice →
    (i : Fin g.roles.length) → (Fin i.val → C) → QueryRuntime.Block capacity (ProtocolWrites.Fresh g fields Advice)
  /-- The first node is the key's codec, with no typed messages. -/
  block_zero : ∀ {C} binaryRequest metadata request body (i : Fin g.roles.length) (past : Fin i.val → C),
    i.val = 0 → block binaryRequest metadata request body i past =
      (⟨first.encode (context request body.commitment),first_bounded _⟩,{})
  /-- Each node's typed messages are the body's fresh writes at it. -/
  block_fresh : ∀ {C} binaryRequest metadata request body (i : Fin g.roles.length) (past : Fin i.val → C),
    (block binaryRequest metadata request body i past).2 = ProtocolWrites.fresh body i
  block_opening : ∀ {C} binaryRequest metadata request body (past : Fin g.openingIndex.val → C),
    block binaryRequest metadata request body g.openingIndex past =
      (openingBase (body.binaryBackend.response,body.primeBackend.response),
        { responses := some (body.binaryBackend.response,body.primeBackend.response) })
  block_prime : ∀ {C} binaryRequest metadata request body (i : Fin g.roles.length) (past : Fin i.val → C),
    i.val = g.primeStart → decodePrimePublic (block binaryRequest metadata request body i past).1 =
      some request.primeInputs
  /-- Nodes depend on answers only through challenge-dependent metadata. -/
  block_independent : ∀ {C} binaryRequest
    (metadata : (request : PublicRequest publicCount primePublic (fields .prime)) → (i : Fin g.roles.length) →
      (Fin (i.val+1) → ProtocolWrites.Fresh g fields Advice) → (Fin i.val → C) → Metadata i),
    (∀ request index writes first second, metadata request index writes first = metadata request index writes second) →
    ∀ request body (i : Fin g.roles.length) (first second : Fin i.val → C),
      block binaryRequest metadata request body i first = block binaryRequest metadata request body i second

namespace Format
variable {g : Geometry} {fields : Fields} {Advice C : Type} {publicCount : ℕ}
variable (fmt : Format g fields Advice publicCount)

instance : Fintype fmt.Key := fmt.keyFintype

abbrev Base := BoundedBytes fmt.capacity
abbrev Node := QueryRuntime.Block fmt.capacity (ProtocolWrites.Fresh g fields Advice)
abbrev Request := PublicRequest publicCount fmt.primePublic (fields .prime)
local notation "Output" => Replay.Output g fields Advice (OpeningBody.Authentication g)
abbrev Point := Replay.Point g fields Advice (OpeningBody.Authentication g) fmt.Key fmt.Node
abbrev BinaryRequest := (Fin publicCount → Bool) → Fin fmt.binaryPublic → fields .binary

/-- Setup metadata for every request and boundary. It may read the fresh
writes bound so far and the strict earlier answers. -/
abbrev RequestMetadata (C : Type) := (request : fmt.Request) → (i : Fin g.roles.length) →
  (Fin (i.val+1) → ProtocolWrites.Fresh g fields Advice) → (Fin i.val → C) → fmt.Metadata i

def ChallengeIndependent (metadata : fmt.RequestMetadata C) : Prop :=
  ∀ request index writes first second, metadata request index writes first = metadata request index writes second

/-- The fresh writes up to and including boundary `i`. -/
def writes (body : FormatBody g fields Advice) (i : Fin g.roles.length) :
    Fin (i.val+1) → ProtocolWrites.Fresh g fields Advice :=
  fun j => ProtocolWrites.fresh body ⟨j.val,by have := i.isLt; have := j.isLt; omega⟩

/-! ## The history codec -/

/-- The first packet reads the key; its node writes no typed message. -/
def firstPacket : Packet (ProtocolWrites.Fresh g fields Advice) fmt.capacity where
  Data := fmt.Key
  codec := fmt.first
  role := .fingerprint
  cache _ := {}
  bounded := fmt.first_bounded

def packets : List (Packet (ProtocolWrites.Fresh g fields Advice) fmt.capacity) :=
  fmt.firstPacket :: fmt.later

theorem packets_roles : fmt.packets.map Packet.role = g.roles := fmt.roles_eq

def blocks : List QueryCodec.Block := fmt.packets.map Packet.queryBlock

theorem blocks_length : fmt.blocks.length = g.roles.length := by
  simpa only [blocks,List.length_map] using congrArg List.length fmt.packets_roles

/-- Parsed packet values: the canonical histories of this format. -/
abbrev Value := QueryCodec.Value fmt.body fmt.blocks

def key (value : fmt.Value) : fmt.Key := value.1

/-- Rebuild the verifier's logical input from parsed packets. -/
def toPoint (value : fmt.Value) : fmt.Point :=
  reindex fmt.packets_roles (embed fmt.body (fmt.key value) fmt.packets value)

theorem toPoint_context (value : fmt.Value) : (fmt.toPoint value).context = fmt.key value := by
  rw [toPoint,reindex_context,embed_context]

/-- The strand history codec of the format's packets. -/
def schema : TranscriptV2.Strand.History.Codec fmt.Value :=
  StrandQueryCodec.schema fmt.wire fmt.body fmt.blocks

/-- The verifier's serializer is the history codec's encoder. -/
theorem toPoint_history (value : fmt.Value) :
    StrandRuntime.history fmt.wire fmt.body (fmt.toPoint value) = fmt.schema.encode value := by
  unfold toPoint
  rw [StrandRuntime.history_reindex,StrandRuntime.history_embed]
  rfl

/-- The history codec: the strand history of every canonical point parses
back to its packet values. This is derived from the per-node codec laws. -/
theorem history_codec (value : fmt.Value) :
    fmt.schema.decode (StrandRuntime.history fmt.wire fmt.body (fmt.toPoint value)) = some value := by
  rw [toPoint_history]
  exact fmt.schema.inverse value

theorem toPoint_injective : Function.Injective fmt.toPoint := by
  intro first second same
  have decoded := congrArg (fun point => fmt.schema.decode (StrandRuntime.history fmt.wire fmt.body point)) same
  simp only [history_codec] at decoded
  exact Option.some.inj decoded

/-- A point is canonical when its packets parse. -/
def Canonical (point : fmt.Point) : Prop := ∃ value, fmt.toPoint value = point

theorem parent_key (value earlier : fmt.Value)
    (previous : StrandQueryCodec.parent fmt.body fmt.blocks value = some earlier) :
    fmt.key value = fmt.key earlier :=
  StrandQueryCodec.parent_first fmt.body _ _ value earlier previous

/-- The verifier's predecessor is the history's parent. -/
theorem toPoint_parent (value earlier : fmt.Value)
    (previous : StrandQueryCodec.parent fmt.body fmt.blocks value = some earlier) :
    (fmt.toPoint value).parent = some (fmt.toPoint earlier) := by
  dsimp only [Value,blocks] at value earlier previous
  unfold toPoint
  rw [reindex_parent,StrandRuntime.embed_parent,previous,Option.map_some,Option.map_some,
    parent_key fmt value earlier previous]

theorem history_parent (value earlier : fmt.Value)
    (previous : StrandQueryCodec.parent fmt.body fmt.blocks value = some earlier) :
    ∃ digest message, fmt.schema.encode value = .child (fmt.schema.encode earlier) digest message :=
  StrandQueryCodec.history_parent fmt.wire fmt.body fmt.blocks value earlier previous

/-- Parsed values and canonical points are the same objects. -/
def valuesEquiv : fmt.Value ≃ {point : fmt.Point // fmt.Canonical point} :=
  Equiv.ofInjective fmt.toPoint fmt.toPoint_injective

theorem valuesEquiv_apply (value : fmt.Value) : (fmt.valuesEquiv value).val = fmt.toPoint value := rfl

theorem valuesEquiv_symm (point : {point : fmt.Point // fmt.Canonical point}) :
    fmt.toPoint (fmt.valuesEquiv.symm point) = point.val := by
  have same := congrArg Subtype.val (fmt.valuesEquiv.apply_symm_apply point)
  rw [valuesEquiv_apply] at same
  exact same

variable {P : Type}

/-- Each canonical point's one ordinary name in the renamed search. -/
def pointCodec (locate : fmt.Value → P) :
    ByteOracleTransport.Codec fmt.Point (StrandSearch.Name P fmt.Value) fmt.Canonical where
  encode point :=
    let value := fmt.valuesEquiv.symm point
    .inl (locate value,some value)
  decode
    | .inl (point,some value) => if point = locate value then some (fmt.valuesEquiv value) else none
    | _ => none
  decode_encode point := by simp only [Equiv.apply_symm_apply,if_true]
  encode_decode raw point found := by
    cases raw with
    | inr _ => cases found
    | inl raw =>
        rcases raw with ⟨raw,value⟩
        cases value with
        | none => cases found
        | some value =>
            change (if raw = locate value then some (fmt.valuesEquiv value) else none) = some point at found
            by_cases equal : raw = locate value
            · rw [if_pos equal] at found
              cases Option.some.inj found
              simp only [Equiv.symm_apply_apply,equal]
            · rw [if_neg equal] at found
              contradiction

/-- A Merkle preimage (first byte `p`) never names a canonical node. -/
theorem pointCodec_merkle_auxiliary (locate : fmt.Value → P) (bytes : P → Bytes)
    (located : ∀ value, bytes (locate value) = (fmt.schema.encode value).input.encode)
    (raw : P) (value : Option fmt.Value) (merkle : (bytes raw).head? = some 112) :
    (fmt.pointCodec locate).decode (.inl (raw,value)) = none := by
  cases value with
  | none => rfl
  | some value =>
      have different : raw ≠ locate value := by
        intro same
        rw [same,located value] at merkle
        have first : ((fmt.schema.encode value).input.encode).head? = some 1 := by
          cases fmt.schema.encode value <;> rfl
        rw [first] at merkle
        exact (by decide : (1 : TranscriptV2.Framing.Byte) ≠ 112) (Option.some.inj merkle)
      simp only [pointCodec,if_neg different]

theorem pointCodec_ordinary (locate : fmt.Value → P) (bytes : P → Bytes) (injective : Function.Injective bytes)
    (located : ∀ value, bytes (locate value) = (fmt.schema.encode value).input.encode)
    (past : List TranscriptV2.Strand.Entry) (raw : P) (value : fmt.Value)
    (parsed : StrandSearch.decode fmt.schema bytes past raw = some value) :
    ((fmt.pointCodec locate).decode (.inl (raw,some value))).map Subtype.val = some (fmt.toPoint value) := by
  have same : raw = locate value := injective
    ((StrandSearch.decode_erases fmt.schema bytes past raw value parsed).symm.trans (located value).symm)
  simp only [pointCodec,if_pos same,Option.map_some,valuesEquiv]
  rfl

/-! ## Request replay -/

variable (binaryRequest : fmt.BinaryRequest) (metadata : fmt.RequestMetadata C) (request : fmt.Request)

/-- The request's nodes, computed from the body alone. -/
def bodyEncoding : ProofBodyReplay.BodyEncoding (g := g) (fields := fields) (Advice := Advice)
    (Authentication := OpeningBody.Authentication g) (Context := fmt.Key) (Block := fmt.Node) (C := C) where
  context body := fmt.context request body.commitment
  block := fmt.block binaryRequest metadata request

def encoding : Replay.Encoding g fields Advice (OpeningBody.Authentication g) fmt.Key fmt.Node C :=
  (fmt.bodyEncoding binaryRequest metadata request).encoding

@[simp] theorem encoding_context (proof : Output) :
    (fmt.encoding binaryRequest metadata request).context proof = fmt.context request proof.body.commitment := rfl

theorem encoding_block (proof : Output) (i : Fin g.roles.length) (past : Fin i.val → C) :
    (fmt.encoding binaryRequest metadata request).block proof i past =
      fmt.block binaryRequest metadata request proof.body i past := rfl

theorem point_same_body (initial : Digest) (first second : Output)
    (same : first.body = second.body) (H : fmt.Point → Digest × C) (index : ℕ) :
    ((fmt.encoding binaryRequest metadata request).chain initial).point first H index =
      ((fmt.encoding binaryRequest metadata request).chain initial).point second H index :=
  congrArg _ (ProofBodyReplay.replay_same_body _ initial first second same H index)

theorem block_challengeIndependent (independent : fmt.ChallengeIndependent metadata)
    (proof : Output) (i : Fin g.roles.length) (first second : Fin i.val → C) :
    (fmt.encoding binaryRequest metadata request).block proof i first =
      (fmt.encoding binaryRequest metadata request).block proof i second :=
  fmt.block_independent binaryRequest metadata independent request proof.body i first second

/-- Filling the protocol writes again changes no node. -/
theorem withProtocolWrites_eq :
    (fmt.encoding binaryRequest metadata request).withProtocolWrites = fmt.encoding binaryRequest metadata request := by
  have hb : (fmt.encoding binaryRequest metadata request).withProtocolWrites.block =
      (fmt.encoding binaryRequest metadata request).block := by
    funext proof i past
    exact Prod.ext rfl (fmt.block_fresh binaryRequest metadata request proof.body i past).symm
  cases he : fmt.encoding binaryRequest metadata request with
  | mk context block =>
      change Replay.Encoding.mk context _ = Replay.Encoding.mk context block
      exact congrArg (Replay.Encoding.mk context) (by simpa only [he,Replay.Encoding.withProtocolWrites] using hb)

/-- The opening node with its typed responses. -/
def openingWire (responses : Response g (fields .binary) × Response g (fields .prime)) : fmt.Node :=
  (fmt.openingBase responses,{ responses := some responses })

section BackendOpening
variable {B : Type} [Field B] [Fintype B] [DecidableEq B]
variable {p k s n t : ℕ} [Fact p.Prime]
variable (P : Application.FieldBackend B k s n t) (R : Application.FieldBackend (ZMod p) k s n t)
variable (binary : fields .binary ≃ B) (prime : fields .prime ≃ ZMod p)
variable (hrow : g.rowDimension = k) (hmask : g.maskingDegree = s) (hproduct : 2*k ≤ n)

/-- The runtime's mandatory opening override is an identity on the
format's encoding. -/
theorem withBackendOpening_eq :
    ((fmt.encoding binaryRequest metadata request).withProtocolWrites).withOpening
      (BackendVerifier.responses P R binary prime hrow hmask hproduct)
      (BackendVerifier.encodeResponses P R binary prime hrow hmask hproduct fmt.openingWire) =
      fmt.encoding binaryRequest metadata request := by
  rw [withProtocolWrites_eq]
  have hb : ((fmt.encoding binaryRequest metadata request).withOpening
      (BackendVerifier.responses P R binary prime hrow hmask hproduct)
      (BackendVerifier.encodeResponses P R binary prime hrow hmask hproduct fmt.openingWire)).block =
      (fmt.encoding binaryRequest metadata request).block := by
    funext proof i past
    by_cases hi : i = g.openingIndex
    · subst i
      rw [Replay.Encoding.withOpening_block,BackendVerifier.encodeResponses_body]
      exact (fmt.block_opening binaryRequest metadata request proof.body past).symm
    · exact Replay.Encoding.withOpening_block_earlier _ _ _ proof i past hi
  cases he : fmt.encoding binaryRequest metadata request with
  | mk context block =>
      change Replay.Encoding.mk context _ = Replay.Encoding.mk context block
      exact congrArg (Replay.Encoding.mk context) (by simpa only [he,Replay.Encoding.withOpening] using hb)

end BackendOpening

/-- The first node's key reads back the request's public bits at every
replayed point. -/
theorem hashPublic_replay (initial : Digest) (proof : Output) (H : fmt.Point → Digest × C) (index : ℕ) :
    fmt.hashPublic (((fmt.encoding binaryRequest metadata request).chain initial).point proof H index).context =
      some request.publicBits := by
  rw [Replay.Encoding.point_context]
  exact fmt.hashPublic_context request proof.body.commitment

def primeBoundary (g : Geometry) : Fin g.roles.length :=
  ⟨g.primeStart,by have := g.roles_length; dsimp only [Geometry.primeStart]; omega⟩

/-- Every replay after the prime-start boundary reads back the request's
signature-circuit public inputs. -/
theorem primePublic_replay (initial : Digest) (proof : Output) (H : fmt.Point → Digest × C)
    (index : ℕ) (hi : index ≤ g.roles.length) (hstart : g.primeStart ≤ index) :
    (((fmt.encoding binaryRequest metadata request).chain initial).point proof H index).readAt
      g.primeStart (fun block => fmt.decodePrimePublic block.1) = some request.primeInputs := by
  change (((fmt.encoding binaryRequest metadata request).chain initial).point proof H index).readAt
    (primeBoundary g).val (fun block => fmt.decodePrimePublic block.1) = _
  rw [Replay.Encoding.readAt_replay _ _ _ _ _ hi (primeBoundary g) hstart]
  exact fmt.block_prime binaryRequest metadata request proof.body _ _ rfl

end Format
end LfzkV2.Current
