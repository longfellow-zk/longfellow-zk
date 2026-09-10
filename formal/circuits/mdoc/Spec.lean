/-
# What the mDOC hash circuit is supposed to prove

`SHA/Spec.lean` and `ECDSA/EcdsaSpec.lean` say what the two primitives compute. This says what
the mDOC **hash** circuit as a whole establishes: `Nat` and `List Nat` only, no wires, no DAG, no
reference to the circuit. A specification that mentions the circuit cannot catch a circuit that is
wrong.

## The statement, in English

Fix a verification time `now`, a document type `docType`, and a list of attribute
identifier/value pairs `(attrId i, attrValue i)`. Fix a GF(2^128) MAC key `α` and tags
`(macE, macDpkX, macDpkY)`. Then `ValidPresentation` says: **there exist**

* a padded byte buffer `preimage` of at most `40 * 64 = 2560` bytes, holding a message of length
  `msgLen ≤ 2551`, whose SHA-256 digest is a 32-byte string `e`;
* a device public key `(dpkX, dpkY)`, each 32 bytes;
* MAC pads `macPad` under which `e`, `dpkX` and `dpkY` carry the given tags;
* byte offsets into `preimage` at which the CBOR key literals `"docType"`, `"validFrom"`,
  `"validUntil"`, `"deviceKeyInfo"` and `"valueDigests"` occur;
* per attribute, a 128-byte `IssuerSignedItem` preimage and a locator for its four CBOR map
  entries;

such that

* the `validFrom` timestamp is `≤ now` and `now ≤` the `validUntil` timestamp (both 20-byte
  ISO-8601 strings, compared big-endian, which is chronological at fixed width);
* the bytes after the `deviceKeyInfo` literal are the COSE-key header, then `dpkX`, then
  `0x22 0x58 0x20`, then `dpkY`;
* the bytes after the `docType` literal are a CBOR text string beginning with `docType`;
* each attribute's `IssuerSignedItem` is a 4-entry CBOR map whose entries, in some order, are
  keyed `"digestID"`, `"random"`, `"elementIdentifier"` and `"elementValue"`, with the last two
  carrying exactly `attrId i` and `attrValue i`; and its SHA-256 digest appears in `preimage`
  behind a `0x58 0x20` header.

`pk_i` — the issuer public key — is **not** here. It is a public input of the *signature*
circuit, which proves ECDSA over the same `e`. The two halves meet only at the MAC tags, which
are public inputs of both; see `## The seam` at the end.

## How the circuit actually works, and therefore what this can promise

It does **not** parse CBOR top-down. It takes prover-supplied byte offsets into the preimage and
checks that specific byte patterns occur there. So the honest statement is existential — *there
exist* offsets at which the preimage has this shape — and it is recorded that way. Whether those
patterns can occur anywhere other than the intended fields is a property of the CBOR encoding of
a well-formed MSO that this specification does **not** establish; see `## Residual trust`.

## Provenance

Every clause below is one function of `mdoc_zk/circuits/src/hash/circuit.rs` or
`mdoc_zk/circuits/src/mso_attribute/circuit.rs`, and carries its name. The byte literals are
`mdoc_zk/proto/src/hash/constants.rs` and `mdoc_zk/proto/src/mso_attribute/constants.rs`
verbatim; the SHA-256 padding clause is `circuits/sha256msg/src/circuit.rs`; the CBOR header
decoder is `mdoc_zk/circuits/src/cbor_decoder/concrete.rs`; the MAC equation is
`circuits/mac_gf128/src/circuit.rs`.

## Bit widths

The circuit's offsets and lengths are 16-bit (MSO) or 10-bit (attribute) bitvectors, and every
addition on them goes through `assert_checked_add`, which rules out wraparound. So plain `Nat`
arithmetic is the faithful reading, and no clause below carries a modulus.
-/

import SHA.Spec
import GF128.Poly

set_option maxRecDepth 100000

namespace MDoc

/-! ## Byte-window vocabulary

`routing::shift_bitvec` reads `a[off + i]` and substitutes zero past the end of the buffer, so
`getD _ 0` is exactly the circuit's out-of-range behaviour, not an approximation. -/

/-- Byte `i` of `bs`, zero past the end. -/
def byteAt (bs : List Nat) (i : Nat) : Nat := bs.getD i 0

/-- The `n` bytes of `bs` starting at `off`, zero-filled past the end. This is what
    `shift_bitvec off n` produces. -/
def window (bs : List Nat) (off n : Nat) : List Nat :=
  (List.range n).map (fun i => byteAt bs (off + i))

/-- `pat` occurs in `bs` starting at `off`. -/
def BytesAt (bs : List Nat) (off : Nat) (pat : List Nat) : Prop :=
  ∀ i, i < pat.length → byteAt bs (off + i) = pat.getD i 0

/-- Every clause below is a conjunction of bounded quantifiers over `Nat` equalities, so the whole
    specification is decidable — which is what makes it testable against a real credential rather
    than only readable. `Nat.decidableBallLT` supplies the quantifiers; this instance is the one
    step it cannot take on its own, because `BytesAt` is a `def` and instance search will not
    unfold it. -/
instance instDecidableBytesAt (bs : List Nat) (off : Nat) (pat : List Nat) :
    Decidable (BytesAt bs off pat) :=
  inferInstanceAs (Decidable (∀ i, i < pat.length → _))

/-- Big-endian value of a byte string. -/
def beVal (bs : List Nat) : Nat := bs.foldl (fun acc b => acc * 256 + b) 0

/-- `memcmp::leq`. `arrange` reverses the bytes so index 0 is most significant, then compares as
    integers; on equal-length ISO-8601 timestamps that is chronological order. The circuit's
    `leq` is `¬ (b < a)`, i.e. non-strict — the validity window is closed at both ends. -/
def LeBytes (a b : List Nat) : Prop := beVal a ≤ beVal b

instance instDecidableLeBytes (a b : List Nat) : Decidable (LeBytes a b) :=
  inferInstanceAs (Decidable (_ ≤ _))

/-! ## The CBOR literals

Verbatim from `proto/src/hash/constants.rs` and `proto/src/mso_attribute/constants.rs`. Each is a
CBOR text-string header followed by a key name, so finding it pins the field that follows. -/

/-- `0x58 0x20` — CBOR byte string of length 32, the header on every digest. -/
def tag32 : List Nat := [0x58, 0x20]

/-- `"docType"` as a CBOR text string. -/
def docTypeKey : List Nat := [0x67, 0x64, 0x6F, 0x63, 0x54, 0x79, 0x70, 0x65]

/-- `"validFrom"`, then tag 0 (`0xC0`) and a 20-char text string (`0x74`). -/
def validFromKey : List Nat :=
  [0x69, 0x76, 0x61, 0x6C, 0x69, 0x64, 0x46, 0x72, 0x6F, 0x6D, 0xC0, 0x74]

/-- `"validUntil"`, likewise. -/
def validUntilKey : List Nat :=
  [0x6A, 0x76, 0x61, 0x6C, 0x69, 0x64, 0x55, 0x6E, 0x74, 0x69, 0x6C, 0xC0, 0x74]

/-- `"deviceKeyInfo"`, the nested `"deviceKey"` map, and the COSE_Key header
    (`A4 01 02 20 01` — `kty: EC2`, `crv: P-256`) down to the `0x21 0x58 0x20` that introduces
    the 32-byte x-coordinate. -/
def deviceKeyInfoKey : List Nat :=
  [0x6D, 0x64, 0x65, 0x76, 0x69, 0x63, 0x65, 0x4B, 0x65, 0x79, 0x49, 0x6E, 0x66, 0x6F,
   0xA1, 0x69, 0x64, 0x65, 0x76, 0x69, 0x63, 0x65, 0x4B, 0x65, 0x79,
   0xA4, 0x01, 0x02, 0x20, 0x01, 0x21, 0x58, 0x20]

/-- `0x22 0x58 0x20` — COSE_Key label `-3` (y) and a 32-byte string, between the two coordinates. -/
def deviceKeyYTag : List Nat := [0x22, 0x58, 0x20]

/-- `"valueDigests"`. -/
def valueDigestsKey : List Nat :=
  [0x6C, 0x76, 0x61, 0x6C, 0x75, 0x65, 0x44, 0x69, 0x67, 0x65, 0x73, 0x74, 0x73]

/-- `"digestID"`, key of logical slot 0 of an `IssuerSignedItem`. -/
def digestIdKey : List Nat := [0x68, 0x64, 0x69, 0x67, 0x65, 0x73, 0x74, 0x49, 0x44]

/-- `"random"`, key of logical slot 1. -/
def randomKey : List Nat := [0x66, 0x72, 0x61, 0x6E, 0x64, 0x6F, 0x6D]

/-- `"elementIdentifier"`, key of logical slot 2. -/
def elementIdentifierKey : List Nat :=
  [0x71, 0x65, 0x6C, 0x65, 0x6D, 0x65, 0x6E, 0x74, 0x49, 0x64, 0x65, 0x6E, 0x74, 0x69,
   0x66, 0x69, 0x65, 0x72]

/-- `"elementValue"`, key of logical slot 3. -/
def elementValueKey : List Nat :=
  [0x6C, 0x65, 0x6C, 0x65, 0x6D, 0x65, 0x6E, 0x74, 0x56, 0x61, 0x6C, 0x75, 0x65]

/-- ISO-8601 timestamps are 20 characters. -/
def timestampLen : Nat := 20

/-- `K_MAX_SHA_BLOCKS`. The MSO preimage buffer is `maxShaBlocks * 64 = 2560` bytes. -/
def maxShaBlocks : Nat := 40

/-- `K_MAX_ATTR_SHA_BLOCKS`. An `IssuerSignedItem` gets a fixed two-block, 128-byte buffer. -/
def attrShaBlocks : Nat := 2

/-- `K_MAX_ATTR_CBOR_LEN`. The width of the window a slot check sees. -/
def maxAttrCborLen : Nat := attrShaBlocks * 64 - 9

/-! ## SHA-256 over a byte buffer

`SHA/Spec.lean` gives the compression function on 16-word blocks. The circuit asserts one
compression step per block of the *whole* buffer, but reads the digest off block `nblocks - 1`
(`assert_final_hash` muxes on a one-hot selector for `nblocks`), so only the first `nblocks`
blocks matter to the statement. -/

/-- Big-endian 4-byte groups. -/
def wordsOfBytes : List Nat → List Nat
  | a :: b :: c :: d :: rest =>
      (a * 2 ^ 24 + b * 2 ^ 16 + c * 2 ^ 8 + d) :: wordsOfBytes rest
  | _ => []

/-- The inverse: each 32-bit word as four big-endian bytes. -/
def bytesOfWords : List Nat → List Nat
  | [] => []
  | w :: ws => w / 2 ^ 24 % 256 :: w / 2 ^ 16 % 256 :: w / 2 ^ 8 % 256 :: w % 256 :: bytesOfWords ws

/-- Split a word list into 16-word blocks, at most `n` of them. Fuel-driven rather than
    well-founded: this codebase avoids WF-compiled recursion because the kernel gets stuck on it,
    and the block count is bounded anyway. -/
def blocksOf : Nat → List Nat → List (List Nat)
  | 0, _ => []
  | _, [] => []
  | n + 1, ws => ws.take 16 :: blocksOf n (ws.drop 16)

/-- Chain the compression function across blocks. -/
def hashBlocks : List Nat → List (List Nat) → List Nat
  | h, [] => h
  | h, m :: ms => hashBlocks (SHA256.blockFrom h m) ms

/-- SHA-256 of the first `nblocks` blocks of `buf`, as 32 big-endian bytes. -/
def sha256 (buf : List Nat) (nblocks : Nat) : List Nat :=
  bytesOfWords (hashBlocks SHA256.H0 (blocksOf nblocks (wordsOfBytes buf)))

/-- `sha256msg::assert_message_hash`'s padding half, clause by clause:

* `assert_nblocks` — `0 < nblocks ≤ maxBlocks`, and `nblocks` is the *unique* block count
  consistent with `msgLen`: the two inequalities pin `nblocks = ⌈(msgLen + 9) / 64⌉`.
* `assert_sha_padding` — `0x80` at `msgLen`; zeros between the message and the length field;
  zeros in every block past `nblocks`.
* `assert_length` — the last eight bytes of block `nblocks - 1` are `msgLen * 8` big-endian.

Note what is *not* here: the bytes below `msgLen` are unconstrained by this clause. They are the
message, and it is the other clauses that say what must be in it. -/
def ShaPadded (maxBlocks : Nat) (buf : List Nat) (msgLen nblocks : Nat) : Prop :=
  0 < nblocks ∧ nblocks ≤ maxBlocks ∧
  msgLen + 9 ≤ 64 * nblocks ∧ 64 * nblocks ≤ msgLen + 72 ∧
  byteAt buf msgLen = 0x80 ∧
  (∀ i, i < 64 * nblocks → msgLen < i → i + 8 < 64 * nblocks → byteAt buf i = 0) ∧
  (∀ i, i < 64 * maxBlocks → 64 * nblocks ≤ i → byteAt buf i = 0) ∧
  (∀ j, j < 8 → byteAt buf (64 * nblocks - 8 + j) = msgLen * 8 / 2 ^ (8 * (7 - j)) % 256)

/-! ## The one-byte CBOR header decoder

`cbor_decoder::decode_one_v8`, transcribed. The attribute circuit uses it to learn how long the
value in a map slot is, which is what lets it check that the four slots tile the buffer. -/

/-- Low five bits of a CBOR initial byte: the *count*. -/
def cborCount (v : Nat) : Nat := v % 32

/-- Top three bits: the *major type*. -/
def cborType (v : Nat) : Nat := v / 32 % 8

/-- Major types 0, 1 — unsigned and negative integers. -/
def cborAtomp (v : Nat) : Bool := cborType v / 2 == 0

/-- Major types 2, 3 — byte and text strings, whose content may be inline. -/
def cborStr (v : Nat) : Bool := cborType v / 2 == 1

/-- Major type 6 — tag. -/
def cborTagp (v : Nat) : Bool := cborType v == 6

/-- Major type 7 — floats and simple values. -/
def cborSpecialp (v : Nat) : Bool := cborType v == 7

/-- Major type 7 with count 20-23: `false`, `true`, `null`, `undefined`. -/
def cborSimpleSpecialp (v : Nat) : Bool := cborSpecialp v && cborCount v / 4 == 5

/-- `(v & 0xDF) == 0x58`: a string whose length is the single following byte. -/
def cborLengthPlusNext (v : Nat) : Bool := v == 0x58 || v == 0x78

/-- A header the decoder rejects: a major-type-7 value other than the four simple ones; a count
    of 25-27 on a type that does not admit a multi-byte length (only integers and tags do); or a
    count of 28-31, which CBOR reserves. -/
def cborInvalid (v : Nat) : Bool :=
  let c := cborCount v
  let goodCount := c ≤ 24 || ((cborAtomp v || cborTagp v) && c ≤ 27)
  (cborSpecialp v && !cborSimpleSpecialp v) || !goodCount

/-- Bytes consumed by the header itself, given the count. -/
def cborBaseLen (c : Nat) : Nat :=
  if c < 24 then 1
  else if c % 4 == 0 then 2
  else if c % 4 == 1 then 3
  else if c % 4 == 2 then 5
  else 9

/-- Total encoded length the decoder reports for the byte alone: the header, plus inline string
    content when the count is the length. -/
def cborLen (v : Nat) : Nat :=
  cborBaseLen (cborCount v) + (if cborStr v && cborCount v < 24 then cborCount v else 0)

/-- Total encoded length of the CBOR item whose header byte is at `idx`, reading one more byte
    when the header says the length is there. This is `assert_cbor_length`'s `k_len + v_len`. -/
def cborItemLen (bs : List Nat) (idx : Nat) : Nat :=
  cborLen (byteAt bs idx) +
    (if cborLengthPlusNext (byteAt bs idx) then byteAt bs (idx + 1) else 0)

/-! ## Statement and witness

The split is `compile/src/allocate_hash.rs`: everything allocated before `pub_inputs_count` is
public, everything after is witness. Note that `e` and the device key are **witness** — the
verifier never sees them, only their MAC tags. -/

/-- The public inputs of the hash circuit. -/
structure Statement where
  /-- `now`, a 20-byte ISO-8601 timestamp. -/
  now : List Nat
  /-- Per disclosed attribute, the CBOR text-string encoding of its identifier — header byte
      included, e.g. `0x6B "family_name"`. At most 32 bytes. -/
  attrId : List (List Nat)
  /-- Per disclosed attribute, the CBOR encoding of its value. At most 64 bytes. -/
  attrValue : List (List Nat)
  /-- `suppress_doc_type_check`: when true the whole `docType` clause is waived. -/
  suppressDocType : Bool
  /-- `expected_doc_type`: at most 32 bytes, matched as a *prefix* of the encoded docType. -/
  docType : List Nat
  /-- `mac_av`, the GF(2^128) MAC key α. Public, drawn per proof. -/
  macKey : Nat
  /-- `mac_e`, the tag on the issuer-signed digest, as (low half, high half). -/
  macE : Nat × Nat
  /-- `mac_device_pkx`. -/
  macDpkX : Nat × Nat
  /-- `mac_device_pky`. -/
  macDpkY : Nat × Nat

/-- Sizes the verifier itself controls. The circuit's `expected_*` buffers are fixed-width, so a
    longer value would silently be truncated rather than rejected; requiring these keeps the
    clauses below honest. -/
def WellFormed (s : Statement) : Prop :=
  s.now.length = timestampLen ∧
  s.docType.length ≤ 32 ∧
  s.attrValue.length = s.attrId.length ∧
  (∀ i, i < s.attrId.length →
    (s.attrId.getD i []).length ≤ 32 ∧ (s.attrValue.getD i []).length ≤ 64)

/-- The witness for one disclosed attribute: its `IssuerSignedItem` preimage, and the locator
    that says where the four CBOR map entries are and which is which. -/
structure AttrWitness where
  /-- 128 bytes: the SHA-padded `IssuerSignedItem`. -/
  preimage : List Nat
  /-- Length of the unpadded `IssuerSignedItem`. -/
  len : Nat
  /-- Where this attribute's digest sits in the MSO preimage (at its `0x58 0x20` header). -/
  digestOff : Nat
  /-- `slot_position`: the four map entries' start offsets, in physical order. -/
  slotPos : List Nat
  /-- `length`: the four map entries' lengths, in physical order. -/
  slotLen : List Nat
  /-- `permutation`: logical slot (0 `digestID`, 1 `random`, 2 `elementIdentifier`,
      3 `elementValue`) to physical index. -/
  perm : List Nat
  deriving Inhabited

/-- The private inputs of the hash circuit. -/
structure Witness where
  /-- 2560 bytes: the SHA-padded COSE `Signature1` buffer the issuer signed over. -/
  preimage : List Nat
  /-- Length of the unpadded buffer. -/
  msgLen : Nat
  /-- `nblocks`, the number of SHA-256 blocks the message occupies. -/
  nblocks : Nat
  /-- `issuer_sig_e`: the 32-byte digest the issuer signature covers. -/
  e : List Nat
  /-- The device public key's 32-byte x-coordinate. -/
  dpkX : List Nat
  /-- ... and y-coordinate. -/
  dpkY : List Nat
  docTypeOff : Nat
  validFromOff : Nat
  validUntilOff : Nat
  devKeyInfoOff : Nat
  valueDigestsOff : Nat
  /-- One per disclosed attribute, in the same order as `Statement.attrId`. -/
  attrs : List AttrWitness
  /-- `mac_ap`: the three one-time pads, each a pair. -/
  macPad : List (Nat × Nat)

/-! ## The clauses of `assert_valid_presentation_and_macs`

Seven, one per child of the scope tree, each named for its Rust function. -/

/-- `shift_preimage`'s own two assertions, which every offset clause carries: the offset is at
    least 5 and lies inside the message. Note the upper bound is `msgLen`, not the buffer size —
    an offset may not point into the padding. -/
def OffsetOk (w : Witness) (off : Nat) : Prop := 5 ≤ off ∧ off < w.msgLen

/-- `assert_mso_sha256_hash` → `assert_message_hash`. The preimage is correctly padded and its
    SHA-256 digest is `e`. This is the bulk of the circuit's non-booleanity assertions and is the
    clause `SHA/Spec.lean` discharges. -/
def MessageHash (w : Witness) : Prop :=
  ShaPadded maxShaBlocks w.preimage w.msgLen w.nblocks ∧ sha256 w.preimage w.nblocks = w.e

/-- Where the docType string's contents begin: after the `"docType"` key and its CBOR text-string
    header, which is two bytes when it is `0x78` (`select(is_two_byte_header, …)` in the circuit)
    and one byte otherwise. Named because `mdoc/Parsing.lean` needs the same expression. -/
def docTypeValueStart (bs : List Nat) (off : Nat) : Nat :=
  off + docTypeKey.length + (if byteAt bs (off + docTypeKey.length) == 0x78 then 2 else 1)

/-- `assert_mso_doc_type`. The literal `"docType"` occurs at `docTypeOff`; the CBOR text-string
    header that follows is one byte, or two when it is `0x78`; and the string's first
    `docType.length` bytes are the expected ones.

    Two things to notice. The whole clause is waived when `suppressDocType` is set — but the
    `OffsetOk` bound is asserted either way. And the string's *own* length is never compared to
    `docType.length`, so this is a prefix check: `"org.iso.18013.5.1.mDL"` is satisfied by a
    credential whose docType is `"org.iso.18013.5.1.mDLX"`. -/
def MsoDocType (s : Statement) (w : Witness) : Prop :=
  OffsetOk w w.docTypeOff ∧
  (s.suppressDocType = false →
    BytesAt w.preimage w.docTypeOff docTypeKey ∧
    BytesAt w.preimage (docTypeValueStart w.preimage w.docTypeOff) s.docType)

/-- `assert_mso_validity`. `now` lies in the closed window `[validFrom, validUntil]`. Both
    comparisons are `memcmp::leq`, which is non-strict, so a credential is valid on the exact
    second it expires. -/
def MsoValidity (s : Statement) (w : Witness) : Prop :=
  OffsetOk w w.validFromOff ∧ OffsetOk w w.validUntilOff ∧
  BytesAt w.preimage w.validFromOff validFromKey ∧
  BytesAt w.preimage w.validUntilOff validUntilKey ∧
  LeBytes (window w.preimage (w.validFromOff + validFromKey.length) timestampLen) s.now ∧
  LeBytes s.now (window w.preimage (w.validUntilOff + validUntilKey.length) timestampLen)

/-- `assert_mso_device_key`. The MSO binds the device key the holder is proving control of:
    `deviceKeyInfo`, the COSE_Key header, `dpkX`, the `-3` label, `dpkY`. Both coordinates are
    checked, and both are MAC'd — that is what stops a holder from presenting someone else's
    credential. -/
def MsoDeviceKey (w : Witness) : Prop :=
  OffsetOk w w.devKeyInfoOff ∧
  BytesAt w.preimage w.devKeyInfoOff deviceKeyInfoKey ∧
  window w.preimage (w.devKeyInfoOff + deviceKeyInfoKey.length) 32 = w.dpkX ∧
  BytesAt w.preimage (w.devKeyInfoOff + deviceKeyInfoKey.length + 32) deviceKeyYTag ∧
  window w.preimage (w.devKeyInfoOff + deviceKeyInfoKey.length + 35) 32 = w.dpkY

/-- `assert_mso_value_digests`. The MSO carries a `valueDigests` map. The literal is located, and
    nothing more: the attribute digests below are *not* required to lie inside it. -/
def MsoValueDigests (w : Witness) : Prop :=
  OffsetOk w w.valueDigestsOff ∧ BytesAt w.preimage w.valueDigestsOff valueDigestsKey

/-! ### The attribute verifier, `mso_attribute::assert_attribute` -/

/-- Offset of the map entry that logical slot `k` names. `slot_offset_and_len` routes through
    `permutation`, so the fields `slotPos`/`slotLen` are indexed *physically* — by position in the
    map — while these two are indexed *logically*, by which key is expected there. -/
def logicalOff (a : AttrWitness) (k : Nat) : Nat := a.slotPos.getD (a.perm.getD k 0) 0

/-- Length of the map entry that logical slot `k` names. -/
def logicalLen (a : AttrWitness) (k : Nat) : Nat := a.slotLen.getD (a.perm.getD k 0) 0

/-- `assert_preimage_header`. `IssuerSignedItem` is CBOR tag 24 wrapping a byte string with a
    one-byte length, and that byte string is a 4-entry map. The declared length must agree with
    the buffer length the SHA clause uses, which is what stops a prover from hashing more or less
    than it locates. -/
def AttrHeader (a : AttrWitness) : Prop :=
  BytesAt a.preimage 0 [0xD8, 0x18, 0x58] ∧
  byteAt a.preimage 4 = 0xA4 ∧
  a.len = byteAt a.preimage 3 + 4

/-- `assert_segments`. The four entries start at byte 5 — right after the `0xA4` map header —
    and tile the payload exactly: no gaps, no overlap, ending flush with `len`. Together with
    `AttrHeader`'s `0xA4` this is what supports reading the four checked slots as *all* of the
    map, without parsing it; the step that is assumed rather than proved is that a CBOR 4-entry
    map is four consecutive key-value encodings, which is the encoding's business, not the
    circuit's. -/
def AttrSegments (a : AttrWitness) : Prop :=
  a.slotPos.getD 0 0 = 5 ∧
  (∀ j, j < 3 → a.slotPos.getD (j + 1) 0 = a.slotPos.getD j 0 + a.slotLen.getD j 0) ∧
  a.len = a.slotPos.getD 3 0 + a.slotLen.getD 3 0

/-- `assert_permutation`. The logical-to-physical map is injective. Redundant given the four
    distinct key prefixes below, and kept in the circuit for defence in depth; kept here for the
    same reason. -/
def AttrPermutation (a : AttrWitness) : Prop :=
  (∀ k, k < 4 → a.perm.getD k 0 < 4) ∧
  (∀ k, k < 4 → ∀ l, l < 4 → k ≠ l → a.perm.getD k 0 ≠ a.perm.getD l 0)

/-- `assert_item_slot_key_only`. Slot `k` starts with the key literal `key`, and its length is
    exactly the key plus one CBOR item whose header the decoder accepts. The circuit does not
    check the value itself — `digestID` and `random` are not disclosed — only that it is one item
    of the declared size, which is what keeps the tiling in `AttrSegments` meaningful.

    `atom` is the circuit's `is_unsigned` flag. It only forbids count 27, an eight-byte length;
    despite the name it does not pin the value's major type. -/
def AttrSlotKeyOnly (a : AttrWitness) (k : Nat) (key : List Nat) (atom : Bool) : Prop :=
  BytesAt a.preimage (logicalOff a k) key ∧
  cborInvalid (byteAt a.preimage (logicalOff a k + key.length)) = false ∧
  (atom = true → cborCount (byteAt a.preimage (logicalOff a k + key.length)) ≠ 27) ∧
  logicalLen a k = key.length + cborItemLen a.preimage (logicalOff a k + key.length)

/-- `assert_item_slot_key_value`. Slot `k` is exactly the key literal followed by `val`, with no
    room for anything else — the length equality is what turns a prefix check into an equality.
    This is the clause that ties `attrId` and `attrValue` to the credential. -/
def AttrSlotKeyValue (a : AttrWitness) (k : Nat) (key val : List Nat) : Prop :=
  BytesAt a.preimage (logicalOff a k) (key ++ val) ∧
  logicalLen a k = key.length + val.length

/-- `assert_attribute`, plus the `tag32` header check its caller does. The digest of the
    `IssuerSignedItem` appears in the MSO preimage behind a `0x58 0x20` header, and the item is a
    four-entry map carrying the disclosed identifier and value.

    `nblocks` is the constant 2 here, so `ShaPadded` forces `56 ≤ len ≤ 119`. -/
def AttrOk (w : Witness) (a : AttrWitness) (id val : List Nat) : Prop :=
  OffsetOk w a.digestOff ∧
  BytesAt w.preimage a.digestOff tag32 ∧
  AttrHeader a ∧
  AttrSegments a ∧
  AttrPermutation a ∧
  AttrSlotKeyOnly a 0 digestIdKey true ∧
  AttrSlotKeyOnly a 1 randomKey false ∧
  AttrSlotKeyValue a 2 elementIdentifierKey id ∧
  AttrSlotKeyValue a 3 elementValueKey val ∧
  ShaPadded attrShaBlocks a.preimage a.len attrShaBlocks ∧
  sha256 a.preimage attrShaBlocks = window w.preimage (a.digestOff + tag32.length) 32

/-- `assert_attributes`. Every disclosed attribute, in order. This is what makes selective
    disclosure sound: the verifier learns the attribute, and that the issuer committed to it. -/
def Attributes (s : Statement) (w : Witness) : Prop :=
  w.attrs.length = s.attrId.length ∧
  ∀ i, i < s.attrId.length →
    AttrOk w (w.attrs.getD i default) (s.attrId.getD i []) (s.attrValue.getD i [])

/-! ### `assert_mac_tags` -/

/-- Low 128 bits of a 32-byte big-endian value, as a GF(2^128) bit pattern. `as_eltw_field` uses
    `pseudo_basis i = 1 <<< i`, so the field element *is* the integer. -/
def macLo (bs : List Nat) : Nat := beVal (bs.drop 16)

/-- High 128 bits, likewise. -/
def macHi (bs : List Nat) : Nat := beVal (bs.take 16)

/-- `mac_gf128::assert_mac`, for one 256-bit message: `tag + pad = α * msg` in each half. This is
    a one-time information-theoretic MAC — `α` and the tag are public, the pad is witness — so it
    binds `msg` across the two circuits without revealing it. -/
def MacOk (α : Nat) (tag pad : Nat × Nat) (msg : List Nat) : Prop :=
  GF128.add tag.1 pad.1 = GF128.mul α (macLo msg) ∧
  GF128.add tag.2 pad.2 = GF128.mul α (macHi msg)

/-- `assert_mac_tags`. Three messages under one key: the issuer-signed digest and both device-key
    coordinates. -/
def MacTags (s : Statement) (w : Witness) : Prop :=
  MacOk s.macKey s.macE (w.macPad.getD 0 (0, 0)) w.e ∧
  MacOk s.macKey s.macDpkX (w.macPad.getD 1 (0, 0)) w.dpkX ∧
  MacOk s.macKey s.macDpkY (w.macPad.getD 2 (0, 0)) w.dpkY

/-! ## The top-level statement -/

/-- **A valid mDOC presentation, hash half.** Existential in the witness, because the circuit
    checks byte patterns at prover-chosen positions rather than parsing CBOR.

    This is a faithful reading of the circuit only under `WellFormed s`. The circuit compares
    against fixed-width public buffers, so an over-long `now`, `docType`, identifier or value
    would be silently truncated there but not here; `WellFormed` is the side condition that makes
    the two agree, and it is the verifier's to discharge. -/
def ValidPresentation (s : Statement) : Prop :=
  ∃ w : Witness,
    MessageHash w ∧ MsoDocType s w ∧ MsoValidity s w ∧ MsoDeviceKey w ∧
    MsoValueDigests w ∧ Attributes s w ∧ MacTags s w

/-! ## Consequences

Small theorems that check the spec says what the prose says. -/

/-- The message is at most `40 * 64 - 9 = 2551` bytes: nine bytes of every block budget go to the
    `0x80` and the eight-byte length field. -/
theorem msgLen_le (w : Witness) (h : MessageHash w) : w.msgLen ≤ 2551 := by
  obtain ⟨⟨_, hmax, hlo, _, _, _, _, _⟩, _⟩ := h
  have : 64 * w.nblocks ≤ 64 * maxShaBlocks := Nat.mul_le_mul_left 64 hmax
  simp only [maxShaBlocks] at this
  omega

/-- `nblocks` is determined by `msgLen`, so a prover cannot choose where the digest is read off:
    the two inequalities of `assert_nblocks` admit exactly one block count. -/
theorem nblocks_unique (buf : List Nat) (m n n' : Nat)
    (h : ShaPadded maxShaBlocks buf m n) (h' : ShaPadded maxShaBlocks buf m n') : n = n' := by
  obtain ⟨_, _, hlo, hhi, _⟩ := h
  obtain ⟨_, _, hlo', hhi', _⟩ := h'
  omega

/-- An `IssuerSignedItem` is between 56 and `maxAttrCborLen = 119` bytes: `nblocks` is hardwired
    to 2, so `assert_nblocks` becomes a two-sided bound on the length. The upper bound is
    `K_MAX_ATTR_CBOR_LEN`, as it should be. The lower bound is a real constraint, not a
    formality — a four-entry map shorter than 56 bytes cannot be proved. -/
theorem attr_len_bounds (w : Witness) (a : AttrWitness) (id val : List Nat)
    (h : AttrOk w a id val) : 56 ≤ a.len ∧ a.len ≤ maxAttrCborLen := by
  obtain ⟨_, _, _, _, _, _, _, _, _, ⟨_, _, hlo, hhi, _⟩, _⟩ := h
  simp only [attrShaBlocks] at hlo hhi
  simp only [maxAttrCborLen, attrShaBlocks]
  omega

/-- The four map entries tile the payload with no slack: they start at byte 5, and their lengths
    sum to exactly `len - 5`. This is what `assert_segments` buys: without parsing the map, the
    circuit still knows the four slots it checked account for every byte of the payload. -/
theorem attr_segments_tile (a : AttrWitness) (h : AttrSegments a) :
    a.len = 5 + (a.slotLen.getD 0 0 + a.slotLen.getD 1 0 + a.slotLen.getD 2 0
                  + a.slotLen.getD 3 0) := by
  obtain ⟨h0, hstep, hend⟩ := h
  have h1 : a.slotPos.getD 1 0 = a.slotPos.getD 0 0 + a.slotLen.getD 0 0 := hstep 0 (by omega)
  have h2 : a.slotPos.getD 2 0 = a.slotPos.getD 1 0 + a.slotLen.getD 1 0 := hstep 1 (by omega)
  have h3 : a.slotPos.getD 3 0 = a.slotPos.getD 2 0 + a.slotLen.getD 2 0 := hstep 2 (by omega)
  omega

/-- The four map entries are also pairwise distinct as *logical* slots: `assert_permutation`
    makes the logical-to-physical map injective, so `digestID`, `random`, `elementIdentifier` and
    `elementValue` are four different entries of the map rather than one entry counted four
    times. -/
theorem attr_slots_distinct (a : AttrWitness) (h : AttrPermutation a) {k l : Nat}
    (hk : k < 4) (hl : l < 4) (hkl : k ≠ l) :
    a.perm.getD k 0 ≠ a.perm.getD l 0 := h.2 k hk l hl hkl

/-- What the whole statement gives about the message, in the user-facing form: there are mDOC
    bytes of length at most 2551 whose SHA-256 digest is the value the MAC binds. -/
theorem presentation_bounds (s : Statement) (h : ValidPresentation s) :
    ∃ w : Witness, w.msgLen ≤ 2551 ∧ sha256 w.preimage w.nblocks = w.e ∧
      MacOk s.macKey s.macE (w.macPad.getD 0 (0, 0)) w.e := by
  obtain ⟨w, hmsg, _, _, _, _, _, hmac, _⟩ := h
  exact ⟨w, msgLen_le w hmsg, hmsg.2, hmac⟩

/-! ## Sanity: the plumbing agrees with the code it transcribes

Two independent things are checked here. First, the byte-to-word conversion, against the one
block `SHA/Spec.lean` names. Second — and this is the check worth having — the CBOR decoder
against the constant table: `cborLen` applied to the first byte of each key literal must return
that literal's length. The two were transcribed from different Rust files, so agreement is
evidence neither was miscopied. -/

theorem wordsOfBytes_emptyPadded :
    wordsOfBytes (0x80 :: List.replicate 63 0) = SHA256.emptyBlock := by rfl

theorem blocksOf_emptyPadded :
    blocksOf 1 (wordsOfBytes (0x80 :: List.replicate 63 0)) = [SHA256.emptyBlock] := by rfl

/-- End to end: the empty message hashes to the FIPS test vector, in bytes. -/
theorem sha256_empty :
    sha256 (0x80 :: List.replicate 63 0) 1 =
      [0xe3, 0xb0, 0xc4, 0x42, 0x98, 0xfc, 0x1c, 0x14, 0x9a, 0xfb, 0xf4, 0xc8,
       0x99, 0x6f, 0xb9, 0x24, 0x27, 0xae, 0x41, 0xe4, 0x64, 0x9b, 0x93, 0x4c,
       0xa4, 0x95, 0x99, 0x1b, 0x78, 0x52, 0xb8, 0x55] := by rfl

/-- A buffer that is a prefix followed by zeros reads as zero past the prefix. Stated here rather
    than in a test file because it is what makes the `beyond active` conjunct of `ShaPadded`
    checkable in linear time: a 2560-byte buffer with 2112 trailing zeros would otherwise cost one
    list traversal per index, which is minutes of kernel reduction rather than seconds. -/
theorem byteAt_append_replicate (xs : List Nat) (k : Nat) :
    ∀ i, xs.length ≤ i → byteAt (xs ++ List.replicate k 0) i = 0 := by
  induction xs with
  | nil =>
      intro i _
      show (List.replicate k (0 : Nat)).getD i 0 = 0
      induction k generalizing i with
      | zero => simp [List.getD]
      | succ m ih =>
          rw [List.replicate_succ]
          cases i with
          | zero => simp [List.getD]
          | succ j => simpa [List.getD] using ih j
  | cons a xs ih =>
      intro i hi
      cases i with
      | zero => simp at hi
      | succ j =>
          have : xs.length ≤ j := by simpa using hi
          simpa [byteAt, List.getD] using ih j this

private theorem getD_repl (n : Nat) : ∀ i, (List.replicate n (0 : Nat)).getD i 0 = 0 := by
  induction n with
  | zero => intro i; simp [List.getD]
  | succ m ih =>
      intro i
      rw [List.replicate_succ]
      cases i with
      | zero => simp [List.getD]
      | succ k => simpa [List.getD] using ih k

private theorem getD_pad (i : Nat) (h : 0 < i) :
    (0x80 :: List.replicate 63 (0 : Nat)).getD i 0 = 0 := by
  cases i with
  | zero => omega
  | succ k => simpa [List.getD] using getD_repl 63 k

/-- And the empty message really is padded, by our own predicate, at one block. -/
theorem shaPadded_empty : ShaPadded maxShaBlocks (0x80 :: List.replicate 63 0) 0 1 := by
  refine ⟨by omega, by simp [maxShaBlocks], by omega, by omega, by rfl, ?_, ?_, ?_⟩
  · intro i _ h0 _; exact getD_pad i h0
  · intro i _ h1; exact getD_pad i (by omega)
  · intro j _
    show (0x80 :: List.replicate 63 (0 : Nat)).getD (64 * 1 - 8 + j) 0 = _
    rw [getD_pad (64 * 1 - 8 + j) (by omega)]
    simp

/-- The decoder agrees with every key literal's length. `0x67 "docType"` is a seven-character
    text string, so its encoding is eight bytes, and so on. -/
theorem cborLen_keys :
    cborLen (docTypeKey.getD 0 0) = docTypeKey.length ∧
    cborLen (validFromKey.getD 0 0) = validFromKey.length - 2 ∧
    cborLen (validUntilKey.getD 0 0) = validUntilKey.length - 2 ∧
    cborLen (valueDigestsKey.getD 0 0) = valueDigestsKey.length ∧
    cborLen (digestIdKey.getD 0 0) = digestIdKey.length ∧
    cborLen (randomKey.getD 0 0) = randomKey.length ∧
    cborLen (elementIdentifierKey.getD 0 0) = elementIdentifierKey.length ∧
    cborLen (elementValueKey.getD 0 0) = elementValueKey.length := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- `validFrom`/`validUntil` carry two extra bytes past the key string: tag 0 and the `0x74`
    header of the 20-character timestamp that the clause then reads. -/
theorem validity_tail :
    validFromKey.length = cborLen (validFromKey.getD 0 0) + 2 ∧
    validFromKey.getD (validFromKey.length - 2) 0 = 0xC0 ∧
    validFromKey.getD (validFromKey.length - 1) 0 = 0x74 ∧
    cborLen 0x74 = 1 + timestampLen := by
  refine ⟨rfl, rfl, rfl, rfl⟩

/-- `0x58 0x20` is the header of a 32-byte CBOR byte string: two header bytes, with the length in
    the second. That is why the attribute digest is read from `digestOff + 2`. -/
theorem tag32_decodes :
    cborLengthPlusNext (tag32.getD 0 0) = true ∧
    cborLen (tag32.getD 0 0) = tag32.length ∧
    tag32.getD 1 0 = 32 := by
  refine ⟨rfl, rfl, rfl⟩

/-- `0xA4` is a four-entry map: the `IssuerSignedItem` header byte the attribute clause pins. -/
theorem map4_decodes : cborInvalid 0xA4 = false ∧ cborCount 0xA4 = 4 ∧ cborType 0xA4 = 5 := by
  refine ⟨rfl, rfl, rfl⟩

/-! ## Executable check

The clauses are decidable, so they can be *run*. Below is a synthetic MSO fragment laid out by
hand from the byte literals, and five `decide`s over it — two that must hold and three that must
not. This is a different kind of evidence from the `rfl` lemmas above: those check that two
transcriptions of the same Rust constant agree, while these check that the offset arithmetic in
`MsoValidity` and `MsoDeviceKey` addresses the bytes it claims to. The `+ 35` between the two
device-key coordinates is exactly the sort of thing only a running check catches.

The same instances let a real credential be checked: dump a `ConcreteGiven` from the Rust side,
emit it as a `Witness`, and `decide` each clause. That is the test worth building next. -/

instance instDecidableOffsetOk (w : Witness) (o : Nat) : Decidable (OffsetOk w o) := by
  unfold OffsetOk; infer_instance

instance instDecidableMsoValidity (s : Statement) (w : Witness) : Decidable (MsoValidity s w) := by
  unfold MsoValidity; infer_instance

instance instDecidableMsoDeviceKey (w : Witness) : Decidable (MsoDeviceKey w) := by
  unfold MsoDeviceKey; infer_instance

instance instDecidableMsoDocType (s : Statement) (w : Witness) : Decidable (MsoDocType s w) := by
  unfold MsoDocType; infer_instance

instance instDecidableMsoValueDigests (w : Witness) : Decidable (MsoValueDigests w) := by
  unfold MsoValueDigests; infer_instance

namespace Demo

/-- ASCII bytes of a string; ISO-8601 timestamps are ASCII by construction. -/
private def ascii (s : String) : List Nat := s.toList.map Char.toNat

private def pkX : List Nat := List.range 32
private def pkY : List Nat := (List.range 32).map (· + 100)

/-- Five filler bytes (offsets below 5 are rejected by `OffsetOk`), then the validity window and
    the device key, laid out exactly as `deviceKeyInfoKey` and `deviceKeyYTag` require. -/
private def preimage : List Nat :=
  List.replicate 5 0
  ++ validFromKey ++ ascii "2024-01-01T00:00:00Z"
  ++ validUntilKey ++ ascii "2030-01-01T00:00:00Z"
  ++ deviceKeyInfoKey ++ pkX ++ deviceKeyYTag ++ pkY

private def w : Witness :=
  { preimage := preimage, msgLen := preimage.length, nblocks := 3
    e := [], dpkX := pkX, dpkY := pkY
    docTypeOff := 0, validFromOff := 5, validUntilOff := 37, devKeyInfoOff := 70
    valueDigestsOff := 0, attrs := [], macPad := [] }

private def st : Statement :=
  { now := ascii "2026-09-08T00:00:00Z", attrId := [], attrValue := []
    suppressDocType := true, docType := [], macKey := 0
    macE := (0, 0), macDpkX := (0, 0), macDpkY := (0, 0) }

/-- The offsets really are where the layout puts them. -/
theorem layout : preimage.length = 170 ∧ (5, 37, 70) =
    (5, 5 + validFromKey.length + timestampLen,
     5 + validFromKey.length + timestampLen + validUntilKey.length + timestampLen) := by
  refine ⟨rfl, rfl⟩

/-- A time inside the window passes. -/
theorem validity_holds : MsoValidity st w := by decide

/-- A time before `validFrom` fails. -/
theorem validity_too_early : ¬ MsoValidity { st with now := ascii "2019-01-01T00:00:00Z" } w := by
  decide

/-- A time after `validUntil` fails. -/
theorem validity_too_late : ¬ MsoValidity { st with now := ascii "2031-01-01T00:00:00Z" } w := by
  decide

/-- Both coordinates are read from the right place. -/
theorem deviceKey_holds : MsoDeviceKey w := by decide

/-- And from *different* places: swapping them fails, so `+ 32` and `+ 35` are not aliased. -/
theorem deviceKey_swapped : ¬ MsoDeviceKey { w with dpkX := pkY, dpkY := pkX } := by decide

end Demo

/-! ## Residual trust

What this specification does not establish, all of which the circuit also does not check. These
belong on the reviewed-assumptions list, not hidden inside a proof.

* **`MsoStructureAssumption`.** `ValidPresentation` says the byte patterns occur *somewhere* at
  or above offset 5 and below `msgLen`. That they occur only where the field names suggest — that
  `docTypeKey` cannot appear inside an attribute value, say — is a property of the CBOR encoding
  of a well-formed MSO. The circuit relies on it and does not verify it. Neither does this.

* **The namespace is not checked.** `K_NAMESPACE_CHECK_CBOR` (`"org.iso.18013.5.1"`) is defined
  in `proto/src/hash/constants.rs` and referenced by no circuit. Nothing ties a disclosed
  attribute to a namespace, so the statement above deliberately has no namespace clause. If two
  namespaces of one credential carry the same element identifier, this proof does not say which
  one the value came from.

* **The digest is not required to be inside `valueDigests`.** `MsoValueDigests` locates the
  literal; `AttrOk` locates a `0x58 0x20`-tagged digest at an unrelated offset. Only the CBOR
  structure of the MSO connects them.

* **The COSE `Signature1` prefix is not checked.** The preimage is supposed to be
  `K_COSE1_PREFIX ‖ …`, and the prover computes every offset as `18 + 7 + offset_in_mso`, but the
  circuit never looks at bytes 0-24 — indeed it constrains no byte of the preimage except through
  the patterns at the prover's own offsets and the SHA padding. What rules out a preimage of some
  other shape is that the issuer's ECDSA signature covers `e`, and issuers sign only well-formed
  COSE structures.

* **`docType` is a prefix.** See `MsoDocType`. A verifier that needs exact equality must supply
  the encoded length itself, which the current interface does not allow.

* **Issuer and device signatures.** Nothing here says the issuer *signed* `e`, or that the
  holder controls `(dpkX, dpkY)`. Those are the signature circuit's obligations, over P-256, and
  `ECDSA/EcdsaSpec.lean` is where they belong.

## The seam

`compile/src/allocate_sig.rs` gives the signature circuit the public inputs `issuer_pk`,
`device_sig_e`, and — identically to this one — `mac_e`, `mac_device_pkx`, `mac_device_pky` and
`mac_av`. Its witness includes `issuer_sig_e` and `device_pk`, MAC'd under the same key.

So the two statements compose. Suppose both circuits verify against the same public `α` and tags
but the hash circuit's `e` differs from the signature circuit's. Subtracting the two `MacOk`
equations gives `α · (e - e') = pad' - pad` in each half, which for `e ≠ e'` determines `α`
uniquely. The pads are witness, so a prover who knew `α` first could always solve this; what makes
it hard is that `α` is drawn by Fiat-Shamir *after* the witness is committed. Against a fixed
commitment the equation holds for exactly one of the `2¹²⁸` values of `α`, so the two `e`'s agree
except with probability `2⁻¹²⁸`, and the same for `dpkX` and `dpkY`.

`MacTags` is the whole of the interface between the halves, and that probability is the whole of
the loss.
-/

end MDoc
