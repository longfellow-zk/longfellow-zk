/-
# From byte windows to a parsed MSO

`mdoc/Spec.lean` records what the circuit checks: byte patterns at prover-chosen offsets. What a
verifier wants to believe is a statement about *fields* — "the credential's `validUntil` is after
now", not "some 13 bytes somewhere spell `validUntil`". This file is the bridge, and it says
precisely what has to be assumed to cross it.

## The shape of the argument

The circuit's weakness is that its offsets are advice. The compensating strength is that the
preimage is *signed by the issuer*, and issuers emit one canonical encoding. So:

1. Postulate a parsed view `Mso` — offsets and field values — of the byte string.
2. Postulate `IssuerFormat`: the byte string encodes that view, **and each of the five key
   literals occurs at exactly one offset in it**. This is the whole assumption, and `OnlyAt` is
   where it lives.
3. Then every existential offset in `ValidPresentation` collapses to the named one, and each
   clause becomes a statement about the parsed field. That is `## Transfer` below, and those are
   theorems, not assumptions.

The point of separating (2) from (3) is that (2) is a claim about *CBOR encoding* which a reader
can check against the mDL profile, or a generator can discharge for a fixed schema, while (3) is
mechanical. Nothing in (3) needs re-auditing when the schema changes.

## Where the argument does not reach

Attributes are different in kind, and the difference is the most useful thing in this file. The
attribute clause does not locate a *literal*; it locates a `0x58 0x20` header, and a 32-byte
digest follows dozens of those in a real MSO — every `valueDigests` entry, both device-key
coordinates, and, with probability around `2⁻¹⁶` per byte position, arbitrary interior positions
of the random salts and digests themselves. Uniqueness is simply false here, and no format
assumption can rescue it.

What rescues it is that the prover must exhibit a 56–119 byte string hashing to the 32 bytes it
points at. So attribute soundness rests on second-preimage resistance of SHA-256, not on the
encoding. That is `NoSecondPreimage`, and `attributes_committed` is the conditional theorem. A
format-only argument that claimed to cover attributes would be wrong.
-/

import mdoc.Spec

namespace MDoc

/-! ## Unique occurrence

The assumption, isolated. Everything else in this file is bookkeeping around it. -/

/-- `pat` occurs at `k` in `bs`, and at no other offset the circuit could have used. The range
    `5 ≤ o < msgLen` is exactly `OffsetOk`, so this is the smallest uniqueness claim that does
    the job — an occurrence in the SHA padding, or in the first five bytes, is irrelevant because
    `shift_preimage` rejects those offsets outright. -/
def OnlyAt (bs : List Nat) (msgLen : Nat) (pat : List Nat) (k : Nat) : Prop :=
  BytesAt bs k pat ∧ ∀ o, 5 ≤ o → o < msgLen → BytesAt bs o pat → o = k

/-- A parsed MSO: where each field sits and what it holds. This is the verifier's mental model,
    and nothing in `Spec.lean` refers to it. -/
structure Mso where
  docTypeOff : Nat
  /-- The docType text-string *contents*, CBOR header excluded. -/
  docTypeVal : List Nat
  validFromOff : Nat
  /-- 20-byte ISO-8601 timestamp. -/
  validFromVal : List Nat
  validUntilOff : Nat
  validUntilVal : List Nat
  devKeyOff : Nat
  /-- 32-byte coordinates of the bound device key. -/
  devKeyX : List Nat
  devKeyY : List Nat
  valueDigestsOff : Nat
  /-- The 32-byte digests the issuer committed to under `valueDigests`. -/
  digests : List (List Nat)

/-! ## The issuer-format assumption

Read this as: *a trusted issuer emits exactly this*. Each conjunct is either a placement fact
(the literal is here and nowhere else) or a content fact (this is what follows it). -/

/-- The five located fields, each with its unique-occurrence claim and its contents. -/
def IssuerFormat (bs : List Nat) (msgLen : Nat) (m : Mso) : Prop :=
  -- docType
  OnlyAt bs msgLen docTypeKey m.docTypeOff ∧
  BytesAt bs (docTypeValueStart bs m.docTypeOff) m.docTypeVal ∧
  -- validity window
  OnlyAt bs msgLen validFromKey m.validFromOff ∧
  window bs (m.validFromOff + validFromKey.length) timestampLen = m.validFromVal ∧
  OnlyAt bs msgLen validUntilKey m.validUntilOff ∧
  window bs (m.validUntilOff + validUntilKey.length) timestampLen = m.validUntilVal ∧
  -- device key
  OnlyAt bs msgLen deviceKeyInfoKey m.devKeyOff ∧
  window bs (m.devKeyOff + deviceKeyInfoKey.length) 32 = m.devKeyX ∧
  window bs (m.devKeyOff + deviceKeyInfoKey.length + 35) 32 = m.devKeyY ∧
  -- valueDigests
  OnlyAt bs msgLen valueDigestsKey m.valueDigestsOff

/-! ## Transfer

Each clause of `ValidPresentation`, restated about the parsed field. These are the theorems the
verifier's reasoning actually needs, and none of them is an assumption. -/

/-- The prover's offset was the only one available. This one lemma does all the work; the rest is
    rewriting. -/
theorem offset_forced {bs : List Nat} {msgLen k o : Nat} {pat : List Nat}
    (hu : OnlyAt bs msgLen pat k) (hlo : 5 ≤ o) (hhi : o < msgLen) (hb : BytesAt bs o pat) :
    o = k := hu.2 o hlo hhi hb

/-- **Validity.** `now` lies inside the credential's real window — the one the issuer wrote,
    not merely one that some 20 bytes of the preimage spell. -/
theorem validity_transfers {st : Statement} {w : Witness} {m : Mso}
    (hf : IssuerFormat w.preimage w.msgLen m) (hv : MsoValidity st w) :
    LeBytes m.validFromVal st.now ∧ LeBytes st.now m.validUntilVal := by
  obtain ⟨_, _, hfu, hfv, huu, huv, _⟩ := hf
  obtain ⟨⟨hflo, hfhi⟩, ⟨hulo, huhi⟩, hfb, hub, hcmpF, hcmpU⟩ := hv
  rw [offset_forced hfu hflo hfhi hfb] at hcmpF
  rw [offset_forced huu hulo huhi hub] at hcmpU
  rw [hfv] at hcmpF
  rw [huv] at hcmpU
  exact ⟨hcmpF, hcmpU⟩

/-- **Device key.** The key the two circuits MAC and the signature circuit verifies against is
    the key the issuer bound into this credential. -/
theorem deviceKey_transfers {w : Witness} {m : Mso}
    (hf : IssuerFormat w.preimage w.msgLen m) (hd : MsoDeviceKey w) :
    w.dpkX = m.devKeyX ∧ w.dpkY = m.devKeyY := by
  obtain ⟨_, _, _, _, _, _, hdu, hdx, hdy, _⟩ := hf
  obtain ⟨⟨hlo, hhi⟩, hb, hx, _, hy⟩ := hd
  rw [offset_forced hdu hlo hhi hb] at hx hy
  exact ⟨hx.symm.trans hdx, hy.symm.trans hdy⟩

/-- **Document type.** The public `docType` is a prefix of the credential's real docType. Prefix,
    not equality: see `MsoDocType`. The `suppressDocType` guard is carried through, because a
    suppressed check transfers nothing. -/
theorem docType_transfers {st : Statement} {w : Witness} {m : Mso}
    (hf : IssuerFormat w.preimage w.msgLen m) (hd : MsoDocType st w)
    (hns : st.suppressDocType = false) (hlen : st.docType.length ≤ m.docTypeVal.length) :
    BytesAt m.docTypeVal 0 st.docType := by
  obtain ⟨hdu, hval, _⟩ := hf
  obtain ⟨⟨hlo, hhi⟩, hrest⟩ := hd
  obtain ⟨hb, hv⟩ := hrest hns
  rw [offset_forced hdu hlo hhi hb] at hv
  intro i hi
  show m.docTypeVal.getD (0 + i) 0 = _
  rw [Nat.zero_add]
  exact (hval i (Nat.lt_of_lt_of_le hi hlen)).symm.trans (hv i hi)

/-- **`valueDigests` is where the issuer put it.** Weak on its own — locating the literal is all
    the circuit does — but it is what a stronger attribute argument would build on. -/
theorem valueDigests_transfers {w : Witness} {m : Mso}
    (hf : IssuerFormat w.preimage w.msgLen m) (hd : MsoValueDigests w) :
    w.valueDigestsOff = m.valueDigestsOff := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hvu⟩ := hf
  obtain ⟨⟨hlo, hhi⟩, hb⟩ := hd
  exact offset_forced hvu hlo hhi hb

/-! ## Attributes: why format is not enough

The other clauses collapsed because a 13-byte literal occurs once. `tag32` is two bytes and
occurs everywhere, so the same move is unavailable. What the circuit gives is weaker and
cryptographic. -/

/-- The 32-byte strings a prover could point an attribute at: everything in the preimage that
    sits behind a `0x58 0x20`, at an offset `shift_preimage` accepts. In a real MSO this contains
    every `valueDigests` entry, both device-key coordinates, and whatever incidental `58 20`
    happens to fall inside a salt. -/
def DigestWindow (bs : List Nat) (msgLen : Nat) (d : List Nat) : Prop :=
  ∃ o, 5 ≤ o ∧ o < msgLen ∧ BytesAt bs o tag32 ∧ window bs (o + tag32.length) 32 = d

/-- Unconditionally, each disclosed attribute hashes to *some* digest window. This is exactly as
    much as the circuit proves, and it is not yet the statement anyone wants. -/
theorem attributes_hash_into_window {st : Statement} {w : Witness}
    (ha : Attributes st w) (i : Nat) (hi : i < st.attrId.length) :
    DigestWindow w.preimage w.msgLen (sha256 (w.attrs.getD i default).preimage attrShaBlocks) := by
  obtain ⟨_, hall⟩ := ha
  obtain ⟨⟨hlo, hhi⟩, htag, _, _, _, _, _, _, _, _, hsha⟩ := hall i hi
  exact ⟨(w.attrs.getD i default).digestOff, hlo, hhi, htag, hsha.symm⟩

/-- **The cryptographic assumption attributes need.** Every digest window a prover can hit with a
    56-119 byte preimage is one the issuer actually committed to.

    This is second-preimage resistance of SHA-256 in the shape the circuit uses it: the windows
    that are *not* committed digests — device-key coordinates, bytes inside a salt — are fixed
    before the prover starts, and hitting one means producing a short preimage for a given
    32-byte target. It cannot be discharged from `IssuerFormat`, and it is not the kind of
    statement that becomes a theorem; it belongs on the assumption list next to
    `MsoStructureAssumption`. -/
def NoSecondPreimage (bs : List Nat) (msgLen : Nat) (m : Mso) : Prop :=
  ∀ p n d, ShaPadded attrShaBlocks p n attrShaBlocks → sha256 p attrShaBlocks = d →
    DigestWindow bs msgLen d → d ∈ m.digests

/-- **Attributes, transferred.** Under that assumption, every disclosed attribute's
    `IssuerSignedItem` hashes to a digest the issuer committed to — which, with `AttrSlotKeyValue`
    pinning the identifier and value bytes, is selective disclosure. -/
theorem attributes_committed {st : Statement} {w : Witness} {m : Mso}
    (hsp : NoSecondPreimage w.preimage w.msgLen m)
    (ha : Attributes st w) (i : Nat) (hi : i < st.attrId.length) :
    sha256 (w.attrs.getD i default).preimage attrShaBlocks ∈ m.digests := by
  obtain ⟨_, hall⟩ := ha
  have hattr := hall i hi
  obtain ⟨⟨hlo, hhi⟩, htag, _, _, _, _, _, _, _, hpad, hsha⟩ := hattr
  exact hsp _ _ _ hpad rfl ⟨(w.attrs.getD i default).digestOff, hlo, hhi, htag, hsha.symm⟩

/-! ## The payoff

Everything above, assembled: what a verifier that had fully parsed the MSO would conclude. -/

/-- The semantic reading of a presentation, stated entirely about the *parsed* MSO. No offsets,
    no windows, no `∃ o`. This is the sentence the deployment cares about. -/
def SemanticClaim (st : Statement) (w : Witness) (m : Mso) : Prop :=
  -- in date, against the issuer's own window
  LeBytes m.validFromVal st.now ∧ LeBytes st.now m.validUntilVal ∧
  -- the MAC'd device key is the one the credential binds
  w.dpkX = m.devKeyX ∧ w.dpkY = m.devKeyY ∧
  -- the requested document type is what the credential says it is
  (st.suppressDocType = false → BytesAt m.docTypeVal 0 st.docType) ∧
  -- every disclosed attribute is one the issuer committed to
  (∀ i, i < st.attrId.length →
    sha256 (w.attrs.getD i default).preimage attrShaBlocks ∈ m.digests)

/-- **Window checks are equivalent to parsing, given the format.** For a witness satisfying the
    circuit's clauses over an issuer-formatted preimage, the existential-offset statement of
    `Spec.lean` implies the parsed statement. The two assumptions are exactly `IssuerFormat` and
    `NoSecondPreimage`; nothing else is taken on trust. -/
theorem parses_as_expected {st : Statement} {w : Witness} {m : Mso}
    (hf : IssuerFormat w.preimage w.msgLen m)
    (hsp : NoSecondPreimage w.preimage w.msgLen m)
    (hlen : st.docType.length ≤ m.docTypeVal.length)
    (hdt : MsoDocType st w) (hval : MsoValidity st w) (hkey : MsoDeviceKey w)
    (hattr : Attributes st w) :
    SemanticClaim st w m := by
  obtain ⟨hfrom, huntil⟩ := validity_transfers hf hval
  obtain ⟨hx, hy⟩ := deviceKey_transfers hf hkey
  exact ⟨hfrom, huntil, hx, hy,
    fun hns => docType_transfers hf hdt hns hlen,
    fun i hi => attributes_committed hsp hattr i hi⟩

/-- The same, from the top-level statement. `signed` is the predicate "this byte string carries a
    valid issuer signature" — supplied by the *other* circuit, through the MAC seam, so it enters
    here as a parameter rather than a definition.

    `hsigned` is the seam: a preimage whose digest carries these public MAC tags was signed by the
    issuer. `hfmt` is the trusted-issuer assumption: anything the issuer signs is in format. Read
    together they are the argument this file exists to make. -/
theorem valid_presentation_parses {st : Statement} (hv : ValidPresentation st)
    (signed : List Nat → Nat → Prop)
    (hsigned : ∀ w : Witness, MessageHash w → MacTags st w → signed w.preimage w.msgLen)
    (hfmt : ∀ bs n, signed bs n → ∃ m : Mso,
      IssuerFormat bs n m ∧ NoSecondPreimage bs n m ∧ st.docType.length ≤ m.docTypeVal.length) :
    ∃ (w : Witness) (m : Mso), SemanticClaim st w m := by
  obtain ⟨w, hmsg, hdt, hval, hkey, _, hattr, hmac⟩ := hv
  obtain ⟨m, hf, hsp, hlen⟩ := hfmt _ _ (hsigned w hmsg hmac)
  exact ⟨w, m, parses_as_expected hf hsp hlen hdt hval hkey hattr⟩

/-! ## What a discharge of `IssuerFormat` would look like

`OnlyAt` is the only hard conjunct, and it is a statement about one fixed byte string, so it is
decidable: for a concrete MSO, `∀ o < msgLen, BytesAt bs o pat → o = k` is a scan. Three routes,
in increasing order of what they buy:

* **Per-credential, by computation.** Replace `BytesAt` with a `Bool` scan and `decide` it for a
  given MSO. Cheap, and it makes the transfer theorems above unconditional for that credential —
  but it says nothing about the next one.

* **Per-schema, by an encoding lemma.** State the mDL MSO schema as a grammar, prove that its
  canonical CBOR encoding contains each key literal once, and instantiate. This is the version
  worth having, and it is a real piece of work: the obligation is that no *field value* can
  contain a key literal, which for text and byte strings means reasoning about lengths, and for
  the digests means they are not chosen by an adversary.

* **Weaken what needs uniqueness.** `validFromKey` and `validUntilKey` end in `0xC0 0x74` — tag 0
  followed by a 20-character text string. A 12- or 13-byte literal ending in a type-pinning tag
  is already hard to forge inside a well-formed value. `valueDigestsKey` has no such tail. Making
  the literals self-delimiting in the *circuit* would shrink the assumption rather than prove it,
  and is the cheaper engineering answer.

The third route is the one to weigh against the second: `IssuerFormat` is an assumption about
every credential the deployment will ever see, and a circuit change can make it smaller.
-/

end MDoc
