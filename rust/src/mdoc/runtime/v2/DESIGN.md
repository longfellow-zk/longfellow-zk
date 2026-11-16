# mdoc v2 application protocol design

The mdoc v2 protocol proves that the holder of an ISO 18013-5 mdoc
presents a document an issuer signed, bound to one session, that discloses
the requested attributes and is valid at the requested time. It reveals
nothing else about the document. It is the application layer of Longfellow
v2, public as `mdoc::v2` (module `mdoc::runtime::v2`). It runs two trusted
circuits: the hash circuit over GF(2^128) checks the signed MSO and the
disclosed attributes. The signature circuit over the P-256 base field checks
the issuer and device ECDSA signatures. They share 768 bits (the issuer
digest and the device key), stored once, in the binary witness. The
composition driver `runtime::v2::foreign::compose` proves both circuits
under one joint Polygero commitment. mdoc supplies the request, the
statement, the circuits, the shared-bit layout, and the `MDA7` envelope that
the final seal closes. Nothing consumes its output except the application,
which receives a `VerifiedProof`.

## Statement

### The request

An application request has the six parts below. Both roles supply all
six; the verifier also takes the proof, and the prover the document.

| Part | Rust parameter | Constraint (checked before any circuit is loaded) |
|---|---|---|
| Session transcript | `transcript: &[u8]` | the transport's `SessionTranscript`: at most `MAX_SESSION_TRANSCRIPT_BYTES` = 64 KiB (see Size limits), exactly one CBOR item that `CborParser::parse_exact` accepts: definite lengths only, nesting depth at most 64, text strings valid UTF-8 (`session_transcript_is_one_item`) |
| Document type | `doc_type: &str` | 1 to `K_DOC_TYPE_BYTES` = 32 bytes |
| Time | `now: &str` | `YYYY-MM-DD[Tt]hh:mm:ss[Zz]`, ASCII digits (`timestamp_digits`) |
| Attributes | `attrs: &[RequestedAttribute]` | exactly `spec.num_attributes`, which must be 1 to `NEXT_MAX_ATTRIBUTES` = 4; one namespace, nonempty UTF-8 of at most `K_NAMESPACE_BYTES` = 64 bytes; identifier valid UTF-8, CBOR-encoded in at most `K_ATTR_ID_BYTES` = 32 bytes; CBOR value at most `K_ATTR_VALUE_BYTES` = 64 bytes, of a kind `circuit_supports` accepts |
| Issuer key | `pkx, pky: &str` | 1 to 64 hex digits each, optional `0x`, canonical P-256 base-field elements (`parse_pk_coordinate`) |
| Spec | `zk_spec: &ZkSpecStruct` | `supports_version()` (version `NEXT_VERSION` = 12) |

`circuit_supports` accepts exactly one well-formed CBOR item: text, bytes,
integer, `true`/`false`, a tag-1004 full-date of 14 bytes, or a tag-0
date-time of 22 bytes. The time is reduced to its fourteen
`YYYYMMDDhhmmss` digits (`K_TIMESTAMP_DIGITS`), so `T`/`t` and `Z`/`z` are
the same request.

### Size limits

The roles bound the variable-length inputs that they parse into CBOR trees,
because a parsed tree can take a few hundred times the memory of its
bytes (deeply nested one-entry maps).

| Input | Limit | Checked by | Rejects with |
|---|---|---|---|
| Session transcript | `MAX_SESSION_TRANSCRIPT_BYTES` = 64 KiB | `Request::check`, before parsing (both roles) | `InvalidInput` |
| Document | `MAX_DOCUMENT_BYTES` = 256 KiB | `document::parse`, before parsing (prover) | `MsoDecodingFailure` |

The session transcript limit follows from its structure. An ISO 18013-5
`SessionTranscript` is `[DeviceEngagementBytes, EReaderKeyBytes, Handover]`.
Device engagement holds a version, the device's ephemeral COSE key, and the
retrieval methods and origin information, a few hundred bytes; the reader
key is one COSE key, under 100 bytes; the handover is `null` (QR), two NFC
handover messages (at most a few hundred bytes), or, for OpenID4VP and the
Digital Credentials API (ISO 18013-7), a short array of a label and one or
three SHA-256 digests or a nonce, about 100 bytes. Real transcripts thus stay
under about 2 KB, and the test fixtures' are 61 to 188 bytes. 64 KiB leaves
a margin of more than 30 over the largest plausible transcript, and bounds
the transcript's parse tree at about 12 MB (191 times its size, the worst
nesting).

The document limit follows from real documents. The document carries the
MSO, whose preimage the hash circuit bounds at `K_MSO_PREIMAGE_LEN`, and the
issuer-signed items, of which only the requested ones must fit a circuit
slot. A wallet may pass its whole credential: a full mDL carries a portrait
(a JPEG, commonly 10 to 30 KB) and may carry a signature image or biometric
templates, some tens of KB in all. The test fixtures, which hold only a few
items, are 1,264 to 3,549 bytes (production Arizona and Malta documents
included). 256 KiB leaves a margin of several times over a full mDL with its
images, and bounds the document stage at about 85 MB (334 times its size,
the worst nesting under an ignored key). The cap is v2's; the CBOR parser,
which v1 shares, has none.

### The claim

The verifier ends with this claim. There is an MSO whose signed
`COSE_Sign1` envelope the issuer key signed (ECDSA P-256 over SHA-256). The
MSO's `docType` equals the requested document type, and its `validFrom` and
`validUntil` bracket the requested time. It names the requested namespace
and a canonical device key `(x, y)`. Its value digests include, for each
requested attribute, the SHA-256 of an `IssuerSignedItem` with the requested
identifier and value. That device key signed `e2`, the device-authentication
digest of this session and document type. The hash circuit proves the MSO
and attribute facts, the canonical device key (`x, y < p`) and the issuer
digest. The signature circuit proves both signatures. The two circuits agree
on the 768 shared bits.

The protocol reduces this claim to the statement below and to the two
circuits' satisfiability at its public inputs (hash circuit plus adapter
fragment over GF(2^128), signature circuit over P-256, from one extracted
witness pair). Committed, never public: the hash witness bits (MSO preimage,
offsets, attribute items, SHA-256 witnesses, the shared 768 bits), the split
mask R and the two quotient pads, and the signature circuit's native private
inputs and pads.

### The transcript statement

The statement is everything the verifier fixes before it reads a proof byte
(transcript I1). For mdoc it is these messages, in this order, at the start
of the first node:

| Message | Values | mdoc source |
|---|---|---|
| `MdocStatement` | as in the transcript design: protocol ID `longfellow/v2/mdoc/transcript/v2`; session transcript; combined hash; (version, attribute count) | the request and `ZkSpecStruct` |
| `Circuit` x 3 | circuit ID, which binds the circuit's layer widths and its output, input and public input counts | hash circuit, adapter fragment, signature circuit |
| `CommitmentLayout` x 2 | per field: (FieldID, committed private inputs before packing, pad cells, fingerprint mask cells); packing descriptor; native runs; bit-stored runs; (mask start, mask width) | binary participant (packing degree 128), then prime participant (degree one) |
| `AdapterLayout` x 1 | adapter mode ID `longfellow/v2/foreign/p256/two-full-field-trees/v1`; (Q = `QUOTIENT_BITS` = 10, 2 trees, virtual leaf count: 768 + 256 + 10 = 1034 per tree); start and width of the two 10-bit quotient pads among the binary private inputs (R's 256 bits are in the split `CommitmentLayout`) | the `P256Mode<QUOTIENT_BITS>` of `link::composition` |
| `JointGeometry` | (k, s, n, t): the spec's one profile (`ZkSpecStruct::config`); each field's cell count follows from its `CommitmentLayout` | `ComposedGeometry::config` |
| `PublicInputs` | Elements(GF2_128, 901 + 788A) | `PublicInputs::derive` (`push_input_hash`) |
| `PublicInputs` | Elements(P256, 258) | `PublicInputs::derive` (`push_input_sig`) |

A is the attribute count. Public inputs are absorbed as the circuit sees
them, including `e2` (transcript decision "Derivable public inputs"). The
session transcript enters twice by construction, not by re-absorption: once
in `MdocStatement`, and once inside `e2`, which the signature circuit reads.
The document type, the time, the attributes and the namespace enter only as
hash public inputs. The issuer key and `e2` enter only as signature public
inputs.

### Public inputs

`PublicInputs::derive` is the one function that turns a checked request into
both vectors; both roles call it.

Hash circuit (`push_input_hash`, layout of `mdoc::circuits::hash::allocate`).
Each byte is 8 elements, least significant bit first; each length is
`K_ATTR_INDEX_BITS` = 10 elements, least significant bit first; every
element is 0 or 1 in GF(2^128); unused bytes are zero.

| Bits | Field | Count |
|---|---|---|
| 0 | time: the 14 ASCII digits | 112 |
| 112 + 788i | attribute i: CBOR text of its identifier (32 bytes), its length | 256 + 10 |
| 112 + 788i + 266 | attribute i: CBOR value (64 bytes), its length | 512 + 10 |
| 112 + 788A | `suppress_doc_type_check`, always 0 | 1 |
| 113 + 788A | document type (32 bytes), its length | 256 + 10 |
| 379 + 788A | namespace of every attribute (64 bytes), its length | 512 + 10 |
| | total | 901 + 788A |

Attribute order is the request's order. For A = 1 to 4 the hash circuit has
1689, 2477, 3265 and 4053 public inputs.

Signature circuit (`push_input_sig`, layout of
`mdoc::compile::circuits::native_circuit`):

| Index | Value |
|---|---|
| 0, 1 | issuer key `pkx`, `pky` |
| 2 + j, j < 256 | bit j of `e2`, as 0 or 1 in P-256 |

`e2 = compute_transcript_hash(transcript, doc_type)`: SHA-256 of the COSE
`Sig_structure` `K_COSE_SIGN1_SIGNING_HEADER || bstr(payload)`, where
`payload = D8 18 || bstr(DeviceAuthentication)` and `DeviceAuthentication =
84 74 "DeviceAuthentication" || transcript || tstr(doc_type) || D8 18 41 A0`
(empty device namespaces). The digest is read as a big-endian integer, and
its bits are taken from the least significant.

### Spec and circuit identity

| Value | Definition | Checked by |
|---|---|---|
| Circuit ID | SHA-256 of the circuit's canonical encoding (`core::proto::v2::compute_id`) | `CircuitReader` recomputes it for every payload |
| Combined hash | SHA-256(signature circuit ID \|\| hash circuit ID), the archive's entry order | `core::proto::v2::archive::from_stream` recomputes it |
| `ZkSpecStruct` | `combined_hash`, `num_attributes`, `version`, `polygero`: one profile for both fields, which the joint commitment shares (`ZkSpecStruct::config`) | `Instance::load`: archive combined ID and version equal the spec's, and both public-input counts match it |
| Adapter fragment ID | the ID of the product-tree fragment that `foreign::adapter` rebuilds from the hash circuit's shape | absorbed in its `Circuit` message |

A spec names its circuits through the combined hash, and the statement
absorbs the combined hash and all three circuit IDs (transcript I3). The
application circuits come only from `CircuitReader`, which recomputes their
IDs from the archive. The adapter fragment is generated:
`Circuit::from_raw` builds it and computes its ID. Neither path lets a
caller supply an ID, and `Circuit` has no public mutable access.

## Invariants

These rules are specific to mdoc. The transcript rules (transcript I1 to
I11) apply unchanged.

**I1. One request, one derivation.** Both roles build their public inputs
with `PublicInputs::derive` from the checked request, and from nothing else.
The prover does not take `e2` from the parsed document, and no other code
computes a public input. `suppress_doc_type_check` is a constant inside the
derivation, not a parameter.
*Enforced by:* `PublicInputs` has private fields and one constructor, whose
only inputs are a `Request` and the field (type); the role-trace test
(transcript I9), which compares the statement messages byte for byte.

**I2. A request is checked once, before anything is loaded.** `Request::check`
validates every row of the request table and is the only way to obtain a
`Request`. Circuit loading, public-input derivation, document parsing and
witness construction take a `Request`, and sampling and proof parsing need
the statement built from them, so none of them runs on an unchecked
request. The checked request is semantic: the time keeps its fourteen
digits (`T`/`t` and `Z`/`z` are one request), and the issuer key's spellings
(`1`, `01`, `0x1`, either letter case) become field elements. On accepted
requests the fixed-width, non-hashed public-input fields are not truncated,
every length is encoded, and the single namespace slot is correct because
all attributes share it. The session is represented in `PublicInputs` by
`e2`, a cryptographic digest, and the spec not at all; the complete
statement binds the spec and the raw session transcript separately
(`MdocStatement`). So neither `e2` nor `PublicInputs` alone is an injective
encoding of the request. The session transcript is one CBOR item, so the
`DeviceAuthentication` preimage of `e2` is self-delimiting: it determines
the (transcript, document type) pair.
*Enforced by:* `Request` has private fields and one constructor (type);
`rejects_invalid_public_inputs_before_loading_or_sampling`,
`namespace_capacity_and_encoding_are_checked_before_proving`,
`request_errors_follow_the_error_table` (tests).

**I3. The spec selects the circuits; their IDs are recomputed.** An
`Instance` is built only by `Instance::load(request, compressed, p256, gf2)`,
from the checked request's spec. It requires an archive whose combined ID
and circuit version equal the spec's, exactly two entries named `sig` and
`hash`, each payload decoding completely to a circuit whose recomputed ID
equals its entry, and a hash circuit with `901 + 788 * spec.num_attributes`
public inputs and a signature circuit with 258. There is no unchecked
loading path for proving or verification.
*Enforced by:* `Instance` has one constructor (type); `CircuitReader` and
`from_stream` recompute IDs (runtime);
`circuit_identifier_enforcement_is_unconditional`,
`instance_load_binds_archive_and_entry_identifiers`,
`instance_load_checks_public_input_counts`, `run_next_error_table` (tests).

**I4. One shared-bit layout.** The 768 shared bits are defined once, in
`mdoc::proto::layout`: `sig::{ISSUER_DIGEST, DEVICE_X, DEVICE_Y}` and
`hash::{ISSUER_DIGEST, DEVICE_X, DEVICE_Y}` are `0..256`, `256..512`,
`512..768` of each circuit's private inputs, and `SHARED` pairs them. Each
256-bit value is the integer's bits, least significant first. Both
compilers, both witness encoders and the link read this table and nothing
else.
*Enforced by:* a `const` assertion that the paired ranges coincide and tile
`0..SHARED_BITS` (compiler); `layout::check_at` in `hash::allocate` and
`native_circuit` (compilation panics on drift) and in `push_witness_hash` and
`push_witness_sig` (`WitnessCreationFailure`) (runtime);
`shared_positions_match_signature_inputs` (test).

**I5. The hash circuit cannot read the link's bits.** The hash circuit is
archived at its natural width. R (`MASK_BITS` = 256), the two quotient pads
(`QUOTIENT_BITS` = 10 each) and the adapter's virtual leaves follow its
inputs, and every sumcheck component reads only its own input prefix. So the
ordinary hash predicate is independent of every challenge-derived value.
`SHARED_BITS + MASK_BITS <= 2^QUOTIENT_BITS` holds.
*Enforced by:* prefix reads in sumcheck (runtime); a `const` assertion in
`mdoc::proto::adapter`; Lean `HashCircuit.readDisjoint`,
`MdocWitness.hashChecks_prefix`, `MdocWitness.hashValid_of_satisfies`.

**I6. One geometry, derived once.** The entry points derive the composition
(`link::composition`) from the spec and the circuits of the `Instance`,
which holds only the two circuits. The composition builds the statement
(`Composition::statement`) with its `ComposedGeometry`; the statement's
geometry messages are written from it, and the proof reader and the
composition read it back through the session (`Opened::geometry`,
transcript I2, I3). No caller passes a geometry.
*Enforced by:* `MdocProof::read` takes the `Bound<ComposedGeometry>` that
`Opened::geometry` returns, and `ComposedStatement::{prove, reduce_and_authenticate}`
take the `Opened` session (type); the mdoc trace test that the absorbed profile
equals the parsing geometry's (transcript I3).

**I7. One envelope, read exactly.** A proof is `"MDA7" || body || seal`. The
body holds only prover data (transcript I11). The reader rejects a wrong
magic, any malformed field, and any length other than exactly one 32-byte
seal after the body. The only acceptance result is `VerifiedProof`, which
only the seal check returns (transcript I10).
*Enforced by:* `Unverified::decoded` (runtime); `VerifiedProof` has no public
constructor (type); `run_next_verifier_bad_proofs` (test); Lean
`ProofBodyCodec`, `ProofOutput`.

**I8. The body is in send order.** The body lists every interactive field in
the order it is sent, then the terminal fields (transcript I4). The reader
consumes the proof in the order the verifier checks it.
*Enforced by:* the proof-length test (transcript I11) and the trace test
`check_trace_matches_wire`, which checks that the absorbed payloads, in send
order, are the interactive section of the body (test); Lean
`ProofBodyCodec`.

**I9. Frozen specs are frozen.** `ZK_SPECS` holds only published specs, and
`provider` loads only those, from a caller's directory, without a compiler.
The development spec NEXT exists only as the pair `compile_next` returns,
never in the registry, and runs through the same entry points.
*Enforced by:* `provider` has no compiler dependency (dependency checker);
`next_is_not_a_frozen_v2_circuit`, `frozen_v2_loader_reads_archive_without_a_compiler`
(tests); distinct v1 and v2 `ZkSpecStruct` types (the `compile_fail`
doctest in `zk_spec.rs`).

**I10. A false statement fails before any randomness.** The prover runs
`document::parse` and both witness encoders right after `Instance::load`,
before `link::composition` and before it draws a coin. `document::parse`
checks the document's layout, type, validity and device key; the encoders
repeat natively the remaining circuit conditions that a parsed document can
fail, those that depend on the request or on the issuer's signatures.
`push_witness_hash` compares each requested value with the document's and
each `IssuerSignedItem`'s SHA-256 with its digest in the MSO.
`push_witness_sig` accepts a signature only if the key and `R = (r, y)` lie
on the curve, `r < n`, and the final accumulated point `eG + rPK - sR` of the
witness is the point at infinity, which holds exactly when `R` is the
recovered point `(e/s)G + (r/s)PK` (`signature_accepted`: six field
multiplications per signature). So another issuer key, another session
transcript (the device signature fails), an item the issuer did not sign,
and a value mismatch all end in `GeneralFailure` before sampling. The
circuits stay the acceptance rule; these checks only make the failure early.
A signature that verifies but has no witness in the affine layout (an
exceptional point) is `WitnessCreationFailure`.
*Enforced by:* the step order in `run_mdoc_prover_encoded`;
`signatures_the_circuit_rejects_fail_while_encoding`,
`attribute_items_the_issuer_did_not_sign_fail_while_encoding`,
`run_false_statements_fail_before_sampling` and
`run_next_mdoc_all_negative_cases`, which check that the generator's state
is unchanged (tests).

## Protocol

### Verifier steps

| Step | Function | Rejects with |
|---|---|---|
| 1. Request | `Request::check`: the spec version first (`ZkSpecStruct::supports_version`), then the spec's attribute count against `NEXT_MAX_ATTRIBUTES` and the count, namespace, session transcript (size, one CBOR item), `public_inputs_fit`, `circuit_supports`, `parse_pk_coordinate` (I2) | `InvalidZkSpecVersion` for the version, `AttributeNumberMismatch` for the count, `UnsupportedAttribute` for a value kind, else `InvalidInput` |
| 2. Circuits | `Instance::load` (I3: archive, IDs, public-input counts) | `CircuitParsingFailure` |
| 3. Composition | `link::composition` (I6) | `GeneralFailure` |
| 4. Public inputs | `PublicInputs::derive` (I1) | none |
| 5. Statement | `transcript::statement(&composition, &request, &public)`, then `Opened::new(&statement)` | `GeneralFailure` |
| 6. Parse | `MdocProof::read(proof, &session.geometry(), &gf2, &p256)` (I6, I7, I8) | `HashParsingFailure` |
| 7. Reduce and open | `ComposedStatement::reduce_and_authenticate(session, &proof.body)` | `GeneralFailure` |
| 8. Seal | `Unverified::checked` | `GeneralFailure` |

The prover runs steps 1 to 5 identically, with `document::parse` and both
witness encoders right after step 2 (I10), then proves and writes.

| Prover step | Function | Rejects with |
|---|---|---|
| Document | `document::parse`: at most `MAX_DOCUMENT_BYTES` = 256 KiB (Size limits), CBOR structure, MSO layout, signed `docType` equals the request's, `validFrom <= now <= validUntil`, device key type 2 (EC2) and curve 1 (P-256), canonical 32-byte coordinates on the curve | `TaggedMsoTooBig`, `MsoDecodingFailure`; a failed predicate is `GeneralFailure` |
| Hash witness | `push_witness_hash` | `NamespacesMissing`, `AttributeNotFound`, `AttributeTooLong`, `TaggedMsoTooBig`, `MsoDecodingFailure`, `WitnessCreationFailure`; a requested value that differs from the document's, or an item that differs from its MSO digest, is `GeneralFailure` |
| Signature witness | `push_witness_sig` | a signature the circuit rejects (`signature_accepted`) is `GeneralFailure`; an exceptional point or a layout drift is `WitnessCreationFailure` |
| Prove and write | `ComposedStatement::prove`, `MdocProof::write` | `GeneralFailure` |

### Messages and challenges

The schedule is the transcript design's challenge schedule, specialized to
mdoc. Hash-side elements are GF(2^128), prime-side elements P-256.
`logw_l` is the log width of layer l. The binary frontend runs the hash
circuit and the adapter fragment in one sumcheck of 20 layers (the fragment
joins at the input end); the prime frontend runs the signature circuit, 11
layers.

| # | Sender | Messages (tag) | Values | Draws that follow |
|---|---|---|---|---|
| 1 | statement | `MdocStatement` (16), `Circuit` (18) x 3, `CommitmentLayout` (19) x 2, `AdapterLayout` (22), `JointGeometry` (20), `PublicInputs` (21) x 2 | see Statement | none: the node continues |
| 2 | joint Polygero | `Commitment` (32) | Bytes(32) root | 2 coefficient vectors per field |
| 3 | witness selection | `FingerprintResponse` (33) x 2 | Elements(GF2_128, 2), Elements(P256, 2) | prime top weights (input) |
| 4 | prime sumcheck, per layer | `SumcheckRound` (48) x `logw_l`, `SumcheckCross` (49), `SumcheckClaims` (50) | Elements(P256, 2), (P256, 1), (P256, 2) | z per round; r != 0; alpha, then the next stage's weights or, at the last stage, the input assertions; after the last stage eta != 0 (input) |
| 5 | split | `SplitOpening` (64) | Elements(P256, 1): mu | conversion pair, each != 0 (input) |
| 6 | P-256 adapter | `P256AdapterQuotients` (65) | Bits(10), Bits(10) | host top weights (input) |
| 7 | binary sumcheck, per layer | as in row 4 | over GF2_128 | as in row 4, without eta |
| 8 | binary dual packing | `PackingU` (80) | Elements(GF2_128, 128) | 128 independent GF2_128 elements |
| 9 | binary dual packing | `PackingA` (81) | Elements(GF2_128, 1) | Polygero batching weights (drawn and used by the joint opening): per field, one weight per equation, then s+1 = 13 samples per batched row |
| 10 | Polygero | `PolygeroResponse` (96) x 2 | per field Elements(F, k+s = 361), Elements(F, 2k = 698) | t = 84 distinct columns out of n = 2443 |
| 11 | encoder | `Seal` (112) | Bytes: every proof byte before the seal | the seal block |

The prime participant has packing degree one, so it sends no packing
messages and has no packing boundaries (transcript I7). Every sub-protocol
here that draws begins by sending; the challenges it needs first (both top
weights, eta, the conversion pair) are `Challenge` inputs (transcript I8),
and the joint opening draws the batching weights itself, right where it
takes both fields' statements. Boundaries: the sumcheck rounds of both frontends,
plus 2 per layer, plus 7 others; the seal is not counted. For A = 1 to 4
the hash circuit has 263, 267, 272 and 275 rounds and the signature circuit
125, so the counts are 457, 461, 466 and 469.

### Verifier checks

mdoc adds no algebraic check of its own. It reduces its claim to the
composition's checks: both sumchecks against the bound public inputs, the
split identity, the adapter's two product trees, dual packing, the joint
Polygero opening, and the seal. Those are specified in the `runtime::v2::zk`,
`runtime::v2::foreign` and `runtime::v2::polygero` designs. mdoc's own checks
are the request (I2), the instance (I3) and the envelope (I7).

## Formats

### MDA7 proof

```text
; integers are little endian; elements in canonical serialization:
; GF2_128 16 bytes, P256 32 bytes
proof      := "MDA7" body seal
body       := interactive terminal
interactive:= root fp_bin fp_prime sc_prime mu quotients sc_host packing
              resp_bin resp_prime              ; in send order
terminal   := rows_bin rows_prime nonces frontier
root       := byte{32}
fp_bin     := gf{2}
fp_prime   := p{2}
sc_prime   := layer_prime{11}         ; per layer: p{2}{logw} p p{2}
mu         := p
quotients  := word word               ; MaskedWord<10>: 2 bytes, LSB first, bits 10..15 zero
sc_host    := layer_host{20}          ; per layer: gf{2}{logw} gf gf{2}
packing    := gf{128} gf              ; U, then A
resp_F     := F{k+s} F{2k}            ; H, then Z
rows_F     := F{t} per physical row   ; u, m, witness rows, f*, in query order
nonces     := byte{32}{t}             ; in sampled-column order
frontier   := u64(f) byte{32}{f}      ; its count, then its digests; the end of the body
seal       := byte{32}                ; first PRF block of the seal node
```

| Part | Bytes |
|---|---:|
| magic, root, fingerprints | 4 + 32 + 32 + 64 |
| prime sumcheck | 32 x sum over 11 layers of (2 logw + 3) |
| mu, quotients | 32 + 4 |
| binary sumcheck | 16 x sum over 20 layers of (2 logw + 3) |
| packing | 16 x 129 = 2064 |
| Polygero responses | 48 x (3k + s) = 50,832 |
| Polygero rows | t x (16 x binary rows + 32 x prime rows) |
| nonces | 32t = 2688 |
| frontier count, frontier, seal | 8, 32f, 32 |

The body has no nested magic and no copy of any setup value (transcript
I11). Every length except the frontier's follows from the absorbed
geometry, so the body's only integer is the frontier count `f`. The reader
reads `f` right after the nonces and requires the proof to be exactly
`4 + B(g) + 8 + 32f + 32` bytes with `f <= 84 * 13 = 1092`, before decoding
anything (proto I3); the Merkle check then decides whether the frontier is
the right set of nodes.

### Circuit archive

A v2 circuit archive is a single zstd frame (compression level
`K_ZSTD_LEVEL` = 16, at most `MAX_ARCHIVE_BYTES` compressed, window at most
`MAX_METADATA_BYTES`) holding one LFA2 archive (`core::proto::v2::archive`)
and nothing after it. For mdoc it has `circuit_version` 12 and exactly two
entries, `sig` then `hash`; the combined ID is SHA-256 of their IDs in that
order. A stored archive is named `<combined hash hex>.lfa2`, in
`src/mdoc/artifacts/circuits` for the repository's own artifacts
(`provider::materialize`, `artifacts::load_circuit_lfa2`), or in a caller's
directory (`provider::materialize_from`).

### NEXT cache

`development_provider::{write_next, read_next}` store a NEXT spec with its
archive:

```text
next  := "MDOCNEXT2" combined_hash(32) u64{6} archive
u64{6} := version num_attributes k n s t
```

A bundle with any other marker is rejected as not a NEXT bundle.

`read_next` accepts only version 12, 1 to 4 attributes and a valid Polygero
geometry, then checks the archive against the spec as `from_compressed`
does. `compile_next` sets the profile to `MDOC_JOINT_PROFILE` =
(349, 12, 2443, 84).

## Rust API

```rust
// Public: mdoc::v2
pub struct RequestedAttribute { pub namespace_id: Vec<u8>, pub id: Vec<u8>, pub cbor_value: Vec<u8> }
pub fn req_attr(namespace: impl AsRef<[u8]>, id: impl AsRef<[u8]>, value: impl AsRef<[u8]>)
    -> RequestedAttribute;

pub struct ZkSpecStruct {
    pub combined_hash: [u8; 32],
    pub num_attributes: usize,
    pub version: usize,
    pub polygero: PolygeroParameters,        // k, n, s, t; shared by both fields
}
impl ZkSpecStruct {
    pub fn supports_version(&self) -> bool;
    pub const fn config(&self) -> PolygeroConfig;   // the one profile
}
pub const SYSTEM_ID: &str = "longfellow-libzk-v2";
pub const ZK_SPECS: [ZkSpecStruct; NUM_ZK_SPECS];           // published, frozen (I9)
pub fn find_zk_spec(system: &str, hash: &[u8; 32]) -> Option<&'static ZkSpecStruct>;

pub fn run_mdoc_prover(spec: &ZkSpecStruct, circuits: &[u8], mdoc: &[u8], pkx: &str, pky: &str,
    transcript: &[u8], attrs: &[RequestedAttribute], now: &str, doc_type: &str)
    -> Result<Vec<u8>, MdocProverErrorCode>;                 // OS randomness
pub fn run_mdoc_prover_inner<R: PrivateRandom>(/* same */, rng: &mut R)
    -> Result<Vec<u8>, MdocProverErrorCode>;
pub fn run_mdoc_verifier(spec: &ZkSpecStruct, circuits: &[u8], pkx: &str, pky: &str,
    transcript: &[u8], attrs: &[RequestedAttribute], now: &str, doc_type: &str, proof: &[u8])
    -> Result<VerifiedProof, MdocVerifierErrorCode>;          // I7: only from the seal

pub mod provider {
    pub struct ProvidedCircuit { /* spec and archive, kept together */ }
    pub fn materialize_from(directory: &Path, version: usize, num_attributes: usize)
        -> Result<ProvidedCircuit, MdocProverErrorCode>;
    pub fn registered_versions_and_attrs() -> Vec<(usize, usize)>;
}
pub fn decompress_circuits(compressed: &[u8], p256: &P256Field, gf2: &Gf2_128Field)
    -> Result<(Circuit<P256Field>, Circuit<Gf2_128Field>), String>;   // IDs recomputed

pub struct MdocProof<F1, F2> { pub body: ComposedProof<2, F1, 4, F2, [MaskedQuotient; 2]> }
impl MdocProof<F1, F2> {
    pub fn read<'a>(bytes: &'a [u8], g: &Bound<'_, ComposedGeometry>, f1: &F1, f2: &F2)
        -> Result<Unverified<'a, Self>, String>;              // I6, I7, I8
    pub(crate) fn write(&self, g: &ComposedGeometry, f1: &F1, f2: &F2, transcript: Transcript)
        -> Result<EncodedProof, String>;                      // seals (transcript I10); prover only
}

// Internal: mdoc::runtime::v2
pub(super) struct Request<'a> { /* spec, parsed issuer key, checked strings and attributes */ }
impl<'a> Request<'a> {
    pub(super) fn check(spec: &'a ZkSpecStruct, pkx: &str, pky: &str, transcript: &'a [u8],
        attrs: &'a [RequestedAttribute], now: &'a str, doc_type: &'a str, p256: &P256Field)
        -> Result<Self, RequestError>;                        // I2: the only constructor
}
pub(super) struct Instance { signature: Circuit<P256Field>, hash: Circuit<Gf2_128Field> }
impl Instance {
    pub(super) fn load(request: &Request<'_>, compressed: &[u8], p256: &P256Field,
        gf2: &Gf2_128Field) -> Result<Self, String>;          // I3: the only constructor
    pub(super) fn signature(&self) -> &Circuit<P256Field>;
    pub(super) fn hash(&self) -> &Circuit<Gf2_128Field>;
}
pub(in crate::mdoc::runtime::v2) struct PublicInputs { hash: Vec<bool>, signature: Vec<P256Element> }
impl PublicInputs {
    pub(in crate::mdoc::runtime::v2) fn derive(request: &Request<'_>, p256: &P256Field)
        -> Self;                                              // I1: the only constructor
}
// link.rs and transcript.rs
pub(super) fn composition(spec: &ZkSpecStruct, signature: &'a Circuit<P256Field>,
    hash: &'a Circuit<Gf2_128Field>, domains: (&'a DH, &'a DS))
    -> Result<Composition<'a, DH, DS>, String>;               // I6
pub(super) struct Identity<'a> { session: &'a [u8], spec: &'a ZkSpecStruct }  // MdocStatement (16)
pub(super) type MdocStatement<'s, DH, DS> = ComposedStatement<'s, .., Identity<'s>>;
```

Both roles share the setup and differ only after the statement exists:

```rust
let request = Request::check(spec, pkx, pky, transcript, attrs, now, doc_type, &p256)?;
let instance = Instance::load(&request, circuits, &p256, &gf2)?;
let composition = link::composition(request.spec(), instance.signature(), instance.hash(), domains)?;
let public = PublicInputs::derive(&request, &p256);
let statement = transcript::statement(&composition, &request, &public)?;

// prover (document::parse and the encoders run right after Instance::load, I10)
let parsed = document::parse(mdoc, &request, &p256)?;
let (wh, ws) = (push_witness_hash(&request, &parsed)?, push_witness_sig(&p256, .., &request, &parsed)?);
let (body, t) = ComposedStatement::prove(Opened::new(&statement), wh, ws, rng)?;
MdocProof { body }.write(statement.geometry(), &gf2, &p256, t)

// verifier
let mut session = Opened::new(&statement);
let proof = MdocProof::read(bytes, &session.geometry(), &gf2, &p256)?;
let t = ComposedStatement::reduce_and_authenticate(session, &proof.body)?;
proof.checked(t)
```

The statement holds the public inputs, so a role cannot prove or verify
against inputs other than those it absorbed (transcript I2). `MdocProof::write`
consumes the transcript, so a proof is sealed once. `checked` consumes the
transcript and the `Unverified` proof, so acceptance has one path.
`ComposedStatement::reduce_and_authenticate` stops before the seal and is
crate-private, so `run_mdoc_verifier` is the only public mdoc verifier. The
prover and verifier modules deny `print_stdout`, `print_stderr` and
`dbg_macro`, because evaluation failures can expose private inputs.

### Error codes

`MdocProverErrorCode` and `MdocVerifierErrorCode` keep the numeric values of
the C library's codes. The v2 entry points return:

| Failure | Prover | Verifier |
|---|---|---|
| Unsupported spec version | `InvalidZkSpecVersion` (8) | `InvalidZkSpecVersion` (10) |
| Attribute count differs from the spec | `InvalidInput` (2) | `AttributeNumberMismatch` (9) |
| Any other request-shape failure: a spec attribute count outside 1 to `NEXT_MAX_ATTRIBUTES`, namespaces differ, a field out of range or malformed (including an empty document type), a session transcript longer than 64 KiB or not one CBOR item, a bad issuer key | `InvalidInput` (2) | `InvalidInput` (7) |
| Unsupported attribute value | `UnsupportedAttribute` (36) | `UnsupportedAttribute` (11) |
| Archive or circuit rejected: `Instance::load` (I3: archive, IDs, public-input counts) | `CircuitParsingFailure` (3) | `CircuitParsingFailure` (1) |
| Proof does not parse | | `HashParsingFailure` (3) |
| Composition, proving, verification or seal fails | `GeneralFailure` (6) | `GeneralFailure` (5) |

A request failure gets the same named error in both roles; the numeric
codes differ. The only exception is the attribute count, which only the
verifier's enum names. Document and witness failures are listed under
Prover steps. The provider returns `InvalidZkSpecVersion` for an unknown
spec, `GeneralFailure` for a missing file, and `CircuitParsingFailure` for a
malformed archive or one whose metadata does not match the spec, as
`Instance::load` does.

## Mistakes the design prevents

| Mistake | What stops it |
|---|---|
| Prover and verifier computing `e2` differently, or the prover taking it from the document | I1: one derivation from the request |
| Two requests that differ in an encoded field but have the same public inputs (a truncated identifier, a namespace missing from the encoding) | I2: `Request::check` before encoding |
| Loading circuits, parsing a document or sampling for an invalid request | I2: those steps take a `Request` |
| Verifying against circuits the spec does not name | I3: combined hash checked; the statement absorbs it and every circuit ID |
| An archive payload edited under its original ID | I3: IDs recomputed on load |
| A spec whose attribute count disagrees with its hash circuit | I3: public input counts checked at load |
| Shared bits at different offsets in the two circuits or witnesses | I4: one table, checked by compilers and encoders |
| The hash predicate reading R, the pads or the leaves | I5: natural width and prefix reads; Lean separation |
| Parsing the proof with a geometry other than the absorbed one | I6: the reader takes `Bound` geometry |
| A proof from another session or document type | the session transcript is in `MdocStatement`, and both enter `e2` |
| Two (session transcript, document type) pairs with the same `e2` preimage | I2: the session transcript must be one CBOR item |
| A spec with different profiles for the two fields | one `polygero` field in `ZkSpecStruct` |
| Trailing or missing bytes, a nested magic, a duplicated setup value | I7 |
| Treating a parsed but unsealed proof as accepted | I7: `VerifiedProof` only from the seal |
| A NEXT archive presented as a frozen spec | I9 |
| A v2 spec passed to the v1 entry points | distinct types; `compile_fail` doctest |
| Public-input order drifting between the compiler and `push_input_hash` | honest proofs fail; the end-to-end tests in `mdoc/runtime/tests/next.rs` |
| Drawing coins for a statement the circuits reject | I10: native checks before sampling |
| Logging a private witness on failure | `deny(clippy::print_stdout, print_stderr, dbg_macro)` |

## Soundness and zero knowledge

### What each check is for

| Check | Purpose | Model |
|---|---|---|
| Spec version, combined hash, recomputed IDs | the circuits are the trusted ones the spec names | premise: trusted application circuits and archives |
| `Request::check` | the public inputs are canonical: no truncation, every length encoded; with the statement's spec and session they bind the request | outside the model (request encoding) |
| Statement | Fiat–Shamir binds the instance and every public input before the commitment | Rust, not Lean (transcript I3): the geometry messages are written from the participants, and the parsing geometry is a copy derived from them; tests check that the absorbed geometry equals the parsing geometry, that the statement comes first, every message's schema, and the golden pins; the Lean model takes the statement messages after the combined hash as fixed setup bytes |
| Composition | extraction of one witness pair satisfying both circuits at the requested public inputs | `CanonicalRuntime.decoded_true_at_request`, `MdocWitness.valid_at_request` |
| Exact envelope and seal | the accepted bytes are one complete canonical proof | `ProofBodyCodec`, `ProofOutput` |

### Soundness

`Mdoc.Soundness.averaged_ratio_le` (`formal/lfzk-v2/LfzkV2/Current/Mdoc/Soundness.lean`)
bounds the probability that the verifier accepts and the extractor fails to
return a witness satisfying the ordinary hash constraints and the signature
circuit at the requested public inputs. For an adversary with at most
`Q < 2^127` distinct SHA queries, with `q = 2^128`, the bound is the exact
`LfzkV2.Current.Soundness.Rate7.failureBound`:

```text
c*Q/q + (1 - c*(q-1)/(2q)) * (1 - (1 - 2/(q-1))^Q) + (C(Q,2) + r + 15)/q^2
```

`c = 1.00000123121...` is the Polygero coefficient for `(349, 12, 2443, 84)`
and `r` the boundary count, at most 469, so `r + 15 = 484 < 2^10`.
`averaged_nonvacuous` gives a strict cap of 0.97, and
`averaged_mdoc_approximation` the all-`Q` form
`Q*2^-127 + Q^2*2^-257 + 2^-246`. `MdocRoundShape.rounds_eq` derives `r`
for each supported shape, and `check_mdoc_round_shapes` checks it against the
Rust compiler. The hash/adapter separation is a theorem
(`HashSeparation`), not a premise.

The bound holds for the instance the statement fixes. That the statement
binds the instance (transcript I3) is enforced by Rust: the writers derive
every statement value from the same objects the verifier uses, and tests
check that the absorbed geometry equals the parsing geometry, that the
statement precedes every prover message, every message's schema, and the
golden pins of the standalone transcript and the mdoc first node. The Lean
model takes the statement messages after the combined hash as fixed setup
bytes, so Lean does not prove I3.

### Zero knowledge

`Mdoc.ZeroKnowledge.statClose` (`.../Mdoc/ZeroKnowledge.lean`) bounds the
statistical distance between the real view and a witness-free simulation by
`(Qpre + Qpost)/2^256`, at most `2^-128` for `Qpre + Qpost <= 2^128`
(`statClose_at_query_budget`). `Mdoc.VerifierPrivacy.acceptance_probability`
specializes it to the runtime verifier's decision. The proof needs the
prover's coins (R, the quotient pads, Polygero masks and nonces) fresh and
uniform: `run_mdoc_prover` draws them from the operating system, and
`run_mdoc_prover_inner` requires the same of its generator. R makes `mu`
uniform; each quotient pad is two fresh bytes, of which the high six bits are
discarded (`FrontendAdapterBits.rawOtpEquiv`). `Mdoc.Completeness` covers
honest acceptance.

### What the prover leaves to its host

The zero-knowledge statement covers the proof the prover returns. It does
not cover what a failed run reveals, nor the prover's memory.

- **Error codes and time to failure.** When the prover fails, its error
  code and its time to failure describe the document: whether it is
  well-formed, whether it has the requested namespace and attributes,
  whether their values match, whether the issuer key and the session
  transcript match its signatures. I10 makes every such failure happen
  before sampling, but parsing and the two encoders, which run in turn, still
  take different times. A wallet must expose neither the code nor the
  timing to the relying party: it reports every failure as one refusal, at
  a time that does not depend on which check failed.
- **Memory.** The prover does not wipe the witness, the parsed document, the
  masks, the nonces or the pads after use; freed memory keeps them until it
  is reused. Memory hygiene (wiping, process isolation, swap and core-dump
  policy) is the host process's responsibility.

### Trust boundary

The proofs hold at whatever public vectors the statement carries. These are
trusted or reviewed, not proved:

- **The verifier's inputs.** The verifier chooses the issuer key (its trust
  list), the session transcript, the document type, the time and the
  requested attributes. The protocol proves facts relative to them.
- **The request encoding.** `compute_transcript_hash`, `push_input_hash`
  and `parse_pk_coordinate` turn the request into public inputs (formal
  README, "Request encoding"). Binding to the session and to the requested
  values rests on this reviewed and tested Rust code.
- **The circuits.** Extraction returns a witness for the circuits the spec
  names, not for an independent ISO 18013-5 specification. The hash circuit
  proves that the namespace text occurs in the signed MSO, not that the
  selected digests belong to that namespace's map. It checks the time digits'
  order, not calendar validity. The signature circuit requires `R.x < n` and
  a nonzero key x-coordinate.
- **The spec.** Whoever publishes a `ZkSpecStruct` vouches for its circuits
  and its Polygero profile; `zk_tool check-profiles` and `certify-hahn`
  certify the profile.
- **The implementation.** Rust is checked against Lean by review, tests and
  the source audit, not by mechanized refinement. Witness preparation and
  field inversion are variable time.

## Open questions

None.
