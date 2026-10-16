# mdoc-zk

`mdoc_zk` is the application layer of Longfellow ZK for
ISO 18013-5 mobile documents
(mDL / mdoc). Given an issuer-signed mdoc, it lets a holder prove in zero
knowledge that:

* the Mobile Security Object (MSO) carries a valid ECDSA P-256 issuer
  signature under a public issuer key,
* the device key embedded in the MSO signed the current session transcript
  (device authentication),
* the MSO is valid at a verifier-supplied timestamp (`validFrom ≤ now ≤
  validUntil`) and has the expected `docType`,
* one or more requested attributes (e.g. `age_over_18` or `birth_date`) are
  present in the MSO's `valueDigests` and satisfy the requested relation
  (`Eq`, or ISO-8601 date `Le` / `Ge` in v8), or that a relying-party
  pseudonym `SHA-256(pnym_seed || context)` is derived from a signed 32-byte
  `pnym_seed` attribute in the MSO,

without revealing anything else about the document.

The statement is split across two circuits over two different fields and tied together by a lightweight MAC:

| Circuit | Field | Proves | Ligero encoding |
|---|---|---|---|
| **Signature** (`MdocSignature`) | P‑256 base field | Two ECDSA verifications (issuer over MSO digest `e`, device over transcript digest) | FFT Reed–Solomon over `Fp2` |
| **Hash** (`MdocHash`) | GF(2¹²⁸) | SHA‑256 of the MSO equals `e`; docType / validity / deviceKey / valueDigests structure; per‑attribute `IssuerSignedItem` parsing + SHA‑256 (or `PnymAttributeVerifier` for pseudonyms) | LCH14 Reed–Solomon over the GF(2¹⁶) subfield |

Both circuits take the values `issuer_sig_e`, `device_pk.x`, `device_pk.y` as
*private* witnesses and assert `tag + ap = av · msg` in GF(2¹²⁸) for each of
them. The prover commits to both witnesses (including the random pads `ap`)
before the challenge `av` is derived from the Fiat–Shamir transcript, so the
three MAC tags published in the proof bind the two circuits to the same hidden
values.

---

## Directory layout

```
mdoc_zk/
├── proto/           mdoc-zk-proto          Constants shared by every other crate (no deps)
├── testcases/       mdoc-zk-testcases      Static mdoc test vectors (no deps)
├── artifacts/       mdoc-zk-artifacts      Pinned circuit archives + prior proofs for old versions
├── circuits/        mdoc-zk-circuits       Circuit definitions, host-side CBOR/mdoc parser
├── compile/         mdoc-zk-compile        Turns circuit definitions into serialized LFA2 archives
├── runtime/         mdoc-zk-runtime        Prover, verifier, proof format, version registry
├── prover_only/     mdoc-zk-prover-only    Minimal binary that links only the prover path
└── verifier_only/   mdoc-zk-verifier-only  Minimal binary that links only the verifier path
```


## Crates

### `proto/` — shared constants

A dependency-free leaf crate so that both the compile side and the runtime
side agree on the same numbers.

| File | Contents |
|---|---|
| [`config.rs`](proto/src/config.rs) | Bit-plucker packing widths (`K_SHA_BIT_PLUCKER`, `K_HASH_V8_BIT_PLUCKER`, …), `K_ATTR_LEN_BITS`, `K_ZSTD_LEVEL` |
| [`hash/constants.rs`](proto/src/hash/constants.rs) | MSO geometry (`K_MAX_SHA_BLOCKS = 40`, `K_MSO_PREIMAGE_LEN`) and the CBOR byte patterns the hash circuit searches for (`docType`, `validFrom`, `validUntil`, `deviceKeyInfo`, `valueDigests`, COSE_Sign1 prefix) |
| [`mso_attribute/constants.rs`](proto/src/mso_attribute/constants.rs) | `IssuerSignedItem` geometry parameterized by `K_MAX_ATTR_SHA_BLOCKS` (`max_attr_cbor_len(K_MAX_ATTR_SHA_BLOCKS) = 119`, `attr_preimage_len(K_MAX_ATTR_SHA_BLOCKS) = 128`, `min_attr_item_cbor_len`, `K_ATTR_RANDOM_NONCE_LEN = 16`), key patterns (`digestID`, `random`, `elementIdentifier`, `elementValue`), comparison operator codes (`K_OP_*`), and pseudonym geometry (`K_PNYM_SEED_LEN = 32`, `K_PNYM_CONTEXT_MAX = 80`, `K_PNYM_SHA_BLOCKS = 2`) |

### `testcases/` — test vectors

[`TestDataStatic`](testcases/src/lib.rs) bundles an issuer public key
(`pkx`/`pky`), a session `transcript`, a `now` timestamp, a `doc_type`, and
the raw `mdoc` bytes. [`vectors.rs`](testcases/src/vectors.rs) contains ~30
real-world mdocs (`TEST_DATA`, `PLUS_18_MDOC_*`, `EUAV_AGE_OVER_18_MDOC_*`,
`AADHAAR_*`, `DHS_COMPLIANCE_*`, …) used by every test and benchmark in this
directory.

### `artifacts/` — pinned circuits and proofs

Binary fixtures that make old proof versions verifiable forever and let the
test-suite check bit-exact backward compatibility.

```
artifacts/
├── circuits/<combined_hash>        original zstd-compressed LFC1 stream (as shipped by the C++ prover)
├── circuits/<combined_hash>.lfa1   same circuits re-wrapped in an LFA1 archive
├── circuits/<combined_hash>.lfa2   same circuits re-encoded in the compact LFC2/LFA2 format
├── proofs/<combined_hash>.bin                 proof previously produced for this circuit
├── proofs/<combined_hash>_hash_witness.bin    witness fed to the hash circuit for that proof
└── proofs/<combined_hash>_sig_witness.bin     witness fed to the signature circuit for that proof
```

`<combined_hash>` is the 32-byte identifier that external callers use to
select a circuit (see `ZK_SPECS` below). [`src/lib.rs`](artifacts/src/lib.rs)
exposes `load_circuit_lfa1/lfa2`, `load_prior_proof`,
`load_prior_{sig,hash}_witness` and `all_circuit_hashes()` (versions 5, 6 and
7 × 1–4 attributes). Files are read relative to `CARGO_MANIFEST_DIR`.

### `circuits/` — circuit definitions

The circuit definition is generic
over a `L: compile_logic::LogicIO`, so the very same code is instantiated with
`CompilerLogic` to emit a circuit and with `EvalLogic` to evaluate it on
concrete values in tests.

```
circuits/src/
├── lib.rs            re-exports, CURRENT_VERSION (= 8)
├── traits.rs         MdocHashCompileField / MdocSigCompileField (+ *RuntimeField under `testonly`):
│                     trait bundles describing what a field must support for each circuit
├── cbor/             HOST-SIDE (not in-circuit) CBOR tooling
│   ├── parse.rs        generic CBOR parser  (CborParser, CborValue, CborElement)
│   ├── mdoc.rs         parse_mdoc(): DeviceResponse → ParsedMdoc (MSO bytes, sig (r,s,e),
│   │                   device key, field offsets, per-attribute ParsedAttr + FieldLocator);
│   │                   compute_transcript_hash() for DeviceAuthentication;
│   │                   pnym_seed_of(), compute_pseudonym(), encode_pnym_cbor_value()
│   ├── cbor_encode.rs  tiny CBOR encoder helpers (encode_cbor_string, …)
│   ├── constants.rs    COSE_Sign1 / DeviceAuthentication header bytes
│   └── test_utils.rs   parse_test_data(): TestDataStatic → (issuer_pk, ParsedMdoc, now)
├── cbor_decoder/     IN-CIRCUIT decoder for a single CBOR head byte (major type, length class)
├── mso_attribute/    IN-CIRCUIT verifiers for IssuerSignedItems (AttributeVerifier + pnym::PnymAttributeVerifier)
├── hash/             IN-CIRCUIT MdocHash — the GF(2^128) circuit
└── signature/        IN-CIRCUIT MdocSignature — the P-256 circuit
```

#### The four-file convention

Each in-circuit module (`cbor_decoder`, `mso_attribute`, `hash`, `signature`)
follows the same layout as the generic circuits in `rust/circuits/*`:

| File | Role | Types |
|---|---|---|
| `circuit.rs` | The constraint logic. Defines the wire-level input structs and the `assert_*` methods that produce `L::Assertions`. | `Given<L>`, `Derived<L>`, `MdocHash` / `MdocSignature` / `AttributeVerifier` / `PnymAttributeVerifier` / `CborByteDecoder` |
| `allocate.rs` | Allocates fresh input wires from a running position counter, one wire per bit. Used by the circuit-level tests; the production (packed) layout lives in `compile/`. | `allocate_given`, `allocate_derived` |
| `concrete.rs` | Plain-Rust mirror of the wire structs plus the functions that fill them from a `ParsedMdoc`. | `ConcreteGiven`, `ConcreteDerived`, `HashInput`, `SignatureInput`, `given()`, `derived()`, `hash_input_of_parsed_mdoc()`, `pnym_hash_input_of_parsed_mdoc()`, `compute_mac_tags()` |
| `evaluate.rs` *(feature `testonly`)* | Lifts `Concrete*` values into constant wires so a circuit can be run directly under `EvalLogic`. | `evaluate_given`, `evaluate_derived` |

"Given" values are inputs (public or private) supplied by the prover;
"Derived" values are auxiliary witnesses (SHA‑256 round state, ECDSA
intermediate points, …) that the prover precomputes so that the circuit only
has to *check* them.

`MdocHash::assert_valid_presentation_and_macs` is the root assertion of the
hash circuit; it fans out to `assert_mso_sha256_hash`, `assert_mso_doc_type`,
`assert_mso_validity`, `assert_mso_device_key`, `assert_mso_value_digests`,
`assert_attributes` (one `AttributeVerifier::assert_attribute` per disclosed
regular attribute), optional `assert_pnym` (`PnymAttributeVerifier::assert_pnym_attribute`
when `pnym == true`), and `assert_mac_tags`. `MdocSignature::assert_signatures_and_macs`
is the root of the signature circuit.

The named assertion paths (e.g.
`assert_valid_presentation_and_macs/assert_valid_presentation/assert_mso_doc_type/cbor_header/...`)
are what the compiler's debug symbols report, and the corruptor tests pin
them.

### `compile/` — producing circuit archives

Instantiates the definitions in `circuits/` with the real compiler and
fixes the production wire layout.

| File | Purpose |
|---|---|
| [`allocator.rs`](compile/src/allocator.rs) | `WireAllocator`: allocates wires and *bit-plucked* packed inputs (several bits per field element, unpacked in-circuit by `circuits-bit-plucker`). |
| [`allocate_hash.rs`](compile/src/allocate_hash.rs) / [`allocate_sig.rs`](compile/src/allocate_sig.rs) | **The authoritative input layout** of each circuit: order of public inputs, position of the public/private boundary (`pub_inputs_count`) and of the subfield boundary. `runtime/src/concrete/modern/*` must push values in exactly this order. |
| [`generate_hash.rs`](compile/src/generate_hash.rs) / [`generate_sig.rs`](compile/src/generate_sig.rs) | Run `compile_compiler::compile`, segment the circuit, print geometry, and call `runtime_ligero::optimize_geometry` to pick `block_enc` for the requested `LigeroProfile { rateinv, nreq }`. |
| [`lib.rs`](compile/src/lib.rs) | `compile_circuits(num_attrs, pnym, hash_profile, sig_profile)` → one LFA2 archive with a `"sig"` and a `"hash"` entry, tagged with `CURRENT_VERSION`; `compile_all_circuits` compiles the 3 v8 circuits `[(1, false), (4, false), (0, true)]` in parallel. |

### `runtime/` — prover and verifier

```
runtime/src/
├── lib.rs           public surface; re-exports mdoc_zk_{circuits,compile,proto}
├── zk_spec.rs       ZkSpecStruct + ZK_SPECS (v5/v6/v7, pinned) + CURRENT_ZK_SPECS (v8):
│                    combined_hash ↔ (version, num_attributes, pnym, Ligero configs)
├── provider.rs      materialize(version, nattrs, pnym) → ProvidedCircuit;
│                    select_current_spec(num_regular, pnym) → &'static ZkSpecStruct
│                    (v < CURRENT: load from artifacts/;  v == CURRENT: compile on the fly
│                     and check the Ligero configs match the spec)
├── prover.rs        run_mdoc_prover[_inner][_ext]: parse mdoc → resolve pnyms / check predicates
│                    → pad 2..=3 attrs to 4 → build witnesses → commit both circuits
│                    → draw `av` → compute MACs → prove both → serialize
├── verifier.rs      run_mdoc_verifier[_inner]: validate request → pad 2..=3 attrs to 4
│                    → rebuild public inputs → verify both proofs
├── proto.rs         MdocProof / MdocProofGeometry wire format
│                    (6 × u128 MAC tags ‖ hash proof ‖ signature proof);
│                    decompress_circuits(): reads zstd LFA2 archives *or* legacy LFC1 streams
├── mac.rs           generate_mac_ap(), push_macs() (modern + legacy tag computation)
├── concrete/        assignment of field elements to wires
│   ├── builder.rs     AssignmentBuilder: push bits / bytes / plucked V8·V32·V256 / nat / u128
│   ├── modern/        version ≥ 8 layouts  (public.rs = public inputs, private.rs = witness)
│   └── legacy/        version 5–7 layouts  (kept so old circuits remain provable)
├── attribute.rs     AttributeOp { Eq, Le, Ge, Pnym }, RequestedAttribute { namespace_id, id, cbor_value, op, context }
├── utils.rs         req_attr(), req_attr_le(), req_attr_ge(), req_pnym(), pad_request_attrs(),
│                    bind_pnym_response(), attr_encoding_fits(), same_namespace(),
│                    parse_pk_coordinate(), circuit_supports(), circuit_supports_comparison()
├── error.rs         MdocProverErrorCode / MdocVerifierErrorCode (stable numeric codes)
└── bin/convert_circuits.rs   re-encodes artifacts/circuits/* into .lfa1 / .lfa2
```

The version switch is centralised: `concrete::push_{witness,input}_{hash,sig}`
and `mac::push_macs` dispatch on `version >= 8` to `modern` or `legacy`.

---

## v8 Extensions: Comparisons & Pseudonyms

Version 8 (`CURRENT_VERSION = 8`) defines 3 circuit pairs in [`CURRENT_ZK_SPECS`](runtime/src/zk_spec.rs).
Each pair bundles the shared P-256 `MdocSignature` circuit with a $\mathrm{GF}(2^{128})$
`MdocHash` circuit and is identified by `combined_hash = SHA-256(sig_circuit_id ‖ hash_circuit_id)`:

| Circuit `(num_attributes, pnym)` | Combined Circuit ID (`combined_hash`) | Hash Circuit ID ($\mathrm{GF}(2^{128})$) | Sig Circuit ID ($\mathbb{F}_{p_{256}}$) | What It Does |
|---|---|---|---|---|
| `(1, false)` | `296fde1f84a185cb9a53cc6fa6defcdfc79fce983303be3d35ed82e7d539e3e7` | `e02f28f1ff71ddafcb9b5a874fff56a588d8897482c343ff2f81dcb8fdb0540a` | `b6c47c2d13f1b7e9c8d412fbcbbf3041cf2b01808b5a8af750f7c44d3fc65daf` | Verifies MSO hash, docType, validity timestamps, device key, namespace `valueDigests`, and **1 disclosed attribute** with `Eq`, `Le`, or `Ge` |
| `(4, false)` | `a95054f45c475263634e1bd721ab08c0b26a80c0ce7d2a0e681c11fb769fc8e6` | `21c7a0c9e35c0bed6b023e46c0ae92559989151d893480a72f40561803f3e421` | `b6c47c2d13f1b7e9c8d412fbcbbf3041cf2b01808b5a8af750f7c44d3fc65daf` | Verifies MSO and **2, 3, or 4 disclosed attributes** with `Eq`, `Le`, or `Ge` (2- and 3-attribute requests are deterministically padded to 4 slots via `pad_request_attrs`) |
| `(0, true)` | `5d7ba0120c56792fd6e46b7aeec6f1cbc9dd253c97291d5d030a30f846841a33` | `1b9e7ed9ea2033dbc108b93d31e60c229da93b8cb949a0cbfa7dd631b8190e41` | `b6c47c2d13f1b7e9c8d412fbcbbf3041cf2b01808b5a8af750f7c44d3fc65daf` | Verifies MSO and **1 relying-party pseudonym** `H = SHA-256(pnym_seed ‖ context)` derived from an issuer-signed 32-byte `pnym_seed` attribute and a public `context` (1..=80 bytes) |


### Circuit Size (Depth & Quads) and Prover/Verifier Speed

| Component / Circuit | Field | Depth (`L` layers) | Quad Terms (`T`) | Wires (`W`) | Inputs (`nin` / `npubin`) | Ligero Witnesses / Quads | `block_enc` (`nrow`) | Archive (`.lfa2` zstd-16) | Proof Size | Prover Time (release) | Verifier Time (release) |
|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---:|---:|
| `MdocSignature` *(shared by all v8)* | $\mathbb{F}_{p_{256}}$ | 21 | 276,481 | 179,677 | 3,941 / 707 | 4,337 / 21 | 4,445 (18) | *(bundled)* | *(bundled)* | *(bundled)* | *(bundled)* |
| `v8_1attr` (`(1, false)` Hash + Sig) | $\mathrm{GF}(2^{128})$ | 22 | 6,037,372 | 3,206,291 | 73,813 / 633 | 74,470 / 22 | 5,255 (171) | 308,092 B | 344,324 B | ~215.9 ms | ~114.0 ms |
| `v8_4attr` (`(4, false)` Hash + Sig) | $\mathrm{GF}(2^{128})$ | 22 | 7,142,545 | 3,796,418 | 85,741 / 1,851 | 85,232 / 22 | 5,246 (195) | 363,530 B | 352,068 B | ~239.5 ms | ~124.6 ms |
| `v8_0attr_pnym` (`(0, true)` Hash + Sig) | $\mathrm{GF}(2^{128})$ | 20 | 6,293,784 | 3,340,760 | 77,486 / 838 | 77,900 / 20 | 5,264 (178) | 316,348 B | 344,388 B | ~220.6 ms | ~115.9 ms |

*(Timings measured via `cargo bench -p mdoc-zk-runtime --bench mdoc_zk_bench_current` on Apple Silicon in release mode; Ligero profile: `rateinv = 7`, `nreq = 132`, Merkle path length `13`.)*

#### Comparison: v8 with `Le`/`Ge` vs. Standard v8 (`Eq`-only)

Adding `Le`/`Ge` date comparisons to `AttributeVerifier` adds `+2` public input bits (`op`), `+3,427` wires, and `+5,465` quad terms per attribute slot, and `+2` sumcheck layers (`L = 20 -> 22`) for the 64-byte equality AND-tree reduction and `Memcmp::leq` multiplexer. Because the extra Ligero witnesses (`+38` for 1-attr, `+62` for 4-attr) and `+2` quad constraints fit within the existing Ligero tableau dimensions (`nrow = 171`, `block_enc = 5,255` for 1-attr; `nrow = 195`, `block_enc = 5,246` for 4-attr), **Ligero tableau size and prover/verifier runtime are unchanged** (within `< 0.3%` measurement noise):

| Metric (`MdocHash` + Bundled Proof) | `v8_1attr` Standard (`Eq`-only) | `v8_1attr` (`Eq`/`Le`/`Ge`) | 1-Attr Delta | `v8_4attr` Standard (`Eq`-only) | `v8_4attr` (`Eq`/`Le`/`Ge`) | 4-Attr Delta |
|---|---:|---:|---:|---:|---:|---:|
| Combined Circuit ID | `5a893815…9291` | `296fde1f…e3e7` | — | `c73b6342…6cd6` | `a95054f4…c8e6` | — |
| Hash Circuit ID | `fb41f450…5180` | `e02f28f1…540a` | — | `564a2080…c67c` | `21c7a0c9…e421` | — |
| Depth (`L` layers) | 20 | 22 | **+2 (+10.0%)** | 20 | 22 | **+2 (+10.0%)** |
| Quad Terms (`T`) | 6,031,907 | 6,037,372 | **+5,465 (+0.09%)** | 7,120,691 | 7,142,545 | **+21,854 (+0.31%)** |
| Wires (`W`) | 3,202,864 | 3,206,291 | **+3,427 (+0.11%)** | 3,782,716 | 3,796,418 | **+13,702 (+0.36%)** |
| Inputs (`nin` / `npubin`) | 73,811 / 631 | 73,813 / 633 | **+2 / +2** | 85,733 / 1,843 | 85,741 / 1,851 | **+8 / +8** |
| Circuit Outputs (`nout`) | 8 | 1 | **-7** | 32 | 4 | **-28** |
| Ligero Witnesses / Quads | 74,432 / 20 | 74,470 / 22 | **+38 (+0.05%) / +2** | 85,170 / 20 | 85,232 / 22 | **+62 (+0.07%) / +2** |
| Ligero `block` / `dblock` | 584 / 1,167 | 584 / 1,167 | **0 (0.00%)** | 583 / 1,165 | 583 / 1,165 | **0 (0.00%)** |
| Ligero `block_enc` (`nrow`) | 5,255 (171) | 5,255 (171) | **0 (0.00%)** | 5,246 (195) | 5,246 (195) | **0 (0.00%)** |
| Archive (`.lfa2` zstd-16) | 299,999 B | 308,092 B | **+8,093 B (+2.70%)** | 344,288 B | 363,530 B | **+19,242 B (+5.59%)** |
| Uncompressed Segmented | 895,483 B | 915,207 B | **+19,724 B (+2.20%)** | 1,068,349 B | 1,120,599 B | **+52,250 B (+4.89%)** |
| Proof Size | 343,204 B | 344,324 B | **+1,120 B (+0.33%)** | 350,852 B | 352,068 B | **+1,216 B (+0.35%)** |
| Prover Peak Heap | 90.84 MB | 90.89 MB | **+56 KB (+0.06%)** | 106.13 MB | 106.31 MB | **+174 KB (+0.16%)** |
| Verifier Peak Heap | 38.21 MB | 38.26 MB | **+55 KB (+0.14%)** | 45.33 MB | 45.53 MB | **+201 KB (+0.44%)** |
| Prover Time (release) | 215.86 ms | 215.94 ms | **+0.08 ms (+0.04%)** | 240.15 ms | 239.45 ms | **-0.70 ms (-0.29%)** |
| Verifier Time (release) | 119.43 ms | 113.96 ms | **~0% (noise)** | 127.23 ms | 124.55 ms | **~0% (noise)** |

### Attribute Comparison Proofs (`Le`, `Ge`)
Regular attribute slots carry a 2-bit public operator `AttributeOp`:
* `AttributeOp::Eq` (`req_attr(ns, id, cbor_val)`): exact CBOR equality.
* `AttributeOp::Le` (`req_attr_le(ns, id, cbor_val)`): `attr_value <= threshold` (e.g. `birth_date <= "2008-04-13"` to prove age ≥ 18).
* `AttributeOp::Ge` (`req_attr_ge(ns, id, cbor_val)`): `attr_value >= threshold`.

`Le` and `Ge` are supported on canonical ISO-8601 CBOR date encodings
(`circuit_supports_comparison`):
* 14-byte `full-date` (`tag(1004)` + 10-byte `YYYY-MM-DD`: `[0xd9, 0x03, 0xec, 0x6a, ...]`), and
* 22-byte `tdate` (`tag(0)` + 20-byte `YYYY-MM-DDTHH:MM:SSZ`: `[0xc0, 0x74, ...]`).

### Pseudonym Proofs (`Pnym`)
* Constructed via `req_pnym(ns, context)` (`id = b"pnym_seed"`, `op = AttributeOp::Pnym`, `context` = 1..=80 raw bytes).
* Calling `run_mdoc_prover_ext` (or `run_mdoc_prover_inner_ext`) locates `pnym_seed` (`bstr(32)`, 34 CBOR bytes `0x58 0x20 || seed`) in the MSO, computes `H = SHA-256(seed || context)` in 2 SHA-256 blocks, populates `cbor_value = 0x58 0x20 || H` in the returned `Vec<RequestedAttribute>`, and proves in zero knowledge that `H` was derived from the issuer-signed `pnym_seed` and the public `context`.
* On the verifier side, use `bind_pnym_response(&verifier_request, &prover_response)?` to copy only the prover's 34-byte pseudonym `cbor_value` into the verifier's own `RequestedAttribute` slice (preserving the verifier's `namespace_id`, `id`, `op`, and `context`) before calling `run_mdoc_verifier`.

### Attribute Encoding Limits & 16-Byte `random` Nonce Requirement
Each disclosed attribute's `IssuerSignedItemBytes` (`d8 18 58 <len> a4 ...`) is
hashed in `K_MAX_ATTR_SHA_BLOCKS` SHA-256 blocks (`2` blocks in current circuits).
Because SHA-256 appends a `0x80` byte and an 8-byte bit-length trailer (`9`
bytes), the maximum unpadded `IssuerSignedItemBytes` length is parameterized by
the block count:
```text
max_attr_cbor_len(num_attr_sha_blocks) = num_attr_sha_blocks * 64 - 9   // 119 bytes for 2 blocks
```
With a **16-byte `random` nonce** (`K_ATTR_RANDOM_NONCE_LEN = 16`, the minimum
per ISO 18013-5 §9.1.2.5), the fixed CBOR map framing of `IssuerSignedItemBytes`
(`d8 18 58 <len> a4` + `"digestID"` + `"random"` + `"elementIdentifier"` +
`"elementValue"`) occupies at least `K_MIN_ATTR_ITEM_OVERHEAD = 70` bytes plus
`cbor_id.len() + cbor_value.len()`. Consequently:
* **Only a 16-byte `random` nonce is supported** for 32-byte attributes such as
  `pnym_seed` under the 2-block (`119`-byte) attribute hash circuit (`70 + 10 + 34 = 114`
  bytes with a 1-byte `digestID`; up to `116` bytes with a 2-byte `uint16` `digestID`).
  A 32-byte `random` nonce would require `131`–`133` bytes (`3` SHA-256 blocks)
  and is rejected by the prover with `MdocProverErrorCode::AttributeTooLong`.
* Both the prover and the verifier validate `attr_encoding_fits(id, cbor_value, K_MAX_ATTR_SHA_BLOCKS)`,
  which ensures `min_attr_item_cbor_len(cbor_id.len(), cbor_value.len()) <= max_attr_cbor_len(K_MAX_ATTR_SHA_BLOCKS)`.


### `prover_only/` and `verifier_only/`

Two tiny `main.rs` files that call `run_mdoc_prover_inner` /
`run_mdoc_verifier_inner` with `black_box`'d dummy inputs. They exist so that
the linked footprint of *just* the prover or *just* the verifier can be
measured in isolation; they are not CLIs.

**Why the number is meaningful.** `black_box` stops the optimizer from
constant-folding the dummy arguments and deleting the call, so each binary
contains every function reachable from its one entry point. The workspace
release profile (`lto = true`, `codegen-units = 1`, `panic = "abort"`) lets
the linker drop everything that is *not* reachable — in particular neither
binary calls `provider::materialize`, so the circuit compiler
(`mdoc-zk-compile`, `compile-compiler`) is not part of these numbers.

**How to measure** (from `rust/`):

```bash
cargo build --release -p mdoc-zk-prover-only -p mdoc-zk-verifier-only

# 1. Raw file size. Includes symbol tables, so it over-states what ships.
ls -l target/release/prover_only target/release/verifier_only

# 2. Shipped size: strip symbols first (works with Apple and GNU strip).
strip -o /tmp/prover_only   target/release/prover_only
strip -o /tmp/verifier_only target/release/verifier_only
ls -l /tmp/prover_only /tmp/verifier_only

# 3. Code vs. data. Watch the __TEXT column (macOS) or text (Linux).
#    On macOS ignore `others`/`dec`: they include the 4 GiB __PAGEZERO reservation.
size target/release/prover_only target/release/verifier_only

# 4. Did crate X get linked? Grep its mangled symbols in the unstripped build.
nm target/release/verifier_only | grep -c mdoc_zk_compile    # expect 0
nm target/release/prover_only   | grep -c runtime_random     # expect > 0

# 5. Optional: attribute bytes to crates / functions.
cargo install cargo-bloat
cargo bloat --release -p mdoc-zk-prover-only   --crates
cargo bloat --release -p mdoc-zk-verifier-only -n 30
```

The difference between the two binaries is the cost of prover-only code
(mdoc parsing, witness generation, Ligero commitment, secure randomness).
To include on-device circuit compilation in the measurement, add a call to
`provider::materialize(CURRENT_VERSION, n, false)` to `prover_only/src/main.rs`
and rebuild.

For reference, on an Apple-silicon macOS host with the default profile the
stripped binaries were roughly 1.08 MB (prover) and 0.95 MB (verifier), with
`__TEXT` of about 0.97 MiB and 0.84 MiB respectively. Treat these as
order-of-magnitude figures; they change with the toolchain, target CPU
flags in `.cargo/config.toml`, and every circuit change.

---

## Circuit versions

| Version | Status | Where circuits come from | Notes |
|---|---|---|---|
| 5, 6, 7 | frozen | `artifacts/circuits/` via `provider::materialize` | Witness/public-input layout in `runtime/src/concrete/legacy/`; docType/namespace are checked outside the circuit; only `AttributeOp::Eq` is supported |
| 8 (`CURRENT_VERSION`) | development | compiled on demand by `mdoc-zk-compile` | Layout in `runtime/src/concrete/modern/`; 3 circuits (`1` attr, `4` attrs, `0` attrs + `1` pnym); docType checked in-circuit; supports `Eq`, `Le`, `Ge`, and `Pnym` |

Each `(version, num_attributes, pnym)` tuple has a `ZkSpecStruct` in
[`zk_spec.rs`](runtime/src/zk_spec.rs) giving its `combined_hash` and the
Ligero parameters for both circuits. External callers identify a circuit by
`("longfellow-libzk-v1", combined_hash)` and look it up with
`find_zk_spec` / `find_zk_spec_by_hex`.

---

## Tests and benchmarks

| Location | What it covers |
|---|---|
| `circuits/tests/all/*_eval.rs` | Evaluate each circuit under `EvalLogic` on real test vectors; negative tests mutate `Concrete*` inputs and expect a specific assertion to fail |
| `circuits/tests/all/*_compile.rs` | Compile each circuit with `compile_eval`, run it on a witness, serialize/deserialize round-trips, and check that corrupted inputs fail at the exact named assertion path |
| `circuits/tests/all/*_corruptors.rs` | Shared tables of `(name, expected_assertion_path, mutation)` used by both the eval and compile tests |
| `circuits/tests/all/test_support.rs` | Generates fresh ECDSA signatures (issuer + device) over a test MSO so signature tests do not depend on real private keys |
| `runtime/tests/all/current_zk.rs` | Compiles the v8 circuits once, then runs prove + verify on every test vector / attribute subset; asserts the compiled Ligero configs equal `CURRENT_ZK_SPECS` |
| `runtime/tests/all/prior_zk.rs` | Loads the v5–v7 artifacts, checks their circuit IDs match `ZK_SPECS`, and proves/verifies with each |
| `runtime/benches/mdoc_zk_bench_{current,v7}.rs` | Criterion benchmarks of prove/verify time and peak memory (via a tracking allocator) |

```bash
# from rust/
cargo test -r -p mdoc-zk-circuits
cargo test -r -p mdoc-zk-runtime
cargo bench   -p mdoc-zk-runtime
cargo run -r  -p mdoc-zk-runtime --bin convert_circuits   # regenerate .lfa1/.lfa2 artifacts
```
