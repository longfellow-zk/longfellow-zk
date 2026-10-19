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
* one or more requested attributes (e.g. `age_over_18`) are present in the
  MSO's `valueDigests` with exactly the claimed values,

without revealing anything else about the document.

The statement is split across two circuits over two different fields and tied together by a lightweight MAC:

| Circuit | Field | Proves | Ligero encoding |
|---|---|---|---|
| **Signature** (`MdocSignature`) | P‑256 base field | Two ECDSA verifications (issuer over MSO digest `e`, device over transcript digest) | FFT Reed–Solomon over `Fp2` |
| **Hash** (`MdocHash`) | GF(2¹²⁸) | SHA‑256 of the MSO equals `e`; docType / validity / deviceKey / valueDigests structure; per‑attribute `IssuerSignedItem` parsing + SHA‑256 | LCH14 Reed–Solomon over the GF(2¹⁶) subfield |

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
| [`mso_attribute/constants.rs`](proto/src/mso_attribute/constants.rs) | `IssuerSignedItem` geometry (`K_MAX_ATTR_CBOR_LEN = 119`, `K_ATTR_PREIMAGE_LEN = 128`) and key patterns (`digestID`, `random`, `elementIdentifier`, `elementValue`) |

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

The circuit definintion is generic
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
│   │                   compute_transcript_hash() for DeviceAuthentication
│   ├── cbor_encode.rs  tiny CBOR encoder helpers (encode_cbor_string, …)
│   ├── constants.rs    COSE_Sign1 / DeviceAuthentication header bytes
│   └── test_utils.rs   parse_test_data(): TestDataStatic → (issuer_pk, ParsedMdoc, now)
├── cbor_decoder/     IN-CIRCUIT decoder for a single CBOR head byte (major type, length class)
├── mso_attribute/    IN-CIRCUIT verifier for one IssuerSignedItem (AttributeVerifier)
├── hash/             IN-CIRCUIT MdocHash — the GF(2^128) circuit
└── signature/        IN-CIRCUIT MdocSignature — the P-256 circuit
```

#### The four-file convention

Each in-circuit module (`cbor_decoder`, `mso_attribute`, `hash`, `signature`)
follows the same layout as the generic circuits in `rust/circuits/*`:

| File | Role | Types |
|---|---|---|
| `circuit.rs` | The constraint logic. Defines the wire-level input structs and the `assert_*` methods that produce `L::Assertions`. | `Given<L>`, `Derived<L>`, `MdocHash` / `MdocSignature` / `AttributeVerifier` / `CborByteDecoder` |
| `allocate.rs` | Allocates fresh input wires from a running position counter, one wire per bit. Used by the circuit-level tests; the production (packed) layout lives in `compile/`. | `allocate_given`, `allocate_derived` |
| `concrete.rs` | Plain-Rust mirror of the wire structs plus the functions that fill them from a `ParsedMdoc`. | `ConcreteGiven`, `ConcreteDerived`, `HashInput`, `SignatureInput`, `given()`, `derived()`, `hash_input_of_parsed_mdoc()`, `compute_mac_tags()` |
| `evaluate.rs` *(feature `testonly`)* | Lifts `Concrete*` values into constant wires so a circuit can be run directly under `EvalLogic`. | `evaluate_given`, `evaluate_derived` |

"Given" values are inputs (public or private) supplied by the prover;
"Derived" values are auxiliary witnesses (SHA‑256 round state, ECDSA
intermediate points, …) that the prover precomputes so that the circuit only
has to *check* them.

`MdocHash::assert_valid_presentation_and_macs` is the root assertion of the
hash circuit; it fans out to `assert_mso_sha256_hash`, `assert_mso_doc_type`,
`assert_mso_validity`, `assert_mso_device_key`, `assert_mso_value_digests`,
`assert_attributes` (one `AttributeVerifier::assert_attribute` per disclosed
attribute) and `assert_mac_tags`. `MdocSignature::assert_signatures_and_macs`
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
| [`lib.rs`](compile/src/lib.rs) | `compile_circuits(num_attrs, hash_profile, sig_profile)` → one LFA2 archive with a `"sig"` and a `"hash"` entry, tagged with `CURRENT_VERSION`; `compile_all_circuits` does 1–4 attributes in parallel. |

### `runtime/` — prover and verifier

```
runtime/src/
├── lib.rs           public surface; re-exports mdoc_zk_{circuits,compile,proto}
├── zk_spec.rs       ZkSpecStruct + ZK_SPECS (v5/v6/v7, pinned) + CURRENT_ZK_SPECS (v8):
│                    combined_hash ↔ (version, num_attributes, Ligero configs)
├── provider.rs      materialize(version, nattrs) → ProvidedCircuit
│                    (v < CURRENT: load from artifacts/;  v == CURRENT: compile on the fly
│                     and check the Ligero configs match the spec)
├── prover.rs        run_mdoc_prover[_inner]: parse mdoc → build witnesses → commit both
│                    circuits → draw `av` → compute MACs → prove both → serialize
├── verifier.rs      run_mdoc_verifier[_inner]: rebuild public inputs → verify both proofs
├── proto.rs         MdocProof / MdocProofGeometry wire format
│                    (6 × u128 MAC tags ‖ hash proof ‖ signature proof);
│                    decompress_circuits(): reads zstd LFA2 archives *or* legacy LFC1 streams
├── mac.rs           generate_mac_ap(), push_macs() (modern + legacy tag computation)
├── concrete/        assignment of field elements to wires
│   ├── builder.rs     AssignmentBuilder: push bits / bytes / plucked V8·V32·V256 / nat / u128
│   ├── modern/        version ≥ 8 layouts  (public.rs = public inputs, private.rs = witness)
│   └── legacy/        version 5–7 layouts  (kept so old circuits remain provable)
├── attribute.rs     RequestedAttribute { namespace_id, id, cbor_value }
├── utils.rs         req_attr(), same_namespace(), parse_pk_coordinate(), circuit_supports()
├── error.rs         MdocProverErrorCode / MdocVerifierErrorCode (stable numeric codes)
└── bin/convert_circuits.rs   re-encodes artifacts/circuits/* into .lfa1 / .lfa2
```

The version switch is centralised: `concrete::push_{witness,input}_{hash,sig}`
and `mac::push_macs` dispatch on `version >= 8` to `modern` or `legacy`.



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
`provider::materialize(CURRENT_VERSION, n)` to `prover_only/src/main.rs`
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
| 5, 6, 7 | frozen | `artifacts/circuits/` via `provider::materialize` | Witness/public-input layout in `runtime/src/concrete/legacy/`; docType/namespace are checked outside the circuit |
| 8 (`CURRENT_VERSION`) | development | compiled on demand by `mdoc-zk-compile` | Layout in `runtime/src/concrete/modern/`; docType is a public input checked in-circuit; attribute values restricted by `utils::circuit_supports` |

Each (version, num_attributes) pair has a `ZkSpecStruct` in
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

---

## Where to make a change

| I want to… | Touch |
|---|---|
| Change *what* the circuit checks | `circuits/src/hash/circuit.rs`, `circuits/src/signature/circuit.rs`, `circuits/src/mso_attribute/circuit.rs` |
| Add / reorder a circuit input | `compile/src/allocate_{hash,sig}.rs` **and** `runtime/src/concrete/modern/{public,private}.rs` (they must stay in lock-step), plus `circuits/src/*/{allocate,evaluate}.rs` for the tests |
| Change a size limit or magic CBOR byte string | `proto/src/**/constants.rs` |
| Add a new test mdoc | `testcases/src/vectors.rs` |
| Ship a new circuit version | bump `CURRENT_VERSION` in `circuits/src/lib.rs`; move the old `CURRENT_ZK_SPECS` into `ZK_SPECS`; drop the old archives/proofs into `artifacts/`; add a `legacy`-style layout if the input order changed |
| Change the proof byte format | `runtime/src/proto.rs` |
| Add an error code | `runtime/src/error.rs` (append only — the numeric values are part of the FFI contract) |
