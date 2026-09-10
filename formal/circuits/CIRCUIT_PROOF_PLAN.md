# Circuit Proof Plan: Verifying Compiled Quads Against High-Level Specs

**Goal.** Prove in Lean that the quad form for a circuit exactly as deployed implements its high-level specification, without trusting the compiler and without hand-modeling circuit source in Lean.

**Pipeline target.** The Rust compiler (`rust/compile/`) and its circuit libraries
(`rust/circuits/*`). 

## ECDSA
`Ecdsa2.Assembly.ecdsa2_sound_of_bytes` takes the committed LFC3 bytes and an accepting input
assignment to `StandardEcdsaVerify`. Its remaining hypotheses are the curve
parameter equations, and the four group-order facts, which are not circuit facts. 

The small `Rung1EndToEnd` example is complete: the Lean kernel checks packed artifact
bytes through the LFC3 commitment and decoder, converts the decoded value to `RawCircuit`, and
proves acceptance equivalent to a handwritten specification. 

Generated bounded checkpoints
also close the byte-to-`DecodedCircuit` path for the historical one-block SHA-256 and ECDSA2
fixtures.


### Current status

| Proof component | Status | Evidence / limitation |
|---|---|---|
| Generic LFC3 packed commitment and decoder | Complete | `quadcert/Lfc3.lean`; kernel-checked page commitments, staged parsing, resumable expansion, opaque composition. |
| Exact bytes-to-spec example | Complete | `quadcert/Rung1EndToEnd.lean`. |
| **ECDSA2, current source: one-run artifact + sidecar** | **Complete** | `rust/circuits/ecdsa2/examples/ecdsa2_artifacts.rs`. Root `e553aae9832473af8e9845b1d7805e9e27a2f41e8c4ce7ca86dd9dc48c38cebf`, `ninput = 1042`, `npublic = 1`, 48,256 terms, 26,939 nodes, 1,048 assertions, 11 layers. The layout covers all 1,042 positions exactly; an independent `lfc3_to_lean` run on the emitted LFC2 reproduces the same root; the sidecar's and the artifact's constant tables are asserted byte-identical. |
| **ECDSA2: bytes to `RawCircuit`** | **Complete** | `Ecdsa2Data.raw_from_bytes`. |
| **ECDSA2: `ValidScheduling`, all eight fields** | **Complete** | `Ecdsa2Sound.valid`, from `ok_check`, `inv_check`, `wireFn_lt`, and the grouping certificates `perm_all` / `hom_all` / `corr_check`. |
| **ECDSA2: `Accepts` → named assertions zero** | **Complete** | `Ecdsa2Sound.assertions_zero`, and `assertions_zero_of_bytes` for the artifact form. Soundness needs only `Backed`; `CoversConstraints` is unproved and is what the converse would need. |
| **ECDSA2: witness predicate → ECDSA specification** | **Complete** | `ECDSA/EcdsaV2.lean`'s `soundness_of_v2`, sorry-free with standard axioms, composing with `ecdsa_circuit_soundness` (itself now sorry-free for both curves). |
| **Lookup tables exact at their nodes** | **Complete** | `ECDSA/Lagrange9.lean`, 190 theorems, 16.7 s. Includes the bit extractors and `isDigit_of_range`. |
| **The 256-bit comparison gadget** | **Complete** | `ECDSA/BitLt.lean`, sorry-free. |
| **ECDSA2: assertion polynomials → witness predicate** | **Complete** | `Ecdsa2.Assembly.ecdsa2_sound` and `ecdsa2_sound_of_bytes`, axiom-clean (`propext, Classical.choice, Quot.sound`). Bridges: `digits_ok`, `loop_ok`, `recon_ok`, `small_ok`, `cmp_ok`. |
| Production verifier circuit pinning | Not implemented | The verifier does not yet select and enforce the formal LFC3 root. |

The historical fixtures referred to in earlier revisions of this document are superseded: the
ECDSA2 numbers above are from current source with the current `npublic = 1` interface.

### End-to-end completion criterion

For each production circuit, the intended theorem chain is:

```text
verifier-selected expected root
  -> packed LFC3 pages and kernel-checked page commitments
  -> staged decode : DecodedCircuit
  -> DecodedCircuit.toRaw using checked certificate advice
  -> ValidScheduling, including sum_local
  -> Accepts iff all circuit assertions hold
  -> witness predicate
  -> handwritten Lean specification
```

Completion means every arrow above is checked by ordinary Lean kernel reduction or proved
lemmas, with no `sorry`, `native_decide`, file-reading elaborator, or trusted generated theorem.
Rust generators may emit data and proof scripts, but incorrect output must fail a Lean check.

---

## 0. Trust base, stated precisely

There are currently two paths. The old sidecar-only path receives generated literals and
therefore trusts more of the Rust representation stack. The target LFC3 path, completed for
Rung1 and validated through decoding on the larger fixtures, is:

```
                         ┌─ LFC3 bytes ─► packed pages ─► root + verified decode ─┐
one in-memory Circuit<F> ┤                                                        ├─► RawCircuit
                         └─ sidecar ─► generated advice ─► refinement + checks ───┘
```

* **Untrusted: compiler transformations.** `algsimp`, CSE, copy insertion and scheduling may
  be wrong. The DAG-plus-wire-map endpoint checks connect advice to the deployed terms, and
  the final meaning theorem checks those terms against the handwritten spec.
* **Untrusted in the target path: artifact/sidecar generators and Lean emitters.** They provide
  bytes, data, and proof hints. The pinned root, verified decoder, refinement theorem, and
  structural checks must reject incorrect output. This statement becomes fully true for a
  circuit only when `raw` is assembled from decoded artifact fields as required in Step 5.
* **Trusted in the legacy path:** the serializer, parser, and Lean emitter. The two Rust
  self-checks (`compute_id` at build, `recompute_id` at parse) use the same representation
  stack, so they do not independently detect a shared `Term`/`Layer`/delta defect.
* **Operational requirement:** artifact and sidecar are produced from one in-memory circuit,
  and the production verifier selects the formally reviewed root.
* No `native_decide`; the Lean compiler is not in the trust base.

Earlier sidecar-only revisions of this document claimed "the Rust compiler is fully untrusted"
and "every byte of the sidecar is re-checked in Lean". **Both claims were wrong for that
path.** LFC3 plus artifact/advice refinement is the mechanism intended to make the first claim
true at the final theorem boundary; the sidecar remains advice rather than authenticated input.

**Closing the gap.** A verified decoder from artifact bytes as Lean data to `DecodedCircuit` is
implemented in `quadcert/Lfc3.lean`. Rung1 also proves the refinement from that value to the
`RawCircuit` used by semantics; the equivalent generated refinement for large circuits remains
on the critical path. A literal with one Lean element per byte remains out of reach; pages
instead use one packed natural each, and no elaborator reads the artifact file.

LFC3 adds one bounded
dictionary level for repeated segment-token runs, and the verifier-facing protocol pins the
exact uncompressed LFC3 bytes with a domain-separated, 4096-byte-page SHA-256 Merkle root.
Generated Lean modules can store each page as one little-endian packed `Nat` and check its leaf
hash by kernel reduction; no file-reading elaborator or `native_decide` is required. The mdoc
four-attribute hash circuit falls from 1,419,484 LFC2 bytes to 1,173,100 LFC3 bytes (287 pages),
and the other v7 variants show the same 17–18% reduction. See
`quadcert/LFC3_PROTOCOL.md`, `quadcert/Sha256.lean`, and
`quadcert/CircuitCommitment.lean`.

For Rung1 this gap is now closed inside Lean: `Rung1Artifact.decode_ok`,
`Rung1Data.artifactRaw_eq_raw`, `Rung1Base.constNat_from_artifact`, and
`Rung1.accepts_artifact_iff_spec` form the byte-to-spec chain. The real verifier does not yet
select this root. Large-artifact checkpoint generation is now implemented by `lfc3_to_lean`:
it stages header/layer/trailer parsing, proves fixed-size term-expansion chunks, and composes
both through opaque generic theorems.

---

## 1. The workflow, step by step

### Step 1 — The author writes a Rust circuit, with two kinds of annotation

Circuits are written as usual against the `Logic` DSL. Two things must be annotated, and neither is a proof.

**(a) Named assertions.** Every constraint carries a name. The compiler already enforces
this — `assert0` rejects an empty name (`logic_impl.rs:123`) — and `assert_all` builds
hierarchical scope paths. Nothing new is required of the author beyond choosing good names,
because the names become the vocabulary the final theorem is stated in.

```rust
pub fn point_equality(&self, pt: &Pt3<Eltw<L>>, zinv: &Eltw<L>, px: &Pt2<Eltw<L>>)
    -> L::Assertions
{
    let (x, y, z) = pt;
    let (px_val, py_val) = px;
    let l = &self.logic;
    l.assert_all("point_equality", &[
        l.assert_eq("px_eq",   &l.mul(x, zinv), px_val),
        l.assert_eq("py_eq",   &l.mul(y, zinv), py_val),
        l.assert_eq("z_zinv",  &l.mul(z, zinv), &l.one()),
    ])
}
```

This yields paths `rung1/point_equality/px_eq`, `…/py_eq`, `…/z_zinv`.

**(b) Input layout.** Wire allocation must record *what each input means*. `WireAllocator`
carries no names, so this was added: allocate through `LayoutBuilder`, which is what advances
the position counter, so a name cannot drift from the position it labels.

```rust
let mut layout = cert::LayoutBuilder::new();          // position 0 = reserved constant `one`
let mut pos = compile_logic::K_FIRST_WIRE_POSITION;
let px   = layout.next(&iologic, &mut pos, "px");
let py   = layout.next(&iologic, &mut pos, "py");
let qx   = layout.next(&iologic, &mut pos, "qx");
let qy   = layout.next(&iologic, &mut pos, "qy");
let qz   = layout.next(&iologic, &mut pos, "qz");
let zinv = layout.next(&iologic, &mut pos, "zinv");
```

`layout.assert_covers(ninput)` checks the layout is total.

### Step 2 — The normal compile chain produces the circuit

`compile()` runs unchanged: `ir_to_quad` → `algsimp` → CSE → `copy` → `scheduler`. Its layered
quad circuit is serialized in the canonical LFC3 verifier-facing representation. The prover
and verifier need not change while this proof work is developed, but the target protocol is
that the verifier pins the LFC3 page root. **The compiler transformation is not trusted.**

The proof build must produce the LFC3 artifact and certificate sidecar from the same in-memory
`Circuit` in one invocation. Recompiling source separately for either output is not an adequate
identity check: compiler or interface drift can produce superficially similar but different
circuits. The build records the artifact root, public/input/output counts, layer sizes, and
term counts next to the generated Lean modules.

### Step 3 — The compiler additionally emits a certificate sidecar

`compile_with_cert()` returns that same circuit plus `ScheduleInfo`, from which
`cert::build_sidecar` produces a byte sidecar containing: a cache of the expanded per-layer
quad terms, the post-materialization quad DAG, the node → wire map, the assertion records
(path → node/wire), the constants table, and the input layout.

The artifact, not the sidecar, owns the layer terms and constants. Sidecar copies are only
caches/advice and must be proved equal to, or constructively refined from, the value decoded
from the pinned artifact. The DAG and wire map are then re-derived structurally in Lean, so a
wrong advice generator or emitter cannot produce a passing certificate. A self-consistent but
semantically wrong compiler output is rejected later by the handwritten-spec bridge. The input
layout remains a chosen semantic mapping and is a residual review item.

### Step 4 — Artifact data and certificate advice are emitted as Lean modules

`lfc3_to_lean` and `cert::emit_lean` write bounded generated `.lean` modules:

| module | contents |
|---|---|
| `<N>Packed{k}`, `<N>Commitment{k}` | packed LFC3 pages and page-hash checks |
| `<N>Header`, `<N>CompressedLayer{l}` | staged header and compressed-layer parser checkpoints |
| `<N>Expansion{l}_{j}`, `<N>ExpandedLayer{l}` | resumable raw-term expansion chunks and per-layer composition |
| `<N>ParseSteps`, `<N>ParseFinish`, `<N>ParseFinal`, `<N>Decode` | opaque parser/expansion composition and final decoder theorem |
| `<N>Wire{k}` | wire-map bisection pieces |
| `<N>Base` | wire-map dispatcher, `wireInv`, `nlayers` |
| `<N>Terms{l}_{j}` | advice term chunks; target refinement checks them against decoded artifact terms |
| `<N>Nodes{k}` | node list chunk **+ `ok_k` / `inv_k`, its own slice of the structural check** |
| `<N>Inv{k}` | inverse-map bisection pieces |
| `<N>Data` | currently assembles advice-side `raw`, `nodes_len`, `wireFn_lt`; it must be refined to decoded artifact data |
| `<N>OkCheck`, `<N>InvCheck` | the composed checks |

The structural certificate modules import `quadcert.Raw` only, and artifact modules import the
small `Lfc3`/commitment stack; generated leaves **never import Mathlib**. `import Mathlib` costs
a ~3.3 GB resident floor per module, which would make chunking pointless.

### Step 5 — Lean checks the artifact and then checks the advice against it

For Rung1, the page-root theorem pins the packed bytes, the staged decoder determines the
`DecodedCircuit`, and a refinement theorem constructs the `RawCircuit` used below. The larger
fixture experiments currently stop at `DecodedCircuit`; adding the analogous generated
artifact/advice refinement is Step 3 of the critical path. Independently,
`validScheduling_of_checks` consumes generated `ok_check` and `inv_check` proofs and produces
seven of the eight `ValidScheduling` fields generically. `sum_local_of_grouping` will supply the
eighth after the emitter generates and Lean checks the grouping/per-node correspondence.

### Step 6 — Complete the circuit-specific spec bridge

The circuit-specific bridge consists of:

- the **constants correspondence**, proved from artifact-owned canonical integers under the
  field-characteristic hypotheses;
- the generated and kernel-checked **`sum_local` certificate** (see Phase A); and
- the handwritten **layout interpretation and meaning lemmas**, one per distinct assertion
  template, plus the final theorem.

For Rung 1 that is roughly 60 lines of Lean against 19 nodes of generated data.

---

## 2. Why this works

### What is actually being proved

The deployed artifact is a list of quad terms per layer. `Accepts` is defined directly on
those terms, mirroring `compile/eval/src/eval.rs` gate for gate. So `Accepts` is a statement
about *the bytes that ship*, not about a model of them.

The final theorem has the shape

```
∀ inputs, Accepts (compiled circuit) inputs  ⟺  Spec (named inputs)
```

and the work is entirely in getting from the left side to the right.

### The three links, and why each is sound

**Link 1: layered circuit ⟶ DAG (`simulation`).**

The layered form is the *optimized* form — algsimp, CSE, copy chains, wire renumbering,
canonical term ordering. Reasoning about it directly would mean reasoning about every
optimization pass. Instead the compiler dumps a **quad DAG**, in which each node's value is
defined compositionally from its operands, and a wire map relating the two.

`simulation` proves: under a valid scheduling, every wire's layer value equals the DAG
interpretation of the node mapped to it.

The soundness argument is that **we check the endpoint of the optimizations.** If the dumped
DAG, scheduled by the dumped wire map, reproduces the deployed layer terms, then the DAG is a
faithful re-description of the deployed circuit — and the DAG is the form in which
compositional reasoning is possible. A mismatch between advice and deployed terms fails the
structural check. If a faulty compiler instead emits a self-consistent but semantically wrong
circuit and DAG, the later DAG-to-handwritten-spec meaning theorem is the check that must fail.

**Link 2: acceptance ⟶ a list of named algebraic facts (`accepts_iff_assertions`).**

`Accepts` is a global property. This lemma converts it into a conjunction indexed by
human-meaningful paths:

```
Accepts c inputs  ⟺  ∀ r ∈ records, interpDag r.assertedNode = 0
```

Both directions matter and rest on *different* checks. `Backed` — every record is carried by
a real circuit constraint — gives `Accepts → assertions zero`, which is what ZK soundness
consumes. `CoversConstraints` — every circuit constraint is carried by a record — gives the
converse, i.e. that there is **no unnamed constraint on the witness**. Without it the spec
bridge would silently prove a theorem about a weaker circuit than the one deployed.

**Link 3: algebra ⟶ spec (the meaning lemmas).**

This is where the hierarchy bottoms out. `interpDag` assigns each assertion node a
**polynomial in the input variables**, and because it is compositional, computing that
polynomial is unfolding plus normalization. For Rung 0:

```
interpDag dag inputs 11  =  y·y − (x·x·x + a·x + b)
```

proved by `simp only [...]` then `ring`. And `AffinePoint.IsOnCurve ⟨x,y⟩ params` is
`y*y = x*x*x + a*x + b`. So the link is literally `p = 0 ↔ spec`, discharged by
`linear_combination`.

### What Lean supplies

- **`ring` / `linear_combination`** discharge the field identities. This is the step that
  connects "a quad term with coefficients" to "an equation a cryptographer wrote down", and
  it is fully automatic. Rung 1's four meaning lemmas are one `simp only` and one `ring` each.
- **Definitional unfolding** makes `interpDag` on a concrete DAG compute, so the polynomial
  is *derived*, not asserted.
- **Kernel decidability** discharges the structural checks without a tactic.
- **Mathlib's vocabulary** lets the right-hand side be ordinary mathematics — `Field`,
  `ProjectiveEquiv`, elliptic curves — rather than a circuit-shaped restatement.


### Proved

| Rung | Circuit | Theorem |
|---|---|---|
| 0 | `EcCircuit::is_on_curve` | `Rung0.accepts_iff_isOnCurve` ⟺ `AffinePoint.IsOnCurve` |
| 1 | `point_equality` + `is_on_curve` | `Rung1.accepts_iff_spec` ⟺ `ProjectiveEquiv` ∧ `IsOnCurve` |

Both 0 `sorry`, axioms `[propext, Classical.choice, Quot.sound]`. Rung 1 runs entirely on
generated data and its statement reads in layout names emitted from the sidecar. It exercises
both assertion mechanisms and uses `structurallyZero` three times.

On independent full ECDSA2-size sidecar data — 48,256 terms, 26,939 nodes, 1,048 assertions,
106 modules —
`ok_check`, `inv_check`, `wireFn_lt`, `nodes_len` are all proved, and
`validScheduling_of_checks` yields `ValidScheduling` for that generated raw circuit with
`sum_local` the sole structural hypothesis. This does not yet identify it with either checked
historical LFC3 fixture. **98 s, 3.0 GB**, and it parallelizes 11.6× (1136 s user / 98 s
wall) because every module is now chunk-local.

### Bottlenecks, ranked

1. ~~**Matched current artifacts and sidecars**~~ — **done for ECDSA2.**
   `rust/circuits/ecdsa2/examples/ecdsa2_artifacts.rs` compiles once and writes the LFC3 bytes,
   the sidecar, every Lean module and a manifest. Root
   `e553aae9832473af8e9845b1d7805e9e27a2f41e8c4ce7ca86dd9dc48c38cebf`, `ninput = 1042`,
   `npublic = 1`, 48,256 terms, 26,939 nodes, 1,048 assertions, 11 layers. The layout covers all
   1,042 positions exactly, and an independent `lfc3_to_lean` run on the emitted LFC2 reproduces
   the same root.
2. ~~**`sum_local` emitter support**~~ — **done**; see Phase A.
3. **ECDSA2 semantic bridge** — the remaining critical path; see Phase C.
4. **One-block SHA specification and schema meanings** — after ECDSA2 closes.
5. **Verifier root selection** — required to turn the proved root into the deployed identity.
6. **DAG-side compression at mdoc scale** — unanswered; gates Phase E, not SHA/ECDSA.
7. **`logw` non-uniformity** — blocks the optional `lfzk` tie-in, not the spec bridge.

### The one lesson from five scaling attempts

Every time something stayed monolithic — the lookup table, the check, the inverse map, the
inverse *check* — it dominated, regardless of how cheap its *reduction* was. Elaborated term
size is the cost, not kernel steps, and one un-chunked item also destroys parallelism. Hash
tables do not help: the kernel accelerates `Nat` arithmetic and comparison but not array
indexing, so a hash lookup is O(n) there.

Composition side-conditions should be stated over **lists of ranges with a contiguity
predicate**, not by splitting numerals: Lean's elaborator folds `5 + (5 + (5 + 4))` back to
`19` before an `a + b` rewrite can fire. `okInvChunks` / `tiles` / `okInv_of_chunks` in
`Raw.lean` are the pattern, and `tiles` is O(number of chunks) rather than O(nodes).

| attempt | time | peak RSS | outcome |
|---|---|---|---|
| `List.getD` lookups | 493 s | 12.8 GB | timeout |
| single if-tree | 444 s | 29 GB | OOM |
| chunked tree, whole-circuit `decide` | 888 s | 43 GB | timeout |
| chunked check, `wireInv` whole | 460 s | 42.7 GB | OOM |
| chunked check + chunked `wireInv` | 368 s | 31.2 GB | success, but `inv_check` alone was 951 s / 31.2 GB |
| **+ chunked `inv_check` (`okInvChunks`)** | **98 s** | **3.0 GB** | **success, 11.6× parallel** |

---

## 5. Corrections to the original plan

Recorded because each cost real time to discover.

- **In-Lean expanded `compute_id` recomputation: dropped.** It hashes every expanded term and
  cannot be localised. Its replacement is kernel-reduced page SHA-256 over the compact LFC3
  payload, followed by the verified Lean decoder. Rung1 exercises the complete path.
- **`ArithmetizedCircuit.soundness` does not exist.** The obligations are
  `ArithmetizedCircuit.arith` (`lfzk/circuit.lean:946`) and `LayeredCircuit.layer_rel`
  (`lfzk/layers.lean:131`).
- **The uniform-`logw` "WLOG" is not a WLOG.** The protocol is per-layer — `layer_h` runs
  `clr->logw` rounds. Deployed circuits are non-uniform (ECDSA2: `logw ∈ {3..13}`).
- **`WireAllocator` carries no names.** The layout had to be added at allocation.
- **`ValidScheduling` had two latent unsatisfiable fields**, both found by building the
  non-vacuity examples: `input_wire` demanded a wire for every index past the end of the DAG
  (`List.getD` is total), and `map_inrange` was missing.
- **Ladder reordered.** `assert_public_key_sound` (PkCircuit) is `sorry`-free.
  ~~`ecdsa_circuit_soundness` depends on `sorryAx`.~~ **No longer true, measured 2026-08-12:**
  `#print axioms ECDSA2.soundness_of_v2` reports only `propext, Classical.choice, Quot.sound`,
  and so does `Ecdsa2.Assembly.digits_ok`. The only `sorry`s left anywhere under `circuits/`
  are the six in `EcdsaComplete.lean`, which is the *completeness* direction and is not on the
  soundness path.

---

## 6. Residual trust items

- **Input layout** (position ↔ witness field). The one place meaning is *chosen* rather than
  checked. Recorded at allocation by `LayoutBuilder`; reviewed once.
- ~~**Constants correspondence**~~ — **now a theorem, not a trust item.** The dumper emits the
  constant table as canonical hex integers from the artifact's own encoding (`constNat`), and
  `Rung1.constsOf_eq_generated` proves the table the proofs use *is* that one, under
  `CharP F p256` and the curve parameters. `Quadcert.cast_sub_eq_neg` supplies the step for
  the negated constants, which the artifact encodes as `p - n`; no 256-bit numeral computation
  is needed, only `n ≤ p`. This is where the P-256 choice enters, and it now enters as an
  explicit hypothesis rather than as prose in a comment.
- **Verifier-selected root = formally proved root.** The LFC3 page commitment, decoder and
  `RawCircuit` refinement discharge the Lean side for Rung1. This remains an operational trust
  item until the production verifier selects the formal root. Large-circuit checkpoint
  generation is already implemented; current-source SHA/ECDSA roots still need to be produced
  and reviewed.
- **SHA-256 collision resistance for root pinning.** Lean proves that the embedded bytes hash
  to the selected root. Treating that short root as a unique commitment to deployed bytes is a
  computational cryptographic assumption, not an unconditional equality theorem.
- **The Lean statement of the spec.**

For a circuit whose chain in the completion criterion is closed, artifact decoding, scheduling,
and assertion semantics are checked. Until then, generated advice and fixture measurements are
evidence, not a substitute for the missing theorem. Two circuit-level obligations are easy to
miss: non-assertion constants must be non-zero (a zero constant in a `Sum` term is read by the
runtime as an *assertion* term, `eval.rs:139`), and input position 0 must be pinned to the
constant `1`.

## Assembly status (measured, not estimated)


### The lemma class that unblocked it

Every meaning lemma stops at the CSE boundary and leaves the table outputs opaque -- that cut is
why `ring` closes in seconds instead of exhausting 12 GB. Nothing said what those wires *were*,
and all three remaining bridges waited on the same missing class. It is now generated:

| generator | lemmas | statement |
|---|---|---|
| `gen_mux_meaning.py` | 256 | `⟨w_x, w_y, w_z⟩ = optPoint u pk rx ry pre params` |
| `gen_bit_meaning.py` | 256 | the three bit wires are the digit's `e`, `r`, `s` bits |
| `gen_bittable.py` | 27 | `digitBit` at the eight nodes, plus the `reconstruct*` weighting bridges |

Each cone is small (37 nodes for a mux coordinate, 12 for a bit) because `IsDigit` collapses the
degree-7 interpolant to one atom. 12,288 modulo-`p` identities were checked during generation --
256 rounds x 8 nodes x (3 coordinates + 3 tables) -- and every one passed before a line of Lean
was emitted.

Two facts are *recovered* rather than assumed, deliberately, because the same association went
missing once before (the `segment_circuit` renumbering bug):

* each mux/bit cone reads exactly one `ers` input, so the wire-to-digit link is read off the
  cone itself;
* the loop order is derived by following each round's output triple to the round that consumes
  it as its accumulator, starting from the one round whose accumulator is the constant point at
  infinity. It closes into a single 256-cycle, 255 -> 0.

### The bridges

| bridge | module | cost |
|---|---|---|
| `hdig` | `E2Digits.digits_ok` / `digits_tuple` | 594 s |
| `hloop` | `E2LoopOk.loop_ok` | 509 s, 5.8 GB, 157 MB olean |
| `he`, `hr`, `hsi` | `E2Recon.recon_ok` | 500 s, 5.1 GB |
| `hpre`, `hax`, `haz`, `hrxi`, `hpki`, `hpkc`, `hrc` | `E2Small.small_ok` | 217 s |
| `hrlt`, `hslt` | `E2Cmp.cmp_ok` | 217 s |
| composition | `E2Ecdsa.ecdsa2_sound` | 4.2 s |

`hloop` is a chain of 256 `LoopFull.cons_step` applications, not 256 `have`s: naming the
intermediates forces Lean to elaborate 256 `LoopFull` types whose list arguments grow, which is
quadratic. `E2Small` needs `clear` on its 458 assertion hypotheses before the closing
`assumption`, or the search unifies each goal against every one of them and times out at `whnf`.



### Cost note

Adding the six `NeZero` instances to `E2Meaning` invalidated all 96 loop-batch modules (2.2 GB
of oleans, ~45 min to rebuild). `E2Meaning` sits under every generated meaning module; new
shared lemmas belong in a leaf module instead. That is why `BitTable.lean`, `CmpBridge.lean` and
`LoopAssembly.lean` are separate files rather than additions to `EcdsaV2`.


## SHA-256: the decoder blocker, diagnosed and fixed in prototype

### The blocker, measured

`readDeltasChunk 148 1024 cur_5_d1` on SHA-256's layer 5 — one 1,024-delta chunk — aborts the
kernel at **18.0 GB after 173 s**, serial, on an idle machine. The ECDSA2 counterpart takes ~1 s.
Isolating what is expensive:

| what is forced | time | peak RSS |
|---|---:|---:|
| list spine and cursor chain only | 4.5 s | 0.78 GB |
| the decoded delta values | 175 s | 9.5 GB |
| full equality against the emitted literal | 173 s | 18.0 GB (abort) |

So it is neither the byte walk nor the cursor: it is forcing the **values**. `Lfc3.Cursor` holds
the 4,096-byte page as one 32,768-bit `Nat` and `readByte` returns `cursor.page % 256`. The `/`
results chain through the cursor and are shared; the `%` results are forced only when the deltas
are compared to their literals, at which point the kernel materialises one multi-kilobyte bignum
per byte.

**An earlier note in this document blamed `laterPages` and proposed removing it from the cursor.
That was wrong** — the scaling probe shows the cursor chain alone is 4.5 s. Diagnose by forcing
one component at a time before refactoring.

### The fix, validated

`quadcert/Lfc3Bytes.lean` supplies the page as a **byte list** advice, tied to the committed page
by `packBytes` — the same advice-plus-linear-check shape `deltasOk` uses for the delta tree.
`readByteB` pops a `cons`: no arithmetic, nothing retained. On the same chunk, same bytes:

| reader | time | peak RSS |
|---|---:|---:|
| packed `Cursor` | 175 s | 9.5 GB |
| byte `BCursor` | **4.5 s** | **0.83 GB** |

**39x faster, 11x smaller**, against a chunk that currently aborts. The Merkle leaf hash keeps
using the packed `Nat`, so **the root does not change** — `packBytes_append` is proved so the
per-page check composes in a balanced tree rather than multiplying a 32,768-bit accumulator once
per byte.

To land it: drop `private` from `Lfc3.decodeDelta`, port `readDeltasChunk_compose` (mechanical —
the packed proof is a 40-line template and nothing in it depends on where a byte comes from),
switch `Cursor` over, and regenerate the 14 cursor modules. Regression test: `raw_from_bytes`
must still give root `e553aae9…`.

## SHA-256: the specification exists

`circuits/SHA/Spec.lean` — FIPS 180-4 transcribed, no circuit vocabulary. `w32`, `rotr`, `shr`,
the bitwise operations over individual bits, `Ch`/`Maj`/`Σ₀`/`Σ₁`/`σ₀`/`σ₁`, `K`, `H0`, the
message schedule, the 64 rounds, `block`, and a `Word32` witness structure with `ofBits`.

**`block_empty` is a kernel-checked test vector** (`[propext]` only, 7 s): the padded empty
message hashes to `e3b0c442…7852b855`. It caught a real bug immediately — the first draft indexed
`zipBits` as `31 - i`, reversing every word, and produced `61d7f4ca…`. Nothing else in the file
would have found that. Any future edit to the spec must keep this theorem.

### Why the SHA meaning layer is easier than ECDSA2's

Measured on the current artifact: 6,840 assertions in **four path families**, and only **two
gadget types**.

| family | count | cone |
|---|---:|---:|
| `is_boolean` | 6,656 | 3 nodes |
| `sha256/rounds/N/round_step/assert_wrapping_sum_prime` | 128 | 307 nodes, 225 inputs |
| `sha256/schedule/N/assert_wrapping_sum_prime` | 48 | 274 nodes, 161 inputs |
| `sha256/final/N/assert_wrapping_sum_prime` | 8 | ~274 nodes |

307 nodes over 225 *inputs* is flat and degree 1 — no cut is needed, unlike ECDSA2's degree-7
interpolants and RCB formulas. `Ch`/`Maj`/`Σ`/`σ` are never their own assertions; they are linear
combinations of bits inside a wrapping sum. Two templates, ~184 nontrivial instances.

The one place SHA is genuinely harder is assembly: 6,840 assertions against ECDSA2's 1,048.
ECDSA2 names 458 in `E2Digits` at 594 s and needs `clear` before `assumption`; naming 6,840 will
not work. It does not have to — 6,656 of them map to **one uniform clause**, so the bridge should
stay inside `∀ r ∈ asserts_k, …` and map a template over it rather than destructuring. Decide
this before writing the generator; it is the one structural choice that does not carry over.

`meaning_gen` currently emits **0** lemmas for SHA and skips all 6,840: its path matching is
ECDSA-specific. Two new cases.


## Landing the cursor fix, and `meaning_gen` for SHA

### Cursor: the `private` keywords are gone

`Lfc3.readByte`, `readUlebLoop`, `readUleb` and `decodeDelta` are no longer `private`. That is
the whole Lean-side prerequisite for stating the refinement between the packed reader and
`Lfc3Bytes.readByteB`; nothing else in `Lfc3` changed, so `Cursor`, `decode` and every generated
module are untouched and the rebuild is semantically a no-op.

Remaining to land: state `Refines c bc` (`packBytes bc.bytes = c.page`, lengths agree, later
pages agree pagewise), prove `readByte_refines` from the two arithmetic facts
`packBytes (b :: bs) % 256 = b` and `packBytes (b :: bs) / 256 = packBytes bs` (both need only
`b < 256`, which `bytesOk` supplies), lift it through `readUleb` and `readDeltasChunk`, and have
the generator emit byte-list advice per page. The root is unaffected throughout.

### `meaning_gen` is no longer ECDSA-only

It hardcoded `Ecdsa2` in eight places and the node count `26939` in one, so it emitted **0**
lemmas for SHA and skipped all 6,840. Now parameterised by `NAME` (namespace and `consts`/`valid`
prefix), `SUPPORT` (the shared module — ECDSA2's is `E2Meaning`, which is not derivable from the
circuit name), and the node count read from the sidecar.

* **Regression:** the ECDSA2 output is **byte-identical** to the committed `Ecdsa2Meaning.lean`,
  267 lemmas.
* **SHA:** `NAME=Sha SUPPORT=ShaMeaning` emits **6,656** lemmas — every `is_boolean` assertion —
  with no `Ecdsa2` reference left in the output.

The `is_boolean` cone is three nodes: `1 * one * x + (p-1) * x * x`, i.e. `x - x²`. Factoring it
is done once by `SHA256F.isBit_of_zero_raw` in `circuits/SHA/Field.lean`, so each generated proof
is a `refine` plus the usual cone chain and `linear_combination` — the same shape
`isDigit_of_zero_raw` gives the ECDSA digit checks.

### The 184 wrapping sums, scoped

Still skipped, and correctly so: they are the real content. A `schedule` assertion's cone reads
exactly `input_block0`, `input_block1`, `input_block9`, `input_block14` and `outw0` — 5 words x
32 bits — which is `W[16] = σ₁(W[14]) + W[9] + σ₀(W[1]) + W[0]`, the specification's
`scheduleStep` on the nose. Confirmed by dumping the cone's inputs.

But the polynomial is **not** linear (measured: a linearity probe at random points fails), because
XOR on bits is `a + b - 2ab` and `σ₀`/`σ₁` are built from it. So each wrapping-sum lemma carries
the degree-2 bit algebra of `σ`/`Σ`/`Ch`/`Maj`. That is more than plumbing, and it is why the
earlier claim that "SHA's meaning layer is easier than ECDSA2's" needs qualifying: it is *simpler
in structure* — two templates against ECDSA2's seven families — but each template is a real
lemma, not a cone chain.

What it needs, in order: `ofBits`-to-field transfer for a 32-bit word given its 32 booleanity
facts; `xorW`/`andW`/`notW` as per-bit identities; `rotr`/`shr` as index shifts on the bit list;
then one lemma per template with the wrapping carry handled by the `w32` bound. `SHA/Spec.lean`
is deliberately stated over bit lists so these stay per-bit rather than becoming bitvector
lemmas.


## Byte lists: emitted, and the refinement that consumes them

### The refinement chain (`quadcert/Lfc3Bytes.lean`, all `[propext, Quot.sound]`)

| lemma | content |
|---|---|
| `packBytes_append` | `packBytes (l ++ r) = packBytes l + 256 ^ l.length * packBytes r` |
| `packBytes_mod` / `packBytes_div` | packing inverts one byte at a time, given `b < 256` |
| `readByte_refines` | the byte reader's result is the packed reader's result, and refinement is preserved |
| `readUleb_refines` | lifted through the ULEB loop, non-canonical rejection included |
| `readDeltasChunk_refines` | lifted to a whole chunk |

`BCursor` mirrors `Cursor` field for field — same `pageRemaining`, same page list — so `readByteB`
mirrors `readByte` branch for branch and the refinement is a structural induction. A first attempt
without `pageRemaining` in `BCursor` would not have gone through: the page-boundary and
last-byte cases have to line up.

**This is the switch, and it is better than changing `Cursor`'s type.** A generated certificate
proves the fast version by `rfl` and transfers:

```lean
have fast : readDeltasChunkB 148 1024 bc = .ok (deltas_5_1, bc') := by rfl   -- 4.5 s
obtain ⟨c', hslow, _⟩ := readDeltasChunk_refines 148 1024 hrefines fast
```

`Cursor`, `decode`, `raw_from_bytes`, the Merkle root and all 873 existing modules are untouched;
the 175 s / 9.5 GB `rfl` never runs.

### `lfc3_to_lean` emits the byte lists

Per page: `pageBytes_i : List Nat`, `pageBytes_ok_i : packBytes pageBytes_i = packedPage_i`, and
`pageBytes_range_i : bytesOk pageBytes_i = true` — both one `rfl`. Plus an index module
`inputBytes : List (List Nat)`.

**No chunking is needed for the page check**, contrary to what the earlier note here assumed:
a full 4,096-byte page checks in **3.3 s / 511 MB** by plain `rfl`, because the kernel evaluates
the `packBytes` fold strictly instead of retaining an intermediate per byte. That is the same
asymmetry that makes reading *from* the packed numeral expensive — the `%` results are forced
late — and it is why `packBytes_append` turns out to be insurance rather than a requirement.
Measured on the regenerated ECDSA2: `E2Bytes0` (full page) 2.9 s, `E2Bytes12` (partial) 1.6 s, so
about 38 s for all 13 pages, parallel across modules. Root unchanged: `e553aae9…`.

### `cursorAt_refines` closes the chain

`bcursorAt`, `packBytes_drop`, `bytesOk_drop`, `PagesRefine_drop`, `PagesRefine_getD` and
**`cursorAt_refines`** are proved, all `[propext, Quot.sound]`. At any offset, the byte cursor
built from the checked page lists refines the packed cursor the generated modules already name,
so the entry point into the fast reader is available:

```
cursorAt_refines  ->  Refines  ->  readByte_refines  ->  readUleb_refines
                                                     ->  readDeltasChunk_refines
```

**The emitted pages are zero-padded to `pageSize`.** `PagesRefine` needs `pageSize ≤ bs.length`
for every later page, which the final short page would fail. `packBytes` is little-endian, so
trailing zeros do not change the value and `pageBytes_ok` still holds — measured, the padded last
page checks in 2.8 s. Without the padding the refinement is proved but undischargeable, which is
the kind of gap that only shows up when something tries to use it.

### The switch is landed, and the SHA blocker is gone

`lfc3_to_lean` now emits, per layer, a byte cursor and a refinement witness beside every packed
cursor, and each `Deltas` module goes through the byte reader:

```lean
theorem deltas_ok_5_1 :
  readDeltasChunk 148 1024 cur_5_d1 = .ok (deltas_5_1, cur_5_d2) :=
  readDeltasChunk_transfer 148 1024 href_cur_5_d1 href_cur_5_d2
    (by rfl : readDeltasChunkB 148 1024 bcur_5_d1 = .ok (deltas_5_1, bcur_5_d2))
```

`readDeltasChunk_transfer` needed one more lemma than expected: the refinement produces *some*
packed cursor, and a certificate has to land on the specific one the next chunk starts from.
`Refines_unique` (via `PagesRefine_unique`) pins it — every field of `Cursor` is a function of the
byte cursor, and `PagesRefine`'s catch-all arm forces the page lists to the same length.

**Measured on SHA-256's layer 5, the chunks that aborted:**

| module | before | after |
|---|---|---|
| `ShaDeltas5_1` | 173 s, 18.0 GB, **kernel abort** | **5 s, 0.70 GB** |
| `ShaDeltas5_6` | kernel abort | **4 s, 0.79 GB** |
| `ShaDeltas5_0` | 8 s | 4 s |
| `ShaBytes` (`pagesRefine`, 50 pages) | — | 12.6 s |
| `ShaLayerCursors5` (13 witnesses) | — | 2 s |

`deltas_ok_5_1` depends on `[propext, Quot.sound]`; `pagesRefine` on `[propext]`. The statement
proved is unchanged — it is still about `readDeltasChunk` on `cursorAt packedInput 54264` — so
`decodeCompressed`, `raw_from_bytes` and the root are untouched.

### `readSegmentsChunk` too, and where layer 5 now stands

`readBoundedB`, `readIndexListChunkB`, `readSegmentsChunkB` and their refinements are proved
(`readBounded_refines`, `readIndexListChunk_refines`, `readSegmentsChunk_refines`,
`readSegmentsChunk_transfer`), and the generator emits segment chunks through the byte reader in
the same shape as the delta chunks. This needed one more `private` dropped from `Lfc3`
(`readBounded`).

Regenerated SHA-256 and built layer 5 as far as it goes:

| module | before | after |
|---|---|---|
| `ShaDeltas5_1` | 173 s, 18.0 GB, kernel abort | 5 s, 0.70 GB |
| `ShaDeltas5_6` | kernel abort | 4 s, 0.79 GB |
| **`ShaDeltaTree5`** | **618 s, 18.7 GB** | **89 s, 1.20 GB** |
| `ShaSegments5_0` | — | 45 s, 4.35 GB |
| `ShaSegments5_1` | — | 30 s, 3.21 GB |
| `ShaSegmentsAll5`, `ShaDeltasAll5` | — | 7 s |
| `ShaBytes` (`pagesRefine`, 50 pages) | — | 13 s |
| **`ShaCompressedLayer5`** | unbuildable | **still fails: 135 s, 12 GB** |

All 12 delta chunks and both segment chunks build. The layer module fails at `tokens_ok_5` — and
`parse_layer_ok_5` inherits it — because **`readCompressedTokens` is the fourth packed-cursor
site** and has not been switched. It reads layer 5's 2,847 tokens through `readUleb`,
`readBounded`, `readIndexListChunk`, `readPhrasesChunk` and `readPhraseRootsChunk` on the packed
cursor, so it hits exactly the same wall.

That is the remaining step, and it is the same recipe a fourth time: drop the `private` from
those readers, mirror them over `BCursor`, prove the refinement by the same `cases` chain, and
emit `tokens_ok` through the transfer. `prefix_ok` and `segcount_ok` need nothing — they read a
handful of bytes and already pass.

The generated SHA modules are staged at `$SCRATCH/sha_lean2/` rather than committed, since
`ShaCompressedLayer5` does not build and would break `lake build quadcert`. One `lfc3_to_lean`
invocation regenerates them.


## The token stage: three costs, not one

`readCompressedTokens` was the last packed-cursor site. Switching it produced two more findings,
both measured, and both of which I had predicted would not be needed.

**1. The byte reader is proved for it.** `readPhrasesChunkB`, `readPhraseRootsChunkB`,
`readCompressedTokensB` and their refinements (`readPhrasesChunk_refines`,
`readPhraseRootsChunk_refines`, `readCompressedTokens_refines`,
`readCompressedTokens_transfer`) are all `[propext, Quot.sound]`, and `lfc3_to_lean` emits
`tokens_ok` through the transfer with byte parse cursors and `hrefParse_i` witnesses. This
required dropping `private` from five more `Lfc3` definitions.

**2. The counting loops were quadratic, independently of the cursor.**
`countSegmentTermsLoop` etc. used `let index := tokens.size - (fuel + 1); tokens[index]?`, which
recomputes a `List.length` and walks `index` cons cells every iteration. Rewritten to recurse on
the token list; the `none` branch was unreachable by construction, so nothing is lost.

**3. It still does not build, and the reason is a third, separate cost.** Measured on layer 5,
with the byte reader *and* structural counting in place:

```
(readCompressedTokensB 1775 segLens_5 bcur_5_s2).isOk = true   -- no literal comparison at all
  -> 125 s, exceeds the 12 GB cap
```

`isOk` forces the counts and nothing else, so the expense is neither the byte reading nor the
comparison against emitted literals. It is `countPhraseTerms`: it walks every segment reference
in the layer — 89,048 terms' worth — and each one does `lengths[segmentIndex]?` on a 1,775-entry
`Array`, which is a list walk. That is ~1.6x10^8 steps inside a single `rfl`.

**The `PTree` treatment fixed it, and SHA-256's largest layer now parses.**

| module | originally | after bytes + structural counting | after the trees |
|---|---|---|---|
| **`ShaCompressedLayer5`** | unbuildable | 135 s, 12 GB, abort | **37 s, 5.1 GB, builds** |

`parse_layer_ok_5`, `tokens_ok_5`, `deltas_all_ok_5` and `segments_all_ok_5` all depend on
`[propext, Quot.sound]`. The layer is 89,048 terms, 11,952 deltas, 56,145 segment symbols and
2,847 tokens.

It did *not* require changing `readCompressedTokens`, as feared. `treeOk` / `treeAt` /
`treeAt_eq` generalise the `deltasOk` pattern; `countSegmentTermsLoopT`, `countPhraseTermsLoopT`
and `countPhraseTokensLoopT` are tree-indexed counterparts with `_eq` lemmas; and
`readCompressedTokensBT` is a *byte-side* reader that takes both trees and **checks them inline**
— `lengths` is a parameter but `phrases` is produced by the read itself, so there is nothing to
state a hypothesis about until it exists. `readCompressedTokensBT_eq` discharges to
`readCompressedTokensB`, and `readCompressedTokens_transferT` chains that to the packed
statement. So `readCompressedTokens`, `readCompressedLayer` and
`readCompressedLayer_eq_of_stages` are untouched and every existing certificate still means what
it did.

The generator emits `segLensTree_i : PTree Nat` and `phrasesTree_i : PTree (Array Nat)` beside
each layer (`PTree.leaf` when the encoding is flat, which makes lookups fall back to indexing).

### What this cost me, and the lesson

I called `readCompressedTokens` "the last site" after the deltas were switched, and "the last
site" again after the segments were. Both times the claim came from reading the code and seeing
one remaining `by rfl`, not from measuring. The token stage had three independent costs stacked
in one `rfl` — cursor representation, loop shape, and lookup complexity — and each was invisible
until the one in front of it was removed.

**Measure the specific sub-expression before predicting what a fix will unblock.** The
`isOk`-versus-full-equality probe that isolated this in one command was available at every step
and would have shown all three at the start.

### Build state

`Lfc3.lean` has changed (five `private` keywords dropped, three counting loops restructured), so
every generated `quadcert` module is stale. **Rebuild only with `formal/tools/leanseq quadcert
20 .`** — a bare `lake build` on any downstream target rebuilds all 873 modules 16-wide and
crashed the machine once already. The SHA modules are staged at `$SCRATCH/sha_lean3/`, not
committed, because `ShaCompressedLayer5` does not build.


## Incident: `quadcert/Sha256.lean` deleted and reconstructed

While iterating on the SHA-256 **circuit**, a cleanup step `rm -f circuits/quadcert/Sha*.lean`
deleted `Sha256.lean` — the hand-written, *non-generated* SHA-256 used by `CircuitCommitment` for
page-leaf hashing. Its name collides with the generated `Sha*` modules. `circuits/quadcert/` is
untracked, so git had no copy, and there were no snapshots.

**Recovered in full from the surviving `.olean`**, which still loaded under `lake env lean`
because that path does not rebuild. A metaprogram enumerated the module's 83 declarations and
printed each definition, including the private ones (whose `_private.quadcert.Sha256.0.…` names
cannot be written as name literals, so they had to be reached by string match) and the four
well-founded recursions (`scheduleLoop`, `packedScheduleLoop`, `rounds`, `packedBlocks`), whose
readable clauses came from `Meta.getEqnsFor?` rather than the `brecOn` body.

**Verified three independent ways:** `hash [] = e3b0c442…7852b855`,
`hash [97,98,99] = ba7816bf…f20015ad`, and `Ecdsa2Commitment0` — which proves a real 4,096-byte
page's leaf hash by `decide` against this module — builds unchanged. Any deviation would fail the
third check.

Only comments and formatting are new. Two lessons:

* **Never glob-delete in `circuits/quadcert/`.** Generated and hand-written modules share the
  directory and, as here, share prefixes. Move to a scratch directory and delete explicitly, or
  filter on the "Generated by" header.
* **A compiled `.olean` is a complete backup of semantics.** Worth knowing, but not worth
  relying on: comments and proof scripts do not survive, and only `def`s recover cleanly.


## SHA-256 decodes

**`Quadcert.Gen.Sha.decode_ok : decode p256 packedInput deltaTrees = .ok decoded`** is proved,
`[propext, Quot.sound]`. The committed 203,104 LFC3 bytes of the one-block SHA-256 circuit —
118,114 terms over 6 layers, 50 pages — decode to the circuit inside the Lean kernel. All 342
generated modules build; total 2,559 s (43 min) serialized, 889 MB of oleans.

| module | |
|---|---:|
| `ShaDecoded` | 238 s, 11.6 GB (the largest) |
| `ShaCommitment14` | 80 s, 2.76 GB |
| `ShaExpansion5_0` | 61 s, 0.78 GB |
| `ShaCompressedLayer5` | 37 s, 5.1 GB |

This was the item recorded as "chunk the compressed-layer parse (new blocker)". It took four
rounds, because the token stage had four independent costs stacked behind one `by rfl`:

1. the cursor held a 4 KB page as a bignum and `readByte` returned `page % 256`, forced late;
2. the counting loops indexed an `Array` by `size - fuel`, quadratic in the token count;
3. `countPhraseTerms` did an `O(S)` list walk per segment reference, ~1.6e8 steps;
4. — and the earlier three fixes each only exposed the next.

Each was invisible until the one in front of it was removed, and each time the remaining `by
rfl`s *looked* like the last site. The probe that separated them —
`(reader …).isOk = true` versus the full equality, one command — was available from the start.

### What is left for SHA-256

The decoder arrow is closed. Remaining, in order: `raw_from_bytes` (the artifact-to-`RawCircuit`
refinement, which for ECDSA2 is generated advice plus checks), `ValidScheduling`, and then the
meaning layer — where `meaning_gen` already emits all 6,656 `is_boolean` lemmas and the 184
wrapping sums need the bit algebra described above.


## `raw_from_bytes`, `ValidScheduling`, and the per-bit algebra

### `raw_from_bytes` was blocked by a name, not by mathematics

`sha256_artifacts` emits the sidecar side under the name **`Sha256Blk`** (`name: "Sha256Blk"` in
the driver), and `Sha256BlkData.lean` already contains `raw`, `advice`, `artifactRaw_eq_raw` and
`raw_from_bytes` — the exact ECDSA2 shape. The earlier `lfc3_to_lean` run used `NAME=Sha`, so the
decode side landed in `Quadcert.Gen.Sha` while `raw_from_bytes` cites
`Quadcert.Gen.Sha256Blk.decode_ok`. Regenerated with the right name; 341 decode modules plus 774
sidecar modules, 1,115 in total, now building under `leanseq`.

Those 774 modules *are* item 2: `Asserts`, `Backed`, `Corr`, `Filt`, `Flat`, `Group`, `Inv`,
`NodeChk`, `NodeFn`, `Nodes`, `OkCheck`, `Perm`, `SumLocal`, `Wire`, `Zero` — the `ValidScheduling`
machinery, in the same families ECDSA2 uses.

### The per-bit algebra exists: `circuits/SHA/Bits.lean`

All `[propext, Quot.sound]` or weaker:

| lemma | content |
|---|---|
| `bitAt_ofBits` | `bitAt (ofBits bs) i = bs.getD i 0` for a boolean list — `bitAt` inverts `ofBits` |
| `zipBits_eq_ofBits` | `zipBits f x y = ofBits ((range 32).map fun i => f (bitAt x i) (bitAt y i))` |
| **`bitAt_zipBits`** | `bitAt (zipBits f x y) i = f (bitAt x i) (bitAt y i)` for `i < 32`, `f` bit-valued |
| `bitAt_shr` | `bitAt (shr n x) i = bitAt x (n + i)` — a shift is an index offset |
| `bitAt_w32` | `w32` does not disturb bits below 32 |
| `zipBits_congr` | `zipBits` depends on its arguments only through their first 32 bits |

`bitAt_zipBits` is the one that matters: it turns a statement about a 32-bit word into 32
independent statements about bits, so `xorW`/`andW`/`notW` — and therefore `σ₀`, `σ₁`, `Σ₀`,
`Σ₁`, `Ch`, `Maj` — become per-bit identities. That is what keeps the 184 wrapping-sum meaning
lemmas degree-1 per bit instead of degree-2 in packed words, and it is why `Spec.lean` was written
over bit lists in the first place.

Two argument-order traps, both caught by the typechecker: `shr` is `shr n x`, not `shr x n`; and
`rotr` likewise takes the amount first.

### Remaining for the meaning layer

`rotr` as an index rotation (the `bitAt_shr` analogue, with the wrap-around case), then one
template lemma per assertion family with the wrapping carry discharged by `Word32.val_lt`. The
`is_boolean` half is already generated — 6,656 lemmas from `meaning_gen` with `NAME=Sha`.
