# Formal verification of the Longfellow ZK circuits

Lean 4 proofs that the bytes shipped in an artifact file describe a circuit whose constraints
force a published specification to hold.

Three circuits are covered end to end. For each, one theorem takes the artifact payload and an
accepting witness and concludes two things at once: those bytes hash to the root the verifier
pins, and the specification holds of the values on the wires.

```lean
theorem Ecdsa2.Assembly.ecdsa2_certified_bytes
    (c : Lfc3.DecodedCircuit)
    (hdec : Lfc3.decode Lfc3.p256 packedInput deltaTrees = .ok c)
    (inputs : Nat → F) …
    (hacc : Accepts ((c.toRaw advice).toQuad (Ecdsa2.consts F)) inputs) … :
    CircuitCommitment.rootOfPacked packedInput = formalRoot
      ∧ ∃ r s e_nat, … ∧ StandardEcdsaVerify pk e_nat r s order params

theorem Sha256Blk.sha256_certified_bytes
    (c : Lfc3.DecodedCircuit)
    (hdec : Lfc3.decode Lfc3.p256 packedInput deltaTrees = .ok c)
    (inputs : Nat → F) (hin0 : inputs 0 = 1)
    (hacc : Accepts ((c.toRaw advice).toQuad (Sha256Blk.consts F)) inputs) :
    CircuitCommitment.rootOfPacked packedInput = formalRoot
      ∧ (List.range 8).map (outWord inputs)
          = SHA256.blockFrom ((List.range 8).map (hWord inputs)) (msgBlock inputs)
```

`packedInput` is the subject of both conjuncts, so the bytes that hash to `formalRoot` are
syntactically the bytes `hdec` decodes — a reader does not have to check by other means that the
literal named in the soundness half is the committed one. `Rung1.certified_bytes_accept_iff_spec`
has the same shape, with an `iff` in place of the implication.

All three depend only on `propext`, `Classical.choice`, `Quot.sound`. There is no `sorry` and no
custom axiom anywhere under `circuits/`.

## How this works

A circuit consists of layers, a layer consists of a list of quads, and a quad is a 4-tuple `⟨g, h0, h1, k⟩` that indicates wire `g` accumulates `k · v[h0] · v[h1]` from the layer beneath. LFC2 is an optimized circuit format for writing a circuit's quads in layer-by-layer form.

A circuit is identified by computing the hash of these quads.

We aim to prove a statement of the form: "The circuit identified by hash XXX verifies that there exists inputs (x,w) such that SPEC(x) holds."
Notice that 'w' is not part of the verification statement, but may be used in the support of the verification.

To do so, the Lean 4 kernel verifies the following string of assertions:

1. There exists a string of bytes that hashes to XXX.
2. Those exact bytes can be parsed into quads.
3. Those quads implement a list of assertions a1(x,w), ..., an(x,w).
4. If for all i\in [1,n], a_i(x,w) = 0, then SPEC(x) holds.

Each of these steps requires special measures.

## Step 1 — the bytes, and their hash

`packedInput` and `deltaTrees` are the **artifact bytes**: the same LFC3 payload the deployed
verifier loads. The payload is one byte string, but it is committed by a **page-Merkle tree** over
4096-byte pages rather than by a single hash. `pageSize` in `Core/CircuitCommitment.lean` matches
`FORMAL_PAGE_SIZE` in `rust/core/proto/src/commitment.rs:33`, so the two implementations agree on
the root.

Three domain-separated hashes:

```
leaf = SHA256( "LFZK-LFC-PAGE-V1\0" ‖ u64LE byteLength ‖ u64LE pageIndex ‖ u32LE pageLength ‖ page )
node = SHA256( "LFZK-LFC-NODE-V1\0" ‖ u32LE level ‖ left ‖ right )        -- odd node duplicated
root = SHA256( "LFZK-LFC-ROOT-V1\0" ‖ u32LE pageSize ‖ u64LE byteLength ‖ u64LE pageCount ‖ treeRoot )
```

The total length and the page index sit *inside* each leaf, so pages cannot be reordered,
duplicated or truncated without changing the root. Each page is one packed `Nat` in its own module
(`…Packed{k}.lean`) and its leaf hash is proved in its own module (`…Commitment{k}.lean`) by
`decide +kernel`; only the 32-byte digests are combined afterwards, so no page content appears
anywhere in the interior of the tree.

### Why pages, measured

There is **no 4 KB limit in Lean**. The kernel will hash any length; what it costs is memory, and
the cost is linear with a steep constant, because SHA-256's message schedule ends up unrolled in
the reduced term:

| page bytes | wall | peak RSS |
|---:|---:|---:|
| 1,024 | 3.5 s | 0.95 GB |
| 4,096 | 11.0 s | 2.8 GB |
| 8,192 | 21.9 s | 5.3 GB |
| 16,384 | 49.3 s | 10.5 GB |

At roughly 0.65 GB per KB, a 16 KB page already wants 10.5 GB, and hashing the 203,104-byte
SHA-256 payload in one piece would want on the order of 130 GB. 4,096 bytes costs 2.8 GB, which
leaves room under the `-M 16000` per-worker cap for the rest of the module. **So the page tree does
not make the work smaller — it makes it fit**, and since each page is an independent module it also
parallelises. Fifty pages at 11 s is about nine minutes.

`Core/CommitPacked.lean`'s `rootOfPacked` derives the page indices and page lengths from the
payload itself, so the root and the parser are stated about the same object rather than about two
literals that happen to be equal.

## Step 2 — the bytes into quads

**The pages are a hashing device, not a parsing unit.** `Lfc3.decode` reads the same paged payload
through a `Cursor` (`Core/Lfc3.lean`), and `readByte` is where the boundary lives: when
`pageRemaining` reaches 1 it pops the next page off `laterPages` and continues. Above `readByte`
the page structure is invisible.

So there is no boundary case to handle. Nothing in the format is page-aligned, and a ULEB varint, a
16- or 32-byte field element, or a quad's delta triple may straddle a 4 KB boundary with no code
noticing — the abstraction never exposes one. Paging affects *what is hashed*, never *what is
parsed*.

### Quads are stored as differences, not as tuples

A layer is not a list of `⟨g, h0, h1, k⟩` tuples on the wire. It is three dictionaries:

* `deltas : Array Delta` — the distinct `(Δg, Δh0, Δh1, kIndex)` steps the layer uses;
* `segments : Array (Array Nat)` — repeated runs of delta indices;
* `tokens` — the stream of segment indices.

Expansion walks tokens → segments → deltas and adds each delta into a running `(g, h0, h1)` state
modulo `2^32`, taking `kIndex` verbatim. So a quad is stored as a difference from its predecessor,
and that difference is stored once and referenced. This is why term counts and byte counts diverge
so widely — the GF(2^128) SHA-256 circuit is 98,993 terms in 28,327 bytes, about 0.29 bytes per
quad.

Two stages, each with its own generated proof modules, composed by `decode_ok`:

1. `decodeCompressed` → `CompressedCircuit` — `…Header`, `…CompressedLayer{l}`, `…ParseSteps`;
2. expansion → `DecodedCircuit` — `…Expansion{l}_{j}`, `…ExpandedLayer{l}`.

Two costs had to be engineered away. Expansion needs `deltas[i]`, and array indexing costs `O(i)`
in the kernel, so `decode` takes the extra **`deltaTrees`** argument: one bisection tree per layer,
supplied as advice and then *checked* — `deltasOk` decides that the tree answers exactly what
indexing would, and `deltaAt_eq` proves expansion is therefore unchanged in meaning, only in cost.
And both stages are otherwise a single `rfl` per layer, which does not fit; `readSegmentsChunk` and
`expandChunk` split them, with `expandChunk_compose` gluing chunks without re-running either.

## Step 3 — the quads into assertions

Step 3 is uniform and mechanical, the same machinery serves any circuit.

**A quad whose coefficient is zero is not a computation.** `layerFails` reads it as a constraint:

```lean
def layerFails (layer : LayerData F) (vin : Nat → F) : Prop :=
  ∃ t ∈ layer.terms, t.k = 0 ∧ vin t.h0 * vin t.h1 ≠ 0
```

so a term `⟨g, h0, h1, 0⟩` contributes nothing to wire `g` and instead demands
`v[h0] · v[h1] = 0`. That, plus every output wire being zero, is all `Accepts` means:
`Accepts c inputs := ¬ circuitFails c inputs ∧ outputsZero c inputs`.

The quads alone do not say *which* product is an assertion *of what*. That comes from the
compiler's **sidecar**, and it arrives as four fields of `Lfc3.RawAdvice`: a DAG (`nodes`), a wire
map (`wireFn`), assertion records (`asserts`, each a triple `⟨assertedNode, wireLayer, wireIndex⟩`)
and the input `layout`. Everything else in a `RawCircuit` comes from the decoded bytes.

**None of the advice is trusted.** Two decidable checks tie it to the quads:

* **`ValidScheduling`** — eight fields, discharged by `ok_check`, `inv_check`, and the grouping
  certificates `perm_all`, `hom_all`, `corr_check`. Its substantive field is `sum_local`, a *local
  simulation*: each DAG sum node's value equals the layer value at its wire. `wire_inj` — no two
  nodes share a wire — is what makes that satisfiable, since `evalLayer` sums every term whose
  output is `g`. `sum_local_of_raw` derives the simulation by grouping each layer's quads by output
  wire and matching them term for term against the DAG.
* **`Backed`** (`backedRawWith`) — every record is carried by a real quad. Either the layer contains
  `⟨wireIndex, i, i, 0⟩` with `wireFn assertedNode = some (wireLayer + 1, i)`, in which case
  `v[i]² = 0` and so `v[i] = 0`; or `wireIndex < noutput` and
  `wireFn assertedNode = some (0, wireIndex)`, in which case `outputsZero` supplies it.

Separately — and this is a pin rather than a check on the advice — **`raw_from_bytes`** proves by
`rfl` that whatever the committed bytes decode to, extended by those four advice fields, *is* the
generated `raw` literal. The layer terms are shared with the artifact rather than copied, so what
that `rfl` actually checks is every dimension and constant the sidecar restates. It is the step
that makes all of the above a statement about the bytes instead of about a generated table.

`assertions_zero_of_accepts` then closes step 3: from `Accepts`, `ValidScheduling` and `Backed` for
every record, each asserted DAG node evaluates to zero. A sidecar that names an assertion no quad
backs makes `backed_check` false and the build fails; a sidecar whose DAG disagrees with the quads
fails `corr_check`. (`CoversConstraints` is the converse — no *unnamed* constraint — and is needed
only for the `↔` direction, not for `Accepts → assertions zero`.)

What the sidecar *is* trusted for is **names**. `layout` is what says position 3 holds the message
hash, and the assertion scope paths are what say which family a record belongs to. A wrong name
would give a true theorem about a different reading of the same wires, which is why the input layout
appears under residual trust below rather than among the checks.

## Step 4 — the assertions into the specification

Steps 1–3 are uniform: the same machinery serves any circuit. Step 4 is the only part that needs
application context, and it is where nearly all the effort goes.

Concretely, for SHA-256: `SHA/Spec.lean` defines the message schedule and compression as *folds*
(`schedule 48`, `rounds 64`), transcribed from FIPS 180-4. A circuit cannot produce a fold. It
produces an indexed recurrence with one witnessed word per computed quantity and one assertion per
step. `SHA/Sound.lean` proves the two agree, and the bridges instantiate it:

* every 32-bit value appears as its 32 bits, each asserted boolean (6,656 assertions);
* each computed word is asserted equal to a wrapping sum of its addends (184 assertions);
* `σ₀`, `σ₁`, `Σ₀`, `Σ₁`, `Ch`, `Maj` never get assertions of their own — they are degree-≤2
  polynomials in the bits *inside* those wrapping sums. `SHA/Sigma.lean` is the bridge for that.

The residual gap between "every assertion is zero" and "these particular nodes are zero" is closed
by `Bridge/Sha256/S2Connect`, `S2Flat`, `S2Assert` and `S2Bytes`: 42,168 references into a
6,840-entry assertion list, resolved through a flat index rather than by membership search.

### The chain, bottom to top

| step | what it produces | where |
|---|---|---|
| 1. commit | `rootOfPacked packedInput = formalRoot` — the pages hash to the pinned root | `Gen/*/…Commitment*.lean`, `Core/CommitPacked.lean` |
| 1. bytes | `packedInput`, `deltaTrees` — the artifact's LFC3 pages | `Gen/*/…Packed.lean`, `…DeltaTree*.lean` |
| 1. decode | `DecodedCircuit` — dimensions, constants, layer terms | `Core/Lfc3.lean` |
| 1. extend | `RawCircuit` — decoded fields plus the sidecar's structural advice | `Core/Ingest.lean` |
| 2. pin | `raw_from_bytes` : what the bytes decode to **is** the generated literal | `Gen/*/…Data.lean` |
| 2. quads | `QuadCircuitData` — layers of `QuadTerm ⟨g, h0, h1, k⟩` | `Core/Ingest.lean` |
| 3. accept | `Accepts` — no layer assertion fails, every output wire is zero | `Core/Semantics.lean` |
| 3. structure | `assertions_zero_of_bytes` — every asserted node evaluates to `0` | `Bridge/*/…Sound.lean` |
| 4. meaning | each assertion, or family of them, read in specification vocabulary | `Bridge/Sha256/`, `Gen/E2/` |
| 4. spec | `StandardEcdsaVerify`, `SHA256.blockFrom` | `circuits/ECDSA/EcdsaSpec.lean`, `circuits/SHA/Spec.lean` |


## What is proved

| circuit | field | assertions | status |
|---|---|---:|---|
| ECDSA2 (P-256 verification) | 𝔽ₚ₂₅₆ | 1,048 | **all four steps** — `ecdsa2_certified_bytes` |
| SHA-256, one block | 𝔽ₚ₂₅₆ | 6,840 | **all four steps** — `sha256_certified_bytes` |
| Rung1 (on-curve check) | 𝔽ₚ₂₅₆ | 297 bytes | **all four steps** — `certified_bytes_accept_iff_spec`, an `iff` |
| SHA-256, one block | GF(2¹²⁸) | 6,840 | **steps 1–3** — `Sha256Gf2.certified_bytes_assertions_zero`; step 4 in progress |
| mdoc_hash | GF(2¹²⁸) | 18,956 + booleanity | **step 4** — `MDoc.Gadget.meaning_of_circuit`; all three arithmetic gadgets proved *and* threaded through `meaning`, `assert_final_hash` closed (`MDoc.Mux.hsel_of_final_hash`), and the SHA hypothesis reduced to one `blockFrom` per block; steps 1–3 not started |
| mdoc_signature | 𝔽ₚ₂₅₆ | 2,108 | **step 4** — `MDoc.sig_meaning`, on top of `soundness_of_v2`; its `chunk_eq` families threaded through `ChunkEq` too, so `MDoc.Gadget.full_meaning_of_circuit` composes both halves over the circuits' own gadgets; steps 1–3 not started |

The first three are the conjunction of a commitment root and a soundness theorem, proved in
`Bridge/*/…EndToEnd.lean`; the soundness halves alone are `ecdsa2_sound_of_bytes`,
`sha256_block_of_bytes` and `accepts_artifact_iff_spec`.

The two mdoc rows run the *other* way round: step 4 first, steps 1–3 not yet. `circuits/mdoc/`
censuses each circuit's assertion set from the Rust (`ASSERTIONS.txt`, `ASSERTIONS-SIG.txt`) and
proves the meaning implication from it, so the layer is being built against a checkable list of
families rather than against an ingested artifact. `MDoc.full_meaning` composes the two halves
into `ValidPresentationFull`. Ingesting the mdoc artifacts is the join point, and the LFC3 parse
cost measured on one-block SHA-256 is the reason it has not been attempted.

### The GF(2^128) variant, and why it exists

The deployed mdoc **hash** circuit — SHA-256, the CBOR window checks, the MACs — is compiled over
GF(2¹²⁸), not over a prime field (`mdoc_zk/compile/src/generate_hash.rs`). That changes step 4 and
nothing else: over a prime field the compiler embeds a 32-bit word *positionally*, as `Σ 2^i·bᵢ`,
and asserts `Π_j (C − P − j·2^32) = 0`; over GF(2¹²⁸) it embeds the word in the **exponent** of the
field generator, `inject(v) = Π_i (1 + (α^(2^i) − 1)·bᵢ) = α^v`, and asserts
`Π_j (got − α^(j·2^32)·want) = 0` (`circuits/analog_adder/src/circuit.rs:117` against `:58`). So
`SHA/Wrap.lean`'s positional theory does not apply and `circuits/GF128/` is its replacement.

The same one-block circuit compiled over both fields is otherwise *structurally isomorphic* —
identical 6,657 inputs, identical 6,840 assertions at identical scope paths — and the binary-field
artifact is markedly cheaper to decode: 28,327 bytes in 7 pages against 203,104 in 50, and a worst
layer of 1,048 distinct deltas against 11,952. A product tree of degree-2 nodes segments well; a
32-term sum with 32 distinct coefficients does not.

`circuits/GF128/` carries no assumptions: `Irred.isGen_of_root` builds everything from `P(α) = 0`
alone, where `P(x) = x^128 + x^7 + x^2 + x + 1` is the deployed reduction polynomial. Its
irreducibility is a theorem, obtained from the kernel-checked fact that `x` has multiplicative
order `2^128 − 1` rather than from a factorisation search.

#### What the binary field buys, and what it costs

The 104 constants the artifact carries are all accounted for, each pinned by a `decide +kernel`
against the deployed table: `1`, `0`, the 32 injection coefficients `α^(2^i) + 1`, the six window
multipliers `α^(j·2^32)`, and — the family that took the longest to find — 64 entries holding
`α^(Kₜ)` for the SHA-256 round constants (`Gf2Sound.constNat_round`). That last one is what ties
the circuit to *SHA-256's* constants rather than to sixty-four arbitrary field elements.

It also explains a shape the prime-field bridge does not have. `algsimp` folds the round constant
into a *product node* rather than injecting it bit by bit, so a round cone's exponent comes out as
`Kₜ + Σ 2^i·bᵢ` — the round constant is a summand of the exponent, exactly as
`T1 = h + Σ₁(e) + Ch + Kₜ + Wₜ` has it, and it is why the adder's addend count `n` is 7 for `a`
and 6 for `e`.

The cost is that a 32-bit word's injection is a *product tree of 32 factors*, where the prime
field has one flat 32-term sum. `Core/ConeChain.lean` exists for that (a chain node may read
earlier chain nodes, which `ConeMid` cannot express). Templating those trees was measured and
rejected: the artifact's 428 injection cones have only 7 distinct leaf-kind mixes but **204**
distinct templates, because the compiler puts the fused 2-, 3- and 4-term factors at different
positions in each — ~2 instances per template, which defeats the point.

What replaces it is the observation that makes the binary field pay for itself. On a boolean wire
an injection factor *is a power of α* (`GF128.injFactor_eq_pow`), and a product of powers of α is
a power of α **whatever the association and whatever the order**. So the tree shape and the leaf
ordering both stop mattering, every row of every cone is one of two shapes,

    [(0,0,0)] ++ [(2+i, a, b) …]   an injection factor  → α^(2^i · x)
    [(k, a, b)]                    a product            → α^(K + eₐ + e_b)

and one lemma each (`chainNode_fac_pow`, `chainNode_prod_pow`) covers all 46,460 of them. In the
prime field an injection factor is a positional term inside a linear form and you have no choice
but to track where it sits; here it is a group element, and position is meaningless.

`Core/ConeChain.chainVals_row` reads a single row against the whole chain, so an instance pays
`O(1)` per row rather than unfolding its cone. Two things about that were only found by measuring:
leaving each row's `have` in the local context makes every later step pay to traverse it (0.10 s
per row at 63 rows against 0.40 s at 255 — the cone is a tree, so each row is `clear`ed once its
consumer is emitted), and `omega` on a flat exponent does not scale at all — 172 s at 64 atoms and
no answer in ten minutes at 128, where a chain of `Nat.add_le_add` over per-term bounds is
instant.

#### The assertion census, and what closes each class

The whole binary-field artifact asserts exactly **two** things:

| shape | count | reading |
|---|---:|---|
| `1·(one·b) + 1·(b·b)` | 6,656 | `b + b² = 0`, so `b` is a bit |
| `1·(x·y)` | 184 | a wrapping-sum product vanishes |

6,656 + 184 = 6,840, which is every assertion in the circuit. Both booleanity coefficients are
the *unit* constant, because in characteristic 2 the prime field's `-1` is `1`; so the cone is one
constant lighter than the prime-field bridge's. `Gf2BoolEdges.lean` discharges all 6,656 as one
edge list (13 slices of 512, ~11 s each) against one template lemma proved once, and the bit nodes
it names sum to exactly `Gf2Words.allBits_sum` — computed independently from the word layer, so
the circuit asserts booleanity of precisely the bits that layer names, no more and no fewer.

That leaves one obligation per injection factor: *which* bit it injects. There are 24,960, so a
per-row proof is the thing to avoid. Evaluating every row at every boolean assignment of its wires
shows they are **five** functions — a witnessed bit (13,696), a three-way xor (6,544), a two-way
xor (624), `Ch` (2,048 = 64 rounds × 32 bits) and `Maj` (2,048) — spelled in **29** distinct
operand orders. Classified syntactically that is 29 cases; classified by truth table it is five,
and the orders cost nothing: a row's value is a `List.sum` of products, so it is invariant under
permuting the pairs and under swapping within a pair. `Gf2Row.sum_eq_of_perm` makes all 29 the
same statement and checks the permutation *as data*, so a whole cone's rows are covered by one
`Form.isBit` and three `decide`s rather than by 24,960 proofs — measured at 0.01 s per row against
0.15 s for the injection layer itself.

The result, per cone, is `injZ<o>`: the cone's value is `α^(Σ 2ⁱ·bᵢ)` with nothing standing but
`inputs 0 = 1` and the artifact's own `is_boolean` assertions. All 29,487 cone leaves are either
the `one` wire or one of the 6,656 asserted bits, so that hypothesis closes.

#### The circuit reads as SHA-256, addend by addend

With the row forms in place, every `assert_wrapping_sum_gf2` cone can be partitioned into 32-row
addend groups and each group's wires resolved against the word layer's bit-node lists. Run over
the artifact (`tools/sha256/gf2_word_probe.py`, report in `tools/sha256/GF2_WORD_AUDIT.md`), **all
184 instances resolve completely, with zero unresolved groups**, and what comes out is FIPS 180-4:

    W4 (48)   W[t+16] = σ₁(W[t+14]) + W[t+9] + σ₀(W[t+1]) + W[t]
    W6 (63)   oute[t] = outa[t-4] + oute[t-4] + Σ₁(oute[t-1]) + Ch(…) + W[t] + Kₜ
    W7 (64)   outa[t] = oute[t-4] + Σ₁(oute[t-1]) + Ch(…) + W[t] + Σ₀(outa[t-1]) + Maj(…) + Kₜ
    W2 (8)    h1[i]   = hin[i] + (a…h at round 63)

with rotation offsets Σ₀ (2,13,22), Σ₁ (6,11,25), σ₀ (7,18,≫3), σ₁ (17,19,≫10), and the register
rotation `e = oute[t-1] … h = oute[t-4]` (`hinBits` for the first four rounds). None of that is a
hand-written correspondence — the words, the offsets and the indexing all come out of the
committed bytes.

One detail is worth stating because it is *measured* rather than assumed: `σ`'s third leg is a
**shift**, not a rotation, and a shift shows up as an arity split. `σ₀`'s `≫3` leg vanishes at the
top three bit positions, so that addend is 29 three-leg rows and 3 two-leg rows; `σ₁`'s `≫10`
gives 22 and 10. A rotation would give 32 three-leg rows throughout.

The `Nat` algebra this lands on — `bitAt` inverting `ofBits`, and `σ₀ σ₁ Σ₀ Σ₁ Ch Maj` reduced to
one identity per output bit — is `SHA/Bits.lean` and `SHA/Sigma.lean`, which mention no field at
all and so port from the prime-field bridge unchanged. `Gf2Spec.lean` is the four case analyses
that say the two *spellings* agree: over a prime field the circuit writes xor as `a + b − 2ab`
because that is the only degree-2 polynomial that does it, and over GF(2^128) addition simply is
xor.

#### One instance of every class, all the way through

One word-layer theorem per wrap class closes the chain. All five are axiom-clean, from the
committed bytes:

    W2   h1[1]    = (outa[62] + hin[1]) % 2^32
    W4   W[23]    = (W[7] + sigma0 (W[8]) + W[16] + sigma1 (W[21])) % 2^32
    W6   oute[6]  = (outa[2] + oute[2] + W[6] + Sigma1 (oute[5])
                     + Ch (oute[5]) (oute[4]) (oute[3]) + K.getD 6 0) % 2^32
    W6b  oute[25] = the same shape, at t = 25 and associated differently
    W7   outa[9]  = as spelled out below

`Gf2WordW7_9.lean` in full, in 27 s:

    wv (outaBits 9) = ( wv (outeBits 5) + wv (wordBits 9) + Sigma1 (wv (outeBits 8))
                      + Ch (wv (outeBits 8)) (wv (outeBits 7)) (wv (outeBits 6))
                      + Sigma0 (wv (outaBits 8))
                      + Maj (wv (outaBits 8)) (wv (outaBits 7)) (wv (outaBits 6))
                      + K.getD 9 0 ) % 2 ^ 32

`Sigma0`, `Sigma1`, `Ch`, `Maj` and `K` are `SHA/Spec.lean`'s own definitions, not restatements of
them, and `wv l` is `ofBits` of the bits at the node indices `l` — so both sides are pinned: the
left to the artifact's wires, the right to FIPS 180-4. The standing hypotheses are `IsGen α`,
`inputs 0 = 1`, the 6,656 `is_boolean` assertions being zero, and this wrap assertion being zero.
Nothing about words, rotations or round constants is assumed.

The route is: the seam (the cone as 32-bit modular arithmetic over up to 224 individual bits) →
one theorem per addend group, each turning 32 bits into a word via `Sigma1_bits`, `sigma0_bits`,
`Ch_bits`, `Maj_bits` or plain `ofBits` → one `ring` to reassociate. What makes each group a
single `ring` rather than 32 per-bit permutation steps is the canonical wire ordering: `xor` legs
by rotation offset and `maj` wires by round, which is free because those forms are symmetric and
their `Form.pairs` agree as multisets under any order.

`σ₀`/`σ₁` need one thing more, and it is the part worth stating because it is *measured* rather
than assumed. `sigma0_bits` puts the `≫d` leg **last** and models it by reading past the end of a
32-element list, where `List.getD` returns `0`; the compiler instead omits the leg, emitting a
two-leg row. Shift and rotation are indistinguishable from a single row, so the leg order is
decided per addend: a rotation offset occurs in all 32 rows, a `≫d` offset in exactly `32 − d`.
That detection is also what merges an addend's two- and three-leg rows, which the naive grouping
splits apart; the boundary rows then close on `xb x 0 = x`.

`ecdsa2_sound_of_bytes` carries four residual hypotheses that are *not* circuit facts and cannot
be: the group order of E(𝔽ₚ) kills the public key, the generator and the reconstructed point, and
`order` is P-256's `n`. Those are standard facts about the curve.

### Residual trust

1. **The root must be pinned externally, and it binds computationally.** The theorems reduce the
   audit to one 32-byte value: an auditor checks that `formalRoot` is the root the deployed
   verifier pins, rather than diffing hundreds of kilobytes. Reading *these* bytes back out of
   that root then relies on SHA-256 collision resistance, the root is a commitment, not an
   unconditional proof of byte equality.
2. **The input layout is chosen, not checked.** Position 1/2 is the public key, 3 the message
   hash; `wordBits t` is `input_block t`; and so on. `layout` is carried into `RawCircuit` and
   read only by `RawCircuit.pos`, a name-to-position lookup for the bridge's convenience —
   `toQuad`, `Accepts` and `interpDag` never mention it. So a permuted layout would still yield a
   true theorem, about a different reading of the same wires. Every other sidecar claim is checked
   against the quads in step 3; this is the exception, and the one an auditor has to read.
3. **Soundness only.** These are `Accepts → spec` theorems. Completeness (`spec → Accepts`) is a
   separate question, needs `CoversConstraints`, and is not what protects a verifier.

## Layout

```
circuits/
  quadcert/          the certificate: bytes → circuit → assertions zero
    Core/            (19)    Lfc3 decoder, quad semantics, cone templates, checkers, commitment
    Gen/             (2800)  generated per-artifact data and structural proofs
    Bridge/Ecdsa2/   (5)     ECDSA2 constants, soundness entry point, certificate
    Bridge/Rung1/    (3)     the small worked example, bytes → geometry
    Bridge/Sha256/   (72)    the SHA-256 meaning bridge, over 𝔽ₚ₂₅₆
    Bridge/Sha256Gf2/(4)     the same circuit over GF(2¹²⁸): steps 1–3
  ECDSA/             (21)    curve arithmetic, ECDSA spec, abstract soundness
  SHA/               (7)     SHA-256 spec, bit lemmas, σ/Σ/Ch/Maj, abstract soundness
  GF128/             (7)     GF(2¹²⁸) as the deployed code represents it, and its wrapping sum
  mdoc/             (15)     mdoc: the hash- and signature-circuit statements, the CBOR
                             parsing bridge, both assertion sets with their meaning proofs,
                             the three arithmetic gadget lemmas and the module that threads
                             them into `meaning`, the SHA-256 block chaining and final-hash
                             mux, and a real credential the hash side is decided against
  tests/ec/                  projective public-key circuit experiments
lfzk/                        the proof system: Ligero, sumcheck, zero-knowledge
merkle/                      Merkle commitment, binding and hiding
tools/
  leanseq                    serial builder — see below
  sha256/                    the SHA-256 bridge generators, with their own README
```

`Gen/` is machine-written and enormous; `Core/` and `Bridge/` are the parts to read.

## Building

`defaultTargets` is `lfzk`, so a bare `lake build` does not touch the certificate.

```bash
lake build quadcert        # structural certificate (bytes → assertions zero)
lake build sha256bridge    # SHA-256 meaning bridge (assertions → SHA256.blockFrom)
lake build ECDSA SHA mdoc  # the specs and abstract soundness theorems

# Regenerate the mdoc golden vector after a circuit change (from rust/):
MDOC_LEAN_GOLDEN_OUT=../formal/circuits/mdoc/Golden.lean \
  cargo test -p mdoc-zk-circuits --test circuits_tests lean_golden

# Re-census the assertion set the meaning proof claims to cover:
MDOC_ASSERTION_CENSUS_OUT=../formal/circuits/mdoc/ASSERTIONS.txt \
  cargo test -p mdoc-zk-circuits --test circuits_tests assertion_census
```

Those two are **step 4** tooling — a witness vector and an assertion census. Step 1 is a different
pipeline. The shipped mdoc artifact bundles both circuits in one zstd'd LFA2 archive, so neither
can be read alone and `lfc3_to_lean` — which takes a bare LFC2 blob — had nothing to eat.
`mdoc_lfc2` splits them, segmenting each half first because `segment_circuit` renumbers every
`k_index`:

```bash
# from rust/ -- writes OUT_DIR/mdoc_{sig,hash}.lfc2
cargo run --release -p mdoc-zk-runtime --bin mdoc_lfc2 -- OUT_DIR [CIRCUIT_HASH]

# then, per half, into formal/circuits/quadcert/Gen/<Name>/
cargo run --release -p core-proto --example lfc3_to_lean -- \
  p256    OUT_DIR/mdoc_sig.lfc2  ../formal/circuits/quadcert MdocSig
cargo run --release -p core-proto --example lfc3_to_lean -- \
  gf2_128 OUT_DIR/mdoc_hash.lfc2 ../formal/circuits/quadcert MdocHash
```

**Measure before planning.** `mdoc_layer_probe` reports per-layer terms, deltas, segments and
tokens, which is what decides ingestion cost — term count alone does not. The two v7 artifacts
differ: `8d079211…` is one attribute (hash 7,757,579 terms, 968,323 LFC3 bytes, 237 pages) and
`5aebdaaa…` is four (9,063,890 terms, 1,173,100 bytes, 287 pages). The **signature circuit is the
same in both** — 481,833 terms, 476,346 bytes, 117 pages — so its ingestion covers every variant.

```bash
cargo run --release -p mdoc-zk-runtime --bin mdoc_layer_probe -- [CIRCUIT_HASH]
```

Handwritten bridge modules for a generated artifact must **not** answer to the `<Name>*` glob that
regeneration deletes first: `Gen/MdocSig` is machine-written, `Bridge/Mdoc/MSigArtifact.lean` is
not. That is why the other handwritten bridges are `S2*`, `E2*` and `Gf2*`.

`sha256bridge` is deliberately a separate library: it is about an hour of `decide +kernel` and
nothing else depends on it.

### Memory discipline

Generated modules are checked with `decide +kernel`, which is memory-hungry — the cap is
`-M 34000` and peaks run to 2.6× nominal. The cap is an *entitlement*, not a usage: almost every
module peaks at 2.5–3.7 GB. It is 34000 rather than 16000 for exactly one module,
`Gen/MdocHash/MdocHashCommitment.lean`, which folds 237 literal page digests into the Merkle root
— about 475 kernel SHA-256 evaluations in a single `decide +kernel`. Its **measured peak is
28.3 GB**; 16000 and 26000 both fail with `(kernel) excessive memory consumption detected`,
reported on every declaration in the module rather than the offending one. Raising the cap does
**not** invalidate existing builds; Lake does not trace `moreLeanArgs`.

On a 40 GB box that module has to run alone, and it needs a `leanseq` ceiling above its peak or
the watchdog kills it:

```bash
tools/leanseq quadcert 32 '^Gen\.MdocHash\.MdocHashCommitment$'
``` **Do not run a bare `lake build quadcert` from cold**:
Lake spawns one worker per core, each entitled to the full cap, which will exhaust a 40 GB
machine. Use the serial builder:

```bash
tools/leanseq quadcert 20 .            # lib, RSS ceiling in GB, module filter
```

It builds one module at a time, kills anything above the ceiling, and writes per-module wall time
and peak RSS to `/tmp/leanseq.times`. Filters match dotted module names (`'^Gen\.Sha256Blk'`).

A cold `quadcert` is roughly 2.5–3 hours; `sha256bridge` about an hour.

### Regenerating

Only needed after a circuit change. `tools/sha256/README.md` documents the SHA-256 pipeline: what
each stage emits, what it checks against the artifact before emitting, and the three quirks of the
current artifact it has to handle. The emitted `.lean` files are committed, so checking the proofs
never requires running a generator.
