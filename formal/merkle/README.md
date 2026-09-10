# Merkle-heap commitment formalization

## Currently implemented theorems

| Theorem | Assumption needed | Model |
|---|---|---|
| `mh_core_completeness`, `mh_wire_completeness`: honest openings verify | none | deterministic |
| `mh_collision_lemma`: two accepting openings at a common index yield a hash collision | injective leaf and node encodings; otherwise any function `H` | combinatorial |
| `mh_binding_of_collision`: binding break ⇒ collision (constructive) | **collision resistance only** | standard model |
| `mh_binding_bound_rom` | bounded adaptive binder plus a combined slot table covering the *located* collision (`ROMBindingGame`, not yet inhabited, see Open obligations) | exact finite answer-tape counting |
| `mh_root_hiding_rom`, `mh_opening_hiding_rom` | certified lazy-sampling local bounds and good-outside-bad coupling, both assumed as structure fields (see Open obligations) | exact oracle-aware statistical-distance ratio |

The two-line summary:

- **Binding needs only collision resistance.** The collision lemma is an
  unconditional implication; the random oracle is used only to get a concrete
  closed-form bound. The nonce size plays no role in binding.
- **Hiding needs the random oracle.** It relies on unqueried oracle points
  being uniform (secret nonce ⇒ leaf digest looks random). A
  collision-resistant hash can leak information, so CR alone cannot give
  hiding.

## How the proofs are modeled in Lean

- **Probability = counting.** The sample space is a `Fintype Ω`; bad events
  are `Finset.filter` sets of samples; every bound is a cardinality
  inequality, finally read as a fraction.
- **The random oracle is finite counting plus bounded execution.** The oracle
  is a function `Enc → D`, but a `t`-query adversary is a bounded adaptive
  oracle program, not an arbitrary function of the entire oracle. Experiment
  spaces also include all real/simulator/adversary coins.
- **Domain separation is not needed.** `Codec.leafEnc : Salt × M → Enc` and
  `Codec.nodeEnc : D × D → Enc` map into the same query type. Their ranges may
  overlap; `Codec.Inj` asserts only same-role injectivity, with stronger
  fiber facts introduced where hiding needs them.
- **Codec and hash are separate.** `Codec` holds the two role encodings —
  fixed protocol geometry — and `Scheme extends Codec` adds the hash. A ROM
  game is parameterized by a `Codec` and varies only its oracle, forming
  `C.withOracle (oracle ω) : Scheme`. This is a typing-level guarantee that a
  hybrid cannot silently perturb the encodings along with the oracle.
- **Fixed shape is a typing-level fact.** `n` is a parameter of
  `commit`/`open`/`check`; there is no API that changes it, mirroring the
  Rust invariant.

## File map

| File | Contents |
|---|---|
| `Heap.lean` | Heap tree `T_n` (nodes `1..2n−1`, leaves `n..2n−1`), paths, copaths, frontier `F(I) = copath(I) \ path(I)`, canonical order, partition/independence/size lemmas |
| `Merkle.lean` | `Codec` / `Scheme` / `Codec.withOracle` / `Codec.Inj`; `commitLabels` / `root` / `openCore` / `checkValues` / `Accepts` mirroring `commitment.rs`+`heap.rs`; claim-independence of reconstruction; core completeness. Both recurrences are ordinary `termination_by 2*n-v` definitions, so they are computable and admit `fun_induction`. `MerkleError` branches live in `Wire.lean` |
| `Collision.lean` | Query-answer traces of a check; the first-divergence argument; collision lemma (single-leaf and multi-leaf); constructive collision extractor |
| `Wire.lean` | Natural-index validation, canonical nonce/frontier serialization, core refinement, and honest wire completeness |
| `RandomOracle.lean` | Bounded adaptive query trees, traces/replay, lazy-sampled tape execution (`Tree.runTape` / `tapeOracle` and the `Tree.run_tapeOracle` bridge), pair-family counting, exact ratio closeness, and distinguisher inequalities |
| `Binding.lean` | Raw binding game, domain baseline, and certified bounded answer-tape theorem with the sharp birthday plus trace coefficient |
| `Hiding.lean` | Simulator correctness/claim independence, explicit oracle-aware real/sim games, normalized root/opening coupling, and tight `(n−q)` arithmetic |
| `Instantiate.lean` | Raw fixed-width byte concatenations, injectivity/range overlap, `2^256`, `n=2^16`, and concrete security corollaries |
| `Extraction.lean` *(planned)* | Stored-label trapdoor, role decoders, partial-tree extractor, complete reconstruction, and deterministic local extraction |
| `ExtractionROM.lean` *(planned)* | Two-stage bounded extraction game, failure cover, fixed-split answer-tape bound, and probability corollaries |
| `MultiExtraction.lean` *(conditional)* | Stateful accumulated-trace extractor for multiple commitments, only if required upstream |

## Building & verifying

`merkle` is registered in `formal/lakefile.toml`:

```bash
cd formal && lake build merkle
```

## Extraction

The first theorem gives full reconstruction when the commitment-phase random-
oracle trace contains the entire derivation of the root.

```lean
theorem mh_extract_complete
    (htr : TraceSound H tr)
    (hfree : CollisionFree tr)
    (hcomplete : CompleteDerivation decoders n rt tr) :
  ∃ out,
    extract decoders n rt tr = some out ∧
    (∀ v, ∀ hv : v ∈ Heap.nodes n,
      out.trapdoor.label v hv =
        commitLabels H leafEnc nodeEnc n
          out.trapdoor.nonce out.message v) ∧
    root H leafEnc nodeEnc n
      out.trapdoor.nonce out.message = rt
```

Consequently, an honest commitment trace yields every leaf message and nonce,
all internal labels, and a complete message/trapdoor whose root is exactly
`rt`. No dummy coordinate is used.

The second theorem is the deterministic core of extraction for an arbitrary
malicious commitment trace. It guarantees exactly the locations that the
adversary can later open successfully.

```lean
theorem mh_extract_explains_of_trace_subset
    (htr : TraceSound H tr)
    (hfree : CollisionFree tr)
    (hacc : Accepts H leafEnc nodeEnc n rt I a pf)
    (hsub : ∀ qa ∈ checkTraceList H leafEnc nodeEnc n I a pf,
      qa ∈ tr) :
  ∃ out,
    extract decoders n rt tr = some out ∧
    (∀ i ∈ I, out.message i = a i) ∧
    openFromTrapdoor out.trapdoor I = pf
```

The final single-commitment ROM theorem packages a syntactically bounded
two-stage adversary. Let `t₁` be its commitment-phase query bound, `t₂` its
opening-phase bound, `d := Heap.heapDepth n`, and

```text
L(t₁,n) := min(2*t₁ + 1, 2*n - 1).
```

The target exact counting statement is:

```text
badTapes ≤
  (choose(t₁,2) + (t₂+d+1)*L(t₁,n)) * |D|^(T-1),
```

where `bad` means that verification accepts but extraction returns no result,
the extracted message disagrees on `I`, or the extracted trapdoor produces a
proof different from `pf`. Dividing by the `|D|^T` answer-tape space gives

```text
Pr[extraction failure] ≤
  (choose(t₁,2) + (t₂+d+1)*L(t₁,n)) / |D|.
```

A total-budget wrapper can always use the coarser numerator

```text
choose(t,2) + (t+d+1)*(2*n-1).
```

Under the book's explicit mild lower-bound condition on `t` (to be proved as
a `Nat` arithmetic side condition, rather than copied from OCR), endpoint
analysis gives the sharper book-shaped bound

```text
Pr[extraction failure] ≤
  (choose(t,2) + (d+1)*(2*n-1)) / |D|,
```

and then the familiar `t²/(2|D|)` estimate. The fixed-split expression remains
the primary theorem and is valid without that simplifying condition.

## Extraction: assumptions, guarantees, and proof

### The extraction game

Extraction uses the two-stage game:

1. The commitment stage has random-oracle access, makes at most `t₁` queries,
   and outputs a root `rt` and private state `aux`. Its query-answer trace is
   `tr`; this is the only trace given to the extractor.
2. The extractor deterministically computes
   `extract rt tr : Option (Extracted n Salt M D)`.
3. The opening stage resumes from `aux`, makes at most `t₂` additional oracle
   queries, and outputs `(I,a,pf)`.
4. Failure means that `pf` verifies but the commitment-phase extractor did
   not already recover the claims and exact opening proof.

The extractor never sees `aux`, the opening-stage trace, `I`, `a`, or `pf`.
Thus a successful theorem says the adversary already knew the accepted
opening when it produced `rt`.

### What is assumed

The deterministic theorems assume:

- a fixed nonempty heap shape `n`; the verifier and extractor use the same
  `n`;
- an arbitrary function `H : Enc → D` and a sound trace containing only
  pairs `(x,H x)`;
- collision-freeness of the relevant trace: equal answers in the trace imply
  equal encoded inputs;
- executable, role-directed partial decoders for leaf and node inputs, with
  round-trip and soundness laws;
- injectivity within each encoding role, as implied by those decoder laws;
- explicit default values for coordinates absent from a partial trace.

The ROM theorem additionally assumes:

- a finite, nonempty digest space and a uniformly sampled random-oracle
  answer tape;
- syntactically bounded adaptive commitment and opening stages;
- an oracle-consistent combined slot table connecting the adaptive execution,
  extracted labels, and selected verifier path to fixed answer-tape slots.

It does **not** assume that leaf and internal encodings have disjoint ranges.
The same byte string may decode in both roles. Heap position determines which
decoder is used: `nodeDec` at internal vertices and `leafDec` at leaves. This
is essential for the concrete 32-byte leaf-payload case, where the raw leaf
and internal input ranges overlap.

The deterministic theorem uses no random-oracle probability and no collision-
resistance assumption beyond the explicit collision-free trace premise. The
ROM analysis is what bounds the probability that this premise or the required
trace stability fails.

### What is guaranteed

For a complete commitment trace:

- every leaf message and nonce is recovered;
- every internal and leaf label satisfies the actual `commitLabels`
  recurrence under `H`;
- the extracted full message commits to exactly `rt`;
- the extracted trapdoor opens every subset exactly as the reconstructed
  tree dictates.

For an arbitrary malicious trace and a later accepted opening:

- every extracted message coordinate in `I` equals the verifier's claim;
- the extracted stored-label trapdoor produces literally the same dependent
  `Opening`, including all nonces and frontier digests;
- no claim is made about unopened coordinates whose preimages were absent
  from the commitment trace.

That last qualification is necessary. A malicious committer can query a root
preimage containing an opaque child digest without knowing a preimage for
that child. Efficient extraction cannot invert the missing random-oracle
value. If the trace is complete—as it is for honest `commit`—this limitation
disappears and the full-reconstruction theorem applies.

### Extractor construction

The current honest API must first be extended with a stored-label trapdoor:

```lean
structure Trapdoor (n : ℕ) (Salt D : Type*) where
  nonce : Fin n → Salt
  label : (v : ℕ) → v ∈ Heap.nodes n → D

def openFromTrapdoor
    (td : Trapdoor n Salt D) (I : Finset (Fin n)) : Opening n I Salt D
```

This is important: `openCore` recomputes a globally honest tree from a message
and nonces, while an extractor initially has only a partial tree. Reusing
`openCore` would silently assume the very random-oracle preimages extraction
is meant to establish.

The extractor then proceeds top-down:

1. Reject if `rt` is not an answer in the commitment trace.
2. Label the root with `rt`.
3. At a known internal vertex, find a trace query with that vertex label as
   its answer and decode its input as `(left,right)`; assign those child
   labels.
4. At a known leaf, find a trace query with that leaf label as its answer and
   decode its input as `(nonce,message)`.
5. Keep knowledge as `Option` values and fill only genuinely missing labels,
   messages, and nonces with explicit defaults when constructing the total
   output.

Using `Option` prevents an arbitrary default digest that happens to equal a
real digest from being incorrectly counted as knowledge.

### Why the deterministic proof works

Assume an accepted verifier trace is contained in the commitment trace.

1. Both computations begin with the same root `rt`.
2. Descend an opened path. The verifier's internal-node query occurs in `tr`
   with the current parent label as its answer. If the extractor selected a
   different query with that answer, the trace would contain a collision.
   Therefore it decodes the same child pair as the verifier.
3. Repeating this argument reaches the leaf. The leaf query in `tr`, same-role
   decoder soundness, and collision-freeness force the extracted nonce and
   message to equal the verifier's values.
4. Every pruned frontier vertex is a child of a vertex on some opened path.
   The same node-query argument therefore forces each extracted frontier
   digest to equal the corresponding proof coordinate.
5. Function extensionality for the exact dependent `Opening` yields literal
   proof equality, not merely a second accepting proof.

For a complete trace this descent succeeds at every vertex, so the local
argument lifts to the global `commitLabels` recurrence and reconstructs all
leaves.

### Why extraction can fail only with small ROM probability

Let `L(t₁,n) = min(2*t₁+1, 2*n-1)`. A `t₁`-query commitment trace can introduce
at most that many non-dummy heap labels. If an accepted opening is not
explained by the commitment-phase extraction, one of three events occurs:

1. **Commitment collision:** two distinct commitment-stage queries have the
   same answer. This costs at most `choose(t₁,2)/|D|`.
2. **Opening-stage hit:** one of at most `t₂` new queries receives one of the
   previously extracted labels. This costs at most `t₂*L(t₁,n)/|D|`.
3. **Verifier-path hit:** a fresh query on a selected accepted path receives
   an extracted label. The selected path has at most `heapDepth n + 1`
   queries, costing at most
   `(heapDepth n+1)*L(t₁,n)/|D|`.

Outside these events, extending the trace cannot change the extracted partial
tree, the accepted verifier trace is already explained by that tree, and the
deterministic theorem forces message and proof equality. The existing fixed-
pair answer-tape lemma in `RandomOracle.lean` will count these three pair
families without treating an arbitrary full-oracle function as a bounded
adversary.

### Implementation order

1. Add `Trapdoor`, `openFromTrapdoor`, and the honest-trapdoor compatibility
   theorem without changing existing completeness results.
2. Add executable role decoders and materialized verifier trace lists.
3. Prove the frontier-attachment, trace-size, and proof-uniqueness lemmas.
4. Implement the option-valued partial-tree extractor.
5. Prove complete-trace reconstruction and honest-trace completeness.
6. Prove local extraction and exact proof equality for partial traces.
7. Prove trace-extension stability and the three-event failure cover.
8. Prove the fixed-split ROM counting and cross-multiplied probability
   theorems.
9. Instantiate fixed raw bytes, 256-bit digests, and `n=2^16`.
10. Add stateful multi-commitment extraction only if required by the
    higher-level protocol proof.

## The domain-separation question

The implementation uses **no** leaf/internal domain-separation tags
(`heap.rs` documents why). For binding this loses nothing provided the tree
shape is fixed and each same-role serialization is injective:

1. Domain-separation tags exist only to stop *shape-reinterpretation*
   (type-confusion / second-preimage) attacks, in which one digest is made to
   mean different things at different depths. All such attacks require the
   verifier to accept a different `num_leaves` than the one used at commit
   time.
2. Here `num_leaves` is fixed public protocol geometry: the prover uses
   `block_enc − dblock` (`prover.rs:101`) and the verifier independently
   re-derives it from its own parameters (`verifier.rs:236-242`). The
   `MerkleProof` carries no shape field — a proof cannot even *suggest* a
   different tree shape.
3. Leaves are always recomputed as `H(nonce ‖ value)` at fixed positions
   `n+i`; the proof supplies only internal siblings. Leaf-vs-internal roles
   are separated by position, not by tag.
4. The first-divergence extractor compares leaf inputs with leaf inputs at the
   same position, or node inputs with node inputs at the same parent. It needs
   each of those encodings to be injective, but it does **not** need their
   ranges to be disjoint.

For hiding, untagged range overlap can create additional random-oracle input
aliasing events. Those must be counted using concrete encoding fiber bounds;
fixed shape alone is not a hiding theorem. The invariants an auditor must
check are therefore both the public fixed shape and canonical/injective
same-role serialization.

## Open obligations

These are real gaps, recorded so nobody mistakes a certificate-shaped theorem
for a finished one.

1. **`ROMBindingGame` has no inhabitant at real parameters.** The counting
   theorem is proved, but nothing yet constructs the combined binder/checker
   execution that discharges `covers_collision`, `answer_sound`, and the two
   pair-count fields. Until that exists, `mh_binding_bound_rom` and
   `mh_binding_bound_rom_65536_256` say nothing about any concrete adversary.
   Note the shape trap recorded in `collision_of_infinite_enc`: phrasing the
   covering obligation over a bare `Collision (oracle answers)` instead of over
   a `LocatedCollision` makes the structure *provably* uninhabitable whenever
   `Enc` is infinite, which forces `2^256 ≤ t(t-1)/2 + (dmax+1)²`.

   Two field shapes are expected to need revision when the instantiation is
   attempted, and should be settled before writing it:
   - `answer_sound` quantifies over *every* slot `j : Fin T`, but lazy sampling
     only pins slots the execution actually consumed
     (`tapeOracle_slotQuery` needs `j < seen.length`). Either fix `T` to the
     consumed length or restrict the field to consumed slots.
   - `fresh_card : freshPairs.card ≤ (dmax+1)^2` looks unachievable, because
     the pair family must be tape-independent while a check query that repeats
     a binder query lands in the binder's slot range, producing cross pairs in
     neither family. The last-fresh-query argument gives
     `choose(t,2) + 2*(dmax+1)*T` instead — the same shape as the extraction
     numerator advertised at the top of this file.
2. **The `t`-query bound is not yet connected to the count.**
   `ROMBindingGame.binder`/`attempt_run` are carried but unused by the proof,
   and `own_card` is an assumption about a supplied `Finset`. Nothing yet ties
   `dmax` to `Heap.heapDepth n`, even though `Heap.pathOf_card_le_heapDepth`
   and `Heap.pathSet_card_le` are the lemmas that would do it. These
   declarations are deliberately retained as scaffolding for obligation 1;
   they are unused, not dead.

   The infrastructure side of this is now **done**: `Tree.runTape` executes a
   bounded adaptive tree against an answer tape with lazy sampling, and
   `Tree.run_tapeOracle` proves that running against the induced total oracle
   `tapeOracle tape seen` reproduces the same output. `Tree.tapeOracle_trace_mem`
   places every query made into the slot list, `Tree.runTape_nodup` +
   `idxOf_ne_of_ne` give distinct slots to distinct queries,
   `Tree.runTape_length_le` bounds consumed slots by the fuel, and
   `Tree.runTape_congr` + `finTape` reduce an infinite tape to `Fin T → D`.
   What remains is to *use* these to build a `ROMBindingGame`.
3. **Hiding assumes its coupling.** `RootHidingGame.agrees`,
   `OpeningHidingGame.agrees`, and the `leafBad`/`nodeBad`/`subtreeBad` sets
   are structure fields, so the lazy-sampling step — the only place the random
   oracle is actually used for hiding — is not formalized. Additionally
   `RootHidingGame.simulatedRoot` is an arbitrary `Ω → D` with no connection to
   `simulateRoot`, so `mh_root_hiding_rom` does not currently mention the
   Merkle simulator at all. `mh_opening_hiding_rom` is sound in this respect.
4. **Wire serialization is not shown to be a deterministic parse.**
   `WireAccepts` is existential over `pf`, and `serializeProof` has no
   injectivity lemma, so the equivalence with the positional list decoding the
   Rust verifier performs is unproved. Three `WireError` constructors
   (`invalidNonceLength`, `proofLengthMismatch`, `rootMismatch`) are declared
   but never produced.
5. **Frontier emission order is unproved.** `frontierList` sorts frontier
   vertices descending; `generate_proof` iterates *parents* descending and
   pushes a child. These coincide (`i₁ > i₂ ⟹ 2i₁ > 2i₂+1`), but no lemma
   records it.
6. **`Extraction.lean` and `ExtractionROM.lean` do not exist yet.** The
   theorems at the top of this file are targets, not results.