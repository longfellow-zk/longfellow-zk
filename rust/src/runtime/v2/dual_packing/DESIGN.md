# Dual packing design

Dual packing reduces a layered sumcheck's input claim over committed packed
words to linear equations over committed cells. A participant whose circuit
inputs live in a subfield K of its field F commits them m at a time, as words
of F, where m = [F:K]. The reduction proves that the K-coordinates of those
words satisfy the input claim. For K = GF(2) this is what makes the binary
circuit's inputs bits; no separate bitness constraint exists. The deployed
profile is binary128: K = GF(2), F = GF(2^128), m = 128, polynomial basis.
The same protocol runs for any finite extension F/K (the generic profile),
and degree one (prime fields, `IdentityExtension`) is the identity. In the v2
stack the layered sumcheck (`runtime::v2::sumcheck`) feeds it, through
`zk::constraint_compiler::compile_packed`; its equations go to
`zk::packing_commitment`, which appends them to the participant's Polygero
`LinearStatement`, and the joint Polygero opening authenticates them.

Code: `runtime/v2/dual_packing.rs` and `runtime/v2/dual_packing/` (protocol),
`runtime/algebra/packing.rs` and `runtime/algebra/packing/` (extension
algebra), `runtime/v2/zk/packing_commitment.rs` and its `prover.rs` and
`verifier.rs` (cell layout and handoff), `runtime/v2/proto/dual_packing.rs`
(proof type). Transcript rules are cited as "transcript I1" and so on, from
`runtime/v2/transcript/DESIGN.md`.

## Notation

| Symbol | Meaning | Rust |
|---|---|---|
| K, F | base field, ambient field, F/K of degree m | `X::Base`, `X::Ambient` |
| sigma | relative Frobenius, sigma(x) = x^abs(K) | `PackingParameters::frobenius` |
| Tr | relative trace, Tr(x) = sum over k < m of sigma^k(x), in K | `PackingParameters::trace` |
| beta_0..beta_(m-1) | packing basis of F over K, beta_0 = 1 | `PackingParameters::basis` |
| alpha_0..alpha_(m-1) | trace-dual basis: Tr(alpha_j beta_k) = [j = k] | `PackingParameters::dual` |
| coord_k(x) | k-th K-coordinate of x in the basis beta | `PackingParameters::coordinates_into` |
| n, N | private inputs, packed words N = ceil(n/m) | `PackingLayout::private_inputs`, `packed_words` |
| W_i | committed word i, i < N | `words` |
| P_s | committed pad or terminal cell s, s < pad_cells | `aux`, `suffix` |

## Statement

**Setup, in the transcript statement (transcript I1, I3).** The participant's
`CommitmentLayout` message carries the FieldID of F, the private input count
n, the pad cell count and the packing descriptor (see Formats). The
descriptor is the single source of the packing degree m; no other statement
value carries it. The `Circuit` message carries the circuit ID. These fix
`PackingParameters` and `PackingLayout`; the protocol reads them through
`Bound` (transcript I2) and absorbs none of them.

**Committed.** Before the protocol starts, the joint Polygero `Commitment`
binds the participant's cell vector
`[W_0..W_(N-1) | P_0..P_(pad_cells-1) | masks]`, with the m+1 mask cells
`t_1..t_(m-1), r, b` when m > 1 and no mask cells when m = 1. The input
values are x_j = coord_(j mod m)(W_(j div m)) for j < n. Every word has unique
coordinates, so the x_j are well defined for any committed word, honest or
not; the unused coordinates of the last word are not constrained.

**Input claim.** From the preceding sumcheck on the same transcript, both
roles derive the `SourceClaim`:

```text
sum_(j<n) rho_j * x_j  =  c + sum_s kappa_s * P_s            (in F)
```

with weights rho_j in F (`weights`, length n, public inputs already
substituted and virtual inputs folded in) and an affine right-hand side
(`rhs.constant` = c, `rhs.terms` = (s, kappa_s)). The claim is a derived
value: it is never absorbed and never sent.

**Output.** For m > 1, two linear equations over the committed cells (rows 1
and 2 below); for m = 1, one equation, the claim itself. If the input claim
is false, the two equations hold for at most a 1/abs(F) fraction of the
packing challenges, for any committed cells and any U and A. The equations
are not checked here; they must be authenticated against the commitment
that preceded the claim.

## Invariants

**I1. One protocol for every degree above one.** The binary128 and generic
profiles send the same messages, draw the same challenges, emit the same two
equations and use the same encodings. A profile selects only arithmetic fast
paths (`native_pack`, `native_dual_basis`, `native_coefficients`,
`relative_trace`) and its descriptor in the statement.
*Enforced by:* the shared transcript steps
`dual_packing::transcript::challenges` and `finish` have no profile
parameter (type); the test
`binary_packing_and_transpose_match_independent_coordinates` checks the fast
paths against the generic formulas; the role-trace test (transcript I9).

**I2. Degree one is the identity.** It has no mask cells, no messages, no
draws, and one equation: the input claim over the unpacked inputs.
*Enforced by:* `mask_cell_count`, the one mask-count rule, gives zero masks,
and `PackingLayout::new` and the prover's mask check use it;
`PackingProof::Direct` is the only degree-one proof and carries nothing;
`identity_has_no_masks_messages_or_challenges` checks that the transcript
state is unchanged (test).

**I3. Packing absorbs exactly U and A.** Its parameters, circuit ID and cell
counts are in the statement. The source claim's weights and right-hand side
are derived from earlier messages and challenges, so absorbing them would add
nothing (transcript I3).
*Enforced by:* `UMessage` (`PackingU`) and `AMessage` (`PackingA`) are the
module's only `Message` types and `SourceClaim` has none (type); the schema
checks (transcript I6).

**I4. U before delta, delta before A, A before the backend.** U closes a node
and delta is read from it; A is sent after delta and before the joint
backend draws its batching challenges.
*Enforced by:* `challenges` (send U, draw delta) and `finish` (send A),
called in this order by both roles, are the only code that sends or draws
for packing (transcript I7, I9); the role-trace test.

**I5. Every U_k has trace zero.** The verifier checks all m traces before it
absorbs anything, so a rejected proof never advances the transcript. The
prover checks its own U, so a false claim fails at the prover.
*Enforced by:* `validate_u` in both roles (runtime); Lean `error_ne_zero`
needs this hypothesis.

**I6. Both equations are authenticated against the original commitment.**
Neither equation alone implies the claim. Both join the same
`LinearStatement` as the participant's layer rows.
*Enforced by:* `PackingCommitment::append_equations` requires exactly one
equation at degree one and two above it, and appends them to the rows of the
`#[must_use]` `CommitmentStatement` (runtime); Lean
`linear_backend_composition_card` charges backend failure separately.

**I7. The basis starts with one, and alpha is its trace dual.** Every
packing basis has beta_0 = 1; degree one uses exactly the basis [1]. Then
t -> sigma(t) - t maps span{beta_k : k > 0} onto the trace-zero hyperplane,
which is the case the Lean hiding proof covers (pivot zero). A binary-field
circuit packs with the binary128 profile.
*Enforced by:* `PackingParameters::with_basis`, the only constructor, rejects
a basis with beta_0 != 1 for every degree and a basis that is not invertible
(the coordinate-matrix inversion) (runtime); `every_packing_basis_starts_with_one`
checks the rejection at degrees 2 and 128, including bases that complement K,
and `distinguished_mask_coordinate_must_complement_the_base_field` shows why
the swapped basis [x, 1] would leak the claim (tests);
`prepare_circuit_layout` rejects a binary field without the binary128 profile
(runtime); Lean `traceDual_eq_gramDual`, `powerBasis_traceDual`.

**I8. Masks are fresh, committed, and used once.** The prover samples
`t_1..t_(m-1), r` from its private randomness and sets b = sigma(r) before
the commitment, and appends them to the committed witness. `prove_packed`
consumes them.
*Enforced by:* `PackingMasks` is not `Clone` (test
`packing_masks_are_not_clone`) and is moved into `prove_packed`;
`PackingCommitment::prepare` samples it together with the committed witness
and keeps it in the move-only `PackingState`, which
`PackingCommitment::prove` consumes (type).

**I9. The source claim is this transcript's sumcheck input claim.** No
caller supplies claim coefficients.
*Enforced by:* `SourceClaim` is built only by `compile_packed` from the
`Constraints` that sumcheck returns on the same `Bound`, and is passed by
value inside `CommitmentStatement` (type, crate-private fields); Lean
`readPackingPacket_off` proves the packing answer cannot change the source.

**I10. One cell layout.** The cells are
`[N words | pad_cells pads | mask cells]`, with N = ceil(n/m) and m+1 mask
cells (none for m = 1); the joint wrapper appends its fingerprint cells
after them.
*Enforced by:* `PackingLayout::new` (checked arithmetic, private fields);
the shape check in `append_equations` (runtime); Lean
`FrontendPackingCells.cells_eq`.

## Protocol

Definitions. W, P, t, r and b are committed. B_k, T and the dependent t_0
are computed from them: they are private intermediate values, computed only
by the prover. U and A are the messages; the rest are public:

```text
D_ik   = sum_(j<m) alpha_j * coord_k(rho_(i*m+j))      ; rho beyond n is zero
B_k    = sum_(i<N) D_ik * W_i                          ; Tr(B_k) = coord_k(sum_j rho_j x_j)
T      = c + sum_s kappa_s * P_s                       ; Tr(alpha_k T) = coord_k(T)
t_0    = sum_(k>0) beta_k * t_k                        ; dependent, not committed
U_k    = B_k - alpha_k*T + sigma(t_k) - t_k            ; k < m
A      = r + sum_(k<m) delta_k * t_k
gamma_k = sigma(delta_k);  eta = sum_k gamma_k*alpha_k;  omega_i = sum_k gamma_k*D_ik
```

The claim holds exactly when Tr(B_k - alpha_k T) = 0 for every k, and
Frobenius differences have trace zero, so honest U_k have trace zero.

| Step | Role | Item | Kind | Size |
|---|---|---|---|---|
| 1 | prover | send `PackingU` (tag 80) | Elements(F, m): U_0..U_(m-1) | m elements |
| 2 | both | node closes; draw delta | `elements(F, m)`, independent uniform | m elements |
| 3 | prover | send `PackingA` (tag 81) | Elements(F, 1): A | 1 element |
| 4 | caller | joint batching draws close the node | Polygero's draws | |

Degree one runs no step. Packing needs no challenge before its first message,
so it takes no `Challenge<T>` input (transcript I8). It closes one boundary of
its own, after `PackingU`; `PackingA` belongs to the node that the joint
batching draws close. For binary128 the draw reads 128 x 16 = 2048 bytes, 64
PRF blocks.

**Verifier.** `reduce`:

1. Check the proof variant against m from the parameters in `Bound`
   (`Direct` iff m = 1), and `rhs.terms` indices against `pad_cells`
   (`validate_proof`, `SourceClaim::validate`).
2. Check Tr(U_k) = 0 for every k (I5).
3. Run the shared steps: absorb U and draw delta (`challenges`), then absorb
   A (`finish`).
4. Return the equations below. There is no check of A itself, and no check
   that b = sigma(r): a dishonest b adds a fixed affine offset, which the
   Lean count covers.

**Equations** (form `sum_w A[c,w]*w + b[c] = 0`, `FieldEquation`):

```text
row 1:  r + sum_(k>0) (delta_k + delta_0*beta_k) * t_k  -  A                   = 0
row 2:  sum_i omega_i * W_i  -  sum_s (eta*kappa_s) * P_s
        - sum_(k>0) (gamma_k + gamma_0*beta_k) * t_k  -  b
        + (sigma(A) - sum_k gamma_k*U_k - eta*c)                              = 0
direct: c + sum_s kappa_s * P_s  -  sum_j rho_j * W_j                          = 0   ; m = 1
```

The t_0 terms are eliminated by `eliminate_dependent` (Lean
`Instance.contract_mask`), so only committed cells carry coefficients. Row 2
is `Instance.nativeLinearVerify_affine` with pivot zero. For an honest prover
both rows hold with b = sigma(r) (`Instance.native_linear_completeness`).

## Formats

**Proof bytes.** Inside the participant's `CircuitProof`, after its sumcheck
proof. m comes from the absorbed descriptor; nothing is length-prefixed.

```text
packing   := ""                          ; m = 1
           | elem(U_0) .. elem(U_(m-1)) elem(A)   ; m > 1
elem      := canonical serialization of F (GF(2^128): u128 little endian, 16 bytes)
```

Size: (m+1) x elem bytes; binary128: 129 x 16 = 2064 bytes. Lean:
`ProofBodyCodec.packing` (U in coordinate order, then A).

**Transcript messages** (transcript byte grammar; u64 little endian):

```text
PackingU := u64(80) u64(2) u64(FieldID(F)) u64(m) elem{m}
PackingA := u64(81) u64(2) u64(FieldID(F)) u64(1) elem
```

Binary128: FieldID `Gf2_128` = 4; 2080 and 48 bytes.

**Packing descriptor** (`PackingParameters::descriptor`, the Bytes packing
descriptor of `CommitmentLayout`, and the only statement value that carries
m):

```text
descriptor := "longfellow/packing-extension/v1"      ; 31 bytes
              u64(len) packing_id                    ; PackingField::packing_id
              u64(len) embedding_id                  ; PackingExtension::embedding_id
              u64(8)   u64(m)
              elem(beta_0) .. elem(beta_(m-1))
```

| Profile | packing_id | embedding_id | m | Descriptor size |
|---|---|---|---|---|
| binary128 | `GF2[x]/(x^128+x^7+x^2+x+1)/polynomial/v1` | `GF2-to-GF128/polynomial/v1` | 128 | 2177 bytes |
| GF(2^128) over GF(256) | same | `GF256-to-GF128/primitive-powers/v1` | 16 | 393 bytes |
| identity (P-256) | `prime/canonical-integer/v1/` then the encoding of -1 | `identity/v1` | 1 | |

**Packed words** (`PackingParameters::pack`): W_i = sum_(j<m) beta_j *
embed(x_(i*m+j)), with zero base coordinates past n. Binary128: bit j of the
u128 of W_i is input i*128+j (`Binary128Extension::native_pack`).

**Binary128 constants** (`runtime/algebra/packing/binary128.rs`): beta_j =
x^j; Tr(v) = bit 121 xor bit 127 of v; alpha_j = (x^(127-j) + [j<7]x^(6-j)
+ [j<2]x^(1-j) + [j=0]) / (x^6+1). `dual_coordinate_numerators` computes all
D_ik of one word with a fixed bit transpose and no data-dependent lookup.

**Cells and equations in Polygero.** `append_equations` places word i at
w = i, pad s at w = N + s, and mask q at w = N + pad_cells + q, with mask
order t_1..t_(m-1), r, b. Each equation becomes one row c = b.len(), after the
layer rows.

## Rust API

```rust
// runtime::algebra::packing (public)
pub trait PackingField: AlgebraicField + RegisteredField + SupportsSampling + Clone + Sized {
    type Packing: PackingExtension<Ambient = Self>;
    fn packing_extension(&self) -> Self::Packing;
    fn packing_id(&self) -> Vec<u8>;              // representation identity, with modulus
}
// outside tests, implemented for P256Field and Gf2_128Field: only registered fields pack (transcript I5)
pub trait PackingExtension {                      // trusted arithmetic for one K -> F
    type Base: AlgebraicField;
    type Ambient: PackingField;
    fn base(&self) -> &Self::Base;
    fn degree(&self) -> usize;
    fn embedding_id(&self) -> Vec<u8>;
    fn embed(&self, f: &Self::Ambient, x: &BaseElement<Self>) -> AmbientElement<Self>;
    fn native_basis(&self, f: &Self::Ambient) -> Vec<AmbientElement<Self>>;
    fn coordinates_into(&self, f: &Self::Ambient, x: &AmbientElement<Self>, out: &mut [BaseElement<Self>]);
    fn relative_frobenius(&self, f: &Self::Ambient, x: &AmbientElement<Self>) -> AmbientElement<Self>;
    fn relative_trace(..) -> AmbientElement<Self>;           // default: orbit sum
    // fast paths, default None/false: native_pack, native_dual_basis,
    // native_coefficients, binary128_profile; input_elements, into_input_elements
}
pub struct PackingParameters<X: PackingExtension> { .. }    // private fields
impl<X: PackingExtension> PackingParameters<X> {
    pub fn new(field: X::Ambient, extension: X) -> Result<Self, String>;  // native basis
    pub fn with_basis(field: X::Ambient, extension: X, basis: Vec<AmbientElement<X>>)
        -> Result<Self, String>;                            // I7
    pub fn degree(&self) -> usize;
    pub fn basis(&self) -> &[AmbientElement<X>];
    pub fn dual(&self) -> &[AmbientElement<X>];
    pub fn pack(&self, values: &[BaseElement<X>]) -> Result<Vec<AmbientElement<X>>, String>;
    pub fn unpack(&self, words: &[AmbientElement<X>], len: usize) -> Result<Vec<BaseElement<X>>, String>;
    pub fn descriptor(&self) -> Vec<u8>;                    // written once, in the statement
    // field, extension, frobenius, trace, coordinates_into, native_coefficients
}
pub struct IdentityExtension<F>;   // binary: Gf2, Binary128Extension, Gf256, Binary128Over256

// runtime::v2::proto::dual_packing (prover/verifier contract)
pub enum PackingProof<E> { Direct, TraceZero { u: Vec<E>, a: E } }
// runtime::v2::proto::tags: Tag::PackingU = 80, Tag::PackingA = 81 (transcript I6)

// runtime::v2::dual_packing::generic, visible in runtime::v2 only
pub struct Affine<E> { constant: E, terms: Vec<(usize, E)> }
pub struct SourceClaim<E> { weights: Vec<E>, rhs: Affine<E>, auxiliary_count: usize } // no Message (I3)
pub struct FieldEquation<E> { constant: E, words: Vec<E>, auxiliary: Vec<(usize, E)>, masks: Vec<E> }
pub struct PackingMasks<E> { cells: Vec<E> }                 // not Clone (I8); Debug omits the cells
impl<E> PackingMasks<E> {
    pub fn sample<X: PackingExtension>(p: &PackingParameters<X>, sample: impl FnMut() -> E) -> Self;
    pub fn cells(&self) -> &[E];
}

// transcript.rs: the shared steps, both roles (I1, I4)
struct UMessage<'a, F: RegisteredField> { f: &'a F, u: &'a [F::E] }   // PackingU, I3
struct AMessage<'a, F: RegisteredField> { f: &'a F, a: &'a F::E }     // PackingA, I3
fn challenges<X: PackingExtension>(p: &PackingParameters<X>, u: &[AmbientElement<X>],
    ts: &mut TranscriptRef<'_>) -> Vec<AmbientElement<X>>;           // send U, draw delta
fn finish<X: PackingExtension>(p: &PackingParameters<X>, a: &AmbientElement<X>,
    ts: &mut TranscriptRef<'_>);                                      // send A

// prover.rs
pub(in crate::runtime::v2) fn prove_packed<X: PackingExtension>(
    ts: &mut Bound<'_, PackingParameters<X>>,
    c: &SourceClaim<AmbientElement<X>>,
    words: &[AmbientElement<X>],
    aux: &[AmbientElement<X>],
    masks: PackingMasks<AmbientElement<X>>,                   // I8: consumed
) -> Result<(PackingProof<AmbientElement<X>>, Vec<FieldEquation<AmbientElement<X>>>), String>;

// verifier.rs
pub(in crate::runtime::v2) fn reduce<X: PackingExtension>(
    ts: &mut Bound<'_, PackingParameters<X>>,
    c: &SourceClaim<AmbientElement<X>>,
    proof: &PackingProof<AmbientElement<X>>,
) -> Result<Vec<FieldEquation<AmbientElement<X>>>, String>;  // one equation, or two (I2, I6)

// runtime::v2::zk::packing_commitment (crate)
pub(crate) struct PackingLayout { .. }                       // private fields (I10)
pub(crate) struct PackingCommitment<F: PackingField, X = <F as PackingField>::Packing> {
    parameters: PackingParameters<X>,                        // source of CommitmentLayout's
    layout: PackingLayout,                                   // packing values (transcript I3)
}
#[must_use]
pub(crate) struct CommitmentStatement<E> { claim: SourceClaim<E>, a: Vec<PolygeroLinearTerm<E>>, b: Vec<E> }
pub(crate) struct PackingState<E> { words: Vec<E>, suffix: Vec<E>, masks: PackingMasks<E> }
impl<F: PackingField, X: PackingExtension<Ambient = F>> PackingCommitment<F, X> {
    pub(crate) fn prepare_inputs(&self, logical: &[BaseElement<X>]) -> Result<PreparedInputs<F::E>, String>;
    pub(crate) fn prepare(&self, inputs: PreparedInputs<F::E>, suffix: Vec<F::E>,
        rng: &mut impl PrivateRandom) -> (PackingState<F::E>, Vec<F::E>);   // state + committed witness (I8)
    pub(crate) fn prove<const W: usize>(t: &mut Bound<'_, Self>, state: PackingState<F::E>,
        statement: CommitmentStatement<F::E>) -> Result<(PackingProof<F::E>, LinearStatement<F::E>), String>;
    pub(crate) fn reduce<const W: usize>(t: &mut Bound<'_, Self>, statement: CommitmentStatement<F::E>,
        proof: &PackingProof<F::E>) -> Result<LinearStatement<F::E>, String>;
}
```

The glue projects `Bound<'_, PackingCommitment>` to
`Bound<'_, PackingParameters>` for the protocol, so the parameters the
protocol uses are the ones the statement absorbed (transcript I2). The proof
reader builds `PackingProof` from the packing degree of the bound
`CircuitProofGeometry`, so it cannot produce the wrong variant or length.
`LinearStatement` carries no source digest: the circuit ID is in the
statement (transcript I3).

## Mistakes the design prevents

| Mistake | What stops it |
|---|---|
| Two profiles absorbing in different orders or with different labels | I1: one pair of shared steps, no profile parameter; labels do not exist (transcript I5, I7) |
| Re-absorbing the circuit ID, descriptor or cell counts in packing | I3: they are statement values; packing has no `Message` for them |
| Absorbing the derived claim weights or RHS | I3: `SourceClaim` has no `Message` impl |
| Drawing delta before U is absorbed, or sending A before delta | I4: `challenges` and `finish` are the only sender and drawer |
| Accepting a U_k with nonzero trace | I5: `validate_u` before any absorb |
| Dropping one of the two equations, or authenticating them elsewhere | I6: `append_equations` requires one or two equations and appends them to the `#[must_use]` statement |
| A degree-one proof with messages, or a degree-m proof with the wrong U length | I2; the reader builds the variant from the absorbed m |
| A basis whose zeroth element is not one (hiding unproved, or U leaks the claim) | I7: `with_basis` rejects it |
| Packing a binary circuit over GF(256), so inputs need not be bits | I7: `prepare_circuit_layout` rejects it |
| Reusing masks across proofs, or masks that were not committed | I8: move-only `PackingMasks`, created with the witness |
| Reducing a claim from another circuit or transcript | I9: `SourceClaim` only from `compile_packed` on the same `Bound` |
| Equations indexing the wrong cells | I10: one `PackingLayout`; `append_equations` shape check |
| A verifier checking against another degree or descriptor than absorbed | transcript I2: parameters come from `Bound` |

## Soundness and zero knowledge

**Trace check (I5).** With Tr(U_k) = 0 for all k, a false claim implies a
nonzero error vector U - honestU
(`DualPacking.ArtinSchreier.Instance.error_ne_zero`). The converse does not
hold: for a true claim, U = honestU + V passes the trace checks for any
nonzero trace-zero V, with error V.

**Challenge delta.** For a fixed false claim, fixed committed cells (any b,
any masks) and fixed U, and any A chosen after delta, both native equations
hold for at most abs(F)^(m-1) of the abs(F)^m values of delta:
`Instance.linear_native_soundness_probability` gives 1/abs(F);
`linear_soundness_by_basis_size` gives 1/abs(K)^m;
`linear_soundness_binary128` gives 2^-128. The missing b = sigma(r) check is
covered by counting the affine offset (`Instance.offset`,
`combined_frobenius_offset`). The application charges this boundary
`.packing => 1/abs(B)` with B = GF(2^128) (`ApplicationCharging.roundBudget`).

**Authentication (I6).** Failure of Polygero to enforce either equation is a
separate event (`Instance.linear_backend_composition_card`), charged to the
joint backend. Degree one adds no packing error: its equation is the claim.

**Composition.** `ApplicationViews.readPackingPacket_off` proves the source
claim is fixed before the packing answer (I9). The Fiat–Shamir composition
with the frontends, the joint backend and the query budget is
`Soundness.Runtime` and `Soundness.Composition.soundness` in `formal/lfzk-v2`.
The cell layout is `ZeroKnowledge.FrontendPackingCells` (`cells_eq`,
`packedWords_digit`, `packedWords_zero_tail`).

**Zero knowledge.** For a true claim, the free masks t_1..t_(m-1) and r map
bijectively to a uniform pair (U in the product of trace-zero hyperplanes,
A in F), for any delta that depends on U: `Masking.transcript_uniform_fiber`,
`Masking.honest_transcript`; the simulator samples U by the forward
Artin–Schreier map and A uniformly
(`ZeroKnowledge.Frontend.Packing.sameDistribution`). These theorems need
beta_0 = 1, which I7 guarantees for every accepted basis. The mask cells
themselves are hidden by the joint Polygero commitment's zero knowledge.

## Open questions

1. **Stamp the source claim?** I9 rests on visibility: `SourceClaim` is
   built only by `compile_packed`. The sumcheck could instead return its
   final constraints stamped like a `Challenge` (boundary and message count),
   and `prove`/`reduce` would accept them before sending `PackingU`.
   Recommendation: yes, since no message separates the last sumcheck draw
   from `PackingU` and the check is free; for degree one, accept the stamp
   before building the direct equation.
