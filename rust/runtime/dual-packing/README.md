# Trace-zero dual packing

This adapter implements the linear-authentication protocol in *Dual Packing
via the Trace Pairing*, sections 4–6, from
`../PippoDreams/papers/dual-packing/main.tex`. The accompanying native verifier
is `DualPacking.ArtinSchreier.Instance.nativeLinearVerify` in
`ArtinSchreierBackend.lean`. This module imports neither sumcheck nor Polygero;
the caller must authenticate **both** returned linear equations against the
original commitment.

## Coordinates and public coefficients

For GF128's existing polynomial basis `beta_j=x^j`, pack the logical bits as
`X_i=sum_j beta_j*x_ij`. The trace-dual basis satisfies
`Tr(alpha_j*beta_k)=[j=k]`, so every committed word has unique bit coordinates.
For arbitrary field-valued source weights `R_ij`, define

```text
D_ik = sum_j alpha_j*digit_k(R_ij)
B_k  = sum_i D_ik*X_i
c    = rhs(auxiliary).
```

Then `Tr(B_k+alpha_k*c)=0` for every k is equivalent to the incoming claim.
The public coefficient rows are transposed as bit matrices and converted into
the dual basis. The optimized conversion retains the common denominator
`alpha_127=1/(x^6+1)` for `P(x)=x^128+x^7+x^2+x+1`.
There is no Frobenius-orbit transform of the coefficients or witness.

Basis state is explicitly owned. Public traces use the fixed parity mask
`Tr(z)=sum_j digit_j(z)*Tr(beta_j)`, checked against the power-sum trace in tests.
Generic custom bases must have a nonzero first coordinate of one, equivalently
`{1,beta_1,...,beta_(m-1)}` must be a basis. Construction checks this condition,
which is required for the fixed dependent-mask relation to hide every
trace-zero coordinate. The native polynomial bases satisfy it.

## Committed masks and interaction

Before challenges, the caller commits 127 independent uniform fields `t_1..t_127`
and independent uniform `r`, together with a scalar cell `b`, honestly `r*r`.
The physical mask cells are `[t_1,...,t_127,r,b]`. There is no committed `t_0`;
it is the dependent value `sum_(k!=0) beta_k*t_k`.

The source weights and affine target are fixed before the adapter starts.
Every target auxiliary refers to a cell fixed by the original commitment.
The interaction is:

1. Send all 128 fields `U_k=B_k+alpha_k*c+t_k+t_k^2`.
2. Check every public trace `Tr(U_k)=0`, then sample 128 independent uniform
   fields `delta_k`. Zero and one challenges are allowed. Set `gamma_k=delta_k^2`.
3. Send `A=r+sum_k delta_k*t_k`, and absorb A before the backend statement.
4. Authenticate the paper's two equations:

```text
A = r + sum_k delta_k*t_k
sum_k gamma_k*U_k
  = sum_i d_i*X_i + eta*c + sum_k gamma_k*t_k + A^2 + b,
d_i = sum_k gamma_k*D_ik,    eta = sum_k gamma_k*alpha_k.
```

Eliminate `t_0` with
`sum_k w_k*t_k=sum_(k!=0)(w_k+w_0*beta_k)*t_k` in each equation.
The square `A^2` is public. Every committed cell appears linearly; **there is
no backend check of b=r*r**. An inconsistent b contributes a fixed affine
offset in the soundness argument, exactly as in the paper and its Lean audit.

The prover receives the logical auxiliary values to evaluate its hidden affine
target. They exclude the adapter cells. In the packed GKR composition they are
the original GKR pad cells. The verifier substitutes
the same affine expression into the second native equation; c is never disclosed.

## Layout, compatibility and security boundary

The adapter adds 129 committed cells, 129 response elements (2064 bytes), two
native linear equations, no extra commitment root and no multiplication gate.
Compared with the previous orbit adapter this is one extra committed cell and
32 extra raw response bytes. Complete proof size also depends on backend geometry.

The standalone binary transcript domain is
`longfellow/dual-packing128/trace-zero/v1`. Ordinary zk-v2 binds the adapter and
layout under `longfellow/v2/packing-commitment/v1` before the root. All combined
v2 proofs use `LFV4` and ambient-only `PLG8`; development caches use `MDOCBIT6`
and `MDOCNEXT3`. Earlier proof/cache versions are rejected. The polynomial
packing basis ID remains 2. V1 formats are unchanged.

The paper proves native interactive reduction error at most `1/|GF128|`, allowing
arbitrary committed masks, r and b. Its backend composition theorem retains
false-equation authentication as a separate event. That theorem is about its
Lean verifier; this Rust implementation is checked against the same expanded
equations by independent tests, without a formal Rust-to-Lean refinement proof.
No composed Fiat–Shamir bound or joint zero-knowledge theorem is claimed here.

Tests cover direct trace-adjoint conversion, parity traces, both native equations
for arbitrary cells and targets, zero/one challenges, hidden affine targets,
full transcript order, malformed messages and codecs, and the Lean regression
that deliberately accepts an inconsistent square cell at one challenge.
The [implementation audit](AUDIT.md) maps these checks to the paper and records
the composition boundary.

```sh
cd rust
cargo test --lib --features experimental,testonly dual_packing -- --test-threads=1
cargo test --lib --features experimental,testonly runtime::zk_v2 -- --test-threads=1
```

## Generic finite extensions

`algebra::packing::PackingExtension` describes a trusted embedding `K -> F`,
with distinct `Base` and `Ambient` arithmetic types, a native basis, typed
base-field coordinates, and relative Frobenius `sigma(x)=x^|K|`. Its default
Frobenius uses arbitrary-size little-endian exponents. `FiniteField` provides
arbitrary-size cardinalities and a representation identity. Field arithmetic
contains no packing-basis state.

Each field selects its default adapter through an explicit `PackingField` impl
and associated `Packing` type. Prime fields select `IdentityExtension<Self>`;
GF128 selects `Binary128Extension`; the experimental sextic field selects
`Prime24Extension`. There is no registration macro or overlapping blanket impl.
A second GF128 adapter over GF256 exercises non-Boolean base-field coordinates;
mdoc continues to use GF2 coordinates.

`PackingParameters::new(field, extension)` owns initialization. `with_basis`
accepts an admissible basis, computes its coordinate transform and trace-dual
basis, and rejects singular choices or an invalid distinguished coordinate.
Relative trace is a Frobenius sum, with no
normalization by the extension degree, including when the characteristic
divides that degree. Construction is preprocessing and can be reused.

`generic::{SourceClaim, Affine, PackingMasks, PackingProof, NativeEquation}`
form the standalone protocol API. A source claim means
`sum_j R_j*embed(x_j)=rhs(auxiliary)` for arbitrary `x_j in K`. Masks must be
sampled uniformly and committed with the packed words and target auxiliaries
before `prove` or `verify`. The caller supplies the commitment context. The
returned native equations use the zero-sum convention and must both be
authenticated against that original commitment. In arbitrary characteristic:

```text
U_k = B_k - alpha_k*c + sigma(t_k) - t_k
A = r + sum_k delta_k*t_k
sum_k sigma(delta_k)*U_k
  = sum_i d_i*X_i - eta*c - sum_k sigma(delta_k)*t_k + sigma(A) - b.
```

Only the final partial block is zero padded by `pack`; a source claim imposes
no separate zero constraints on unused coordinates of a committed word.

For degree one, the protocol returns one direct equation. It allocates no
mask cells, emits no proof bytes and touches neither transcript nor randomness.
For a singleton basis `[beta]`, the packed coefficient is `R/beta`.

The generic envelope `LPK1` binds the ambient field, base field, embedding,
extension degree and chosen basis to trusted parameters, and rejects truncated
or noncanonical encodings before allocating response vectors. The existing
polynomial GF128/GF2 profile preserves its 2064-byte messages and transcript
exactly. Its optimized transpose feeds the same native-equation kernel as the
generic implementation; a differential test checks messages, equations and
transcript state. Other profiles use a descriptor-separated transcript.

Tests cover GF128/GF2, GF128/GF256, GF4/GF2, GF9/GF3, GF25/GF5,
the sextic MLDSA extension, nonunit bases, identity packing over P256, arbitrary
mask scalars, exhaustive GF9 false-claim challenges, and authentication of the
generic equations through Polygero using the original commitment. The native
interactive error is at most `1/|F|`; backend authentication and Fiat–Shamir
composition remain separate obligations.
