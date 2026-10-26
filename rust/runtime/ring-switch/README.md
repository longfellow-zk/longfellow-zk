# Flat trace ring switching (Rust prototype)

`runtime::ring_switch` reduces arbitrary bit-linear claims to one native
GF128 linear relation. It uses the existing polynomial basis, with no tower
construction and no inner sumcheck. It imports neither sumcheck nor Polygero.
The caller must authenticate the returned relation against its original
commitment; reconstructing the relation alone does not accept a proof.

Write each packed word as `X_i = sum_j beta_j*x_ij`, with
`beta_j = x^j` in the existing GF128 encoding. The trace-dual basis satisfies
`Tr(alpha_j*beta_k) = [j=k]`. Then

```text
rho_i,s = sum_j alpha_j * R_i,j^(2^-s)
V_s     = sum_i rho_i,s * X_i
sum_i,j R_i,j*x_i,j = sum_s V_s^(2^s).
```

The caller commits 127 independent masks `R_s` and the dependent checksum
`S = sum_(s=1..127) R_s^(2^s)`, together with the packed words and caller
auxiliaries. After the coefficients and hidden affine target are fixed,
the transcript samples nonzero beta. The prover sends only

```text
M_s = V_s + beta^(2^-s)*R_s,     s=1,...,127.
```

Component zero is implicit, so the affine target is never disclosed.
After the **entire response** is absorbed, the transcript samples 127
independent gamma values (not powers of one value). The output equation is

```text
rhs(aux) + sum_(s=1..127) (M_s^(2^s) + gamma_s*M_s)
  = dot(a, packed_words) + beta*S
    + sum_(s=1..127) gamma_s*beta^(2^-s)*R_s,

a_i = rho_i,0 + sum_(s=1..127) gamma_s*rho_i,s.
```

This adds **2032 response bytes**, **128 committed mask/checksum cells**,
**one linear equation**, **zero roots**, and **zero multiplication
constraints**. The total proof-size change also depends on the backend layout.
The nominal interactive adapter bound is `2/|GF128| = 2^-127`; it is not an
end-to-end Fiat–Shamir bound for Longfellow. Joint zero knowledge with the
backend and Lean formalization remain deferred.

The implementation supports dense input coefficients without a low-rank
factorization. Expand each public coefficient into polynomial coordinates,
`R_i,j = sum_h beta_h*r_i,j,h`, where every `r_i,j,h` is a bit. Then

```text
C_i,h = sum_j alpha_j*r_i,j,h
Z_h   = sum_i C_i,h*X_i
V_s   = sum_h beta_h^(2^-s)*Z_h.
```

This moves the Frobenius powers past the large sum and compresses the
witness into only **128 fields**. Each public coefficient row is transposed
as a 128-by-128 **bit** matrix using shifts, masks and XORs. For the existing
polynomial `P(x)=x^128+x^7+x^2+x+1`, all dual coordinates share the factor
`d=1/P'(x)=1/(x^6+1)=alpha_127`. If `u` packs the transposed bits in reverse
coefficient order, then

```text
C_i,h = d * (u XOR (u >> 121) XOR (u >> 126) XOR (u >> 127)).
```

The common factor `d` is applied after accumulation. The remaining large
loop uses 128 carryless field multiply-accumulates per packed word. The
127 components are obtained by evaluating the degree-at-most-127 polynomial
`sum_h Z_h*T^h` at the Frobenius conjugates of `x`. Public reconstruction
reuses the same transposed coordinates and the images
`Psi(beta_h)=beta_h+sum_s gamma_s*beta_h^(2^-s)`.
This computation preserves the messages and transcript exactly. It uses
fixed memory access patterns for witness data and no lookup tables.
Public trace-dual basis state is explicitly owned by the caller.

The tensor optimization in §4 of *Sumcheck bit packing* applies when the
source weights have a small decomposition `R_i,j = sum_h C_h,i * D_h,j`.
For one term, another possible compression is
`Y_j = sum_i C_i * bit_i,j`. This does not change the adapter messages,
masks or algebraic relation. The dense transpose above needs no such
tensor decomposition.

The current v9 caller does not supply such a decomposition. Its one-hand
GKR terminates with weights `m_u[r] + alpha*q_r[r]`, where
`q_r[r] = sum_(g,l) a[g]*Q[g,l,r]*m_u[l]`; assertion terms use their sampled
replacement coefficients. The wiring-derived `q_r` need not be a monomial
evaluation. In the two-attribute benchmark, the first 128 packed rows of
the private GKR coefficients already have rank 128 over GF128, before and
after the MAC equations are combined. Consequently a small exact tensor
decomposition of the current claim is unavailable. See the
[measurement](../../benches/results/2026-10-26-flat-v9/factoring.txt).
The dense transpose optimization applies directly to these full-rank
weights. GKR remains one-hand.

`core::bits::PackedBits` owns logical bits without field dependencies.
Packing is raw polynomial coordinates. The authenticated manifest has packing
basis ID 2. Packed application proofs use `LFB2` and caches use `MDOCBIT2`;
the former tower prototype's proofs and caches are rejected. Direct-field
v8's `LFV2` encoding and NEXT selection are unchanged.

```sh
cd rust
cargo test --release --lib --features experimental ring_switch
cargo test --release --lib --features experimental packed
```
