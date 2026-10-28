# LFD2: degree-separated LFC2 experiment

`degree-separated` enables an explicit `compile_degree_separated` compiler API.
The v9 development provider and ML-DSA v2 benchmark select that API with this
feature. Ordinary `compile_v2`, frozen circuits and v1 retain their conventions.
The source logic API still numbers user inputs from one. The new lowering pass
renumbers them from zero and removes the source API's reserved input slot.
A missing polynomial factor is compiler metadata, never an input or layer wire.
Unit copy chains are eliminated before scheduling. Application input builders
on this path do not prepend a field element equal to one.

## Encoding

The four-byte magic is `LFD2`. The remaining header and coefficient table use
LFC2's encoding, including field identifiers, dimensions and single-copy count.
Each layer starts with `logw, nw` followed by three independent streams, in this
order:

| Stream | Delta dictionary entry | Value accumulated at output g |
|---|---|---|
| Quadratic | dg, dh0, dh1, coefficient index | k W[h0] W[h1] |
| Linear | dg, dh0, coefficient index | k W[h0] |
| Constant | dg, coefficient index | k |

Each stream has LFC2's dictionary count, entries, segment dictionary and macro
token sequence. Indices use the same bounded ULEB128 and wrapped zigzag delta
encoding. The previous g and input indices reset to zero at the start of each
stream and continue across its tokens. Omitted input coordinates consume no
bytes. The expanded polynomial is the sum of all three streams.

Zero coefficients remain assertion markers only in the quadratic stream:
their two input values must have zero product. Linear and constant coefficients
must be nonzero. The reader applies its expanded term budget to all three
streams together, validates dimensions and indices, and checks macro index
ranges using translated prefix bounds rather than expanding every occurrence.
The circuit ID has a new domain and authenticates the degree and all expanded
terms. Segmentation and coefficient-table renumbering preserve that ID.

`to_bytes_lfc2` emits LFD2 when affine streams are present; both the general
reader and `from_bytes_lfc2` accept it. Legacy LFC2 bytes and identities are
unchanged. LFC1 writing rejects affine streams. LFD2 is for sumcheck-v2.

The initial in-memory implementation reuses the existing compressed delta
container for each stream. Linear and constant dictionary entries therefore
still reserve two `u32` input slots in memory; the omitted slots are zero.
It does not expand millions of linear terms into separate field-element objects.
`Layer::for_each_term` traverses its own stream; `streams()` enumerates all three.
`num_terms()` includes all streams, including for transcript padding.

## Sumcheck

After sampling output weights a and assertion challenges, write the layer claim
as

```
claim = sum_l W[l] (sum_{g,r} a[g] Q[g,l,r] W[r] + sum_g a[g] L[g,l])
        + C_a,
C_a = sum_g a[g] C[g].
```

Assertion terms use their independent sampled coefficients in place of aQ.
Subtract the public C_a and run the existing masked dot-product rounds with

```
q_l[l] = sum_{g,r} a[g] Q[g,l,r] W[r] + sum_g a[g] L[g,l].
```

At the final monomial point u, let m[l] be its monomial weights. The two hidden
claims are A = sum_l m[l]W[l] and B = sum_l m[l]q_l[l]. Their product checks the
last round claim. With

```
L_u = sum_{g,l} a[g] L[g,l] m[l],
q_r[r] = sum_{g,l} a[g] Q[g,l,r] m[l],
```

we have B = sum_r q_r[r]W[r] + L_u. Consequently the next claim is
A + alpha B - alpha L_u, with input weights m + alpha q_r. Both parties compute
C_a and L_u publicly, and the symbolic constraint builder applies those exact
offsets. No extra masked messages, committed cells or constant wire are needed.
The numerical code reuses the monomial weights for L_u and the quadratic binding;
coefficients +1 and -1 in the linear stream use additions and subtractions.

The format and compiler change circuit identities, challenges and proof bytes.
This experiment does not extend the security theorem to the existing experimental
v9 packing composition.

## Measurements

See [the comparison](../../benches/results/2026-10-28-degree-streams/README.md)
for compressed/uncompressed bytes, decoded circuit allocations, prover heap,
and online prover/verifier times. Serialized uncompressed bytes, decoded circuit
storage and peak prover memory are distinct quantities; all are measured.
