# Foreign storage

`runtime::v2::foreign` is the cross-field mechanism of v2. It lets a frontend in
one field keep some of its values as bits in the binary commitment. Foreign
storage sits beside packing as a way of storing frontend inputs.

Frontends emit affine claims over their inputs and pads without knowing where
those values live. Storage reductions discharge those claims:

| Storage | Reduction |
|---|---|
| native cells | Polygero rows |
| packed binary bits | the packing reduction |
| foreign bit groups | a split, then the exponent-tree adapter |

The adapter is the opening protocol of foreign storage. It proves explicitly
stated modular claims over bit groups and never reads another protocol's
internals.

## Modules

Storage maps and the split of a frontend's batched claim belong to the zk
layer (see [Storage](../zk/README.md#storage)):

- `zk::storage` has the following types.
  - `StorageMap`: each value is `Native(cell)` or `Foreign(coordinates)`.
  - `Run`: the map's layout parameters as bound to the transcript.
  - `BitGroup<N>` and `Group`: typed and untyped positions of bits in the
    binary input array.
  - `ReservedSuffix`: an allocator for the bits after the format circuit's
    inputs.
  - `ModularClaim`: a linear claim over foreign bit groups, modulo the
    claim field's order.
- `zk::split` handles a participant whose values are partly native and partly
  foreign. Its own commitment holds `[native private inputs | R | native pads]`.
  1. The verifier draws a fresh nonzero `eta`.
  2. The prover sends `mu = eta<w_F, v_F> + R`.
  3. The batched claim `<w, v> = t` splits into a native row,
     `eta<w_N, v_N> - R + mu - eta*t = 0`, and a foreign modular claim,
     `<eta*w_F, v_F> + R_bits = mu (mod p)`.

  R is uniform and used only here, so `mu` hides `<w_F, v_F>`. Only R's
  residue modulo p matters, so R's bits have no range check.

This module discharges the modular claims:

- `adapter`: the fixed product-tree fragment, the definitions of its virtual
  leaves, and the P-256 encoder (`p256`).
- `word`: three types.
  - `Word<N>`: the integer quotient, used only inside the adapter.
  - `Otp<N>`: the committed one-time pad, built only by the prover from
    `ceil(N/8)` fresh bytes.
  - `MaskedWord<N>`: an element of GF(2)^N. It is the only one of these
    types that appears in a proof, and its canonical encoding (zero
    padding enforced) is defined once here.

## The P-256 adapter

The adapter uses the coordinate prime p, not the ECDSA scalar order. Two
independent nonzero full-field challenges `alpha` rescale the foreign claim
after `mu` is fixed. Write each rescaled bit coefficient as `A_i` and the target
as `C`, both canonical modulo p. Honest bits satisfy `sum A_i*b_i = C + k*p` for
a quotient `k < 2^10`.

With `M = 2^128-1`, the fixed generator `g` satisfies `g^(-p) = X`, so each tree
checks:

```text
product_i (1 + b_i*(g^A_i - 1)) * product_j X^(2^j * k_j) = g^C
```

p exceeds M, so the exponent sums wrap modulo M. The two independent rescalings
bound multiplicative-group collisions (`Adapter.Bad`). Each quotient is a
`Word<10>`. Its bits are committed only as `Otp<10>` pads, and the proof
carries `MaskedWord<10> = k xor o`. A quotient leaf `X^(2^j*(m_j xor o_j))`
is affine in the committed pad bit `o_j`, with coefficients chosen by the
public bit `m_j`.

The leaves are virtual inputs of the binary participant: per-proof
definitions `c0 + c1*x[source]` over committed bits, which constraint
compilation substitutes like public inputs. Each tree's target is folded into
its first leaf. The archived fragment is therefore a challenge-free product
tree whose outputs assert `product + 1 = 0`.

## Binary input layout

```text
[public | hash private (issuer digest, device x, y inside) | R | O_0 | O_1 | leaves]
 <---------- hash ninput ---------->
          <------------------ committed ------------------->
 <------------------------------ fragment ninput ----------------------------->
```

The hash circuit is archived at its natural width. R, the quotient pads and the
virtual leaves lie beyond it, and sumcheck lets each component read only its
own input prefix. So the hash circuit cannot address them by construction.
The adapter fragment is rebuilt deterministically from the hash circuit's
shape; its circuit ID is bound with the others.

## Transcript

Before the shared root, a mixed frontend binds its layout parameters: its
circuit ID, its storage map as runs, and the position of R's bits. The other
participants bind their own layouts in the same way. After the root, only the
statement, prover messages and fixed domain labels are absorbed: `mu`, the
masked quotients, and the frontends' and backend's own messages. Challenge-
and message-derived values (claim weights, leaf definitions, quotients) are
never absorbed; both roles recompute them.
