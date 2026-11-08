# P256 claim adapter

The adapter connects a P256 coordinate-field claim to Boolean inputs committed
in GF(2^128). It uses the coordinate prime p, not the ECDSA scalar order.
The application owns the protocol sequence in its prover and verifier.

Prime-field sumcheck first fixes all masked messages. Fresh random weights combine
all layer equations and the final input equation into one linear claim. Its
shared-input contribution is hidden by a uniform, precommitted scalar R:
mu = eta * <shared weights, shared bits> + R. The prime-field opening checks the
remaining inputs, R and pads. The binary source contains canonical bits for R
and the shared digest/key values.

Only after mu and its weights are fixed does each of two independent nonzero
P256 challenges rescale that claim. Write the resulting bit coefficients as
A_i and the target as C, using canonical representatives modulo p. Honest bits
satisfy sum A_i*b_i = C + k*p. For M = 2^128-1, the fixed binary-field generator
g satisfies g^(-p) = X. Consequently the adapter checks

```text
product_i (1 + b_i*(g^A_i - 1))
  * product_j (1 + k_j*(X^(2^j) - 1)) = g^C.
```

The two independent rescalings limit multiplicative-group collisions. Each
quotient uses ten bits, hidden by precommitted one-time pads. The public masked
advice has a canonical 20-bit encoding. Binary packing enforces every source
bit; canonical range predicates enforce R and device coordinates below p.
Exact digest-bit constraints retain SHA-256 digests even when they exceed p.

The tree builder constructs sparse circuit IR directly. Its topology is fixed
by the widths, while the public coefficient table depends on the challenges.
Both roles derive the same instance. A leaf is encoded as 1 + power*b + b,
so power=1 keeps the same topology without introducing a zero-coefficient
assertion marker. Internal nodes multiply and lone nodes carry forward.
There is no padding between circuit fragments and no separate leaf commitment.
The tree has 4,150 wires excluding shared inputs and 8,288 terms.

The trees and hash circuit use one global wire array per layer, ordinary
layered sumcheck and one final packing reduction. One joint Polygero opening
authenticates both fields. The adapter is included in the current v2 extraction
and joint zero-knowledge analysis, under the oracle and trusted-circuit
assumptions documented in the [formal v2 analysis](../../../../../../formal/lfzk-v2/README.md).
