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
bit, and canonical range predicates enforce the device coordinates below p.
The R bits have no range check: the handoff uses only R's residue modulo p
(`Handoff.product_handoff`), so a non-canonical encoding of R such as R+p is
harmless. Exact digest-bit constraints retain SHA-256 digests even when they
exceed p.

The hash circuit cannot read the reserved 256 R (mask) bits or the 20 quotient
OTP bits: they are appended to the compiled hash circuit's inputs after
application compilation. Tests check every input-layer gate and assertion in
all four supported compiled circuit shapes; the check has no runtime cost and
is not repeated when archives are loaded. Both the soundness and the
zero-knowledge endpoints assume this separation (`MdocWitness.ReadDisjoint`).
Adapter coefficients and masked advice belong to the separate product-tree
circuit.

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
