# Sumcheck V2

Lean proofs for the projective, single-hand protocol at Rust snapshot
`21cb029`, with the earlier `fcf8a3a` terminal retained, in
[`rust/runtime/v2/sumcheck`](../../rust/runtime/v2/sumcheck/README.md).
The library and namespace are `SumcheckV2`. From `formal/`, run:

```sh
lake build SumcheckV1 SumcheckV2.APITest
```

The default `lake build` includes both protocols and the V2 API checks. The
legacy development is in [`sumcheck-v1`](../sumcheck-v1/SumcheckV1/README.md);
its `LfzkV1` clients continue to use `SumcheckV1`.

## Protocol modeled

Each table contains monomial coefficients, equivalently projective-cube values.
Binding the low index bit at `z` maps a pair `(a,b)` to `a + z*b`. A round
polynomial and its incoming claim satisfy

```text
P(x) = c0 + c1*x + c2*x²
C    = c0 + c2
C'   = z²*C + (1-z²)*c0 + z*c1.
```

The message carries `c0,c1`, with pads subtracted in the masked protocol. The
incoming claim supplies `c2 = C-c0`. This is a coefficient identity; no
interpolation nodes or division by two are used. All algebraic theorems work
over any field, including characteristic two. Finite-field counting theorems
add `Fintype` and `DecidableEq` assumptions.

For a native layer, let `Q[l,r]`, `L[l]`, and `K` be its effective quadratic,
linear, and constant coefficients after output weighting and assertion-coefficient
replacement. Linear assertions contribute to `L`; quadratic assertions contribute
to `Q`. The same `Q` is used in both bindings:

```text
q_l[l]    = Σr Q[l,r]*W[r] + L[l]
C - K     = dot q_l W
m[i]      = Πj u[j]^(bit j of i)
A         = dot m W
B         = dot m q_l = dot q_r W + dot m L
q_r[r]    = Σl Q[l,r]*m[l]
a_next[i] = m[i] + alpha*q_r[i]
C_next    = A + alpha*(B - dot m L).
```

The linear terminal commits four pad cells and checks

```text
d      = A*pB + B*pA - pD          (sent before nonzero r)
mA,mB  = A+r*pA, B+r*pB            (sent before alpha)
0      = C+r*(d+pD)+r²*pAB-mA*mB
C_next = mA+alpha*mB-r*pA-alpha*r*pB-alpha*L(u).
```

Honesty sets `pAB=pA*pB`; soundness does not assume it. A false reduced claim
leaves a nonzero quadratic with at most two nonzero roots. The additional
terminal loss is `2/(|F|-1)`, plus the usual `1/|F|` combining loss.
[`LinearTerminal`](SumcheckV2/LinearTerminal.lean) proves this reduction and
its affine symbolic row. [`LinearTerminalMasking`](SumcheckV2/LinearTerminalMasking.lean)
proves the local honest masking bijection for nonzero `r`.

The `Masked` product-slot terminal below belongs to the retained earlier
checkpoint. Its explicit product-consistency premise is not part of the
new verifier or soundness proof.

## Checked results

| Module | Main results |
|---|---|
| [RoundPoly](SumcheckV2/RoundPoly.lean) | `RoundPoly.toPoly_ofPoly` reconstructs every degree-at-most-two polynomial from its projective sum and transmitted coefficients. `eval_toPoly` identifies its polynomial evaluation with the runtime update. |
| [Round](SumcheckV2/Round.lean) | `sumcheck_step_completeness`, `sumcheck_step_reduction`, and `bad_round_roots`: a false incoming claim can become true at no more than two challenges. |
| [Multi](SumcheckV2/Multi.lean) | `sumcheck_multi_completeness` and `sumcheck_multi_reduction` for consistent true polynomial chains. Empty chains return the incoming claim; mismatched message/challenge counts reject. |
| [DotProduct](SumcheckV2/DotProduct.lean) | `roundMessage_eval` proves the coefficient constructor's update for any supplied claim; `dot_bindPair` specializes it to a true claim. `evaluate_eq_dot` identifies repeated folding with monomial weights. `honest_completeness` proves the full honest round sequence ends at the product of the folded scalars. `dot_product_reduction` specializes soundness to these tables. |
| [Layer](SumcheckV2/Layer.lean) | `tensor_rebinding`, `nextWeights_correct`, and `layer_completeness` prove the single-hand transition. `layer_reduction` shows a false incoming claim reaching a true next claim must encounter a bad round or a bad final combination. `bad_combine_roots` bounds the latter by one challenge. |
| [Affine](SumcheckV2/Affine.lean) | `affine_rebinding`, `affine_layer_completeness`, and `affine_layer_reduction` prove the native linear and constant corrections. They use the same quadratic round and linear combination bad events, without adding a constant-one input. |
| [Masked](SumcheckV2/Masked.lean) | `PadExpression.eval_rounds` proves symbolic execution agrees with unmasked numerical execution. `lowered_terminal_iff` proves product-slot lowering with an explicit product-consistency premise. `eval_claimNext` proves claim combination; `input_constraint_eq` and `input_constraint_iff` prove the public/private input split and its signs. |
| [Challenges](SumcheckV2/Challenges.lean) | `challenge_bad_card_le` gives the local bounds of two roots per round and one per final-claim combination used by the Fiat–Shamir analysis. |
| [APITest](SumcheckV2/APITest.lean) | Kernel-checked uses over prime and characteristic-two fields, scalar tables, malformed round counts, false incoming claims, repeated pad identifiers, product-slot consistency, and the chained Fiat–Shamir API. Imports V1 and V2 together. |

`Cube n` is a low-bit-first coefficient table with `2^n` entries. Tables with
non-power-of-two lengths can be represented by zero padding. The scalar case
`n = 0` has one entry and no rounds. The true polynomial chain is constructed
from the actual folds; its consistency, degree bound, and terminal value are
proved in `truePolys_consistent`, `truePolys_degree`, and `truePolys_final`.

## Soundness and transcript boundary

The [witness-selection adapter](SumcheckV2/WitnessSelection.lean) separates
candidate selection from ordinary quadratic sumcheck. Two masked fingerprints
first select a unique frontend witness outside a `choose(L,2)/q²` collision
event. `selected_round_bad_card_le` then pays two roots, without a candidate-list
multiplier. The selected witness includes frontend pads and terminal cells;
it need not fix Polygero's internal hiding rows.

[`Chained.failure_bound`](SumcheckV2/ChainedFiatShamir.lean) proves
`2Q/q + (Q+1)/|Link|` against an arbitrary adaptive total-oracle query tree,
under the typed [chain representation](../transcript-v2/README.md) and local
algebraic reduction laws. `Q` bounds distinct queries, not accepted-proof rounds.
One answer contains the link, the current field challenge and any unrelated
challenge coordinates; the adversary sees all prior answers. Ancestor-dependent
round data gives the required independence from the answer being counted.
The chain theorem derives query charging rather than assuming it.

The selection component separately costs `Q*choose(L,2)/q²`. Combining frontend
bad events in the generic theorem charges the common chain exception once.
The [current mdoc composition](../lfzk-v2/LfzkV2/Current/MdocStrandOracle.lean)
derives the application reduction from actual adaptive runtime acceptance and
includes the nonzero terminal corrections. Canonical query encoding and
requested-public readback are checked. The explicit ideal-sampler oracle
assumption and Rust source correspondence remain separate from these algebraic
proofs. This component result alone is not an application's
end-to-end security certificate.

`BadRoundEvent` means a false projective sum is repaired by the current
challenge. Its bound comes from the roots of a nonzero quadratic difference.
`BadCombineEvent` means at least one of `A,B` is wrong but `A + alpha*B` is
correct; there is at most one such `alpha`.

The typed Fiat–Shamir strategies reconstruct each message from the preceding
oracle answers. The current answer is absent from that reconstruction.
`ChainedFiatShamir` lifts the local two-root bound to `2Q/|F|`, charging queries
rather than rounds in an accepted proof. The complete replay separately accounts
for nonzero terminal scales and committed candidate families. The local API
checks exhibit two distinct bad challenges over `F₂`.

## Runtime correspondence and scope

These are component algebra and soundness-reduction proofs. The table identifies
the Rust operations modeled; it is not a source-level refinement certificate.

| Rust source | Lean model |
|---|---|
| `sumcheck-v2/src/prover.rs`, `dense.rs` | `roundMessage`, `fold`, `honestMessages` |
| `sumcheck-v2/src/monomial.rs` | `monomialWeights`, `evaluate_eq_dot` |
| `sumcheck-v2/src/quad.rs` | `bindRightAffine`, `bindLeft`, `affine_rebinding`, `affine_nextWeights_correct` |
| `sumcheck-v2/src/symbolic.rs` at `21cb029` | Shared `PadExpression` operations and `LfzkV2.Linear.buildConstraints_correct`, including both public corrections |
| `zk-v2/src/constraint_compiler.rs` at `21cb029` | `LfzkV2.Linear.compiled_iff_clear` and `Linear.Runtime.CompiledFS`; the new backend has only affine rows |
| `sumcheck-v2/src/transcript.rs` | Prefix-dependent challenge strategies |

`roundMessage` takes the incoming claim explicitly, matching
`prover::quad_round_poly`'s `c1 = p(1) - claim`. It does not replace that claim
with the true dot product. `roundMessage_eq_honestMessage` supplies the honest
specialization under `claim = dot q w`. For a false incoming claim, the exact
discrepancy between the next claim and the folded dot product is
`(z²-z) * (claim - dot q w)`, as proved by `roundMessage_eval`.

The companion [`LfzkV2.Native`](../lfzk-v2/LfzkV2/Native/Circuit.lean) frontend
constructs all three effective streams, with separate linear and quadratic
assertion occurrences. It proves complete circuit reconstruction, corrected
symbolic execution, sparse compilation, honest construction, and soundness
reduction including zero outputs and invalid assertions. Its challenge tests
have the same sharp budget `logv + Σ(min(1, assertions) + 2*logw + 1)`.
The [`LfzkV2.Packed`](../lfzk-v2/README.md) composition connects those native
semantics to packed input equations, the committed Polygero candidate family,
causal Fiat–Shamir replay, the two-field MAC, and both Merkle commitments.
The earlier quadratic/unpacked model remains available in its original namespace.

The remaining correspondence obligations are specific:

- Map a finite Rust array to `Cube n` with zero padding, and prove the in-place
  fold and truncated monomial-weight routine realize that map.
- Relate Rust field operations and accumulators to Lean's exact `Field`
  operations; the current algebraic model does not verify limb arithmetic or
  accumulator overflow bounds.
- Relate the Rust sparse traversal, array layout, and tableau coordinates to
  `LfzkV2`'s circuit tensors and explicit input/pad coordinate maps.

This algebraic component omits serialization; the current runtime composition
adds canonical proof-body and transcript-query codecs.
The retained linear-terminal checkpoint is in `LfzkV2.Linear.Runtime`,
including its packed/direct rows, adaptive Fiat–Shamir, MAC, and two Merkle
commitments. The current MAC-free runtime and its shared commitment are modeled
separately in [`LfzkV2.Current`](../lfzk-v2/README.md#current-mac-free-protocol).
`LfzkV2.Packed` retains the earlier product-checked checkpoint.
Neither this component library nor the complete soundness composition asserts
full joint zero knowledge. Existing V1 proofs and certificates remain unchanged.
