# Sumcheck V2

Lean proofs for the projective, single-hand protocol at Rust snapshot
`fcf8a3a`, in
[`rust/runtime/sumcheck-v2`](../../rust/runtime/sumcheck-v2/README.md).
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

After the sumcheck rounds, the terminal constraint checks the reduced claim
against `A*B`. The two final claims must be fixed before `alpha` is sampled.

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
| [FiatShamir](SumcheckV2/FiatShamir.lean) | `layer_tape_card_le` counts bad tapes with separate budgets of two per round and one per final-claim combination. `RoundStrategy` and `combinatorial_fiat_shamir` specialize the same data and bound to round-only tapes. |
| [APITest](SumcheckV2/APITest.lean) | Kernel-checked uses over prime and characteristic-two fields, scalar tables, malformed round counts, false incoming claims, repeated pad identifiers, product-slot consistency, and mixed challenge budgets. Imports V1 and V2 together. |

`Cube n` is a low-bit-first coefficient table with `2^n` entries. Tables with
non-power-of-two lengths can be represented by zero padding. The scalar case
`n = 0` has one entry and no rounds. The true polynomial chain is constructed
from the actual folds; its consistency, degree bound, and terminal value are
proved in `truePolys_consistent`, `truePolys_degree`, and `truePolys_final`.

## Soundness and transcript boundary

`BadRoundEvent` means a false projective sum is repaired by the current
challenge. Its bound comes from the roots of a nonzero quadratic difference.
`BadCombineEvent` means at least one of `A,B` is wrong but `A + alpha*B` is
correct; there is at most one such `alpha`.

Strategies are functions of the earlier challenge prefix. Their types do not
permit access to the current or later challenges when choosing a message,
incoming claim, or true polynomial. For `R` sumcheck slots and `L` combination
slots, let `N = R+L`. The mixed theorem bounds bad tapes by

```text
(2R + L) * |F|^(N-1).
```

Thus uniform independent field challenges give the usual `(2R + L)/|F|`
upper bound. The Lean theorem is stated as a natural-number cardinality bound,
including empty tapes. Over very small fields it can be trivial: the API
checks exhibit two distinct bad challenges over `F₂`.

The counting proof reuses the protocol-independent prefix/fiber lemmas in
`SumcheckV1.Grinding`. V2 round algebra, table folds, and layer transitions
are proved separately from V1's affine-endpoint protocol.

## Runtime correspondence and scope

These are component algebra and soundness-reduction proofs. The table identifies
the Rust operations modeled; it is not a source-level refinement certificate.

| Rust source | Lean model |
|---|---|
| `sumcheck-v2/src/prover.rs`, `dense.rs` | `roundMessage`, `fold`, `honestMessages` |
| `sumcheck-v2/src/monomial.rs` | `monomialWeights`, `evaluate_eq_dot` |
| `sumcheck-v2/src/quad.rs` | `bindRightAffine`, `bindLeft`, `affine_rebinding`, `affine_nextWeights_correct` |
| `sumcheck-v2/src/symbolic.rs` | Shared `PadExpression` operations and `LfzkV2.Native.buildConstraints_correct`, including both public corrections |
| `zk-v2/src/constraint_compiler.rs` | `lowered_terminal_iff`, `input_constraint_eq`, and `LfzkV2.Native.compiled_iff_clear`; `LfzkV2.Packed` authenticates the packed source equation |
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

Serialization and concrete transcript encoding are also outside the model.
The complete protocol composition is in `LfzkV2.Packed`; this component library
does not itself assert a full zero-knowledge theorem. Later changes to terminal
masking or the backend are outside the stated snapshot. Existing `LfzkV1`
security certificates remain about V1.
