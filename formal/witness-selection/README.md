# Masked witness selection

This component analyzes the protocol implemented by
[`runtime::v2::witness_selection`](../../rust/runtime/v2/witness-selection/README.md).
It treats a fixed committed list of candidate frontend cell vectors, each with
two dedicated mask cells. Polygero's internal hiding rows are outside that
projection. Different backend candidates may project to the same frontend
witness; the projected list is a set and removes those duplicates.

For original cells `w`, masks `(m₁,m₂)` and independent uniform vectors `(a₁,a₂)`,
the response is `(m₁+dot(a₁,w), m₂+dot(a₂,w))`. The mask cells do not occur among
the random coefficient coordinates. Responses can be chosen after the vectors.

## Collision counting

`Algebra.lean` and `Collision.lean` supply the local algebra and finite counts
used by the Fiat–Shamir analysis:

- A pair of distinct candidates collides with probability at most `1/q²`.
  If the original cells agree but a mask differs, collision is impossible.
  Otherwise each vector fixes one independent coefficient at a nonzero
  difference coordinate. The argument works in every characteristic.
- A list of `L` candidates has collision probability at most `choose(L,2)/q²`.
  This is a union over unordered pairs, not a union over possible responses.
- Outside that event, every response pair matches at most one candidate.
  `select` depends only on the early list, vectors and responses.
- A later local bad-challenge bound of `β` for one matching witness remains `β`
  when written as an existential over the list. There is no frontend list
  multiplier after selection.
- Fresh masks translate responses bijectively for each fixed original witness
  and coefficient pair. This is a response-hiding component, not a proof of the
  complete committed protocol's zero knowledge.

The collision and uniqueness results also cover an empty original cell vector.
Soundness allows arbitrary commitment-fixed mask values; private uniform masks
are needed for the response-hiding argument, not for the collision bound.

## Fiat–Shamir

`ChainedFiatShamir.lean` uses an adaptive total-oracle query tree. One answer
contains the feedback link, **both** vectors and an independent `Rest` component
for other fields' challenge coordinates. Lists read the fixed preimage and
ancestor answers. Their independence from the current answer is proved using
`PrefixPoints`. With at most `L` candidates, the collision charge over `Q`
distinct queries is at most

```
Q * choose(L,2) / q².
```

The [typed chain theorem](../transcript-v2/README.md) adds the common exception
`(Q+1)/|Link|` and derives boundary-query order and charging even with repeated
queries and branch exploration. Scaled local counts avoid divisibility or
nonempty-vector assumptions. For a joint invocation, sum the per-field charges;
independence of the failure events across fields is unnecessary.

The separate
[`SumcheckV2.WitnessSelection`](../sumcheck-v2/SumcheckV2/WitnessSelection.lean)
module proves a two-root bound after selection. Ordinary quadratic sumcheck's
adaptive `2Q/q` charge is in
[`SumcheckV2.ChainedFiatShamir`](../sumcheck-v2/SumcheckV2/ChainedFiatShamir.lean).
`Q` counts queries, not rounds in an accepted proof. Prior complete answers
remain visible to the adversary.

[`polygero.FiatShamir.WitnessSelection`](../polygero/FiatShamir/WitnessSelection.lean)
refines the frontend term in the existing committed-composition theorem into
selection error plus fixed-witness frontend error. It projects candidate
indices before selecting; it does not assume all internal backend rows become
unique. Polygero's extraction and outside-list errors remain separate.

Thus the intended accounting has the shape

```
backend extraction/outside-list errors
  + Q * sum_i choose(L_i,2)/q_i²
  + fixed-witness frontend error
  + (Q+1)/2^256.
```

The `2Q/q` frontend specialization concerns ordinary quadratic sumcheck with
uniform field challenges. Nonzero terminal scales and other protocol tests
retain their own corrections. The typed oracle model proves adaptive charging
and link/seal guessing bounds. Its full-parent preimage and local reduction
laws are instantiated by the
[current runtime composition](../lfzk-v2/LfzkV2/Current/IdealProofRate7.lean),
which derives its failure event from actual adaptive verifier acceptance.
Rust source correspondence and the ideal-sampler oracle model remain explicit;
the full application composition is not proved by this component alone. Charge the shared
chain exception once when combining the component bad events. No new end-to-end
security-bit certificate follows merely from these component theorems.

The commitment fixes the candidate list independently of the later Polygero
statement. Early selection from that list is an analysis object. The actual
Polygero extractor still reconstructs its statement by replaying sumcheck
verification before it can identify good columns. This development establishes
no executable-extractor runtime bound.

`lake build WitnessSelection.APITest` checks this module, characteristic-two
and prime-field examples, empty vectors, and the foundational axioms of its bounds.
The sumcheck and Polygero adapters are checked in their respective API tests.
The retained v1 proof sources are unchanged.
