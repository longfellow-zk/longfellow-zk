# Chained V2 transcript

This library proves adaptive oracle-query accounting for a typed transcript
with link feedback and a checked final seal. It uses the existing
`Bcs.TotalOracle` finite random-oracle model: the adversary may query arbitrary
points in any order, repeat queries, and explore branches. `Q` bounds the
number of distinct queried points. A deterministic query tree represents each
fixed choice of the prover's private randomness.

Each oracle answer is a pair `(link, challenges)`. These are parts of **one**
answer, rather than an oracle answer followed by a separately seeded generator.
The challenge component can contain the whole block used by a round, including
both fingerprint vectors and the other field's coordinates.

## Representation and replay

`Chain` describes deterministic verifier replay, including reconstruction of
statements from earlier challenges. Its input representation must satisfy:

- Every successor input uniquely identifies its full parent input and the
  link claimed for that parent. This is a property of canonical framed
  preimages, not an ability to invert a hash digest.
- Successor inputs carry the actual parent answer's link.
- The rank increases at each boundary, including the separately domain-separated
  final input. Thus a proof with `R` boundary rounds has `R+1` distinct inputs.
- The final seal is the link coordinate of that final answer. The complete-proof
  representation must bind the actual canonical body, including authentication
  data, to this input.

The last body-binding requirement is part of the encoding correspondence, not
an additional conclusion of the abstract `Chain` laws. `APITest` supplies a
finite one-round instance whose final input distinguishes two different bodies.
The laws also cover zero-round proofs.

[`Recompute`](TranscriptV2/Recompute.lean) expresses verifier replay as an
oracle program and proves that it preserves the prover's output while recovering
the exact final state. It is used by the Merkle explanation adapter. Its queries
are not added to the adversary's Fiat--Shamir charging budget.

## Checked bounds

`link_guess_ratio_le` bounds out-of-order or unqueried parent links by
`Q/|Link|`. Stop the search immediately before its first query to a parent.
That stopped prefix is independent of the parent's answer. Each distinct
earlier child supplies at most one candidate link. Across all parents, a child
is counted at most once because it identifies one full parent input. Hence
the total number of guesses is at most `Q`, without a depth or birthday factor.

`final_seal_guess_ratio_le` adds at most `1/|Link|`: if the final input was not queried,
the prover's output and the verifier's reconstruction of that input are
independent of its answer. A passing seal then guesses one link.

Outside these events, `Chain.parent_queried_before` proves that each child was
queried after its parent. `Chain.required_fresh_queries` proves that a valid
seal requires at least `R+1` fresh queries. `short_search_ratio_le` bounds a
valid seal from a search below this budget by

```
epsilon_chain = (Q+1)/|Link|.
```

`Reduction` is a proof-only certificate that a failure implies a local bad
boundary and a valid final seal. It contains no query-order or query-charging assumption.
`Reduction.failure_ratio_le` derives

```
Pr[failure] <= Q*num/den + (Q+1)/|Link|,
```

when each point's bad-answer count times `den` is at most `num*|Answer|`, with
`den > 0`, and its local predicate is independent of its own answer. Integer
rounding is handled once in the shared counting lemma; adapters need no pivot
or divisibility argument. The sumcheck and witness-selection adapters
derive this independence from ancestor-dependent data using `PrefixPoints`.
`SumcheckV2.Chained.ofRoundReplay` constructs the local reduction from ordinary
sumcheck's claim/true-sum identities and evaluation updates. A false initial
claim reaching a true terminal claim must be repaired at some boundary:

- [`SumcheckV2.Chained.failure_bound`](../sumcheck-v2/SumcheckV2/ChainedFiatShamir.lean):
  `2Q/q + (Q+1)/|Link|` for ordinary quadratic sumcheck with uniform field challenges.
- [`WitnessSelection.Chained.failure_bound`](../witness-selection/WitnessSelection/ChainedFiatShamir.lean):
  `Q*choose(L,2)/q² + (Q+1)/|Link|` for a list of at most `L` projected candidates.

With a 32-byte link, `|Link|=2^256`. For multiple frontend components, use their
combined local bad event in the generic theorem so the common chain exception
is charged once. Repeated queries provide no new answer; branch exploration
uses additional distinct points. Adding chained queries changes the required
query count, not the polynomial's local bad-root bound.

[`SharedCharging`](TranscriptV2/SharedCharging.lean) combines single-answer
charges with grouped parent-first two-answer charges while retaining their
actual queried roles. Its per-point budget includes the grouped cost at each
parent, so the final bound uses the largest combined role cost and one distinct
query budget. The theorem still requires the protocol's local response counts
and the reduction of accepted failures to those charges. In particular, a
joint opening must count complete response tuples, not a single-field projection.

[`SharedReduction`](TranscriptV2/SharedReduction.lean) connects those charges
to a sealed accepted path. Its algebraic certificate supplies either a local
bad boundary or an adjacent parent/child event. Feedback proves that the parent
was queried first, outside the existing chain exception. With combined local
cost at most `epsilon` at every query role, the resulting bound is
`Q*epsilon + (Q+1)/|Link|`. The certificate does not assume an ordered query
trace. The `feedback_sum` lemma also accounts for child inputs carrying a
claimed parent link: only the matching link contributes, so the protocol's
summed response budget is preserved.

## Scope

These are conditional ROM component theorems. The
[current mdoc composition](../lfzk-v2/LfzkV2/Current/IdealProofRate7.lean)
instantiates the preimage laws, algebraic cover and shared query charges for
actual adaptive runtime acceptance event, including nonzero-sampling and
Polygero errors. Canonical input bytes and the first-context extractor are
connected by checked parsers and replay equalities. The oracle supplies a
uniform link and the correctly distributed joint challenge block, with
independent auxiliary randomness and consistent repeated answers. Rust's
SHAKE and rejection sampling are audited against this ideal-sampler model;
the full byte-stream coupling is separate. This component library alone does
not establish an application's end-to-end bound.

The counting proof does not construct a timed extractor. Polygero's
statement-dependent extraction needs verifier replay of sumcheck to reconstruct
its statement. A commitment-only candidate list and early fingerprint selection
are distinct analysis objects; they do not let the backend decoder omit that
replay. Internal noncomputable definitions do not establish extractor complexity.

From `formal/`, run `lake build TranscriptV2.APITest`. The API tests cover
body binding, a guessed seal with no queries, an out-of-order guessed link,
an ordinary ordered execution, the required fresh-query count, and enforce the
foundational-axiom lists of the bounds. Protocol adapters have their own API tests.
