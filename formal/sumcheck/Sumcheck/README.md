# Sumcheck

The sumcheck verifier's round step, its soundness and completeness, and the challenge-tape counting
that Fiat–Shamir arguments reuse. This page lists only the theorems that other libraries call
(`Lfzk`, `Bcs`). Everything is in namespace `Sumcheck`.

## Round polynomials — `Interp.lean`

- **`RoundPoly F d`, `Interp F d`.** A round polynomial is sent as `d + 1` evaluations at fixed
  nodes. Nodes `0` and `1` are pinned, because the verifier's sum check reads them. Longfellow's
  `WPoly = Poly<3, Field>` is `RoundPoly F 2` (`Lfzk.WPoly`).
- **`RoundPoly.eval_lagrange_eq_of_agree`.** Suppose the transmitted evaluations agree with a
  polynomial `P` of degree `≤ d` at the nodes. Then the verifier's Lagrange evaluation equals `P`
  at every challenge. `Lfzk.WPoly` uses it for honest rounds.

## One round — `Round.lean`

- **`check_round_c claim p r`.** The verifier's round step (`verifier_layers.h` `layer_c`). It
  checks `p(0) + p(1) = claim` and returns the next claim `p(r)`.
- **`sumcheck_step_reduction`.** Let `P` be the true round polynomial and suppose the incoming
  claim is false (`≠ P(0) + P(1)`). If the round check passes, then either:
  - the outgoing claim is still false (`≠ P(r)`); or
  - `BadRoundEvent P p r` holds: `p` differs from `P` at `0` or `1`, yet agrees with `P` at `r`.

  This is the round transition of every LayerStep round-by-round chain: `Lfzk.RbrChain`,
  `Lfzk.RbrLongfellow`, and, for the deployed zero-knowledge verifier,
  `Lfzk.RbrZkLongfellow.zkRound_budget`. There the de-padded round passes `check_round_c` by
  construction.

## The per-round count — `FiatShamir.lean`

- **`bad_round_roots`.** Let the true polynomial have degree `≤ deg`, and the transmitted one
  degree `d ≤ deg`. Then at most `deg` challenges `r` satisfy `BadRoundEvent`, since they are roots
  of a nonzero difference. At `deg = 2` this is the `2/|F|` per sumcheck round charged in every
  Longfellow bound (`Lfzk.RbrBudgets.sumcheckRound`).

## Many rounds — `Multi.lean`

- **`verify_multi_round`** iterates `check_round_c` over a list of rounds.
- **`sumcheck_multi_reduction`.** Suppose the verifier accepts a run that starts from a false
  claim. Then either the final claim differs from the last true polynomial at its challenge, or
  some round has a `BadRoundEvent`. `Lfzk.Layers` uses it for the clear-verifier layer soundness.
- **`sumcheck_multi_completeness`.** An honest run from the true claim is accepted. It ends at the
  last true polynomial evaluated at its challenge. There is no degree or field-size condition. The
  zero-knowledge simulator (`Lfzk.ZkSim`) uses it.

## Grinding on a challenge tape — `Grinding.lean`

This part is protocol-free counting.

- **`Prefix C i`, `extract_prefix`.** The first `i` slots of a tape. A bad event at slot `i` is a
  predicate on `(prefix, slot value)`, so by its type it cannot read later slots.
- **`slot_bad_card_le`, `tape_bad_card_le`.** Suppose that from every prefix, at most `β i` values
  of slot `i` are bad. Then at most `(∑ i, β i) · |C|^(n−1)` of the `|C|^n` tapes are bad at some
  slot.

This is the counting step of round-by-round Fiat–Shamir: `Bcs.RbrCore.rbr_card_le`
(`RoundByRound.lean`). The fiber decomposition behind it (`card_filter_prefix_r`, `card_fiber_eq`)
is reused by `Bcs.RecomputedRbr`.

`Counting.lean` holds small cardinality lemmas (`card_prod_filter`, `pairs_card_le`,
`event_card_le_split`, …) that `Lfzk.Types`, `Lfzk.Mac` and `Lfzk.ZkHiding` use as plumbing.
