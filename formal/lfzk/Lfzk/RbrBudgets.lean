import Lfzk.Layers
import Lfzk.Rounds
import Bcs.RoundByRound

/-!
# Longfellow's per-round escape budgets

For each round of the schedule in `Lfzk.Rounds`, how many oracle answers escape doom.  This is the
`beta` of `Bcs.RbrCore`, and it is the one place the flat analysis and the round-by-round one share
all their content: every bound below is an existing lfzk or sumcheck count, pulled back along the
round's decoder.

## The pullback, and why it is the honest model

`Bcs.RbrCore` counts over one linearly ordered tape of oracle answers in a single type `C`, because
a per-slot count needs a linear order on the slots and a tuple of tapes has none.  Longfellow's
rounds draw from four different spaces, so each round **decodes** its answer:

| round | decodes into | budget over the challenge space | source |
|---|---|---|---|
| layer 0's pair | `F × F` | `2 * \|F\|` out of `\|F\|²` | `layer_claim_zero_card` |
| layer `ly`'s `alpha` | `F` | `1` | `layer_alpha_bad_card` |
| sumcheck round | `F` | `deg = 2` | `Sumcheck.bad_round_roots` |
| input binding | `F` | `1` | `input_binding_bad_card` |
| Ligero challenge | a Ligero challenge | the escaping set | `Ligero.V3.ligerov3_roundByRound` |
| Ligero query | an `r`-subset of `n` | the accepting queries | same |

and `Bcs.card_decode_le` multiplies by `k`, the decoder's fibre bound — `k = |C| / |Y|` for a
balanced decoder.  That is what the deployed system does (it hashes, then derives), so there is no
idealisation to name; and a decoder that is *not* balanced, such as an `r`-subset sampled by drawing
indices and deduplicating, shows up as a larger `k` instead of being assumed away.

The two Ligero rounds need no theorem here: `Ligero.V3.ligerov3_roundByRound` already delivers its
two obligations as a `Finset` and a density, so `Bcs.card_preimage_le_of_balanced` applied to that
`Finset` is the budget directly.  What is here is the four **field** rounds, which are the ones whose
counts live in `lfzk` and `sumcheck`.

## What this file does not do

It does not build the state function.  Each budget below is stated at an arbitrary claim — "from
*any* wrong claim, at most this many answers make it right" — which is exactly the round-local
content, and is what a state function will instantiate at the claim its prefix determines.
Assembling those into a `Bcs.Rbr` for a whole run is the next step.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.RbrBudgets

open Finset Sumcheck
open scoped Classical

variable {C F : Type} [Fintype C] [Field F] [Fintype F] [DecidableEq F]

/-! ## The sumcheck rounds

The classical root count.  `Sumcheck.bad_round_roots` says a prover whose round polynomial is fixed
before the challenge survives at most `deg` of the `|F|` challenges — those are the roots of a
degree-`deg` difference — and `deg = 2` on the ZK path, where `WPoly = Poly<3, Field>` fixes the
transmitted degree.
-/

/--
**A sumcheck round's budget.**  At most `2k` oracle answers let a fixed round polynomial through.

Stated at an arbitrary `(P_true, poly)` pair because that is what the round-local content is: the
state function will supply the pair its prefix determines, and this bound does not care which.
-/
theorem sumcheckRound {d : ℕ} [Interp F d] (decode : C → F) (k : ℕ)
    (hbal : ∀ y : F, (univ.filter fun c : C => decode c = y).card ≤ k)
    (P_true : Polynomial F) (poly : RoundPoly F d) (deg : ℕ)
    (hdeg : P_true.natDegree ≤ deg) (hd : d ≤ deg) :
    (univ.filter fun c : C => BadRoundEvent P_true poly (decode c)).card ≤ k * deg :=
  Bcs.card_decode_le decode k hbal _ deg (bad_round_roots P_true poly deg hdeg hd)

/-! ## The layer challenges

Two per layer, drawn back to back by `begin_layer` and therefore decoded from **one** answer:
`alpha`, which combines the two inherited claims, and `beta`, which replaces the coefficient of
every assert-zero gate.  The layer claim is affine in each, hence a bilinear form in the pair, which
is what makes `2/|F|` the right price rather than `2/|F|²`.
-/

variable {Witness : Type} [SumcheckInterp F] {nc nv logw logc : ℕ}

omit [SumcheckInterp F] in
/--
**Layer 0's pair budget.**  At most `2k|F|` of the `k|F|²` answers collapse a non-zero output
claim — a `2/|F|` fraction, from the bilinear zero count.

`hne` is the non-degeneracy the run supplies: for an unsatisfied circuit the honest claim is not
identically zero on `F × F`.  That is `ArithmetizedCircuit.arith`'s content, and it is README gap 3's
strongest item — noted here because this is where it is spent.
-/
theorem layerPair (LC : LayeredCircuit Witness nc nv logw logc F)
    (decode : C → F × F) (k : ℕ)
    (hbal : ∀ y : F × F, (univ.filter fun c : C => decode c = y).card ≤ k)
    (w : Witness) (betas : ℕ → F) (st : LayerState logw logc F)
    (hne : ¬ (layer_claim (nc := nc) (nv := nv) (LC.Quad 0 0) (LC.V 1 w betas) 0
                st.q st.g0 st.g1 = 0 ∧
              layer_claim (nc := nc) (nv := nv) (LC.Quad 0 0) (LC.V 1 w betas) 1
                st.q st.g0 st.g1 = 0 ∧
              layer_claim (nc := nc) (nv := nv) (LC.Quad 0 1) (LC.V 1 w betas) 0
                st.q st.g0 st.g1 = 0 ∧
              layer_claim (nc := nc) (nv := nv) (LC.Quad 0 1) (LC.V 1 w betas) 1
                st.q st.g0 st.g1 = 0)) :
    (univ.filter fun c : C =>
        LC.Degenerate w betas (decode c).2 (decode c).1 st).card
      ≤ k * (2 * Fintype.card F) :=
  Bcs.card_decode_le decode k hbal
    (fun p : F × F => LC.Degenerate w betas p.2 p.1 st) (2 * Fintype.card F)
    (layer_claim_zero_card LC w betas st hne)

omit [SumcheckInterp F] in
/--
**A layer's `alpha` budget.**  At most `k` answers let the combination of the two inherited claims
collapse a wrong one: one bad `alpha` per layer, so `1/|F|`.

This is the per-layer term the flat bound charges `nl` times.
-/
theorem layerAlpha (LC : LayeredCircuit Witness nc nv logw logc F)
    (decode : C → F) (k : ℕ)
    (hbal : ∀ y : F, (univ.filter fun c : C => decode c = y).card ≤ k)
    (ly : ℕ) (w : Witness) (betas : ℕ → F) (st : LayerState logw logc F) (c0 c1 : F) :
    (univ.filter fun c : C =>
        InputBindingBad (LC.V ly w betas st.g0 st.q) (LC.V ly w betas st.g1 st.q)
          c0 c1 (decode c)).card
      ≤ k * 1 :=
  Bcs.card_decode_le decode k hbal _ 1 (layer_alpha_bad_card LC ly w betas st c0 c1)

/-! ## The input binding

`elt_field`'s `alpha_in`, drawn after LayerStep closes.  It combines the two surviving
input-layer claims against the committed witness, and at most one value of it fails to separate two
different pairs — the same count as a layer's `alpha`, which is why `input_binding_bad_card` serves
both.
-/

omit [SumcheckInterp F] in
/-- **The input-binding budget.**  At most `k` answers, i.e. `1/|F|`. -/
theorem inputBind (decode : C → F) (k : ℕ)
    (hbal : ∀ y : F, (univ.filter fun c : C => decode c = y).card ≤ k)
    (WL WR eL eR : F) :
    (univ.filter fun c : C => InputBindingBad WL WR eL eR (decode c)).card ≤ k * 1 :=
  Bcs.card_decode_le decode k hbal _ 1 (input_binding_bad_card WL WR eL eR)

/-! ## The budget of a whole run

Summing the table: one layer-0 pair at `2·kpair·|F|`, `nl` layer `alpha`s at `kfld`, `nl · nrnd`
sumcheck rounds at `2·kfld`, and one input binding at `kfld`.

**The two `k`s are different, and that is not a wrinkle but the point.**  One tape carries all the
rounds, so `|C|` is the same for every round while the space decoded into is not: a layer pair lands
in `F × F` and a field round in `F`, so a balanced decoder has `kpair = |C| / |F|²` and
`kfld = |C| / |F|`.  Dividing the sum by `|C|`:

```
2·kpair·|F| / |C|                     =  2 / |F|
kfld · (1 + nl·(1 + 2·nrnd)) / |C|    =  (1 + nl·(1 + 2·nrnd)) / |F|
```

so the field rounds cost `(3 + nl·(1 + 2·nrnd)) / |F|` — which is, term for term, the flat bound's
`3/|F| + nl·(1 + nrnd·d)/|F|` at `d = 2`.  **The round-by-round route loses nothing on the field
rounds.**  Every bit it does lose is in the two Ligero rounds, where a max replaces a
cover-weighted product; `../longfellow-nizk-plan.md` §6 has that arithmetic and the parameter row it
forces.
-/

/-- The field rounds' total budget.  `kpair` is the layer-pair decoder's fibre bound (over `F × F`)
and `kfld` every field decoder's (over `F`); they differ because one tape serves rounds that decode
into different spaces. -/
def fieldBudget (kpair kfld nl nrnd cardF : ℕ) : ℕ :=
  kpair * (2 * cardF) + nl * kfld + nl * nrnd * (2 * kfld) + kfld

/-- The budget, collected: one bilinear term and one linear term.  Divided by `|C|` at a balanced
decoder this is `2/|F| + (1 + nl·(1 + 2·nrnd))/|F|`, the flat bound's field terms exactly. -/
theorem fieldBudget_eq (kpair kfld nl nrnd cardF : ℕ) :
    fieldBudget kpair kfld nl nrnd cardF
      = 2 * kpair * cardF + kfld * (1 + nl * (1 + 2 * nrnd)) := by
  unfold fieldBudget
  ring

end Lfzk.RbrBudgets
