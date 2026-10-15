import Lfzk.RbrLayerStep

/-!
# The Longfellow LayerStep, instantiated

`Lfzk.RbrLayerStep` takes the five per-role transitions as data and the five escape budgets as
hypotheses.  This file supplies the two transitions that carry Longfellow's field rounds and proves
both of their budgets.

## `Wrong` does not need two shapes after all

The previous pass concluded that a uniform `Wrong` would have to branch on the layer, because the
sumcheck round compares *one claim to one value* while

```lean
ClaimsCorrect LC ly w betas st  :=  st.claim0 = V ly w betas st.g0 st.q ∧
                                    st.claim1 = V ly w betas st.g1 st.q
InputBindingBad WL WR eL eR a   :=  (WL ≠ eL ∨ WR ≠ eR) ∧ WL + a * WR = eL + a * eR
```

both compare **pairs**.  That was over-read.  The pair never has to *rest* in the state: a layer
boundary closes the old layer and combines the new pair at `alpha` in **one** step, so the pair
exists only inside that step.  Its pair-ness therefore belongs inside the *proof* — in
`Boundary.sound`'s conclusion and in `InputBindingBad`'s disjunct — not in the state, and `Wrong`
stays single-shaped:

```lean
Wrong H cand (some ws) := ws.claim ≠ H.sum cand ws.layer ws.st ws.alpha ws.bound
```

The consequence is better than the fix that was planned: the layer boundary and the input binding
turn out to be the **same transition** — close, then combine — with the **same budget**, `k * 1`.
`combineStep` serves both.  The input binding is just the last one, with `W` the committed witness's
evaluations instead of the next layer's.

`alpha` had to join the state, because the layer polynomial folds the two `g` points at it
(`Quad::bind_g`), so the honest claim depends on it.

## What is discharged and what is not

| input to `layerStep_ratio_le` | status |
|---|---|
| `budget_round` | **proved** (`roundStep_budget`): `k * 2`, from `Sumcheck.sumcheck_step_reduction` and `RbrBudgets.sumcheckRound` |
| `budget_pair` | **proved** (`combineStep_budget`): `k * 1`, from `RbrBudgets.inputBind` |
| `budget_in` | **proved**: the same `combineStep_budget`, at the committed witness |
| `budget_lig`, `budget_query` | hypothesis.  `Ligero.V3.ligerov3_roundByRound` supplies the `Finset`s and `Bcs.card_preimage_le_of_balanced` pulls them back; needs the Ligero state added to `LayerStepState` |
| `wrong_init` | hypothesis.  `zero_claims_wrong` is the lemma |
| `right_of_accepts` | hypothesis.  `mevent_fail_subset` read as a chain of implications, plus `final_binding` |

## The two facts a caller supplies about the boundary

`Boundary` carries the closing map as data and two facts about it, and each is a named piece of
`lfzk` rather than a new assumption:

* `rel` — the honest full sum at a layer is the `alpha`-combination of that layer's two honest
  claims.  This is `LayeredCircuit.layer_rel`;
* `sound` — a wrong surviving claim together with a passing layer-identity check leaves the *next*
  layer's claimed pair wrong.  This is the deterministic content of `verify_layer` /
  `Lfzk.final_binding`: the check pins `eqq * wc0 * wc1` against the surviving claim, and `eqq` is
  public, so a wrong claim forces a wrong pair.  It carries **no budget** — no challenge is drawn by
  it — which is why the whole boundary costs `k * 1` and not more.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.RbrLongfellow

open Finset Sumcheck
open scoped Classical

variable {C F X Cand : Type} [Fintype C] [Field F] [Fintype F] [DecidableEq F]
variable {Witness : Type} {nc nv logw logc : ℕ}

/-! ## The honest values, as data

`sum cand ly st a bnd` is the honest partial sum of layer `ly`'s polynomial — folded at `a`, bound
at `bnd` — for candidate `cand`; `poly` is the honest round polynomial there.  The three conditions
are `Sumcheck.consistent_true_polys` plus the degree bound, which `LayeredCircuit.consistent` and
`ArithmetizedCircuit.round_poly_natDegree_le_two` prove for Longfellow's layer polynomial.
-/

/-- The honest partial sums and round polynomials of a LayerStep. -/
structure Honest (F Cand : Type) [Field F] (logw logc : ℕ) where
  /-- The honest claim at a layer, state, `beta0`, fold coefficient and bound prefix.  `beta0` is an
  argument because layer 0's quad is bound at it, so layer 0's honest claim depends on it. -/
  sum : Cand → ℕ → LayerState logw logc F → F → F → List F → F
  /-- The honest round polynomial there. -/
  poly : Cand → ℕ → LayerState logw logc F → F → F → List F → Polynomial F
  /-- Its degree is the transmitted one: `WPoly = Poly<3, Field>`. -/
  deg_le : ∀ cand ly st b a bnd, (poly cand ly st b a bnd).natDegree ≤ 2
  /-- It sums over `{0,1}` to the honest incoming claim. -/
  sum_eq : ∀ cand ly st b a bnd,
    (poly cand ly st b a bnd).eval 0 + (poly cand ly st b a bnd).eval 1 = sum cand ly st b a bnd
  /-- Evaluating it at the round's challenge gives the honest outgoing claim. -/
  next_eq : ∀ cand ly st b a bnd r,
    (poly cand ly st b a bnd).eval r = sum cand ly st b a (bnd ++ [r])

/--
Doom, on all three states:

* `start` — the candidate does not satisfy the circuit.  This is what `wrong_init` says, and it is
  why the state has to distinguish "not started" from "failed";
* `running ws` — the current claim is not the honest one;
* `failed` — wrong for every candidate: the run is rejected, so it is never the accepting run.
-/
def Wrong [SumcheckInterp F] (H : Honest F Cand logw logc) (Sat : Cand → Prop)
    (LigDoomed : X → Prop) (cand : Cand) :
    RbrLayerStep.WState logw logc F X → Prop
  | .start => ¬ Sat cand
  | .running ws => ws.claim ≠ H.sum cand ws.layer ws.st ws.beta0 ws.alpha ws.bound
  | .challenged x => LigDoomed x
  | .accepted => False
  | .failed => True

/-! ## The sumcheck round

Changes `bound` and `claim` only, leaving `layer`, `alpha` and `st` alone — so the honest value it is
compared against is the *same function* before and after, which is exactly the situation
`Sumcheck.sumcheck_step_reduction` handles.
-/

/-- One sumcheck round: run the round check against the transmitted polynomial, record the
challenge. -/
def roundStep [SumcheckInterp F]
    (prover : ℕ → LayerState logw logc F → F → F → List F → RoundPoly F 2)
    (decode : C → F) (c : C) :
    RbrLayerStep.WState logw logc F X → RbrLayerStep.WState logw logc F X
  | .start => .failed
  | .challenged _ => .failed
  | .accepted => .failed
  | .failed => .failed
  | .running ws =>
      match check_round_c ws.claim
        (prover ws.layer ws.st ws.beta0 ws.alpha ws.bound) (decode c) with
      | none => .failed
      | some cl => .running { ws with bound := ws.bound ++ [decode c], claim := cl }

/--
**The sumcheck round's budget: `k * 2`.**

From a wrong claim, an answer escapes only by decoding to one of the at most two roots of the
difference between the transmitted round polynomial and the honest one.
-/
theorem roundStep_budget [SumcheckInterp F] (H : Honest F Cand logw logc) (Sat : Cand → Prop) (LigDoomed : X → Prop)
    (prover : ℕ → LayerState logw logc F → F → F → List F → RoundPoly F 2)
    (decode : C → F) (k : ℕ)
    (hbal : ∀ y : F, (univ.filter fun c : C => decode c = y).card ≤ k)
    (cand : Cand) (s : RbrLayerStep.WState logw logc F X) (hw : Wrong H Sat LigDoomed cand s) :
    (univ.filter fun c : C =>
        ¬ Wrong H Sat LigDoomed cand (roundStep prover decode c s)).card ≤ k * 2 := by
  classical
  cases s with
  | challenged _ =>
      refine le_trans (Finset.card_le_card (t := (∅ : Finset C)) ?_) (by simp)
      intro c hc
      simp only [mem_filter, mem_univ, true_and, roundStep, Wrong, not_true] at hc
  | accepted =>
      refine le_trans (Finset.card_le_card (t := (∅ : Finset C)) ?_) (by simp)
      intro c hc
      simp only [mem_filter, mem_univ, true_and, roundStep, Wrong, not_true] at hc
  | start =>
      refine le_trans (Finset.card_le_card (t := (∅ : Finset C)) ?_) (by simp)
      intro c hc
      simp only [mem_filter, mem_univ, true_and, roundStep, Wrong, not_true] at hc
  | failed =>
      refine le_trans (Finset.card_le_card (t := (∅ : Finset C)) ?_) (by simp)
      intro c hc
      simp only [mem_filter, mem_univ, true_and, roundStep, Wrong, not_true] at hc
  | running ws =>
      have hwrong : ws.claim ≠ H.sum cand ws.layer ws.st ws.beta0 ws.alpha ws.bound := hw
      have hfalse : ws.claim
          ≠ (H.poly cand ws.layer ws.st ws.beta0 ws.alpha ws.bound).eval 0
            + (H.poly cand ws.layer ws.st ws.beta0 ws.alpha ws.bound).eval 1 := by
        rw [H.sum_eq cand ws.layer ws.st ws.beta0 ws.alpha ws.bound]; exact hwrong
      refine le_trans (Finset.card_le_card (t := univ.filter fun c : C =>
        BadRoundEvent (H.poly cand ws.layer ws.st ws.beta0 ws.alpha ws.bound)
          (prover ws.layer ws.st ws.beta0 ws.alpha ws.bound) (decode c)) ?_) ?_
      · intro c hc
        simp only [mem_filter, mem_univ, true_and] at hc ⊢
        rcases hchk : check_round_c ws.claim
          (prover ws.layer ws.st ws.beta0 ws.alpha ws.bound) (decode c) with _ | cl
        · rw [roundStep, hchk] at hc
          exact absurd trivial hc
        · rw [roundStep, hchk] at hc
          have hesc : cl
              = H.sum cand ws.layer ws.st ws.beta0 ws.alpha (ws.bound ++ [decode c]) := by
            simpa [Wrong] using hc
          rcases sumcheck_step_reduction
            (H.poly cand ws.layer ws.st ws.beta0 ws.alpha ws.bound)
            (prover ws.layer ws.st ws.beta0 ws.alpha ws.bound) ws.claim cl (decode c) hchk hfalse
            with hstill | hbad
          · exact absurd
              (by rw [hesc, ← H.next_eq cand ws.layer ws.st ws.beta0 ws.alpha ws.bound (decode c)])
              hstill
          · exact hbad
      · exact RbrBudgets.sumcheckRound decode k hbal
          (H.poly cand ws.layer ws.st ws.beta0 ws.alpha ws.bound)
          (prover ws.layer ws.st ws.beta0 ws.alpha ws.bound) 2
          (H.deg_le cand ws.layer ws.st ws.beta0 ws.alpha ws.bound) (le_refl 2)

/-! ## The layer boundary, and the input binding

The same transition: **close** the layer just finished — the deterministic layer-identity check,
which draws no challenge and so carries no budget — then **combine** the next pair of claims at the
answer.  The layer boundary uses it with `W` the next layer's honest claims; the input binding uses
it with `W` the committed witness's evaluations.
-/

/-- The closing map and the two facts about it.  See the module docstring for which `lfzk` lemma
supplies each. -/
structure Boundary [SumcheckInterp F] (H : Honest F Cand logw logc) where
  /-- Close a layer: check its identity and form the next state, or reject. -/
  close : ℕ → LayerState logw logc F → F → F → List F → F → Option (LayerState logw logc F)
  /-- Which layer LayerStep moves to. -/
  next : ℕ → ℕ
  /-- The honest pair of claims at the layer moved to. -/
  W : Cand → ℕ → LayerState logw logc F → F → F × F
  /-- **The layer relation.**  `LayeredCircuit.layer_rel`. -/
  rel : ∀ cand ly st b a,
    H.sum cand ly st b a [] = (W cand ly st b).1 + a * (W cand ly st b).2
  /-- **Closing is sound.**  `verify_layer` / `Lfzk.final_binding`: a wrong surviving claim plus a
  passing identity check leaves the next layer's claimed pair wrong.  No challenge is drawn, so no
  budget is charged. -/
  sound : ∀ cand ly st b a bnd cl st', close ly st b a bnd cl = some st' →
    cl ≠ H.sum cand ly st b a bnd →
    ((W cand (next ly) st' b).1 ≠ st'.claim0 ∨ (W cand (next ly) st' b).2 ≠ st'.claim1)

/-- Close the current layer and combine the next pair of claims at the answer. -/
def combineStep [SumcheckInterp F] {H : Honest F Cand logw logc} (B : Boundary H)
    (decode : C → F) (c : C) :
    RbrLayerStep.WState logw logc F X → RbrLayerStep.WState logw logc F X
  | .start => .failed
  | .challenged _ => .failed
  | .accepted => .failed
  | .failed => .failed
  | .running ws =>
      match B.close ws.layer ws.st ws.beta0 ws.alpha ws.bound ws.claim with
      | none => .failed
      | some st' =>
          .running { layer := B.next ws.layer
                     beta0 := ws.beta0
                     st := st'
                     alpha := decode c
                     bound := []
                     claim := st'.claim0 + decode c * st'.claim1 }

/--
**The boundary's budget: `k * 1`.**

At most one `alpha` fails to separate the claimed pair from the honest one
(`RbrBudgets.inputBind`, which is `input_binding_bad_card`), so at most `k` answers decode to it.

This is the layer boundary *and* the input binding: they are the same step, so they have the same
budget.  `1/|F|` per boundary, which is the flat bound's per-layer `alpha` term and its `alpha_in`
term, both.
-/
theorem combineStep_budget [SumcheckInterp F] {H : Honest F Cand logw logc} (Sat : Cand → Prop) (LigDoomed : X → Prop)
    (B : Boundary H) (decode : C → F) (k : ℕ)
    (hbal : ∀ y : F, (univ.filter fun c : C => decode c = y).card ≤ k)
    (cand : Cand) (s : RbrLayerStep.WState logw logc F X) (hw : Wrong H Sat LigDoomed cand s) :
    (univ.filter fun c : C =>
        ¬ Wrong H Sat LigDoomed cand (combineStep B decode c s)).card ≤ k * 1 := by
  classical
  cases s with
  | challenged _ =>
      refine le_trans (Finset.card_le_card (t := (∅ : Finset C)) ?_) (by simp)
      intro c hc
      simp only [mem_filter, mem_univ, true_and, combineStep, Wrong, not_true] at hc
  | accepted =>
      refine le_trans (Finset.card_le_card (t := (∅ : Finset C)) ?_) (by simp)
      intro c hc
      simp only [mem_filter, mem_univ, true_and, combineStep, Wrong, not_true] at hc
  | start =>
      refine le_trans (Finset.card_le_card (t := (∅ : Finset C)) ?_) (by simp)
      intro c hc
      simp only [mem_filter, mem_univ, true_and, combineStep, Wrong, not_true] at hc
  | failed =>
      refine le_trans (Finset.card_le_card (t := (∅ : Finset C)) ?_) (by simp)
      intro c hc
      simp only [mem_filter, mem_univ, true_and, combineStep, Wrong, not_true] at hc
  | running ws =>
      have hwrong : ws.claim ≠ H.sum cand ws.layer ws.st ws.beta0 ws.alpha ws.bound := hw
      -- the closing step does not read the answer, so `st'` is fixed across the count
      rcases hclose : B.close ws.layer ws.st ws.beta0 ws.alpha ws.bound ws.claim with _ | st'
      · refine le_trans (Finset.card_le_card (t := (∅ : Finset C)) ?_) (by simp)
        intro c hc
        simp only [mem_filter, mem_univ, true_and] at hc
        rw [combineStep, hclose] at hc
        exact absurd trivial hc
      · have hpair := B.sound cand ws.layer ws.st ws.beta0 ws.alpha ws.bound ws.claim st'
          hclose hwrong
        refine le_trans (Finset.card_le_card (t := univ.filter fun c : C =>
          InputBindingBad (B.W cand (B.next ws.layer) st' ws.beta0).1
            (B.W cand (B.next ws.layer) st' ws.beta0).2
            st'.claim0 st'.claim1 (decode c)) ?_) ?_
        · intro c hc
          simp only [mem_filter, mem_univ, true_and] at hc ⊢
          rw [combineStep, hclose] at hc
          have hesc : st'.claim0 + decode c * st'.claim1
              = H.sum cand (B.next ws.layer) st' ws.beta0 (decode c) [] := by
            simpa [Wrong] using hc
          rw [B.rel cand (B.next ws.layer) st' ws.beta0 (decode c)] at hesc
          exact ⟨hpair, hesc.symm⟩
        · exact RbrBudgets.inputBind decode k hbal _ _ _ _

/-! ## Layer 0, and `wrong_init`

The one round that is not a boundary.  Nothing precedes it, so there is no layer to close; what it
draws is the **pair** `(beta0, alpha0)`, and the escape is that the pair collapses a non-zero output
claim rather than that a single `alpha` fails to separate.  So its budget is `RbrBudgets.layerPair`'s
`k * 2|F|`, not `k * 1` — the non-constant pair budget the plan's §5d flagged.

`wrong_init` falls out for free here, and that is the point of `WState.start`: doom at `start` *is*
"the candidate does not satisfy the circuit", so `Fails` — no candidate satisfies — gives it
immediately.  The content that used to look like it belonged in `wrong_init` is really in
`initStep_budget`'s `harith`.
-/

/-- Layer 0's pair slot: start LayerStep at `st0`, with `beta0` and `alpha0` decoded from the one
answer `begin_layer` draws. -/
def initStep [SumcheckInterp F] (st0 : LayerState logw logc F) (decode : C → F × F) (c : C) :
    RbrLayerStep.WState logw logc F X → RbrLayerStep.WState logw logc F X
  | .challenged _ => .failed
  | .accepted => .failed
  | .start =>
      .running { layer := 0
                 beta0 := (decode c).1
                 st := st0
                 alpha := (decode c).2
                 bound := []
                 claim := st0.claim0 + (decode c).2 * st0.claim1 }
  | .running _ => .failed
  | .failed => .failed

/--
**Layer 0's budget: `k * 2|F|`.**

From a candidate that does not satisfy the circuit, at most `2|F|` of the `|F|²` pairs
`(beta0, alpha0)` collapse the output claim — the bilinear zero count `layer_claim_zero_card` — so
at most `k * 2|F|` answers decode into them.

Three hypotheses, and each is an existing piece of `lfzk`:

* `hzero0`, `hzero1` — the run starts from claims of zero, which is how both verifiers initialise
  (`claim: [Expression::zero, Expression::zero]`, `verifier_layers.h:L70`);
* `hclaim` — `H.sum` at layer 0 *is* the layer claim, so an escape is exactly
  `LayeredCircuit.Degenerate`.  Note the `betas` argument is `tail`: by `V_local`, layer 0's
  `V 1 w betas` does not see `betas 0`, which is what makes the count a count over the *pair*;
* `harith` — an unsatisfied circuit has a non-vanishing honest claim somewhere on `F × F`.  This is
  `ArithmetizedCircuit.arith`, README gap 3's strongest item, and this is where it is spent.
-/
theorem initStep_budget [SumcheckInterp F] (H : Honest F Cand logw logc) (Sat : Cand → Prop) (LigDoomed : X → Prop)
    (LC : LayeredCircuit Witness nc nv logw logc F) (wOf : Cand → Witness) (tail : ℕ → F)
    (st0 : LayerState logw logc F) (decode : C → F × F) (k : ℕ)
    (hbal : ∀ y : F × F, (univ.filter fun c : C => decode c = y).card ≤ k)
    (hzero0 : st0.claim0 = 0) (hzero1 : st0.claim1 = 0)
    (hclaim : ∀ (cand : Cand) (b a : F),
      H.sum cand 0 st0 b a [] = layer_claim (nc := nc) (nv := nv) (LC.Quad 0 b)
        (LC.V 1 (wOf cand) tail) a st0.q st0.g0 st0.g1)
    (cand : Cand)
    (harith : ¬ Sat cand →
      ¬ (layer_claim (nc := nc) (nv := nv) (LC.Quad 0 0) (LC.V 1 (wOf cand) tail) 0
            st0.q st0.g0 st0.g1 = 0 ∧
         layer_claim (nc := nc) (nv := nv) (LC.Quad 0 0) (LC.V 1 (wOf cand) tail) 1
            st0.q st0.g0 st0.g1 = 0 ∧
         layer_claim (nc := nc) (nv := nv) (LC.Quad 0 1) (LC.V 1 (wOf cand) tail) 0
            st0.q st0.g0 st0.g1 = 0 ∧
         layer_claim (nc := nc) (nv := nv) (LC.Quad 0 1) (LC.V 1 (wOf cand) tail) 1
            st0.q st0.g0 st0.g1 = 0))
    (s : RbrLayerStep.WState logw logc F X) (hw : Wrong H Sat LigDoomed cand s) :
    (univ.filter fun c : C =>
        ¬ Wrong H Sat LigDoomed cand (initStep st0 decode c s)).card ≤ k * (2 * Fintype.card F) := by
  classical
  cases s with
  | challenged _ =>
      refine le_trans (Finset.card_le_card (t := (∅ : Finset C)) ?_) (by simp)
      intro c hc
      simp only [mem_filter, mem_univ, true_and, initStep, Wrong, not_true] at hc
  | accepted =>
      refine le_trans (Finset.card_le_card (t := (∅ : Finset C)) ?_) (by simp)
      intro c hc
      simp only [mem_filter, mem_univ, true_and, initStep, Wrong, not_true] at hc
  | running _ =>
      refine le_trans (Finset.card_le_card (t := (∅ : Finset C)) ?_) (by simp)
      intro c hc
      simp only [mem_filter, mem_univ, true_and, initStep, Wrong, not_true] at hc
  | failed =>
      refine le_trans (Finset.card_le_card (t := (∅ : Finset C)) ?_) (by simp)
      intro c hc
      simp only [mem_filter, mem_univ, true_and, initStep, Wrong, not_true] at hc
  | start =>
      have hnsat : ¬ Sat cand := hw
      refine le_trans (Finset.card_le_card (t := univ.filter fun c : C =>
        LC.Degenerate (wOf cand) tail (decode c).2 (decode c).1 st0) ?_) ?_
      · intro c hc
        simp only [mem_filter, mem_univ, true_and] at hc ⊢
        -- escaping means the combined claim, which is zero, is the honest one
        have hesc : st0.claim0 + (decode c).2 * st0.claim1
            = H.sum cand 0 st0 (decode c).1 (decode c).2 [] := by
          simpa [initStep, Wrong] using hc
        rw [hclaim cand (decode c).1 (decode c).2, hzero0, hzero1] at hesc
        show layer_claim (nc := nc) (nv := nv) (LC.Quad 0 (decode c).1)
          (LC.V 1 (wOf cand) tail) (decode c).2 st0.q st0.g0 st0.g1 = 0
        rw [← hesc]
        ring
      · exact RbrBudgets.layerPair LC decode k hbal (wOf cand) tail st0 (harith hnsat)

/-! ## The Ligero rounds

The last two slots, and the only ones whose escape set arrives as a **`Finset`** rather than as a
root count.  `Ligero.V3.ligerov3_roundByRound` (Phase 1) hands over exactly that:

* the challenges that escape doom are contained in `classifier.escaping θ`
  (`not_doomedAfter_mem_escaping`);
* from a doomed challenge, the accepting queries are contained in
  `classifier.acceptingQueries challenge`, whose density is at most `coverRatio n e g r θ`
  (`query_density_le_of_doomedAfter`).

So both budgets are one application of `Bcs.card_preimage_le_of_balanced`, and the *sizes* of those
two `Finset`s are what Phase 1's two density bounds control.  Nothing about Ligero is re-derived
here; the file does not even import it, because the escape sets enter as `Finset`s and the doom
predicate as `LigDoomed`.

**This is where the round-by-round route pays for itself and where it pays its price.**  Every field
round above costs a root count; these two cost the max of a failure mass and a cover ratio, where
the flat bound takes their cover-weighted product.  `../longfellow-nizk-plan.md` §6 has the
arithmetic and the parameter row it forces.
-/

/-- The Ligero challenge round: draw the linear-combination challenge and record it. -/
def ligeroChallengeStep (decodeChal : C → X) (c : C) :
    RbrLayerStep.WState logw logc F X → RbrLayerStep.WState logw logc F X
  | .start => .failed
  | .running _ => .challenged (decodeChal c)
  | .challenged _ => .failed
  | .accepted => .failed
  | .failed => .failed

/-- The Ligero query round: accept iff the drawn query is one the opened columns pass. -/
def ligeroQueryStep {Q : Type} [DecidableEq Q] (decodeQuery : C → Q)
    (accepting : X → Finset Q) (c : C) :
    RbrLayerStep.WState logw logc F X → RbrLayerStep.WState logw logc F X
  | .start => .failed
  | .running _ => .failed
  | .challenged x => if decodeQuery c ∈ accepting x then .accepted else .failed
  | .accepted => .failed
  | .failed => .failed

omit [Fintype F] [DecidableEq F] in
/--
**The Ligero challenge round's budget: `k * |escaping θ|`.**

An answer escapes only by decoding to a challenge that is not doomed at `θ`, and Phase 1's
`not_doomedAfter_mem_escaping` puts every such challenge in `classifier.escaping θ`.  Phase 1's
`escaping_density_le` is what makes that `Finset` small.
-/
theorem ligeroChallengeStep_budget [SumcheckInterp F] [DecidableEq X]
    (H : Honest F Cand logw logc) (Sat : Cand → Prop) (LigDoomed : X → Prop)
    (decodeChal : C → X) (k : ℕ)
    (hbal : ∀ y : X, (univ.filter fun c : C => decodeChal c = y).card ≤ k)
    (escaping : Finset X)
    (hesc : ∀ x : X, ¬ LigDoomed x → x ∈ escaping)
    (cand : Cand) (s : RbrLayerStep.WState logw logc F X) :
    (univ.filter fun c : C =>
        ¬ Wrong H Sat LigDoomed cand (ligeroChallengeStep decodeChal c s)).card
      ≤ k * escaping.card := by
  classical
  cases s with
  | running ws =>
      refine le_trans (Finset.card_le_card (t := univ.filter fun c : C =>
        decodeChal c ∈ escaping) ?_) (Bcs.card_preimage_le_of_balanced decodeChal k hbal escaping)
      intro c hc
      simp only [mem_filter, mem_univ, true_and] at hc ⊢
      exact hesc _ (by simpa [ligeroChallengeStep, Wrong] using hc)
  | start =>
      refine le_trans (Finset.card_le_card (t := (∅ : Finset C)) ?_) (by simp)
      intro c hc
      simp only [mem_filter, mem_univ, true_and, ligeroChallengeStep, Wrong, not_true] at hc
  | challenged _ =>
      refine le_trans (Finset.card_le_card (t := (∅ : Finset C)) ?_) (by simp)
      intro c hc
      simp only [mem_filter, mem_univ, true_and, ligeroChallengeStep, Wrong, not_true] at hc
  | accepted =>
      refine le_trans (Finset.card_le_card (t := (∅ : Finset C)) ?_) (by simp)
      intro c hc
      simp only [mem_filter, mem_univ, true_and, ligeroChallengeStep, Wrong, not_true] at hc
  | failed =>
      refine le_trans (Finset.card_le_card (t := (∅ : Finset C)) ?_) (by simp)
      intro c hc
      simp only [mem_filter, mem_univ, true_and, ligeroChallengeStep, Wrong, not_true] at hc

omit [Fintype F] [DecidableEq F] in
/--
**The Ligero query round's budget: `k * max_x |accepting x|`.**

From a doomed challenge, an answer escapes only by decoding to an accepting query, and Phase 1's
`query_density_le_of_doomedAfter` bounds that `Finset` by a `coverRatio n e g r θ` fraction of the
`n.choose r` query sets.

`bq` is a uniform bound over the challenge, because `Bcs.RbrCore`'s budget is per *slot* and the
challenge is not fixed at the slot — it is whatever the previous answer decoded to.  The cover ratio
is uniform in the challenge, so this loses nothing.
-/
theorem ligeroQueryStep_budget [SumcheckInterp F] {Q : Type} [Fintype Q] [DecidableEq Q]
    (H : Honest F Cand logw logc) (Sat : Cand → Prop) (LigDoomed : X → Prop)
    (decodeQuery : C → Q) (k : ℕ)
    (hbal : ∀ y : Q, (univ.filter fun c : C => decodeQuery c = y).card ≤ k)
    (accepting : X → Finset Q) (bq : ℕ) (hbq : ∀ x : X, (accepting x).card ≤ bq)
    (cand : Cand) (s : RbrLayerStep.WState logw logc F X) :
    (univ.filter fun c : C =>
        ¬ Wrong H Sat LigDoomed cand (ligeroQueryStep decodeQuery accepting c s)).card
      ≤ k * bq := by
  classical
  cases s with
  | challenged x =>
      refine le_trans (Finset.card_le_card (t := univ.filter fun c : C =>
        decodeQuery c ∈ accepting x) ?_) ?_
      · intro c hc
        simp only [mem_filter, mem_univ, true_and] at hc ⊢
        by_contra hnot
        simp only [ligeroQueryStep, if_neg hnot, Wrong, not_true] at hc
      · exact le_trans (Bcs.card_preimage_le_of_balanced decodeQuery k hbal (accepting x))
          (Nat.mul_le_mul_left k (hbq x))
  | start =>
      refine le_trans (Finset.card_le_card (t := (∅ : Finset C)) ?_) (by simp)
      intro c hc
      simp only [mem_filter, mem_univ, true_and, ligeroQueryStep, Wrong, not_true] at hc
  | running _ =>
      refine le_trans (Finset.card_le_card (t := (∅ : Finset C)) ?_) (by simp)
      intro c hc
      simp only [mem_filter, mem_univ, true_and, ligeroQueryStep, Wrong, not_true] at hc
  | accepted =>
      refine le_trans (Finset.card_le_card (t := (∅ : Finset C)) ?_) (by simp)
      intro c hc
      simp only [mem_filter, mem_univ, true_and, ligeroQueryStep, Wrong, not_true] at hc
  | failed =>
      refine le_trans (Finset.card_le_card (t := (∅ : Finset C)) ?_) (by simp)
      intro c hc
      simp only [mem_filter, mem_univ, true_and, ligeroQueryStep, Wrong, not_true] at hc

omit [Fintype F] [DecidableEq F] in
/-- **`wrong_init`, discharged.**  If no candidate satisfies the circuit then the initial state is
doomed for every candidate — immediately, because that is what doom at `start` says. -/
theorem wrong_init [SumcheckInterp F] (H : Honest F Cand logw logc) (Sat : Cand → Prop) (LigDoomed : X → Prop)
    (hfail : ∀ cand : Cand, ¬ Sat cand) (cand : Cand) :
    Wrong H Sat LigDoomed cand .start := hfail cand

/-! ## Assembling LayerStep

The five step functions, dispatched into a `RbrLayerStep.Steps`, and the acceptance predicate they define.

**Every field is given the prefix.**  `RbrLayerStep.Steps` hands each transition `(m, pref)`, and the
prover's data — its round polynomials, the `wc0`/`wc1` a layer closes with, the columns the Ligero
query opens — is read from there.  That matters for soundness, not tidiness: a transition that
ignored the prefix would be modelling a prover that cannot see its own transcript, which is a
restriction on the adversary rather than an abstraction of it.  The budget theorems above are stated
for a *fixed* polynomial, closing map and accepting set, which is exactly right — at one slot the
prefix is fixed, so nothing in them changes.

`layerPair 0` is the one role whose transition differs from its class-mates: it is `initStep`, not
`combineStep`, because nothing precedes it.  `RbrLayerStep.layerStep_ratio_le` charges one budget per class, so
the assembled bound takes the larger of the two — `k * 2|F|` — which costs about one bit on that one
term.  Splitting the sum at `ly = 0` recovers it and is noted in the plan's §5d.
-/

section Assemble

variable [SumcheckInterp F] [DecidableEq X] {Q : Type} [Fintype Q] [DecidableEq Q]
variable {nl : ℕ} {w : ℕ → ℕ}

/-- The Longfellow LayerStep's transitions, dispatched by role. -/
noncomputable def lfSteps {H : Honest F Cand logw logc}
    (st0 : LayerState logw logc F)
    (B : ∀ m : ℕ, (Fin m → C) → Boundary H)
    (prover : ∀ m : ℕ, (Fin m → C) →
      ℕ → LayerState logw logc F → F → F → List F → RoundPoly F 2)
    (decodePair : C → F × F) (decodeF : C → F) (decodeChal : C → X) (decodeQuery : C → Q)
    (accepting : ∀ m : ℕ, (Fin m → C) → X → Finset Q) :
    RbrLayerStep.Steps C F X logw logc nl w where
  pair ly m pref c s :=
    if ly.val = 0 then initStep st0 decodePair c s else combineStep (B m pref) decodeF c s
  round _ _ m pref c s := roundStep (prover m pref) decodeF c s
  inputBind m pref c s := combineStep (B m pref) decodeF c s
  ligeroChallenge _ _ c s := ligeroChallengeStep decodeChal c s
  ligeroQuery m pref c s := ligeroQueryStep decodeQuery (accepting m pref) c s

/-- The state LayerStep ends in. -/
noncomputable def layerStepFinal {H : Honest F Cand logw logc} (Sat : Cand → Prop)
    (LigDoomed : X → Prop) (steps : RbrLayerStep.Steps C F X logw logc nl w)
    (tape : Fin (Rounds.Role.length nl w) → C) : RbrLayerStep.WState logw logc F X :=
  (RbrLayerStep.layerStepChain steps (Wrong H Sat LigDoomed) .start).state
    (Rounds.Role.length nl w)
    (Bcs.trunc tape (Rounds.Role.length nl w) le_rfl)

/--
**Acceptance: LayerStep reaches `accepted`.**

This is a *definition*, and it is the right one to make.  `lfzk`'s existing statements take
`accepts : Ω → Prop` abstract and then carry two hypotheses about it —
`IsWellFormedTranscript.round_count`, that an accepted run has `logc + 2·logw` rounds, and
`LigeroRun.accepts_sub`, that an accepted run is one whose Ligero verifier accepted.  Here the round
count *is* the schedule (`Lfzk.Rounds`, Phase 4) and the Ligero acceptance *is* the query-membership
test in `ligeroQueryStep`, so neither has to be assumed.

What remains a modelling fact rather than a theorem is that each transition transliterates its
verifier step — `check_round_c` the round check, `Boundary.close` the layer identity, `accepting` the
opened-column test.  That is README gap 1, unchanged and not enlarged: the same debt, now attached to
five named functions instead of to one opaque predicate.
-/
noncomputable def Accepts {H : Honest F Cand logw logc} (Sat : Cand → Prop)
    (LigDoomed : X → Prop) (steps : RbrLayerStep.Steps C F X logw logc nl w)
    (tape : Fin (Rounds.Role.length nl w) → C) : Prop :=
  layerStepFinal (H := H) Sat LigDoomed steps tape = .accepted

/-- The obligation `Bcs.ClaimChain.toRbr` calls `right_of_accepts`, named once so that the assembled
theorem's hypothesis list stays readable. -/
def RightOfAccepts {H : Honest F Cand logw logc} (Sat : Cand → Prop) (LigDoomed : X → Prop)
    (steps : RbrLayerStep.Steps C F X logw logc nl w)
    (Acc : (Fin (Rounds.Role.length nl w) → C) → Prop) : Prop :=
  ∀ tape : Fin (Rounds.Role.length nl w) → C, Acc tape →
    ∃ cand : Cand, ¬ (RbrLayerStep.layerStepChain steps (Wrong H Sat LigDoomed)
        (.start : RbrLayerStep.WState logw logc F X)).Wrong cand
      ((RbrLayerStep.layerStepChain steps (Wrong H Sat LigDoomed)
        (.start : RbrLayerStep.WState logw logc F X)).state (Rounds.Role.length nl w)
        (Bcs.trunc tape (Rounds.Role.length nl w) le_rfl))

omit [Fintype C] [Fintype F] [DecidableEq F] [DecidableEq X] in
/--
**`right_of_accepts`, discharged.**

An accepting run's final state is `accepted`, where doom is `False` — so *every* candidate is
undoomed there, and the existential needs only that the candidate list is non-empty.

That the obligation comes out this cheaply is what `WState.accepted` was for.  With an `Option`
state there would be no way to say "the run ended well" as opposed to "the run has not failed", and
this hypothesis would have had to carry the whole final check.
-/
theorem right_of_accepts {H : Honest F Cand logw logc} [Nonempty Cand] (Sat : Cand → Prop)
    (LigDoomed : X → Prop) (steps : RbrLayerStep.Steps C F X logw logc nl w) :
    RightOfAccepts (H := H) Sat LigDoomed steps (Accepts (H := H) Sat LigDoomed steps) := by
  intro tape hacc
  obtain ⟨cand⟩ := ‹Nonempty Cand›
  refine ⟨cand, ?_⟩
  show ¬ Wrong H Sat LigDoomed cand _
  rw [show (RbrLayerStep.layerStepChain steps (Wrong H Sat LigDoomed)
        (.start : RbrLayerStep.WState logw logc F X)).state (Rounds.Role.length nl w)
        (Bcs.trunc tape (Rounds.Role.length nl w) le_rfl)
      = RbrLayerStep.WState.accepted from hacc]
  exact not_false

/-! ## LayerStep's data, bundled

`layerStep_ratio_le` below takes twenty-five arguments, one per piece of the protocol, and that is the
right shape for reading it.  It is the wrong shape for *composing* it: `Lfzk.Nizk` needs one LayerStep
per commitment, so every one of the twenty-five becomes a family indexed by the commitment, and
threading them by hand is what left `Nizk.nizk_ratio_le`'s `R` and `hb` on the caller.

`LayerStepData` is the bundle.  The five class budgets are **parameters**, not fields, so a family
`Pre → LayerStepData … bpair bround bin blig bquery` has budgets that are uniform in the commitment *by
typing* — which is what a parameter row quotes.  Everything a commitment may choose is a field.
-/

/--
**Everything LayerStep needs at one commitment.**

The transitions' data (`LC`, `st0`, `B`, `prover`, the four decoders, `accepting`), the decoders'
fibre bounds, layer 0's three facts, the two Ligero `Finset`s, and one `≤` per class budget.
-/
structure LayerStepData (C F X Q Cand Witness : Type) [Fintype C] [Field F] [Fintype F]
    [DecidableEq F] [SumcheckInterp F] [DecidableEq X] [Fintype Q] [DecidableEq Q]
    (nc nv logw logc nl : ℕ) (w : ℕ → ℕ)
    (H : Honest F Cand logw logc) (Sat : Cand → Prop) (LigDoomed : X → Prop)
    (bpair bround bin blig bquery : ℕ) where
  /-- The circuit LayerStep is about. -/
  LC : LayeredCircuit Witness nc nv logw logc F
  /-- Each candidate's witness. -/
  wOf : Cand → Witness
  /-- The input layer's tail. -/
  tail : ℕ → F
  /-- Layer 0's incoming state. -/
  st0 : LayerState logw logc F
  /-- The layer boundary, as a function of the prefix. -/
  B : ∀ m : ℕ, (Fin m → C) → Boundary H
  /-- The prover's round polynomials, as a function of the prefix. -/
  prover : ∀ m : ℕ, (Fin m → C) →
    ℕ → LayerState logw logc F → F → F → List F → RoundPoly F 2
  /-- `begin_layer`'s coin decoder: the layer's two points. -/
  decodePair : C → F × F
  /-- The field-element decoder, used by every sumcheck round and every boundary. -/
  decodeF : C → F
  /-- Ligero's linear-combination decoder. -/
  decodeChal : C → X
  /-- Ligero's query decoder. -/
  decodeQuery : C → Q
  /-- The columns a Ligero query accepts, as a function of the prefix and the challenge. -/
  accepting : ∀ m : ℕ, (Fin m → C) → X → Finset Q
  /-- `decodePair`'s balance. -/
  kpair : ℕ
  /-- `decodeF`'s balance. -/
  k : ℕ
  /-- `decodeChal`'s balance. -/
  kchal : ℕ
  /-- `decodeQuery`'s balance. -/
  kq : ℕ
  hbalPair : ∀ y : F × F, (univ.filter fun c : C => decodePair c = y).card ≤ kpair
  hbalF : ∀ y : F, (univ.filter fun c : C => decodeF c = y).card ≤ k
  hbalChal : ∀ y : X, (univ.filter fun c : C => decodeChal c = y).card ≤ kchal
  hbalQuery : ∀ y : Q, (univ.filter fun c : C => decodeQuery c = y).card ≤ kq
  /-- The run starts from claims of zero (`verifier_layers.h:L70`). -/
  hzero0 : st0.claim0 = 0
  /-- The run starts from claims of zero. -/
  hzero1 : st0.claim1 = 0
  /-- `H.sum` at layer 0 is the layer claim, so an escape there is `Degenerate`. -/
  hclaim : ∀ (cand : Cand) (b a : F),
    H.sum cand 0 st0 b a [] = layer_claim (nc := nc) (nv := nv) (LC.Quad 0 b)
      (LC.V 1 (wOf cand) tail) a st0.q st0.g0 st0.g1
  /-- An unsatisfied circuit's honest claim does not vanish on all of `F × F`
  (`ArithmetizedCircuit.arith`). -/
  harith : ∀ cand : Cand, ¬ Sat cand →
    ¬ (layer_claim (nc := nc) (nv := nv) (LC.Quad 0 0) (LC.V 1 (wOf cand) tail) 0
          st0.q st0.g0 st0.g1 = 0 ∧
       layer_claim (nc := nc) (nv := nv) (LC.Quad 0 0) (LC.V 1 (wOf cand) tail) 1
          st0.q st0.g0 st0.g1 = 0 ∧
       layer_claim (nc := nc) (nv := nv) (LC.Quad 0 1) (LC.V 1 (wOf cand) tail) 0
          st0.q st0.g0 st0.g1 = 0 ∧
       layer_claim (nc := nc) (nv := nv) (LC.Quad 0 1) (LC.V 1 (wOf cand) tail) 1
          st0.q st0.g0 st0.g1 = 0)
  /-- The Ligero challenges that do not doom the run — `ligerov3_roundByRound`'s `escaping`. -/
  escaping : Finset X
  hesc : ∀ x : X, ¬ LigDoomed x → x ∈ escaping
  /-- A bound on the accepting-column count — `ligerov3_roundByRound`'s query budget. -/
  bq : ℕ
  hbq : ∀ (m : ℕ) (pref : Fin m → C) (x : X), (accepting m pref x).card ≤ bq
  /-- `layerPair 0` is `initStep`, which costs `kpair · 2|F|`. -/
  hbp0 : kpair * (2 * Fintype.card F) ≤ bpair
  /-- A later `layerPair` is `combineStep`, which costs `k`. -/
  hbp1 : k * 1 ≤ bpair
  hbround : k * 2 ≤ bround
  hbin : k * 1 ≤ bin
  hblig : kchal * escaping.card ≤ blig
  hbquery : kq * bq ≤ bquery

namespace LayerStepData

variable {H : Honest F Cand logw logc} {Sat : Cand → Prop} {LigDoomed : X → Prop}
variable {bpair bround bin blig bquery : ℕ}
variable (D : LayerStepData C F X Q Cand Witness nc nv logw logc nl w H Sat LigDoomed
  bpair bround bin blig bquery)

/-- The transitions this data defines. -/
noncomputable def steps : RbrLayerStep.Steps C F X logw logc nl w :=
  lfSteps (H := H) (nl := nl) (w := w) D.st0 D.B D.prover D.decodePair D.decodeF D.decodeChal
    D.decodeQuery D.accepting

theorem budget_pair : ∀ (ly : Fin nl) (m : ℕ) (pref : Fin m → C) (cand : Cand)
    (s : RbrLayerStep.WState logw logc F X), Wrong H Sat LigDoomed cand s →
    (univ.filter fun c : C =>
      ¬ Wrong H Sat LigDoomed cand (D.steps.pair ly m pref c s)).card ≤ bpair := by
  intro ly m pref cand s hw
  by_cases hly : ly.val = 0
  · simp only [steps, lfSteps, if_pos hly]
    exact le_trans (initStep_budget H Sat LigDoomed D.LC D.wOf D.tail D.st0 D.decodePair D.kpair
      D.hbalPair D.hzero0 D.hzero1 D.hclaim cand (D.harith cand) s hw) D.hbp0
  · simp only [steps, lfSteps, if_neg hly]
    exact le_trans (combineStep_budget Sat LigDoomed (D.B m pref) D.decodeF D.k D.hbalF cand s hw)
      D.hbp1

theorem budget_round : ∀ (ly : Fin nl) (j : Fin (w ly.val)) (m : ℕ) (pref : Fin m → C)
    (cand : Cand) (s : RbrLayerStep.WState logw logc F X), Wrong H Sat LigDoomed cand s →
    (univ.filter fun c : C =>
      ¬ Wrong H Sat LigDoomed cand (D.steps.round ly j m pref c s)).card ≤ bround := by
  intro ly j m pref cand s hw
  exact le_trans
    (roundStep_budget H Sat LigDoomed (D.prover m pref) D.decodeF D.k D.hbalF cand s hw) D.hbround

theorem budget_in : ∀ (m : ℕ) (pref : Fin m → C) (cand : Cand)
    (s : RbrLayerStep.WState logw logc F X), Wrong H Sat LigDoomed cand s →
    (univ.filter fun c : C =>
      ¬ Wrong H Sat LigDoomed cand (D.steps.inputBind m pref c s)).card ≤ bin := by
  intro m pref cand s hw
  exact le_trans
    (combineStep_budget Sat LigDoomed (D.B m pref) D.decodeF D.k D.hbalF cand s hw) D.hbin

theorem budget_lig : ∀ (m : ℕ) (pref : Fin m → C) (cand : Cand)
    (s : RbrLayerStep.WState logw logc F X), Wrong H Sat LigDoomed cand s →
    (univ.filter fun c : C =>
      ¬ Wrong H Sat LigDoomed cand (D.steps.ligeroChallenge m pref c s)).card ≤ blig := by
  intro m pref cand s _
  exact le_trans (ligeroChallengeStep_budget H Sat LigDoomed D.decodeChal D.kchal D.hbalChal
    D.escaping D.hesc cand s) D.hblig

theorem budget_query : ∀ (m : ℕ) (pref : Fin m → C) (cand : Cand)
    (s : RbrLayerStep.WState logw logc F X), Wrong H Sat LigDoomed cand s →
    (univ.filter fun c : C =>
      ¬ Wrong H Sat LigDoomed cand (D.steps.ligeroQuery m pref c s)).card ≤ bquery := by
  intro m pref cand s _
  exact le_trans (ligeroQueryStep_budget H Sat LigDoomed D.decodeQuery D.kq D.hbalQuery
    (D.accepting m pref) D.bq (D.hbq m pref) cand s) D.hbquery

end LayerStepData

set_option maxHeartbeats 1000000 in
/--
**The Longfellow LayerStep, round by round.**

```
Pr[ LayerStep accepts  ∧  no candidate satisfies the circuit ]
    ≤  |Cand| · (nl·bpair + (∑ ly, w ly)·bround + bin + blig + bquery) / |C|
```

Every budget is discharged: `bpair` by `initStep_budget` at layer 0 and `combineStep_budget` after,
`bround` by `roundStep_budget`, `bin` by `combineStep_budget`, and the two Ligero ones by
`ligeroChallengeStep_budget` / `ligeroQueryStep_budget`.  `wrong_init` and `right_of_accepts` are the
two one-line facts above.

What is left as hypotheses is exactly the protocol's own content, and each is a named piece of
`lfzk` or `ligero`:

* `hzero0`, `hzero1` — the run starts from claims of zero (`verifier_layers.h:L70`);
* `hclaim` — `H.sum` at layer 0 is the layer claim, so an escape there is `Degenerate`;
* `harith` — an unsatisfied circuit's honest claim does not vanish on all of `F × F`
  (`ArithmetizedCircuit.arith`, README gap 3's strongest item);
* `H`'s three fields and `Boundary`'s two — `consistent_true_polys`, `layer_rel`, `final_binding`;
* `hesc`, `hbq` — Phase 1's `ligerov3_roundByRound`, as two `Finset`s.

`bpair` takes the larger of layer 0's `kpair·2|F|` and a later boundary's `k`, because
`RbrLayerStep.layerStep_ratio_le` charges one budget per role class and `layerPair 0` shares its class with the
rest.  That costs about one bit on one term; splitting the sum at `ly = 0` recovers it.
-/
theorem layerStep_ratio_le [DecidableEq C] [Nonempty C] [Fintype Cand] [Nonempty Cand]
    {H : Honest F Cand logw logc} (Sat : Cand → Prop) (LigDoomed : X → Prop)
    -- the circuit and the candidate witnesses
    (LC : LayeredCircuit Witness nc nv logw logc F) (wOf : Cand → Witness) (tail : ℕ → F)
    -- the transitions' data
    (st0 : LayerState logw logc F)
    (B : ∀ m : ℕ, (Fin m → C) → Boundary H)
    (prover : ∀ m : ℕ, (Fin m → C) →
      ℕ → LayerState logw logc F → F → F → List F → RoundPoly F 2)
    (decodePair : C → F × F) (decodeF : C → F) (decodeChal : C → X) (decodeQuery : C → Q)
    (accepting : ∀ m : ℕ, (Fin m → C) → X → Finset Q)
    -- the decoders' fibre bounds
    (kpair k kchal kq : ℕ)
    (hbalPair : ∀ y : F × F, (univ.filter fun c : C => decodePair c = y).card ≤ kpair)
    (hbalF : ∀ y : F, (univ.filter fun c : C => decodeF c = y).card ≤ k)
    (hbalChal : ∀ y : X, (univ.filter fun c : C => decodeChal c = y).card ≤ kchal)
    (hbalQuery : ∀ y : Q, (univ.filter fun c : C => decodeQuery c = y).card ≤ kq)
    -- layer 0
    (hzero0 : st0.claim0 = 0) (hzero1 : st0.claim1 = 0)
    (hclaim : ∀ (cand : Cand) (b a : F),
      H.sum cand 0 st0 b a [] = layer_claim (nc := nc) (nv := nv) (LC.Quad 0 b)
        (LC.V 1 (wOf cand) tail) a st0.q st0.g0 st0.g1)
    (harith : ∀ cand : Cand, ¬ Sat cand →
      ¬ (layer_claim (nc := nc) (nv := nv) (LC.Quad 0 0) (LC.V 1 (wOf cand) tail) 0
            st0.q st0.g0 st0.g1 = 0 ∧
         layer_claim (nc := nc) (nv := nv) (LC.Quad 0 0) (LC.V 1 (wOf cand) tail) 1
            st0.q st0.g0 st0.g1 = 0 ∧
         layer_claim (nc := nc) (nv := nv) (LC.Quad 0 1) (LC.V 1 (wOf cand) tail) 0
            st0.q st0.g0 st0.g1 = 0 ∧
         layer_claim (nc := nc) (nv := nv) (LC.Quad 0 1) (LC.V 1 (wOf cand) tail) 1
            st0.q st0.g0 st0.g1 = 0))
    -- the Ligero rounds, from Phase 1
    (escaping : Finset X) (hesc : ∀ x : X, ¬ LigDoomed x → x ∈ escaping)
    (bq : ℕ) (hbq : ∀ (m : ℕ) (pref : Fin m → C) (x : X), (accepting m pref x).card ≤ bq)
    -- the budgets
    (bpair : ℕ) (hbp0 : kpair * (2 * Fintype.card F) ≤ bpair) (hbp1 : k * 1 ≤ bpair)
    -- acceptance and extraction failure, abstract: `right_of_accepts` discharges `hright` at
    -- `Accepts`, and Phase 6 supplies `Fails` from the Ligero extractor
    {Acc : (Fin (Rounds.Role.length nl w) → C) → Prop} {Fails : Prop}
    (hfail : Fails → ∀ cand : Cand, ¬ Sat cand)
    (hright : RightOfAccepts (H := H) Sat LigDoomed
      (lfSteps (H := H) st0 B prover decodePair decodeF decodeChal decodeQuery accepting) Acc)
    (hT : 1 ≤ Rounds.Role.length nl w) :
    ((univ.filter fun tape : Fin (Rounds.Role.length nl w) → C =>
        Acc tape ∧ Fails).card : ℚ)
        / (Fintype.card C : ℚ) ^ Rounds.Role.length nl w
      ≤ ((Fintype.card Cand *
            (nl * bpair + (∑ i ∈ Finset.range nl, w i) * (k * 2) + k * 1
              + kchal * escaping.card + kq * bq) : ℕ) : ℚ)
          / (Fintype.card C : ℚ) := by
  classical
  have h := RbrLayerStep.layerStep_ratio_le
    (Accepts := Acc) (Fails := Fails)
    (lfSteps (H := H) st0 B prover decodePair decodeF decodeChal decodeQuery accepting)
    (Wrong H Sat LigDoomed) (.start : RbrLayerStep.WState logw logc F X)
    bpair (k * 2) (k * 1) (kchal * escaping.card) (kq * bq)
    (fun hf cand => hfail hf cand)
    (by
      -- the layer pair: `initStep` at layer 0, `combineStep` after
      intro ly m pref cand s hw
      by_cases hly : ly.val = 0
      · simp only [lfSteps, if_pos hly]
        exact le_trans (initStep_budget H Sat LigDoomed LC wOf tail st0 decodePair kpair hbalPair
          hzero0 hzero1 hclaim cand (harith cand) s hw) hbp0
      · simp only [lfSteps, if_neg hly]
        exact le_trans (combineStep_budget Sat LigDoomed (B m pref) decodeF k hbalF cand s hw)
          hbp1)
    (by
      intro ly j m pref cand s hw
      exact roundStep_budget H Sat LigDoomed (prover m pref) decodeF k hbalF cand s hw)
    (by
      intro m pref cand s hw
      exact combineStep_budget Sat LigDoomed (B m pref) decodeF k hbalF cand s hw)
    (by
      intro m pref cand s _
      exact ligeroChallengeStep_budget H Sat LigDoomed decodeChal kchal hbalChal escaping hesc
        cand s)
    (by
      intro m pref cand s _
      exact ligeroQueryStep_budget H Sat LigDoomed decodeQuery kq hbalQuery
        (accepting m pref) bq (hbq m pref) cand s)
    hright hT
  exact h

/-! ## LayerStep as an object, for composition

`layerStep_ratio_le` reads a *ratio* off LayerStep, which fixes the commitment.  `Lfzk.Nizk` sums over
commitments, so it needs LayerStep as a `Bcs.Rbr` object, one per commitment.  These three
declarations are that, and with them `Nizk.nizk_ratio_le`'s `R` and `hb` stop being caller inputs.
-/

omit [Fintype C] [Fintype F] [DecidableEq F] [DecidableEq X] in
/-- **`right_of_accepts` at any acceptance predicate that implies LayerStep's.**  `Accepts` is the
LayerStep reaching `.accepted`; a compiled verifier's acceptance is a different predicate, and all the
obligation needs is that it implies this one. -/
theorem rightOfAccepts_of_imp {H : Honest F Cand logw logc} [Nonempty Cand] (Sat : Cand → Prop)
    (LigDoomed : X → Prop) (steps : RbrLayerStep.Steps C F X logw logc nl w)
    {Acc : (Fin (Rounds.Role.length nl w) → C) → Prop}
    (hle : ∀ tape, Acc tape → Accepts (H := H) Sat LigDoomed steps tape) :
    RightOfAccepts (H := H) Sat LigDoomed steps Acc :=
  fun tape hacc => right_of_accepts (H := H) Sat LigDoomed steps tape (hle tape hacc)

namespace LayerStepData

variable {H : Honest F Cand logw logc} {Sat : Cand → Prop} {LigDoomed : X → Prop}
variable {bpair bround bin blig bquery : ℕ}
variable (D : LayerStepData C F X Q Cand Witness nc nv logw logc nl w H Sat LigDoomed
  bpair bround bin blig bquery)

/--
**LayerStep, as a round-by-round argument.**

Every budget discharged by the five lemmas above; `wrong_init` is `hfail`; `right_of_accepts` is
`hright`, which `rightOfAccepts_of_imp` supplies from nothing but `Acc → Accepts`.
-/
noncomputable def rbr [DecidableEq C] [Nonempty C] [Fintype Cand]
    {Acc : (Fin (Rounds.Role.length nl w) → C) → Prop} {Fails : Prop}
    (hfail : Fails → ∀ cand : Cand, ¬ Sat cand)
    (hright : RightOfAccepts (H := H) Sat LigDoomed D.steps Acc) :
    Bcs.Rbr C (Rounds.Role.length nl w) Acc Fails :=
  RbrLayerStep.layerStepRbr D.steps (Wrong H Sat LigDoomed)
    (.start : RbrLayerStep.WState logw logc F X) bpair bround bin blig bquery
    (fun hf cand => hfail hf cand)
    D.budget_pair D.budget_round D.budget_in D.budget_lig D.budget_query hright

/-- **Its per-slot budget is the class budget**, times the list factor once.  This is `Nizk`'s `hb`,
as an equality rather than a hypothesis. -/
theorem rbr_beta [DecidableEq C] [Nonempty C] [Fintype Cand]
    {Acc : (Fin (Rounds.Role.length nl w) → C) → Prop} {Fails : Prop}
    (hfail : Fails → ∀ cand : Cand, ¬ Sat cand)
    (hright : RightOfAccepts (H := H) Sat LigDoomed D.steps Acc) :
    (D.rbr (Fails := Fails) hfail hright).beta
      = fun i => Fintype.card Cand *
          RbrLayerStep.classBudget (nl := nl) (w := w) bpair bround bin blig bquery
            (Rounds.Role.indexEquiv.symm i) := rfl

/-- **The bundled form of `layerStep_ratio_le`.**  Same statement, one data argument. -/
theorem ratio_le [DecidableEq C] [Nonempty C] [Fintype Cand] [Nonempty Cand]
    {Acc : (Fin (Rounds.Role.length nl w) → C) → Prop} {Fails : Prop}
    (hfail : Fails → ∀ cand : Cand, ¬ Sat cand)
    (hright : RightOfAccepts (H := H) Sat LigDoomed D.steps Acc)
    (hT : 1 ≤ Rounds.Role.length nl w) :
    ((univ.filter fun tape : Fin (Rounds.Role.length nl w) → C =>
        Acc tape ∧ Fails).card : ℚ)
        / (Fintype.card C : ℚ) ^ Rounds.Role.length nl w
      ≤ ((Fintype.card Cand *
            (nl * bpair + (∑ i ∈ Finset.range nl, w i) * bround + bin + blig + bquery) : ℕ) : ℚ)
          / (Fintype.card C : ℚ) :=
  RbrLayerStep.layerStep_ratio_le (Accepts := Acc) (Fails := Fails) D.steps (Wrong H Sat LigDoomed)
    (.start : RbrLayerStep.WState logw logc F X) bpair bround bin blig bquery
    (fun hf cand => hfail hf cand)
    D.budget_pair D.budget_round D.budget_in D.budget_lig D.budget_query hright hT

end LayerStepData

end Assemble

end Lfzk.RbrLongfellow
