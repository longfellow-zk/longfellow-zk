import Lfzk.RbrChain

/-!
# LayerStep, round by round

One `Bcs.ClaimChain` over the whole schedule of `Lfzk.Rounds`: `nl` layers, layer `ly` carrying `w ly` sumcheck rounds
each, then the input binding and the two Ligero rounds.  The chain dispatches on
`Rounds.Role.indexEquiv.symm`, so each slot gets the transition its role calls for, and
`layerStep_ratio_le` collects the budget by role class into the closed form a parameter row quotes.

## The `betas` obstruction, and why it is not one

Writing this exposed a design constraint that the abstract scaffolding could not have shown.  The
obvious state function is "the claim at layer `ly` is wrong", i.e. `¬ ClaimsCorrect LC ly w betas st`,
which unfolds to `st.claim0 ≠ LC.V ly w betas st.g0 st.q`.  But `LayeredCircuit.V_local` says
`V ly w betas` depends on `betas i` for **`i ≥ ly`** — on the betas of layer `ly` *and every layer
below it*.  If `beta` were drawn per layer in protocol order, as `begin_layer` draws it, then the
honest value at layer `ly` would depend on answers from *later* slots, and `Bcs.ClaimChain.Wrong`
would not be a function of the state.  The chain could not be written at all.

The resolution is not a modelling change: it is the model `soundness_probability_v3` already uses.
Its `hbetasG` reads

```lean
hbetasG : (fun ω => Function.update tail 0 (pairG ω).1) = betas
```

— `betas 0` is random, drawn as one coordinate with `alpha 0`, and `betas i = tail i` for `i > 0` is
a **fixed parameter**.  So by `V_local`, `V ly w betas` for `ly ≥ 1` depends only on `tail`, and
`V 0 w betas` depends only on `betas 0`, which layer 0's pair slot draws.  Everything is
prefix-measurable once `beta0` is carried in the state, which is why `LayerStepState` has that field.

**What this costs is honesty about what is proved, not soundness.**  The flat theorem does not model
per-layer random betas either, so this chain is exactly as strong; a version where every layer's
`beta` is a fresh challenge in causal order is a separate question, and one the flat proof does not
answer.  It is recorded in `../longfellow-nizk-plan.md` §5 as the open item it is.

## What is here and what is not

Here: the state, the per-role dispatch, and the budget collected by class — so the bound is
`|Cand| · (nl·bpair + (∑ ly, w ly)·bround + bin + blig + bquery) / |C|` with the five per-class escape
counts as inputs.

Not here: three of those five inputs.  `bround` is `Lfzk.RbrChain.scStep_budget`, `bin` is
`Lfzk.RbrBudgets.inputBind`, and `bpair` is `Lfzk.RbrBudgets.layerPair` / `layerAlpha`; the two
Ligero ones come from `Ligero.V3.ligerov3_roundByRound` through
`Bcs.card_preimage_le_of_balanced`.  Supplying them is instantiation, and the transitions they are
stated against are the ones `Steps` takes as data — which is what keeps this file about LayerStep
rather than about any one round.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.RbrLayerStep

open Finset
open scoped Classical

/-! ## The state -/

/--
**The verifier's state during LayerStep.**

`beta0` is `betas 0`, fixed once layer 0's pair slot is read; see the module docstring for why it
has to be in the state.  `bound` and `claim` are the current layer's sumcheck in progress, as in
`Lfzk.RbrChain.ScState`; `st` is the layer's incoming `LayerState`.
-/
structure LayerStepState (logw logc : ℕ) (F : Type) where
  /-- Which layer LayerStep is in. -/
  layer : ℕ
  /-- `betas 0`, the one random beta in the model this inherits. -/
  beta0 : F
  /-- The layer's incoming claims and points. -/
  st : LayerState logw logc F
  /-- The coefficient combining this layer's two inherited claims, drawn at its pair slot.  The
  layer polynomial folds the two `g` points at it, so the honest claim depends on it and it has to
  be in the state. -/
  alpha : F
  /-- Challenges bound so far in this layer's sumcheck. -/
  bound : List F
  /-- The current sumcheck claim. -/
  claim : F

/--
**LayerStep's state.**

Three-way rather than `Option`, because `start` has to say something: `Bcs.ClaimChain`'s
`wrong_init` is a statement about the *initial* state, and for Longfellow it is "no candidate
satisfies the circuit".  With `Option`, the initial state would have to be `none` — which is wrong
for every candidate vacuously, making `wrong_init` free but `right_of_accepts` unprovable, since a
run that starts at `none` never leaves it.
-/
inductive WState (logw logc : ℕ) (F X : Type) where
  /-- Before layer 0's pair slot: LayerStep has not started. -/
  | start
  /-- LayerStep in progress. -/
  | running (ws : LayerStepState logw logc F)
  /-- After Ligero's linear-combination challenge, carrying it.  `X` is that challenge's type; it is
  a parameter so that this file stays free of Ligero. -/
  | challenged (x : X)
  /-- After Ligero's query round, with the query accepted.  The run ends here. -/
  | accepted
  /-- A check has failed, so the run is rejected. -/
  | failed

/-! ## The transitions, as data

One field per role class.  Each takes the prefix length `m` and the prefix, so a transition may read
the prover's messages — which under Fiat--Shamir are functions of the challenge prefix, so reading
the prefix is reading them.  Taking `m` explicitly rather than tying it to the slot avoids a
dependent match on the role at every use.
-/

/-- The per-role transitions of a LayerStep. -/
structure Steps (C F X : Type) (logw logc nl : ℕ) (w : ℕ → ℕ) where
  /-- `begin_layer`: close the previous layer, combine its claims at `alpha`, start the sumcheck. -/
  pair : Fin nl → ∀ m : ℕ, (Fin m → C) → C → WState logw logc F X → WState logw logc F X
  /-- One sumcheck round of a layer. -/
  round : ∀ ly : Fin nl, Fin (w ly.val) →
    ∀ m : ℕ, (Fin m → C) → C → WState logw logc F X → WState logw logc F X
  /-- `elt_field`: bind the input-layer claims against the committed witness. -/
  inputBind : ∀ m : ℕ, (Fin m → C) → C → WState logw logc F X → WState logw logc F X
  /-- Ligero's linear-combination challenge. -/
  ligeroChallenge : ∀ m : ℕ, (Fin m → C) → C → WState logw logc F X → WState logw logc F X
  /-- Ligero's query set. -/
  ligeroQuery : ∀ m : ℕ, (Fin m → C) → C → WState logw logc F X → WState logw logc F X

/-- A budget, one value per role class. -/
def classBudget {nl : ℕ} {w : ℕ → ℕ} (bpair bround bin blig bquery : ℕ) :
    Rounds.Role nl w → ℕ
  | .layerPair _ => bpair
  | .sumcheck _ _ => bround
  | .inputBind => bin
  | .ligeroChallenge => blig
  | .ligeroQuery => bquery

section Chain

variable {C F X Cand : Type} [Fintype C] [Field F] [Fintype F] [DecidableEq F]
variable {logw logc nl : ℕ} {w : ℕ → ℕ}

/-- The transition a role calls for.  Split out from `layerStepChain` so that it reduces on a
*constructor*: the dispatch inside `layerStepChain` is on `indexEquiv.symm i`, which is opaque, and
rewriting that to a constructor is what lets each budget branch discharge one hypothesis. -/
def stepAt (steps : Steps C F X logw logc nl w) (rl : Rounds.Role nl w) (m : ℕ)
    (pref : Fin m → C) (c : C) (s : WState logw logc F X) : WState logw logc F X :=
  match rl with
  | .layerPair ly => steps.pair ly m pref c s
  | .sumcheck ly j => steps.round ly j m pref c s
  | .inputBind => steps.inputBind m pref c s
  | .ligeroChallenge => steps.ligeroChallenge m pref c s
  | .ligeroQuery => steps.ligeroQuery m pref c s

/--
**LayerStep as a claim chain.**  Each slot gets the transition its role calls for.

`Rounds.Role.indexEquiv` is what makes this well defined: it is a *bijection*, so every slot has
exactly one role and every role exactly one slot.  Without `Rounds.Role.card_role` this dispatch
could silently drop a round or double-book a slot.
-/
noncomputable def layerStepChain (steps : Steps C F X logw logc nl w)
    (Wrong : Cand → WState logw logc F X → Prop) (init : WState logw logc F X) :
    Bcs.ClaimChain C (Rounds.Role.length nl w) (WState logw logc F X) Cand where
  init := init
  step i pref c s := stepAt steps (Rounds.Role.indexEquiv.symm i) i.val pref c s
  Wrong := Wrong

/-- **LayerStep's budget, collected by role class.**  `Rounds.Role.sum_slot_eq_sum_role` reindexes
the sum over slots into one over roles, and `sum_role_const` closes it. -/
theorem layerStep_budget_sum (bpair bround bin blig bquery : ℕ) :
    ∑ i : Fin (Rounds.Role.length nl w),
        classBudget (nl := nl) (w := w) bpair bround bin blig bquery
          (Rounds.Role.indexEquiv.symm i)
      = nl * bpair + (∑ i ∈ Finset.range nl, w i) * bround + bin + blig + bquery := by
  rw [Rounds.Role.sum_slot_eq_sum_role
    (classBudget (nl := nl) (w := w) bpair bround bin blig bquery)]
  exact Rounds.Role.sum_role_const _ bpair bround bin blig bquery
    (fun _ => rfl) (fun _ _ => rfl) rfl rfl rfl

omit [Field F] [Fintype F] [DecidableEq F] in
/--
**LayerStep, round by round.**

```
Pr[ the verifier accepts  ∧  extraction fails ]
    ≤  |Cand| · (nl·bpair + (∑ ly, w ly)·bround + bin + blig + bquery) / |C|
```

Five escape counts in, one bound out, with the list factor paid once
(`Bcs.ClaimChain.doom_preserved_of_perCandidate`).  Each `budget_*` hypothesis is a round-local
statement — "from a wrong state, at most this many answers make it right" — and the module docstring
names the lemma that supplies each.
-/
theorem layerStep_ratio_le [DecidableEq C] [Nonempty C] [Fintype Cand]
    (steps : Steps C F X logw logc nl w)
    (Wrong : Cand → WState logw logc F X → Prop) (init : WState logw logc F X)
    (bpair bround bin blig bquery : ℕ)
    {Accepts : (Fin (Rounds.Role.length nl w) → C) → Prop} {Fails : Prop}
    (wrong_init : Fails → ∀ cand : Cand, Wrong cand init)
    (budget_pair : ∀ (ly : Fin nl) (m : ℕ) (pref : Fin m → C) (cand : Cand)
      (s : WState logw logc F X), Wrong cand s →
      (univ.filter fun c : C => ¬ Wrong cand (steps.pair ly m pref c s)).card ≤ bpair)
    (budget_round : ∀ (ly : Fin nl) (j : Fin (w ly.val)) (m : ℕ) (pref : Fin m → C) (cand : Cand)
      (s : WState logw logc F X), Wrong cand s →
      (univ.filter fun c : C => ¬ Wrong cand (steps.round ly j m pref c s)).card ≤ bround)
    (budget_in : ∀ (m : ℕ) (pref : Fin m → C) (cand : Cand) (s : WState logw logc F X),
      Wrong cand s →
      (univ.filter fun c : C => ¬ Wrong cand (steps.inputBind m pref c s)).card ≤ bin)
    (budget_lig : ∀ (m : ℕ) (pref : Fin m → C) (cand : Cand) (s : WState logw logc F X),
      Wrong cand s →
      (univ.filter fun c : C => ¬ Wrong cand (steps.ligeroChallenge m pref c s)).card ≤ blig)
    (budget_query : ∀ (m : ℕ) (pref : Fin m → C) (cand : Cand) (s : WState logw logc F X),
      Wrong cand s →
      (univ.filter fun c : C => ¬ Wrong cand (steps.ligeroQuery m pref c s)).card ≤ bquery)
    (right_of_accepts : ∀ tape : Fin (Rounds.Role.length nl w) → C, Accepts tape →
      ∃ cand : Cand, ¬ (layerStepChain steps Wrong init).Wrong cand
        ((layerStepChain steps Wrong init).state (Rounds.Role.length nl w)
          (Bcs.trunc tape (Rounds.Role.length nl w) le_rfl)))
    (hT : 1 ≤ Rounds.Role.length nl w) :
    ((univ.filter fun tape : Fin (Rounds.Role.length nl w) → C =>
        Accepts tape ∧ Fails).card : ℚ)
        / (Fintype.card C : ℚ) ^ Rounds.Role.length nl w
      ≤ ((Fintype.card Cand *
            (nl * bpair + (∑ i ∈ Finset.range nl, w i) * bround + bin + blig + bquery) : ℕ) : ℚ)
          / (Fintype.card C : ℚ) := by
  have hbound := Bcs.ClaimChain.claimChain_ratio_le (layerStepChain steps Wrong init)
    (fun i => classBudget (nl := nl) (w := w) bpair bround bin blig bquery
      (Rounds.Role.indexEquiv.symm i))
    wrong_init
    (by
      intro i pref cand hw
      -- dispatch on the role at this slot; each branch is one hypothesis
      cases hrole : Rounds.Role.indexEquiv.symm i with
      | layerPair ly =>
          simp only [layerStepChain, stepAt, hrole, classBudget]
          exact budget_pair ly i.val pref cand _ hw
      | sumcheck ly j =>
          simp only [layerStepChain, stepAt, hrole, classBudget]
          exact budget_round ly j i.val pref cand _ hw
      | inputBind =>
          simp only [layerStepChain, stepAt, hrole, classBudget]
          exact budget_in i.val pref cand _ hw
      | ligeroChallenge =>
          simp only [layerStepChain, stepAt, hrole, classBudget]
          exact budget_lig i.val pref cand _ hw
      | ligeroQuery =>
          simp only [layerStepChain, stepAt, hrole, classBudget]
          exact budget_query i.val pref cand _ hw)
    right_of_accepts hT
  rwa [layerStep_budget_sum (nl := nl) (w := w) bpair bround bin blig bquery] at hbound

/-! ## Slicing on the commitment

`layerStep_ratio_le` fixes the commitment: `Fails` is a proposition, because the Ligero oracle and the
candidate list are decided before any challenge is drawn.  The composed sample space is
`Pre × tape` — everything the commitment stage decided, then the challenge tape — so a composed bound
needs one LayerStep per commitment and a sum over `Pre`.  `Bcs.rbr_ratio_le_prod` does that sum; what is
needed here is LayerStep as an `Rbr` rather than as a ratio, so that the family can be formed.
-/

/-- LayerStep as a `Bcs.Rbr`, so that `Bcs.rbr_card_le_prod` can slice on the commitment.  Same
inputs as `layerStep_ratio_le`; that theorem is the ratio read off this object. -/
noncomputable def layerStepRbr [Fintype Cand]
    (steps : Steps C F X logw logc nl w)
    (Wrong : Cand → WState logw logc F X → Prop) (init : WState logw logc F X)
    (bpair bround bin blig bquery : ℕ)
    {Accepts : (Fin (Rounds.Role.length nl w) → C) → Prop} {Fails : Prop}
    (wrong_init : Fails → ∀ cand : Cand, Wrong cand init)
    (budget_pair : ∀ (ly : Fin nl) (m : ℕ) (pref : Fin m → C) (cand : Cand)
      (s : WState logw logc F X), Wrong cand s →
      (univ.filter fun c : C => ¬ Wrong cand (steps.pair ly m pref c s)).card ≤ bpair)
    (budget_round : ∀ (ly : Fin nl) (j : Fin (w ly.val)) (m : ℕ) (pref : Fin m → C) (cand : Cand)
      (s : WState logw logc F X), Wrong cand s →
      (univ.filter fun c : C => ¬ Wrong cand (steps.round ly j m pref c s)).card ≤ bround)
    (budget_in : ∀ (m : ℕ) (pref : Fin m → C) (cand : Cand) (s : WState logw logc F X),
      Wrong cand s →
      (univ.filter fun c : C => ¬ Wrong cand (steps.inputBind m pref c s)).card ≤ bin)
    (budget_lig : ∀ (m : ℕ) (pref : Fin m → C) (cand : Cand) (s : WState logw logc F X),
      Wrong cand s →
      (univ.filter fun c : C => ¬ Wrong cand (steps.ligeroChallenge m pref c s)).card ≤ blig)
    (budget_query : ∀ (m : ℕ) (pref : Fin m → C) (cand : Cand) (s : WState logw logc F X),
      Wrong cand s →
      (univ.filter fun c : C => ¬ Wrong cand (steps.ligeroQuery m pref c s)).card ≤ bquery)
    (right_of_accepts : ∀ tape : Fin (Rounds.Role.length nl w) → C, Accepts tape →
      ∃ cand : Cand, ¬ (layerStepChain steps Wrong init).Wrong cand
        ((layerStepChain steps Wrong init).state (Rounds.Role.length nl w)
          (Bcs.trunc tape (Rounds.Role.length nl w) le_rfl))) :
    Bcs.Rbr C (Rounds.Role.length nl w) Accepts Fails :=
  Bcs.ClaimChain.toRbr (layerStepChain steps Wrong init)
    (fun i => classBudget (nl := nl) (w := w) bpair bround bin blig bquery
      (Rounds.Role.indexEquiv.symm i))
    wrong_init
    (by
      intro i pref cand hw
      cases hrole : Rounds.Role.indexEquiv.symm i with
      | layerPair ly =>
          simp only [layerStepChain, stepAt, hrole, classBudget]
          exact budget_pair ly i.val pref cand _ hw
      | sumcheck ly j =>
          simp only [layerStepChain, stepAt, hrole, classBudget]
          exact budget_round ly j i.val pref cand _ hw
      | inputBind =>
          simp only [layerStepChain, stepAt, hrole, classBudget]
          exact budget_in i.val pref cand _ hw
      | ligeroChallenge =>
          simp only [layerStepChain, stepAt, hrole, classBudget]
          exact budget_lig i.val pref cand _ hw
      | ligeroQuery =>
          simp only [layerStepChain, stepAt, hrole, classBudget]
          exact budget_query i.val pref cand _ hw)
    right_of_accepts

omit [Field F] [Fintype F] [DecidableEq F] in
/-- `layerStepRbr`'s per-slot budget is the class budget, times the list factor once. -/
theorem layerStepRbr_beta [Fintype Cand]
    (steps : Steps C F X logw logc nl w)
    (Wrong : Cand → WState logw logc F X → Prop) (init : WState logw logc F X)
    (bpair bround bin blig bquery : ℕ)
    {Accepts : (Fin (Rounds.Role.length nl w) → C) → Prop} {Fails : Prop}
    (wrong_init budget_pair budget_round budget_in budget_lig budget_query right_of_accepts) :
    (layerStepRbr steps Wrong init bpair bround bin blig bquery (Accepts := Accepts) (Fails := Fails)
      wrong_init budget_pair budget_round budget_in budget_lig budget_query
      right_of_accepts).beta
      = fun i => Fintype.card Cand *
          classBudget (nl := nl) (w := w) bpair bround bin blig bquery
            (Rounds.Role.indexEquiv.symm i) := rfl

/--
**LayerStep, summed over commitments.**

```
Pr over (commitment, tape) [ LayerStep accepts ∧ extraction failed ]
    ≤  |Cand| · (nl·bpair + (∑ ly, w ly)·bround + bin + blig + bquery) / |C|
```

One LayerStep per commitment, and the bound is uniform in it — which is what a parameter row quotes,
since the budgets come from the code parameters and not from the adversary's commitment.
`layerStepRbr` builds the family's members.
-/
theorem layerStep_ratio_le_prod {Pre : Type} [Fintype Pre] [Nonempty Pre]
    [DecidableEq C] [Nonempty C] [Fintype Cand]
    {Acc : Pre × (Fin (Rounds.Role.length nl w) → C) → Prop} {Fails : Pre → Prop}
    (R : ∀ pre : Pre, Bcs.Rbr C (Rounds.Role.length nl w)
      (fun tape => Acc (pre, tape)) (Fails pre))
    (bpair bround bin blig bquery : ℕ)
    (hb : ∀ (pre : Pre) (i : Fin (Rounds.Role.length nl w)), (R pre).beta i
      ≤ Fintype.card Cand * classBudget (nl := nl) (w := w) bpair bround bin blig bquery
          (Rounds.Role.indexEquiv.symm i))
    (hT : 1 ≤ Rounds.Role.length nl w) :
    ((univ.filter fun omega : Pre × (Fin (Rounds.Role.length nl w) → C) =>
        Acc omega ∧ Fails omega.1).card : ℚ)
        / (Fintype.card Pre * (Fintype.card C : ℚ) ^ Rounds.Role.length nl w)
      ≤ ((Fintype.card Cand *
            (nl * bpair + (∑ i ∈ Finset.range nl, w i) * bround + bin + blig + bquery) : ℕ) : ℚ)
          / (Fintype.card C : ℚ) := by
  classical
  refine Bcs.rbr_ratio_le_prod R _ (fun pre => ?_) hT
  calc ∑ i, (R pre).beta i
      ≤ ∑ i, Fintype.card Cand *
          classBudget (nl := nl) (w := w) bpair bround bin blig bquery
            (Rounds.Role.indexEquiv.symm i) := Finset.sum_le_sum (fun i _ => hb pre i)
    _ = Fintype.card Cand * ∑ i,
          classBudget (nl := nl) (w := w) bpair bround bin blig bquery
            (Rounds.Role.indexEquiv.symm i) := by rw [Finset.mul_sum]
    _ = Fintype.card Cand * (nl * bpair + (∑ i ∈ Finset.range nl, w i) * bround + bin + blig + bquery) := by
        rw [layerStep_budget_sum (nl := nl) (w := w) bpair bround bin blig bquery]

end Chain

end Lfzk.RbrLayerStep
