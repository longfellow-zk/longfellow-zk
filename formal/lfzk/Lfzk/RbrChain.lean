import Lfzk.RbrBudgets
import Bcs.ClaimChain

/-!
# One sumcheck, round by round

The shape check `../longfellow-nizk-plan.md` §8 asks for before the induction over layers: a real
`Bcs.ClaimChain` built from real `sumcheck` definitions, with a real budget, so that the design is
tested against the library rather than against a sketch.

What it establishes is that the granularity of the round-by-round argument can be **one slot per
sumcheck round**, not one per layer.  That was the open question: `lfzk`'s layer lemmas
(`lemma_sumcheck_soundness`, `sumcheck_ci_of_arithmetized`) are stated per *layer*, over the whole
round list at once, so the obvious chain would consume a layer per slot and charge
`(1 + 2·nrnd)/|F|` for it.  `Sumcheck.sumcheck_step_reduction` turns out to be exactly a claim-chain
step — from a false claim, either the next claim is false or this round was lucky — so a per-round
chain works and the budget is `deg` per round.  At the certified parameters the coarser reading
would have cost about five bits on the field rounds; they are `2^-127` against Ligero's `2^-120`, so
it would not have bound, but per-round is both sharper and no harder.

## The state

`ScState F` is `Option (List F × F)`: the challenges bound so far and the current claim, or `none`
if a round check already failed.  Two points:

* **the bound challenges are part of the state**, because `Bcs.ClaimChain.Wrong` sees only the
  state.  The honest claim to compare against depends on where the sumcheck has been bound, so the
  state has to carry it.  This is not bookkeeping — it is the verifier's own state;
* `none` is **wrong for every candidate**.  A run whose round check failed is rejected, so it can
  never be the accepting run `right_of_accepts` talks about, and keeping it doomed is what lets
  `step` be total.

## The two consistency hypotheses

`truePoly` and `trueSum` are the honest round polynomial and the honest claim.  They are supplied
rather than constructed, with the two conditions the reduction needs:

* `hsum` — the honest round polynomial sums over `{0,1}` to the honest incoming claim;
* `hnext` — evaluating it at the round's challenge gives the honest *outgoing* claim.

Together they are `Sumcheck.consistent_true_polys`, which `LayeredCircuit.consistent`
(`Layers.lean`) proves for Longfellow's layer polynomial.  So instantiating this chain at a
Longfellow layer is a matter of supplying that lemma, not of proving anything new.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.RbrChain

open Finset Sumcheck
open scoped Classical

/-- A sumcheck in progress: the challenges bound so far and the current claim, or `none` if a round
check has already failed. -/
abbrev ScState (F : Type) : Type := Option (List F × F)

variable {C F Cand : Type} [Fintype C] [Field F] [Fintype F] [DecidableEq F] {d : ℕ} [Interp F d]

/-- One round's state transition: run the round check, and record the challenge. -/
def scStep (decode : C → F) (prover : List F → RoundPoly F d) (c : C) : ScState F → ScState F
  | none => none
  | some st =>
      match check_round_c st.2 (prover st.1) (decode c) with
      | none => none
      | some cl => some (st.1 ++ [decode c], cl)

/-- The claim is wrong for this candidate.  A failed round check is wrong for every candidate: the
run is rejected, so it can never be the accepting run, and this keeps `scStep` total. -/
def ScWrong (trueSum : Cand → List F → F) (cand : Cand) : ScState F → Prop
  | none => True
  | some st => st.2 ≠ trueSum cand st.1

/--
**One sumcheck as a claim chain.**

`decode` is the round's challenge, read off the oracle answer; `prover` is the transmitted round
polynomial at a given bound prefix — a function of the prefix, which is what Fiat--Shamir gives
structurally; `trueSum` is the honest claim.  Doom is "the claim is wrong", for every candidate.
-/
def scChain (n : ℕ) (decode : C → F) (prover : List F → RoundPoly F d)
    (trueSum : Cand → List F → F) (claim0 : F) :
    Bcs.ClaimChain C n (ScState F) Cand where
  init := some ([], claim0)
  step _ _ c s := scStep decode prover c s
  Wrong cand s := ScWrong trueSum cand s

omit [Fintype C] [Fintype F] in
@[simp] theorem scChain_step (n : ℕ) (decode : C → F) (prover : List F → RoundPoly F d)
    (trueSum : Cand → List F → F) (claim0 : F) (i : Fin n) (pref : Fin i.val → C) (c : C)
    (s : ScState F) :
    (scChain n decode prover trueSum claim0).step i pref c s = scStep decode prover c s := rfl

omit [Fintype C] [Fintype F] in
@[simp] theorem scChain_Wrong (n : ℕ) (decode : C → F) (prover : List F → RoundPoly F d)
    (trueSum : Cand → List F → F) (claim0 : F) (cand : Cand) (s : ScState F) :
    (scChain n decode prover trueSum claim0).Wrong cand s = ScWrong trueSum cand s := rfl

/--
**The per-round budget: `k * deg`.**

From a wrong claim, an answer escapes only by being one of at most `deg` lucky challenges — the
roots of the difference between the transmitted round polynomial and the honest one — and at most
`k` answers decode to each.  `Sumcheck.sumcheck_step_reduction` is the step, and
`Lfzk.RbrBudgets.sumcheckRound` is the count.

The two hypotheses are the sumcheck consistency conditions; see the module docstring.
-/
theorem scStep_budget (decode : C → F) (k : ℕ)
    (hbal : ∀ y : F, (univ.filter fun c : C => decode c = y).card ≤ k)
    (prover : List F → RoundPoly F d)
    (truePoly : Cand → List F → Polynomial F) (trueSum : Cand → List F → F)
    (deg : ℕ) (hd : d ≤ deg)
    (hdeg : ∀ (cand : Cand) (bnd : List F), (truePoly cand bnd).natDegree ≤ deg)
    (hsum : ∀ (cand : Cand) (bnd : List F),
      (truePoly cand bnd).eval 0 + (truePoly cand bnd).eval 1 = trueSum cand bnd)
    (hnext : ∀ (cand : Cand) (bnd : List F) (r : F),
      (truePoly cand bnd).eval r = trueSum cand (bnd ++ [r]))
    (cand : Cand) (s : ScState F) (hw : ScWrong trueSum cand s) :
    (univ.filter fun c : C =>
        ¬ ScWrong trueSum cand (scStep decode prover c s)).card ≤ k * deg := by
  classical
  cases s with
  | none =>
      -- a failed check stays failed, so nothing escapes
      refine le_trans (Finset.card_le_card (t := (∅ : Finset C)) ?_) (by simp)
      intro c hc
      simp only [mem_filter, mem_univ, true_and, scStep, ScWrong, not_true] at hc
  | some st =>
      have hwrong : st.2 ≠ trueSum cand st.1 := hw
      have hfalse : st.2 ≠ (truePoly cand st.1).eval 0 + (truePoly cand st.1).eval 1 := by
        rw [hsum cand st.1]; exact hwrong
      refine le_trans (Finset.card_le_card (t := univ.filter fun c : C =>
        BadRoundEvent (truePoly cand st.1) (prover st.1) (decode c)) ?_) ?_
      · intro c hc
        simp only [mem_filter, mem_univ, true_and] at hc ⊢
        rcases hchk : check_round_c st.2 (prover st.1) (decode c) with _ | cl
        · rw [scStep, hchk] at hc
          exact absurd trivial hc
        · rw [scStep, hchk] at hc
          have hesc : cl = trueSum cand (st.1 ++ [decode c]) := by
            simpa [ScWrong] using hc
          rcases sumcheck_step_reduction (truePoly cand st.1) (prover st.1) st.2 cl
            (decode c) hchk hfalse with hstill | hbad
          · exact absurd (by rw [hesc, ← hnext cand st.1 (decode c)]) hstill
          · exact hbad
      · exact Lfzk.RbrBudgets.sumcheckRound decode k hbal (truePoly cand st.1) (prover st.1)
          deg (hdeg cand st.1) hd

/--
**One sumcheck, round by round.**

```
Pr[ the verifier accepts  ∧  no candidate's claim was ever right ]  ≤  |Cand| · n · k · deg / |C|
```

At a balanced field decoder (`k = |C| / |F|`) and `deg = 2` this is `2·|Cand|·n / |F|` — the
textbook sumcheck error, times the one list factor, with each round charged separately so that a
Fiat--Shamir compiler can consume it.

`right_of_accepts` is the verifier's final check and stays a hypothesis: it is the protocol-specific
half, and for Longfellow it is what `Lfzk.final_binding` and `get_last_eval` supply.
-/
theorem sumcheck_rbr_ratio_le [DecidableEq C] [Nonempty C] [Fintype Cand]
    (n : ℕ) (hn : 1 ≤ n) (decode : C → F) (k : ℕ)
    (hbal : ∀ y : F, (univ.filter fun c : C => decode c = y).card ≤ k)
    (prover : List F → RoundPoly F d)
    (truePoly : Cand → List F → Polynomial F) (trueSum : Cand → List F → F) (claim0 : F)
    (deg : ℕ) (hd : d ≤ deg)
    (hdeg : ∀ (cand : Cand) (bnd : List F), (truePoly cand bnd).natDegree ≤ deg)
    (hsum : ∀ (cand : Cand) (bnd : List F),
      (truePoly cand bnd).eval 0 + (truePoly cand bnd).eval 1 = trueSum cand bnd)
    (hnext : ∀ (cand : Cand) (bnd : List F) (r : F),
      (truePoly cand bnd).eval r = trueSum cand (bnd ++ [r]))
    {Accepts : (Fin n → C) → Prop} {Fails : Prop}
    (wrong_init : Fails → ∀ cand : Cand, claim0 ≠ trueSum cand [])
    (right_of_accepts : ∀ tape : Fin n → C, Accepts tape →
      ∃ cand : Cand, ¬ (scChain n decode prover trueSum claim0).Wrong cand
        ((scChain n decode prover trueSum claim0).state n (Bcs.trunc tape n le_rfl))) :
    ((univ.filter fun tape : Fin n → C => Accepts tape ∧ Fails).card : ℚ)
        / (Fintype.card C : ℚ) ^ n
      ≤ ((Fintype.card Cand * ∑ _i : Fin n, k * deg : ℕ) : ℚ) / (Fintype.card C : ℚ) :=
  Bcs.ClaimChain.claimChain_ratio_le _ (fun _ => k * deg)
    (fun hfail cand => by simpa [scChain, ScWrong] using wrong_init hfail cand)
    (fun _i _pref cand hw =>
      scStep_budget decode k hbal prover truePoly trueSum deg hd hdeg hsum hnext cand _ hw)
    right_of_accepts hn

/-- The budget sum, written out: `n` rounds at `k * deg` each. -/
theorem scChain_budget_sum (n k deg : ℕ) : (∑ _i : Fin n, k * deg) = n * (k * deg) := by
  simp [Finset.sum_const]

end Lfzk.RbrChain
