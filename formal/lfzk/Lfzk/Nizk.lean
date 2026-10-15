import Lfzk.RbrLongfellow

/-!
# The non-interactive Longfellow bound, composed

The Phase 6 assembly of `../longfellow-nizk-plan.md`: LayerStep's round-by-round bound, summed
over commitments, plus the price of compiling the oracle away with a Merkle tree.

```
Pr[ the compiled verifier accepts  ∧  no candidate satisfies the circuit ]
    ≤  |Cand| · (nl·bpair + (∑ ly, w ly)·bround + bin + blig + bquery) / |C|   +   merkleTerm
```

## What is proved here, and what the two hypotheses are

The first summand is `Lfzk.RbrLayerStep.layerStep_ratio_le_prod`, and every one of its budgets is a theorem
(`Lfzk.RbrLongfellow`, Phase 5).  The composition itself is this file, and it takes two inputs:

* the family `R` of round-by-round arguments, one per commitment.  `RbrLayerStep.layerStepRbr` builds a member
  from `RbrLongfellow`'s five step budgets, `wrong_init` and `right_of_accepts` — all proved;
* `hmerkle`, the price of the compilation: that the *compiled verifier's* acceptance is bounded by
  LayerStep's acceptance plus `merkleTerm`.  This is **discharged** in `Lfzk.NizkMerkle`, by
  `Bcs.drop_explains_ratio_le` at `Coins := Fin L → C` — see `nizk_ratio_le_merkle` there for the
  composed bound with no `hmerkle` left to assume.

Keeping it a hypothesis *here* is still deliberate: it names the interface in the types, so a
different compilation (a different coin space, or a non-Merkle commitment) instantiates this file
rather than re-deriving it.

## Two things this bound is not

**It is not yet the grinding bound.**  `Bcs.Rbr` is the *sequential* round-by-round notion: the tape
slots are the protocol's challenge rounds in order, so `T = L`.  A grinding adversary needs
`Bcs.RbrCore` with the bad event indexed by *the query made at each slot*, which is the same missing
FS-adversary shape as `hmerkle`.  When it lands, the bound reads the same with `T = t + L`, and the
factor `T` is not a loss: security is advantage per unit of work and the adversary spent `T` to get
it (`../extractor-plan.md` §5.1).

**It carries no numeral.**  Quoting `≤ 2^-lam` needs a certified parameter row, and §6 of the plan
shows the existing grid row is *infeasible* for the round-by-round objective — `2^-107.5` against a
`2^-120` target, because the challenge round pays `(threshold − 1)/|F|` in full where the flat bound
multiplies it by a cover ratio.  Re-optimising costs about 23% more openings and no bits.  That
re-scan is Phase 8a, and until it is certified there is no row to substitute.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.Nizk

open Finset
open scoped Classical

variable {C F X Cand Pre : Type} [Fintype C] [DecidableEq C] [Nonempty C]
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype Cand] [Fintype Pre] [Nonempty Pre]
variable {logw logc nl : ℕ} {w : ℕ → ℕ}

/--
**The composed non-interactive bound.**

`Acc` is LayerStep's acceptance — `RbrLongfellow.Accepts`, LayerStep reaching its `accepted` state —
and `VerAcc` is the compiled verifier's, the one a real verifier decides.  `hmerkle` is the step
between them, and the module docstring says what supplies it.

The arithmetic is one `le_trans`; the content is in the two hypotheses, and in that they are the
*only* two.  Every per-round escape count feeding the first summand is a theorem.
-/
theorem nizk_ratio_le
    {Acc VerAcc : Pre × (Fin (Rounds.Role.length nl w) → C) → Prop} {Fails : Pre → Prop}
    (R : ∀ pre : Pre, Bcs.Rbr C (Rounds.Role.length nl w)
      (fun tape => Acc (pre, tape)) (Fails pre))
    (bpair bround bin blig bquery : ℕ)
    (hb : ∀ (pre : Pre) (i : Fin (Rounds.Role.length nl w)), (R pre).beta i
      ≤ Fintype.card Cand *
          RbrLayerStep.classBudget (nl := nl) (w := w) bpair bround bin blig bquery
            (Rounds.Role.indexEquiv.symm i))
    (hT : 1 ≤ Rounds.Role.length nl w)
    (merkleTerm : ℚ)
    (hmerkle :
      ((univ.filter fun omega : Pre × (Fin (Rounds.Role.length nl w) → C) =>
          VerAcc omega ∧ Fails omega.1).card : ℚ)
          / (Fintype.card Pre * (Fintype.card C : ℚ) ^ Rounds.Role.length nl w)
        ≤ ((univ.filter fun omega : Pre × (Fin (Rounds.Role.length nl w) → C) =>
              Acc omega ∧ Fails omega.1).card : ℚ)
            / (Fintype.card Pre * (Fintype.card C : ℚ) ^ Rounds.Role.length nl w)
          + merkleTerm) :
    ((univ.filter fun omega : Pre × (Fin (Rounds.Role.length nl w) → C) =>
        VerAcc omega ∧ Fails omega.1).card : ℚ)
        / (Fintype.card Pre * (Fintype.card C : ℚ) ^ Rounds.Role.length nl w)
      ≤ ((Fintype.card Cand *
            (nl * bpair + (∑ i ∈ Finset.range nl, w i) * bround + bin + blig + bquery) : ℕ) : ℚ)
          / (Fintype.card C : ℚ) + merkleTerm := by
  have hlayerStep := RbrLayerStep.layerStep_ratio_le_prod (Cand := Cand) R bpair bround bin blig bquery hb hT
  linarith

/--
**At a target.**  If the composed bound is at most `2^-lam`, the argument meets `lam` bits.

Stated separately because it is the form a parameter row is quoted in, and because the *inputs* to
it are what Phase 8a has to certify: `bpair`, `bround`, `bin`, `blig`, `bquery` and `merkleTerm` at a
row of the Ligero grid re-optimised for the round-by-round objective.
-/
theorem nizk_ratio_le_target {ratio bound merkleTerm : ℚ} (lam : ℕ)
    (hbound : ratio ≤ bound + merkleTerm)
    (htarget : bound + merkleTerm ≤ (1 : ℚ) / 2 ^ lam) :
    ratio ≤ (1 : ℚ) / 2 ^ lam := le_trans hbound htarget

/--
**The composed bound at Longfellow's own LayerStep.**

`nizk_ratio_le` with `R` and `hb` gone: the family is built from a family of
`RbrLongfellow.LayerStepData`, one per commitment, and the per-slot budget is `LayerStepData.rbr_beta`, an
equality.  Because the five class budgets are `LayerStepData` *parameters* rather than fields, they are
uniform in the commitment by typing — which is exactly the condition a parameter row needs.

What is left is `hfail` (extraction failure means no candidate satisfies the circuit — Ligero's
extractor, `Phase 6`), `hright` (the compiled acceptance implies LayerStep reaches `.accepted`,
which `RbrLongfellow.rightOfAccepts_of_imp` reduces to that implication alone), and `hmerkle`
(discharged in `Lfzk.NizkMerkle`).
-/
theorem nizk_ratio_le_longfellow
    [SumcheckInterp F] [DecidableEq X] [Nonempty Cand]
    {Q Witness : Type} [Fintype Q] [DecidableEq Q] {nc nv : ℕ}
    {H : RbrLongfellow.Honest F Cand logw logc} {Sat : Cand → Prop} {LigDoomed : X → Prop}
    {Acc VerAcc : Pre × (Fin (Rounds.Role.length nl w) → C) → Prop} {Fails : Pre → Prop}
    (bpair bround bin blig bquery : ℕ)
    (Dfam : ∀ _pre : Pre, RbrLongfellow.LayerStepData C F X Q Cand Witness nc nv logw logc nl w
      H Sat LigDoomed bpair bround bin blig bquery)
    (hfail : ∀ pre : Pre, Fails pre → ∀ cand : Cand, ¬ Sat cand)
    (hright : ∀ pre : Pre, RbrLongfellow.RightOfAccepts (H := H) Sat LigDoomed (Dfam pre).steps
      (fun tape => Acc (pre, tape)))
    (hT : 1 ≤ Rounds.Role.length nl w)
    (merkleTerm : ℚ)
    (hmerkle :
      ((univ.filter fun omega : Pre × (Fin (Rounds.Role.length nl w) → C) =>
          VerAcc omega ∧ Fails omega.1).card : ℚ)
          / (Fintype.card Pre * (Fintype.card C : ℚ) ^ Rounds.Role.length nl w)
        ≤ ((univ.filter fun omega : Pre × (Fin (Rounds.Role.length nl w) → C) =>
              Acc omega ∧ Fails omega.1).card : ℚ)
            / (Fintype.card Pre * (Fintype.card C : ℚ) ^ Rounds.Role.length nl w)
          + merkleTerm) :
    ((univ.filter fun omega : Pre × (Fin (Rounds.Role.length nl w) → C) =>
        VerAcc omega ∧ Fails omega.1).card : ℚ)
        / (Fintype.card Pre * (Fintype.card C : ℚ) ^ Rounds.Role.length nl w)
      ≤ ((Fintype.card Cand *
            (nl * bpair + (∑ i ∈ Finset.range nl, w i) * bround + bin + blig + bquery) : ℕ) : ℚ)
          / (Fintype.card C : ℚ) + merkleTerm :=
  nizk_ratio_le (Cand := Cand)
    (fun pre => (Dfam pre).rbr (Fails := Fails pre) (hfail pre) (hright pre))
    bpair bround bin blig bquery
    (fun pre i => le_of_eq (congrFun ((Dfam pre).rbr_beta (hfail pre) (hright pre)) i))
    hT merkleTerm hmerkle

end Lfzk.Nizk
