import Lfzk.Nizk
import Bcs.CoinSpace

/-!
# Phase 3c: the Merkle term, discharged

`Lfzk.Nizk.nizk_ratio_le` takes the price of the compilation as a hypothesis, `hmerkle`, because
`Bcs.drop_explains_card_le` is stated over `(Fin T → D) × (Challenge × Query)` — an adversary handed
one challenge and one query — while a Fiat–Shamir adversary is handed nothing and derives both from
the tape.

`Bcs.CoinSpace` is the fix: the same two counts over `(Fin T → D) × Coins` for an arbitrary coin
space with two projections `challengeOf`, `queryOf`.  This file instantiates it at
`Coins := Fin L → C`, the Fiat–Shamir coin tape, and so turns `hmerkle` into a theorem.

## What the two events are

`CompiledAccepts` is what a real verifier decides.  The round-by-round argument bounds the *oracle*
protocol's acceptance, which here is `CompiledAccepts` together with an extraction that explains it —
that conjunction is what the `Bcs.Rbr` family `R` is indexed by.  The gap between the two is
`merkleNumerator commitFuel T / |D|`, and that is exactly what `Bcs.drop_explains_ratio_le` pays.

The only work is the sample space: `Fintype.card (Fin T → D) = |D|^T` and
`Fintype.card (Fin L → C) = |C|^L`, so `nizk_ratio_le`'s denominator `|Pre| · |C|^L` and
`drop_explains_ratio_le`'s `|D|^T · |Coins|` are the same number written two ways.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.Nizk

open Finset Bcs Merkle Merkle.MH Merkle.RandomOracle
open scoped Classical

variable {C Cand : Type} [Fintype C] [DecidableEq C] [Nonempty C] [Fintype Cand]
variable {Statement Oracle Challenge Response Query : Type}
variable {Opening : Query → Type}
variable {Enc D Salt M Aux Aux' : Type}
variable {n commitFuel respondFuel revealFuel T nl : ℕ} {w : ℕ → ℕ}

/--
**`hmerkle`, at the Fiat–Shamir coin space.**

`Bcs.drop_explains_ratio_le` with `Coins := Fin L → C`, restated in the sample space
`(Fin T → D) × (Fin L → C)` that `nizk_ratio_le` uses.  The two statements differ only in how the
denominator is written.
-/
theorem hmerkle_of_coinSpace
    [Fintype D] [DecidableEq D] [Inhabited D] [DecidableEq Enc] [Inhabited Salt] [Inhabited M]
    {codec : Codec Salt M D Enc} (dec : RoleDecoders codec)
    (K : Compiler Statement Oracle Challenge Response Query Opening M n)
    (A : Adversary Enc D Salt M Challenge Response Query Aux Aux'
      n commitFuel respondFuel revealFuel)
    (challengeOf : (Fin (Rounds.Role.length nl w) → C) → Challenge)
    (queryOf : (Fin (Rounds.Role.length nl w) → C) → Query)
    (statement : (Fin T → D) × (Fin (Rounds.Role.length nl w) → C) → Statement)
    (Fails : (Fin T → D) → Prop)
    (ht₁ : commitFuel ≤ T)
    (hT : 2 * n + (revealFuel + respondFuel) + commitFuel ≤ T) (hT1 : 1 ≤ T) :
    ((univ.filter fun omega : (Fin T → D) × (Fin (Rounds.Role.length nl w) → C) =>
        CompiledAccepts K A codec (statement omega)
            (challengeOf omega.2) (queryOf omega.2) omega.1 ∧ Fails omega.1).card : ℚ)
        / (Fintype.card (Fin T → D) *
            (Fintype.card C : ℚ) ^ Rounds.Role.length nl w)
      ≤ ((univ.filter fun omega : (Fin T → D) × (Fin (Rounds.Role.length nl w) → C) =>
            (CompiledAccepts K A codec (statement omega)
                (challengeOf omega.2) (queryOf omega.2) omega.1 ∧
              ExtractionExplains codec dec n commitFuel (revealFuel + respondFuel) T
                A.commit (A.openingStage (challengeOf omega.2) (queryOf omega.2))
                omega.1) ∧ Fails omega.1).card : ℚ)
          / (Fintype.card (Fin T → D) *
              (Fintype.card C : ℚ) ^ Rounds.Role.length nl w)
        + (merkleNumerator commitFuel T : ℚ) / (Fintype.card D : ℚ) := by
  have hden : (Fintype.card (Fin T → D) : ℚ) *
        (Fintype.card C : ℚ) ^ Rounds.Role.length nl w
      = (Fintype.card D : ℚ) ^ T *
        Fintype.card (Fin (Rounds.Role.length nl w) → C) := by
    rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    push_cast
    ring
  rw [hden]
  exact drop_explains_ratio_le dec K A challengeOf queryOf statement
    (fun omega => Fails omega.1) ht₁ hT hT1

/--
**The non-interactive Longfellow bound, with the Merkle term proved.**

`Lfzk.Nizk.nizk_ratio_le` with its `hmerkle` hypothesis discharged by `hmerkle_of_coinSpace`.  So:

```
Pr[ the compiled verifier accepts  ∧  no candidate satisfies the circuit ]
    ≤  |Cand| · (nl·bpair + (∑ ly, w ly)·bround + bin + blig + bquery) / |C|
       +  merkleNumerator(commitFuel, T) / |D|
```

over the Fiat–Shamir sample space `(Fin T → D) × (Fin L → C)`: the hash tape, and the coin tape the
verifier's challenges and queries are both derived from.

The only remaining inputs are the round-by-round family `R` — every one of whose budgets is a theorem
in `Lfzk.RbrLongfellow` — and the three fuel inequalities the Merkle extractor needs.  There is no
`hmerkle` left to assume.

Two things this is still not, both unchanged from `Lfzk.Nizk`: it is the *sequential* round-by-round
notion rather than the grinding one, and it carries no numeral, since quoting `≤ 2^-lam` needs a
certified round-by-round parameter row (the plan's Phase 8a).
-/
theorem nizk_ratio_le_merkle
    [Fintype D] [DecidableEq D] [Inhabited D] [DecidableEq Enc] [Inhabited Salt] [Inhabited M]
    {codec : Codec Salt M D Enc} (dec : RoleDecoders codec)
    (K : Compiler Statement Oracle Challenge Response Query Opening M n)
    (A : Adversary Enc D Salt M Challenge Response Query Aux Aux'
      n commitFuel respondFuel revealFuel)
    (challengeOf : (Fin (Rounds.Role.length nl w) → C) → Challenge)
    (queryOf : (Fin (Rounds.Role.length nl w) → C) → Query)
    (statement : (Fin T → D) × (Fin (Rounds.Role.length nl w) → C) → Statement)
    {Fails : (Fin T → D) → Prop}
    (R : ∀ pre : Fin T → D, Bcs.Rbr C (Rounds.Role.length nl w)
      (fun tape =>
        CompiledAccepts K A codec (statement (pre, tape))
            (challengeOf tape) (queryOf tape) pre ∧
          ExtractionExplains codec dec n commitFuel (revealFuel + respondFuel) T
            A.commit (A.openingStage (challengeOf tape) (queryOf tape)) pre)
      (Fails pre))
    (bpair bround bin blig bquery : ℕ)
    (hb : ∀ (pre : Fin T → D) (i : Fin (Rounds.Role.length nl w)), (R pre).beta i
      ≤ Fintype.card Cand *
          RbrLayerStep.classBudget (nl := nl) (w := w) bpair bround bin blig bquery
            (Rounds.Role.indexEquiv.symm i))
    (hlen : 1 ≤ Rounds.Role.length nl w)
    (ht₁ : commitFuel ≤ T)
    (hT : 2 * n + (revealFuel + respondFuel) + commitFuel ≤ T) (hT1 : 1 ≤ T) :
    ((univ.filter fun omega : (Fin T → D) × (Fin (Rounds.Role.length nl w) → C) =>
        CompiledAccepts K A codec (statement omega)
            (challengeOf omega.2) (queryOf omega.2) omega.1 ∧ Fails omega.1).card : ℚ)
        / (Fintype.card (Fin T → D) *
            (Fintype.card C : ℚ) ^ Rounds.Role.length nl w)
      ≤ ((Fintype.card Cand *
            (nl * bpair + (∑ i ∈ Finset.range nl, w i) * bround + bin + blig + bquery) : ℕ) : ℚ)
          / (Fintype.card C : ℚ)
        + (merkleNumerator commitFuel T : ℚ) / (Fintype.card D : ℚ) :=
  by
  refine nizk_ratio_le
    (Acc := fun omega =>
      CompiledAccepts K A codec (statement omega)
          (challengeOf omega.2) (queryOf omega.2) omega.1 ∧
        ExtractionExplains codec dec n commitFuel (revealFuel + respondFuel) T
          A.commit (A.openingStage (challengeOf omega.2) (queryOf omega.2)) omega.1)
    (VerAcc := fun omega =>
      CompiledAccepts K A codec (statement omega)
        (challengeOf omega.2) (queryOf omega.2) omega.1)
    R bpair bround bin blig bquery hb hlen
    ((merkleNumerator commitFuel T : ℚ) / (Fintype.card D : ℚ)) ?_
  -- the two sample spaces are the same number written two ways
  have hden : (Fintype.card (Fin T → D) : ℚ) *
        (Fintype.card C : ℚ) ^ Rounds.Role.length nl w
      = (Fintype.card D : ℚ) ^ T *
        Fintype.card (Fin (Rounds.Role.length nl w) → C) := by
    rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, Fintype.card_fin]
    push_cast
    ring
  rw [hden]
  -- `nizk_ratio_le`'s filters carry a different `DecidablePred` instance for the
  -- same predicate; `congr` is exactly what `Finset.filter_congr_decidable` uses
  convert drop_explains_ratio_le dec K A challengeOf queryOf statement
    (fun omega => Fails omega.1) ht₁ hT hT1 using 3
  congr

/--
**The whole soundness chain, in one statement.**

`nizk_ratio_le_merkle` with `R` and `hb` gone too: the round-by-round family is built from a family
of `RbrLongfellow.LayerStepData`, so every per-round escape count is a theorem *inside* this statement
rather than an input to it.

```
Pr[ the compiled verifier accepts  ∧  extraction fails ]
    ≤  |Cand| · (nl·bpair + (∑ ly, w ly)·bround + bin + blig + bquery) / |C|
       +  merkleNumerator(commitFuel, T) / |D|
```

Three hypotheses remain, and each is a named piece of the protocol rather than of the argument:

* `hfail` — extraction failure means no candidate satisfies the circuit.  Ligero's extractor;
* `hright` — the compiled verifier's acceptance implies LayerStep reaches `.accepted`.  This is the
  transliteration debt of README gap 1, and `RbrLongfellow.rightOfAccepts_of_imp` reduces the whole
  `right_of_accepts` obligation to exactly this implication;
* the three fuel inequalities the Merkle extractor needs.

Every budget numeral is now `LayerStepData`'s: `bpair ≥ kpair·2|F|`, `bround ≥ 2k`, `bin ≥ k`,
`blig ≥ kchal·|escaping|`, `bquery ≥ kq·bq`, in terms of the four decoder balances and
`ligerov3_roundByRound`'s two `Finset`s.
-/
theorem nizk_ratio_le_merkle_longfellow
    [Fintype D] [DecidableEq D] [Inhabited D] [DecidableEq Enc] [Inhabited Salt] [Inhabited M]
    {F X Q Witness : Type} [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F]
    [DecidableEq X] [Fintype Q] [DecidableEq Q] [Nonempty Cand]
    {logw logc nc nv : ℕ}
    {H : RbrLongfellow.Honest F Cand logw logc} {Sat : Cand → Prop} {LigDoomed : X → Prop}
    {codec : Codec Salt M D Enc} (dec : RoleDecoders codec)
    (K : Compiler Statement Oracle Challenge Response Query Opening M n)
    (A : Adversary Enc D Salt M Challenge Response Query Aux Aux'
      n commitFuel respondFuel revealFuel)
    (challengeOf : (Fin (Rounds.Role.length nl w) → C) → Challenge)
    (queryOf : (Fin (Rounds.Role.length nl w) → C) → Query)
    (statement : (Fin T → D) × (Fin (Rounds.Role.length nl w) → C) → Statement)
    {Fails : (Fin T → D) → Prop}
    (bpair bround bin blig bquery : ℕ)
    (Dfam : ∀ _pre : Fin T → D, RbrLongfellow.LayerStepData C F X Q Cand Witness nc nv logw logc nl w
      H Sat LigDoomed bpair bround bin blig bquery)
    (hfail : ∀ pre : Fin T → D, Fails pre → ∀ cand : Cand, ¬ Sat cand)
    (hright : ∀ pre : Fin T → D,
      RbrLongfellow.RightOfAccepts (H := H) Sat LigDoomed (Dfam pre).steps
        (fun tape =>
          CompiledAccepts K A codec (statement (pre, tape))
              (challengeOf tape) (queryOf tape) pre ∧
            ExtractionExplains codec dec n commitFuel (revealFuel + respondFuel) T
              A.commit (A.openingStage (challengeOf tape) (queryOf tape)) pre))
    (hlen : 1 ≤ Rounds.Role.length nl w)
    (ht₁ : commitFuel ≤ T)
    (hT : 2 * n + (revealFuel + respondFuel) + commitFuel ≤ T) (hT1 : 1 ≤ T) :
    ((univ.filter fun omega : (Fin T → D) × (Fin (Rounds.Role.length nl w) → C) =>
        CompiledAccepts K A codec (statement omega)
            (challengeOf omega.2) (queryOf omega.2) omega.1 ∧ Fails omega.1).card : ℚ)
        / (Fintype.card (Fin T → D) *
            (Fintype.card C : ℚ) ^ Rounds.Role.length nl w)
      ≤ ((Fintype.card Cand *
            (nl * bpair + (∑ i ∈ Finset.range nl, w i) * bround + bin + blig + bquery) : ℕ) : ℚ)
          / (Fintype.card C : ℚ)
        + (merkleNumerator commitFuel T : ℚ) / (Fintype.card D : ℚ) :=
  nizk_ratio_le_merkle (Cand := Cand) dec K A challengeOf queryOf statement
    (fun pre => (Dfam pre).rbr (Fails := Fails pre) (hfail pre) (hright pre))
    bpair bround bin blig bquery
    (fun pre i => le_of_eq (congrFun ((Dfam pre).rbr_beta (hfail pre) (hright pre)) i))
    hlen ht₁ hT hT1

end Lfzk.Nizk
