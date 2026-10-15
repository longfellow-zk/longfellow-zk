import Lfzk.RbrSplitS
import Lfzk.NizkAdaptiveTwoField

/-!
# The re-committing Fiat–Shamir bounds at the mixed accounting

`Lfzk.CertifiedV1.Row.adaptive_ratio_le` and `Lfzk.NizkAdaptiveTwoField.twofield_adaptive_ratio_le`
charge every Fiat–Shamir query point `|Cand| · classBudget role`, so the two Ligero slots pay the
list factor that `Lfzk.RbrSplitS` shows they do not owe.  This file restates both at the mixed
accounting: a point pays `|Cand| · b` at a field role and `blig` / `bquery` at a Ligero role
(`RbrSplitS.escapesAt_cardS`).  The adversary, the verifier, the Merkle side and every premise are
those of the two theorems; only the bound changes.

## The bound

`CostV1.Params.nizkBoundS cardCand` is `nizkBound` with the list factor on the field densities only:

```text
cardCand · (2·nl + 2·totalRounds + 1)/|F|  +  (fail + arith)  +  cover  +  merkleTerm
```

and the per-query coefficient `Row.fsCoefficientS = max(cardCand · 2/|F|, fail + arith, cover)`.

```text
Pr[ JointAccepts ∧ Fails ]  ≤  R.boundS + N · R.fsCoefficientS + tape·(L + N)/2^digestBits
                                                                       Row.adaptive_ratio_leS
```

At the certified rows (all by `native_decide`, with the re-commitment terms absorbed):

| row | `boundS` | coefficient | headline |
|---|---|---|---|
| `v8Hash` | `2^-115.50` | `2^-116.94` | `2^-115 + N · 2^-116` (`v8Hash_adaptive_rhs_leS`) |
| `v8Sig` | `2^-122.69` | `2^-122.69` | `2^-122 + N · 2^-122` (`v8Sig_adaptive_rhs_leS`) |
| `p256sha` (two-field) | `2^-115.49` | `2^-116.94` | `2^-115 + N · 2^-116` (`p256sha_adaptive_rhs_leS`) |

against `2^-114 + N · 2^-115` (hash, two-field) and `2^-121 + N · 2^-121` (signature) at the
per-candidate accounting of `NizkAdaptive` / `NizkAdaptiveTwoField`.

## What is still a hypothesis

Exactly the premises of `CertifiedV1.Row.adaptive_ratio_le` and
`NizkAdaptiveTwoField.twofield_adaptive_ratio_le`, which this file takes verbatim.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! ## 1. The bound functions -/

namespace Lfzk.CostV1.Params

/-- **The composed bound at the mixed accounting**: the list factor on the field densities only. -/
def nizkBoundS (P : Params) (cardCand commitFuel T : ℕ) : ℚ :=
  (cardCand : ℚ) * P.fieldDensity + P.ligeroDensity + P.merkleTerm commitFuel T

end Lfzk.CostV1.Params

namespace Lfzk.CertifiedV1

open Finset Bcs Bcs.AdaptiveCommit Merkle Merkle.MH Merkle.RandomOracle
  Merkle.RandomOracle.TwoOracleTree RbrLongfellow Lfzk.NizkGrinding Lfzk.NizkAdaptive
  Lfzk.RbrLayerStepS
open scoped Classical

/-- The row's bound at the mixed accounting. -/
def Row.boundS (R : Row) : ℚ := R.params.nizkBoundS R.cardCand R.commitFuel R.tape

/-- The worst slot's density at the mixed accounting, at a list size `cardCand`: a field slot's
`cardCand · 2/|F|`, the Ligero challenge slot's `fail + arith`, the query slot's `cover`. -/
def Row.maxDensityAt (R : Row) (cardCand : ℕ) : ℚ :=
  max (max ((cardCand : ℚ) * (2 / (R.params.row.fieldSize : ℚ)))
    (R.params.row.fail + R.params.row.arith)) R.params.row.cover

/-- **The work-normalized coefficient at the mixed accounting**: what one hash query can buy. -/
def Row.fsCoefficientS (R : Row) : ℚ := R.maxDensityAt R.cardCand

/-- **The budgets, in densities, at the mixed accounting.** -/
theorem budgets_le_boundS (R : Row) {cardC cardCand cardD : ℕ} (hC : 0 < cardC)
    (hF : 0 < R.params.row.fieldSize) (hD : cardD = 2 ^ R.params.digestBits) :
    ((cardCand * (R.params.nl * pairBudget cardC R.params.row.fieldSize
          + (∑ i ∈ Finset.range R.params.nl, R.params.rounds i)
            * pairBudget cardC R.params.row.fieldSize
          + inBudget cardC R.params.row.fieldSize) + ligBudget R.params.row cardC
          + queryBudget R.params.row cardC : ℕ) : ℚ) / (cardC : ℚ)
        + (merkleNumerator R.commitFuel R.tape : ℚ) / (cardD : ℚ)
      ≤ R.params.nizkBoundS cardCand R.commitFuel R.tape := by
  have hc : (0 : ℚ) < (cardC : ℚ) := by exact_mod_cast hC
  have hf : (0 : ℚ) < (R.params.row.fieldSize : ℚ) := by exact_mod_cast hF
  set f : ℚ := (R.params.row.fieldSize : ℚ)
  set c : ℚ := (cardC : ℚ)
  have hfa := add_nonneg (LigeroV1LayerStep.fail_nonneg R.params.row)
    (LigeroV1LayerStep.arith_nonneg R.params.row)
  have hcv := LigeroV1LayerStep.cover_nonneg R.params.row
  have hbp : (pairBudget cardC R.params.row.fieldSize : ℚ) ≤ c * (2 / f) := by
    unfold pairBudget
    refine le_trans (Nat.cast_div_le) (le_of_eq ?_)
    push_cast
    ring
  have hbi : (inBudget cardC R.params.row.fieldSize : ℚ) ≤ c * (1 / f) := by
    unfold inBudget
    refine le_trans (Nat.cast_div_le) (le_of_eq ?_)
    ring
  have hbl : (ligBudget R.params.row cardC : ℚ) ≤ c * (R.params.row.fail + R.params.row.arith) := by
    unfold ligBudget
    refine le_trans (Nat.floor_le (mul_nonneg hfa (Nat.cast_nonneg _))) (le_of_eq ?_)
    ring
  have hbq : (queryBudget R.params.row cardC : ℚ) ≤ c * R.params.row.cover := by
    unfold queryBudget
    refine le_trans (Nat.floor_le (mul_nonneg hcv (Nat.cast_nonneg _))) (le_of_eq ?_)
    ring
  have hS : (∑ i ∈ Finset.range R.params.nl, R.params.rounds i) = R.params.totalRounds := rfl
  have hfield :
      ((R.params.nl * pairBudget cardC R.params.row.fieldSize
          + (∑ i ∈ Finset.range R.params.nl, R.params.rounds i)
            * pairBudget cardC R.params.row.fieldSize
          + inBudget cardC R.params.row.fieldSize : ℕ) : ℚ)
        ≤ c * R.params.fieldDensity := by
    rw [hS]
    push_cast
    have h1 : (R.params.nl : ℚ) * (pairBudget cardC R.params.row.fieldSize : ℚ)
        ≤ (R.params.nl : ℚ) * (c * (2 / f)) :=
      mul_le_mul_of_nonneg_left hbp (Nat.cast_nonneg _)
    have h2 : (R.params.totalRounds : ℚ) * (pairBudget cardC R.params.row.fieldSize : ℚ)
        ≤ (R.params.totalRounds : ℚ) * (c * (2 / f)) :=
      mul_le_mul_of_nonneg_left hbp (Nat.cast_nonneg _)
    have hrhs : c * R.params.fieldDensity
        = (R.params.nl : ℚ) * (c * (2 / f)) + (R.params.totalRounds : ℚ) * (c * (2 / f))
          + c * (1 / f) := by
      unfold Lfzk.CostV1.Params.fieldDensity
      push_cast
      field_simp
      ring
    rw [hrhs]
    linarith
  have hmerkle : (merkleNumerator R.commitFuel R.tape : ℚ) / (cardD : ℚ)
      = R.params.merkleTerm R.commitFuel R.tape := by
    unfold Lfzk.CostV1.Params.merkleTerm
    rw [hD]
    push_cast
    rfl
  unfold Lfzk.CostV1.Params.nizkBoundS
  rw [hmerkle]
  refine add_le_add ?_ le_rfl
  rw [div_le_iff₀ hc]
  have hk := mul_le_mul_of_nonneg_left hfield (Nat.cast_nonneg cardCand : (0 : ℚ) ≤ cardCand)
  have hlig : R.params.ligeroDensity = (R.params.row.fail + R.params.row.arith)
      + R.params.row.cover := rfl
  push_cast
  push_cast at hk
  rw [hlig]
  nlinarith [hk, hbl, hbq]

/-- **Every slot's mixed budget is at most `|C|` times the mixed worst density.** -/
theorem maxBudget_le_densityS (R : Row) {cardC cardCand : ℕ} (hC : 0 < cardC)
    (hF : 0 < R.params.row.fieldSize) :
    (maxBudget (cardCand * pairBudget cardC R.params.row.fieldSize)
        (cardCand * pairBudget cardC R.params.row.fieldSize)
        (cardCand * inBudget cardC R.params.row.fieldSize) (ligBudget R.params.row cardC)
        (queryBudget R.params.row cardC) : ℚ)
      ≤ (cardC : ℚ) * R.maxDensityAt cardCand := by
  have hc : (0 : ℚ) < (cardC : ℚ) := by exact_mod_cast hC
  have hf : (0 : ℚ) < (R.params.row.fieldSize : ℚ) := by exact_mod_cast hF
  set f : ℚ := (R.params.row.fieldSize : ℚ)
  set c : ℚ := (cardC : ℚ)
  set k : ℚ := (cardCand : ℚ)
  have hk : (0 : ℚ) ≤ k := Nat.cast_nonneg _
  have hfa := add_nonneg (LigeroV1LayerStep.fail_nonneg R.params.row)
    (LigeroV1LayerStep.arith_nonneg R.params.row)
  have hcv := LigeroV1LayerStep.cover_nonneg R.params.row
  have hbp : (pairBudget cardC R.params.row.fieldSize : ℚ) ≤ c * (2 / f) := by
    unfold pairBudget
    refine le_trans (Nat.cast_div_le) (le_of_eq ?_)
    push_cast
    ring
  have hbi : (inBudget cardC R.params.row.fieldSize : ℚ) ≤ c * (2 / f) := by
    unfold inBudget
    refine le_trans (Nat.cast_div_le) ?_
    rw [show c * (2 / f) = 2 * (c / f) by ring]
    have : 0 ≤ c / f := by positivity
    linarith
  have hbl : (ligBudget R.params.row cardC : ℚ) ≤ c * (R.params.row.fail + R.params.row.arith) := by
    unfold ligBudget
    refine le_trans (Nat.floor_le (mul_nonneg hfa (Nat.cast_nonneg _))) (le_of_eq ?_)
    ring
  have hbq : (queryBudget R.params.row cardC : ℚ) ≤ c * R.params.row.cover := by
    unfold queryBudget
    refine le_trans (Nat.floor_le (mul_nonneg hcv (Nat.cast_nonneg _))) (le_of_eq ?_)
    ring
  have h1 : c * (k * (2 / f)) ≤ c * R.maxDensityAt cardCand :=
    mul_le_mul_of_nonneg_left (le_trans (le_max_left _ _) (le_max_left _ _)) hc.le
  have h2 : c * (R.params.row.fail + R.params.row.arith) ≤ c * R.maxDensityAt cardCand :=
    mul_le_mul_of_nonneg_left (le_trans (le_max_right _ _) (le_max_left _ _)) hc.le
  have h3 : c * R.params.row.cover ≤ c * R.maxDensityAt cardCand :=
    mul_le_mul_of_nonneg_left (le_max_right _ _) hc.le
  have hkp : k * (pairBudget cardC R.params.row.fieldSize : ℚ) ≤ c * (k * (2 / f)) := by
    have := mul_le_mul_of_nonneg_left hbp hk
    linarith
  have hki : k * (inBudget cardC R.params.row.fieldSize : ℚ) ≤ c * (k * (2 / f)) := by
    have := mul_le_mul_of_nonneg_left hbi hk
    linarith
  unfold maxBudget
  push_cast
  refine max_le (max_le (max_le (max_le ?_ ?_) ?_) ?_) ?_ <;> linarith

/-! ## 2. One field, a re-committing prover -/

/--
**A certified V1 row against a re-committing Fiat–Shamir prover, at the mixed accounting.**

`Row.adaptive_ratio_le` with the same premises and the list factor dropped at the two Ligero slots:

```text
Pr[ JointAccepts  ∧  Fails(context of the proof's root) ]
    ≤  R.boundS  +  N · R.fsCoefficientS  +  R.tape · (L + N) / 2^digestBits
```
-/
theorem Row.adaptive_ratio_leS {R : Row} (h : R.Valid)
    {C Cand : Type} [Fintype C] [DecidableEq C] [Nonempty C] [Fintype Cand] [Nonempty Cand]
    {F Equations Witness : Type} [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F]
    [Fintype Equations] [DecidableEq Equations]
    {logw logc nc nv : ℕ}
    {Statement Oracle Challenge Response Query : Type} {Opening : Query → Type}
    {Enc D Salt M : Type} {n : ℕ}
    [Fintype D] [DecidableEq D] [Inhabited D] [DecidableEq Enc] [Inhabited Salt] [Inhabited M]
    {Msg Out : Type} [DecidableEq Msg] [Inhabited Msg] {tA N : ℕ}
    {codec : Codec Salt M D Enc} (dec : RoleDecoders codec)
    (K : Compiler Statement Oracle Challenge Response Query Opening M n)
    (body : TwoOracleTree Enc D (Point D Msg C R.params.nl R.params.rounds) C Out tA N)
    (dflt : C) (rootOf : Out → D) (msgOf : Out → ℕ → Msg)
    (claimOf : Out → OpeningClaim n Salt M D)
    (statementOf : Out → (Fin (Rounds.Role.length R.params.nl R.params.rounds) → C) → Statement)
    (responseOf : Out → Response)
    (challengeOf : Out → (Fin (Rounds.Role.length R.params.nl R.params.rounds) → C) → Challenge)
    (queryOf : Out → (Fin (Rounds.Role.length R.params.nl R.params.rounds) → C) → Query)
    {Fails : D × List (Enc × D) → Prop}
    (hF : Fintype.card F = R.params.row.fieldSize)
    (accR : ∀ _κ : D × List (Enc × D), ∀ m : ℕ, (Fin m → C) → Msg →
      LigeroV1LayerStep.Chal F Equations R.params.nw R.params.nq →
        Finset (LigeroV1LayerStep.Qry R.params.row))
    (hlig : ∀ κ, Fails κ →
      ∃ (LigDoomed : LigeroV1LayerStep.Chal F Equations R.params.nw R.params.nq → Prop)
        (ML : MsgLigeroData C (LigeroV1LayerStep.Chal F Equations R.params.nw R.params.nq)
          (LigeroV1LayerStep.Qry R.params.row) Msg LigDoomed),
        ML.accepting = accR κ ∧
        (ML.escaping.card : ℚ) ≤ (R.params.row.fail + R.params.row.arith)
          * Fintype.card (LigeroV1LayerStep.Chal F Equations R.params.nw R.params.nq) ∧
        ML.bq = LigeroV1LayerStep.queryCount R.params.row)
    (H : ∀ _κ : D × List (Enc × D), RbrLongfellow.Honest F Cand logw logc)
    (Sat : D × List (Enc × D) → Cand → Prop)
    (Ffam : ∀ κ, RbrSplit.FieldData C F (LigeroV1LayerStep.Chal F Equations R.params.nw R.params.nq)
        (LigeroV1LayerStep.Qry R.params.row) Cand Witness nc nv logw logc (H κ) (Sat κ))
    (hexact : ∀ κ, (Ffam κ).Exact)
    (MD : ∀ κ, MsgData C Msg (H κ))
    (hfail : ∀ κ, Fails κ → ∀ cand : Cand, ¬ Sat κ cand)
    (hright : ∀ (mt : Fin R.tape → D) (ct : Fin (R.fsLen N) → C),
      Fails ((lfSetup body dflt rootOf msgOf).context mt ct) →
      JointAccepts K codec (lfSetup body dflt rootOf msgOf) (lfCheck codec claimOf) rootOf claimOf
        statementOf responseOf challengeOf queryOf mt ct →
      (lfSetup body dflt rootOf msgOf).Explains dec id claimOf mt ct →
      RbrSplit.LayerStepAccepts
        (RbrSplit.stepsOf (nl := R.params.nl) (w := R.params.rounds)
          (withMsgs (Ffam ((lfSetup body dflt rootOf msgOf).context mt ct))
            (MD ((lfSetup body dflt rootOf msgOf).context mt ct))
            (msgOf ((lfSetup body dflt rootOf msgOf).proof mt ct)))
          (fun m pref => accR ((lfSetup body dflt rootOf msgOf).context mt ct) m pref
            (msgOf ((lfSetup body dflt rootOf msgOf).proof mt ct) m)))
        ((lfSetup body dflt rootOf msgOf).challenges mt ct))
    (htA : tA ≤ R.commitFuel) (htape : 2 * n + tA ≤ R.tape)
    (hcand : Fintype.card Cand = R.cardCand)
    (hD : Fintype.card D = 2 ^ R.params.digestBits) :
    ((univ.filter fun ω : (Fin R.tape → D) × (Fin (R.fsLen N) → C) =>
        JointAccepts K codec (lfSetup body dflt rootOf msgOf) (lfCheck codec claimOf) rootOf
            claimOf statementOf responseOf challengeOf queryOf ω.1 ω.2 ∧
          Fails ((lfSetup body dflt rootOf msgOf).context ω.1 ω.2)).card : ℚ)
        / ((Fintype.card D : ℚ) ^ R.tape * (Fintype.card C : ℚ) ^ R.fsLen N)
      ≤ R.boundS + N * R.fsCoefficientS
        + ((R.tape * (Rounds.Role.length R.params.nl R.params.rounds + N) : ℕ) : ℚ)
          / 2 ^ R.params.digestBits := by
  classical
  set S := lfSetup body dflt rootOf msgOf with hS
  choose LigD ML hacc hesc hbq using hlig
  have hFpos : 0 < R.params.row.fieldSize := by rw [← hF]; exact Fintype.card_pos
  have hCpos : 0 < Fintype.card C := Fintype.card_pos
  have ep : 2 * Fintype.card C / Fintype.card F
      = pairBudget (Fintype.card C) R.params.row.fieldSize := by rw [hF]; rfl
  have ei : Fintype.card C / Fintype.card F
      = inBudget (Fintype.card C) R.params.row.fieldSize := by rw [hF]; rfl
  set bp := pairBudget (Fintype.card C) R.params.row.fieldSize
  set bi := inBudget (Fintype.card C) R.params.row.fieldSize
  set bl := ligBudget R.params.row (Fintype.card C)
  set bq := queryBudget R.params.row (Fintype.card C)
  have hB : ∀ (κ : D × List (Enc × D)) (hκ : Fails κ),
      MsgBudgets (Ffam κ) (ML κ hκ) bp bp bi bl bq := by
    intro κ hκ
    obtain ⟨hp0, hp1, hr, hi⟩ := (hexact κ).field_budgets
    obtain ⟨-, -, hchal, hqq⟩ := hexact κ
    refine ⟨hp0.trans_eq ep, hp1.trans_eq ep, hr.trans_eq ep, hi.trans_eq ei,
      LigeroV1LayerStep.mul_le_floor (add_nonneg (LigeroV1LayerStep.fail_nonneg _)
        (LigeroV1LayerStep.arith_nonneg _)) (hesc κ hκ) hchal, ?_⟩
    rw [hbq κ hκ]
    exact LigeroV1LayerStep.queryBudget_le hqq
  obtain ⟨Bad, hBad⟩ : ∃ Bad : D × List (Enc × D) → Point D Msg C R.params.nl R.params.rounds →
      C → Prop, Bad = fun κ q c => ∃ hκ : Fails κ, DoomedAt (Ffam κ) (MD κ) (ML κ hκ) dflt q ∧
        EscapesAt (Ffam κ) (MD κ) (ML κ hκ) dflt q c := ⟨_, rfl⟩
  -- the mixed per-point budget
  let beta : Point D Msg C R.params.nl R.params.rounds → ℕ := fun q =>
    mixedBudget (nl := R.params.nl) (w := R.params.rounds) (Fintype.card Cand) bp bp bi bl bq q.role
  have hbad : ∀ κ q, (univ.filter fun c : C => Bad κ q c).card ≤ beta q := by
    intro κ q
    by_cases hκ : Fails κ
    · by_cases hd : DoomedAt (Ffam κ) (MD κ) (ML κ hκ) dflt q
      · refine le_trans (Finset.card_le_card ?_)
          (RbrSplitS.escapesAt_cardS (Ffam κ) (MD κ) (ML κ hκ) (hB κ hκ) dflt q hd)
        intro c hc
        simp only [mem_filter, mem_univ, true_and, hBad] at hc ⊢
        obtain ⟨_, _, he⟩ := hc
        exact he
      · refine le_trans (Finset.card_le_card (t := (∅ : Finset C)) ?_) (by simp)
        intro c hc
        simp only [mem_filter, mem_univ, true_and, hBad] at hc
        obtain ⟨_, hd', _⟩ := hc
        exact absurd hd' hd
    · refine le_trans (Finset.card_le_card (t := (∅ : Finset C)) ?_) (by simp)
      intro c hc
      simp only [mem_filter, mem_univ, true_and, hBad] at hc
      obtain ⟨hκ', _⟩ := hc
      exact absurd hκ' hκ
  set βmax := NizkGrinding.maxBudget (Fintype.card Cand * bp) (Fintype.card Cand * bp)
    (Fintype.card Cand * bi) bl bq with hβmax
  have hmax : ∀ q, beta q ≤ βmax := fun q => classBudget_le_max q.role
  let slotBeta : Fin (Rounds.Role.length R.params.nl R.params.rounds) → ℕ := fun i =>
    mixedBudget (nl := R.params.nl) (w := R.params.rounds) (Fintype.card Cand) bp bp bi bl bq
      (Rounds.Role.indexEquiv.symm i)
  have hslot : ∀ (out : Out) (i : Fin (Rounds.Role.length R.params.nl R.params.rounds))
      (cp : Fin i.val → C),
      beta (S.hashInput out i.val cp) ≤ slotBeta i := by
    intro out i cp
    show mixedBudget (nl := R.params.nl) (w := R.params.rounds) (Fintype.card Cand) bp bp bi bl bq
        (roleAt i.val) ≤ _
    rw [roleAt_val]
  have hsum : ∑ i, slotBeta i
      = Fintype.card Cand * (R.params.nl * bp
          + (∑ i ∈ Finset.range R.params.nl, R.params.rounds i) * bp + bi) + bl + bq :=
    mixed_budget_sum (nl := R.params.nl) (w := R.params.rounds) _ _ _ _ _ _
  have hchain : ∀ (mt : Fin R.tape → D) (ct : Fin (R.fsLen N) → C),
      JointAccepts K codec S (lfCheck codec claimOf) rootOf claimOf statementOf responseOf
        challengeOf queryOf mt ct →
      S.Explains dec id claimOf mt ct → Fails (S.context mt ct) →
      (S.grinding mt Bad beta hbad).RoundBad ct := by
    intro mt ct hacc' hexp hκ
    set κ := S.context mt ct with hκdef
    set out := S.proof mt ct
    set ch := S.challenges mt ct
    have hlayerStep := hright mt ct hκ hacc' hexp
    rw [← hacc κ hκ] at hlayerStep
    let hR := layerStepRbr (nl := R.params.nl) (w := R.params.rounds) (Ffam κ) (MD κ) (ML κ hκ)
      (hB κ hκ) (Fails := Fails κ) (hfail κ) (msgOf out)
    obtain ⟨k, hd, he⟩ := hR.exists_escape ch (hR.doomed_start hκ _)
      (hR.accepts_undoomed ch hlayerStep)
    obtain ⟨hdq, hesq⟩ := link_at (Ffam κ) (MD κ) (ML κ hκ) dflt (rootOf out) msgOf out k.val
      (Sumcheck.extract_prefix ch k) (ch k) k.isLt hd he
    refine ⟨k, ?_⟩
    subst hBad
    exact ⟨hκ, hdq, hesq⟩
  have hgen := S.ratio_le codec dec (lfCheck codec claimOf) id claimOf (lfCheck_trace codec claimOf)
    Bad beta hbad βmax hmax slotBeta hslot (length_pos R) (by omega) htape
    (by have := Row.fuel_room h; omega) le_rfl
    (fun mt ct => JointAccepts K codec S (lfCheck codec claimOf) rootOf claimOf statementOf
      responseOf challengeOf queryOf mt ct) Fails (fun mt ct hacc' => hacc'.2.1) hchain
  refine le_trans hgen ?_
  -- the densities
  have hc : (0 : ℚ) < (Fintype.card C : ℚ) := by exact_mod_cast hCpos
  have hseq := budgets_le_boundS R hCpos hFpos (cardCand := Fintype.card Cand) hD
  have hmaxd := maxBudget_le_densityS R hCpos hFpos (cardCand := Fintype.card Cand)
  have hnum := adaptiveNumerator_le
    (Lfs := Rounds.Role.length R.params.nl R.params.rounds + N) htA htape
  have hDq : (Fintype.card D : ℚ) = 2 ^ R.params.digestBits := by rw [hD]; push_cast; rfl
  have hDpos : (0 : ℚ) < (Fintype.card D : ℚ) := by exact_mod_cast Fintype.card_pos
  have hnumq : (adaptiveNumerator (2 * n) tA
        (Rounds.Role.length R.params.nl R.params.rounds + N) : ℚ) / (Fintype.card D : ℚ)
      ≤ (merkleNumerator R.commitFuel R.tape : ℚ) / (Fintype.card D : ℚ)
        + ((R.tape * (Rounds.Role.length R.params.nl R.params.rounds + N) : ℕ) : ℚ)
          / 2 ^ R.params.digestBits := by
    rw [← hDq, ← add_div]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hnum) hDpos.le
  rw [hsum]
  have hsplit : ((N * βmax + (Fintype.card Cand * (R.params.nl * bp
          + (∑ i ∈ Finset.range R.params.nl, R.params.rounds i) * bp + bi) + bl + bq) : ℕ) : ℚ)
        / (Fintype.card C : ℚ)
      = ((Fintype.card Cand * (R.params.nl * bp
          + (∑ i ∈ Finset.range R.params.nl, R.params.rounds i) * bp + bi) + bl + bq : ℕ) : ℚ)
          / (Fintype.card C : ℚ)
        + N * ((βmax : ℚ) / (Fintype.card C : ℚ)) := by
    push_cast
    field_simp
    ring
  have hβ : (βmax : ℚ) / (Fintype.card C : ℚ) ≤ R.maxDensityAt (Fintype.card Cand) := by
    rw [div_le_iff₀ hc]
    linarith
  rw [hsplit]
  have hbound : R.boundS = R.params.nizkBoundS (Fintype.card Cand) R.commitFuel R.tape := by
    rw [hcand]; rfl
  have hcoef : R.fsCoefficientS = R.maxDensityAt (Fintype.card Cand) := by
    unfold Row.fsCoefficientS; rw [hcand]
  rw [hbound, hcoef]
  have hN : (0 : ℚ) ≤ N := Nat.cast_nonneg N
  have := mul_le_mul_of_nonneg_left hβ hN
  linarith

/-! ## 3. The certified rows, one field -/

/-- **The v8 hash row's mixed bound plus the re-commitment term at `N = 0`**: at most `2^-115`. -/
theorem v8Hash_adaptive_slack_boundS :
    v8Hash.boundS
        + ((v8Hash.tape * Rounds.Role.length v8Hash.params.nl v8Hash.params.rounds
            : ℕ) : ℚ) / 2 ^ v8Hash.params.digestBits
      ≤ (1 : ℚ) / 2 ^ 115 := by
  native_decide

/-- **The v8 hash row's mixed coefficient plus the per-query re-commitment term**: at most
`2^-116`. -/
theorem v8Hash_adaptive_slack_coeffS :
    v8Hash.fsCoefficientS + (v8Hash.tape : ℚ) / 2 ^ v8Hash.params.digestBits
      ≤ (1 : ℚ) / 2 ^ 116 := by
  native_decide

/-- `115` is the mixed bound's exact integer bit level at the v8 hash row. -/
theorem v8Hash_boundS_sharp : ¬ v8Hash.boundS ≤ (1 : ℚ) / 2 ^ 116 := by
  native_decide

/-- `116` is the mixed coefficient's exact integer bit level at the v8 hash row. -/
theorem v8Hash_fsCoefficientS_sharp : ¬ v8Hash.fsCoefficientS ≤ (1 : ℚ) / 2 ^ 117 := by
  native_decide

/-- **The v8 hash row's numerals at the mixed accounting**: within `2^-115 + N · 2^-116`. -/
theorem v8Hash_adaptive_rhs_leS (N : ℕ) :
    v8Hash.boundS + N * v8Hash.fsCoefficientS
        + ((v8Hash.tape * (Rounds.Role.length v8Hash.params.nl v8Hash.params.rounds + N) : ℕ) : ℚ)
          / 2 ^ v8Hash.params.digestBits
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 116) := by
  have hsb := v8Hash_adaptive_slack_boundS
  have hsc := v8Hash_adaptive_slack_coeffS
  have hsplit : ((v8Hash.tape
        * (Rounds.Role.length v8Hash.params.nl v8Hash.params.rounds + N) : ℕ) : ℚ)
        / 2 ^ v8Hash.params.digestBits
      = ((v8Hash.tape * Rounds.Role.length v8Hash.params.nl v8Hash.params.rounds
          : ℕ) : ℚ) / 2 ^ v8Hash.params.digestBits
        + N * ((v8Hash.tape : ℚ) / 2 ^ v8Hash.params.digestBits) := by
    push_cast
    ring
  rw [hsplit]
  have hN : (0 : ℚ) ≤ N := Nat.cast_nonneg N
  have := mul_le_mul_of_nonneg_left hsc hN
  nlinarith

/-- **The v8 signature row's mixed bound plus the re-commitment term at `N = 0`**: at most
`2^-122`. -/
theorem v8Sig_adaptive_slack_boundS :
    v8Sig.boundS
        + ((v8Sig.tape * Rounds.Role.length v8Sig.params.nl v8Sig.params.rounds
            : ℕ) : ℚ) / 2 ^ v8Sig.params.digestBits
      ≤ (1 : ℚ) / 2 ^ 122 := by
  native_decide

/-- **The v8 signature row's mixed coefficient plus the per-query re-commitment term**: at most
`2^-122`. -/
theorem v8Sig_adaptive_slack_coeffS :
    v8Sig.fsCoefficientS + (v8Sig.tape : ℚ) / 2 ^ v8Sig.params.digestBits
      ≤ (1 : ℚ) / 2 ^ 122 := by
  native_decide

/-- `122` is the mixed bound's exact integer bit level at the v8 signature row. -/
theorem v8Sig_boundS_sharp : ¬ v8Sig.boundS ≤ (1 : ℚ) / 2 ^ 123 := by
  native_decide

/-- **The v8 signature row's numerals at the mixed accounting**: within `2^-122 + N · 2^-122`. -/
theorem v8Sig_adaptive_rhs_leS (N : ℕ) :
    v8Sig.boundS + N * v8Sig.fsCoefficientS
        + ((v8Sig.tape * (Rounds.Role.length v8Sig.params.nl v8Sig.params.rounds + N) : ℕ) : ℚ)
          / 2 ^ v8Sig.params.digestBits
      ≤ (1 : ℚ) / 2 ^ 122 + N * ((1 : ℚ) / 2 ^ 122) := by
  have hsb := v8Sig_adaptive_slack_boundS
  have hsc := v8Sig_adaptive_slack_coeffS
  have hsplit : ((v8Sig.tape
        * (Rounds.Role.length v8Sig.params.nl v8Sig.params.rounds + N) : ℕ) : ℚ)
        / 2 ^ v8Sig.params.digestBits
      = ((v8Sig.tape * Rounds.Role.length v8Sig.params.nl v8Sig.params.rounds
          : ℕ) : ℚ) / 2 ^ v8Sig.params.digestBits
        + N * ((v8Sig.tape : ℚ) / 2 ^ v8Sig.params.digestBits) := by
    push_cast
    ring
  rw [hsplit]
  have hN : (0 : ℚ) ≤ N := Nat.cast_nonneg N
  have := mul_le_mul_of_nonneg_left hsc hN
  nlinarith

end Lfzk.CertifiedV1

/-! ## 4. Two fields, one re-committing prover, at the mixed accounting -/

namespace Lfzk.NizkAdaptiveTwoField

open Finset Bcs Bcs.AdaptiveCommit Merkle Merkle.MH Merkle.RandomOracle
  Merkle.RandomOracle.TwoOracleTree RbrLongfellow Lfzk.NizkGrinding Lfzk.NizkAdaptive
  Lfzk.CertifiedV1 Lfzk.Mac Lfzk.RbrLayerStepS
open scoped Classical

section ComposeS

variable {R₁ R₂ : Row}
variable {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]
variable {D : Type} [Fintype D] [DecidableEq D] [Inhabited D]
variable {Enc X Out : Type} [DecidableEq Enc]
variable {Fmac : Type} [Field Fmac] [Fintype Fmac] [DecidableEq Fmac] {nblk : ℕ}
variable {Cand₁ F₁ Equations₁ Witness₁ Msg₁ : Type} [Fintype Cand₁] [Nonempty Cand₁] [Field F₁]
  [Fintype F₁] [DecidableEq F₁] [SumcheckInterp F₁] [Fintype Equations₁] [DecidableEq Equations₁]
  [Inhabited Msg₁] {nc₁ nv₁ logw₁ logc₁ : ℕ}
variable {Cand₂ F₂ Equations₂ Witness₂ Msg₂ : Type} [Fintype Cand₂] [Nonempty Cand₂] [Field F₂]
  [Fintype F₂] [DecidableEq F₂] [SumcheckInterp F₂] [Fintype Equations₂] [DecidableEq Equations₂]
  [Inhabited Msg₂] {nc₂ nv₂ logw₂ logc₂ : ℕ}
variable {Statement₁ Oracle₁ Challenge₁ Response₁ Query₁ : Type} {Opening₁ : Query₁ → Type}
variable {Statement₂ Oracle₂ Challenge₂ Response₂ Query₂ : Type} {Opening₂ : Query₂ → Type}
variable {Salt₁ M₁ Salt₂ M₂ : Type} [Inhabited Salt₁] [Inhabited M₁] [Inhabited Salt₂]
  [Inhabited M₂] {n₁ n₂ : ℕ}

/--
**Two-field Longfellow against one re-committing Fiat–Shamir prover, at the mixed accounting.**

`twofield_adaptive_ratio_le` with the same premises; each side's Ligero slots pay no list factor:

```text
Pr[ both compiled verifiers accept  ∧  no two good witnesses agree on the common value ]
    ≤  R₁.boundS + R₂.boundS + 1/|Fmac|  +  N · max(κS₁, κS₂, 1/|Fmac|)
       +  2 · R₁.tape · (1 + L₁ + L₂ + N) / 2^digestBits
```
-/
theorem twofield_adaptive_ratio_leS (h₁ : R₁.Valid) {tA N : ℕ}
    {codec₁ : Codec Salt₁ M₁ D Enc} (dec₁ : RoleDecoders codec₁)
    {codec₂ : Codec Salt₂ M₂ D Enc} (dec₂ : RoleDecoders codec₂)
    (K₁ : Compiler Statement₁ Oracle₁ Challenge₁ Response₁ Query₁ Opening₁ M₁ n₁)
    (K₂ : Compiler Statement₂ Oracle₂ Challenge₂ Response₂ Query₂ Opening₂ M₂ n₂)
    (body : TwoOracleTree Enc D (Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds
      R₂.params.rounds) C Out tA N)
    (dflt : C) (rootOf₁ rootOf₂ : Out → D) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim n₁ Salt₁ M₁ D) (claimOf₂ : Out → OpeningClaim n₂ Salt₂ M₂ D)
    (statementOf₁ : Out → (Fin (len2 R₁ R₂) → C) → Statement₁) (responseOf₁ : Out → Response₁)
    (challengeOf₁ : Out → (Fin (len2 R₁ R₂) → C) → Challenge₁)
    (queryOf₁ : Out → (Fin (len2 R₁ R₂) → C) → Query₁)
    (statementOf₂ : Out → (Fin (len2 R₁ R₂) → C) → Statement₂) (responseOf₂ : Out → Response₂)
    (challengeOf₂ : Out → (Fin (len2 R₁ R₂) → C) → Challenge₂)
    (queryOf₂ : Out → (Fin (len2 R₁ R₂) → C) → Query₂)
    (S₁ : Side R₁ (((D × D) × List (Enc × D)) × C × X) C Cand₁ F₁ Equations₁ Witness₁ Msg₁
      nc₁ nv₁ logw₁ logc₁)
    (S₂ : Side R₂ (((D × D) × List (Enc × D)) × C × X) C Cand₂ F₂ Equations₂ Witness₂ Msg₂
      nc₂ nv₂ logw₂ logc₂)
    (hF₁ : Fintype.card F₁ = R₁.params.row.fieldSize)
    (hF₂ : Fintype.card F₂ = R₂.params.row.fieldSize)
    (hcand₁ : Fintype.card Cand₁ = R₁.cardCand) (hcand₂ : Fintype.card Cand₂ = R₂.cardCand)
    (hD₁ : Fintype.card D = 2 ^ R₁.params.digestBits)
    (hD₂ : Fintype.card D = 2 ^ R₂.params.digestBits)
    (aP : (D × D) × List (Enc × D) → Fmac) (decode : C → Fmac) (kmac : ℕ)
    (hbal : ∀ x : Fmac, (univ.filter fun c : C => decode c = x).card ≤ kmac)
    (hmac : kmac * Fintype.card Fmac ≤ Fintype.card C)
    (keyB tagOf : Out → Fin nblk → Fmac)
    (common₁ : Witness₁ → Fin nblk → Fmac) (common₂ : Witness₂ → Fin nblk → Fmac)
    (hright₁ : ∀ (mt : Fin R₁.tape → D) (ct : Fin (len2 R₁ R₂ + N) → C),
      let S := setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂
      let σ := (S.context mt ct, S.challenges mt ct ⟨0, by omega⟩, pubOf (S.proof mt ct))
      (∀ cand, ¬ S₁.Sat σ cand) →
      JointAccepts K₁ codec₁ S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ claimOf₁
        statementOf₁ responseOf₁ challengeOf₁ queryOf₁ mt ct →
      S.Explains dec₁ Prod.fst claimOf₁ mt ct →
      RbrSplit.LayerStepAccepts
        (RbrSplit.stepsOf (nl := R₁.params.nl) (w := R₁.params.rounds)
          (withMsgs (S₁.field σ) (S₁.MD σ) (msgOf₁ (S.proof mt ct)))
          (fun m pref => S₁.accR σ m pref (msgOf₁ (S.proof mt ct) m)))
        (fun i => S.challenges mt ct ⟨1 + i.val, by omega⟩))
    (hright₂ : ∀ (mt : Fin R₁.tape → D) (ct : Fin (len2 R₁ R₂ + N) → C),
      let S := setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂
      let σ := (S.context mt ct, S.challenges mt ct ⟨0, by omega⟩, pubOf (S.proof mt ct))
      (∀ cand, ¬ S₂.Sat σ cand) →
      JointAccepts K₂ codec₂ S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ claimOf₂
        statementOf₂ responseOf₂ challengeOf₂ queryOf₂ mt ct →
      S.Explains dec₂ Prod.snd claimOf₂ mt ct →
      RbrSplit.LayerStepAccepts
        (RbrSplit.stepsOf (nl := R₂.params.nl) (w := R₂.params.rounds)
          (withMsgs (S₂.field σ) (S₂.MD σ) (msgOf₂ (S.proof mt ct)))
          (fun m pref => S₂.accR σ m pref (msgOf₂ (S.proof mt ct) m)))
        (fun i => S.challenges mt ct
          ⟨1 + Rounds.Role.length R₁.params.nl R₁.params.rounds + i.val, by omega⟩))
    (hrow₁ : ∀ (mt : Fin R₁.tape → D) (ct : Fin (len2 R₁ R₂ + N) → C) (a : Witness₁),
      let S := setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂
      JointAccepts K₁ codec₁ S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ claimOf₁
        statementOf₁ responseOf₁ challengeOf₁ queryOf₁ mt ct →
      S₁.Good (S.context mt ct, S.challenges mt ct ⟨0, by omega⟩, pubOf (S.proof mt ct)) a →
      macTag (aP (S.context mt ct) + decode (S.challenges mt ct ⟨0, by omega⟩))
        (keyB (S.proof mt ct)) (common₁ a) = tagOf (S.proof mt ct))
    (hrow₂ : ∀ (mt : Fin R₁.tape → D) (ct : Fin (len2 R₁ R₂ + N) → C) (a : Witness₂),
      let S := setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂
      JointAccepts K₂ codec₂ S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ claimOf₂
        statementOf₂ responseOf₂ challengeOf₂ queryOf₂ mt ct →
      S₂.Good (S.context mt ct, S.challenges mt ct ⟨0, by omega⟩, pubOf (S.proof mt ct)) a →
      macTag (aP (S.context mt ct) + decode (S.challenges mt ct ⟨0, by omega⟩))
        (keyB (S.proof mt ct)) (common₂ a) = tagOf (S.proof mt ct))
    (htA₁ : tA ≤ R₁.commitFuel) (htA₂ : tA ≤ R₂.commitFuel)
    (htape : 2 * n₂ + 2 * n₁ + tA ≤ R₁.tape) (htape₂ : R₁.tape = R₂.tape) :
    ((univ.filter fun ω : (Fin R₁.tape → D) × (Fin (len2 R₁ R₂ + N) → C) =>
        JointAccepts K₁ codec₁ (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ claimOf₁ statementOf₁ responseOf₁
            challengeOf₁ queryOf₁ ω.1 ω.2 ∧
          JointAccepts K₂ codec₂ (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ claimOf₂ statementOf₂ responseOf₂
            challengeOf₂ queryOf₂ ω.1 ω.2 ∧
          ¬ ∃ a₁ a₂,
            S₁.Good ((setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂).context ω.1 ω.2,
              (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂).challenges ω.1 ω.2
                ⟨0, by omega⟩,
              pubOf ((setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂).proof ω.1 ω.2)) a₁ ∧
            S₂.Good ((setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂).context ω.1 ω.2,
              (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂).challenges ω.1 ω.2
                ⟨0, by omega⟩,
              pubOf ((setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂).proof ω.1 ω.2)) a₂ ∧
            common₁ a₁ = common₂ a₂).card : ℚ)
        / ((Fintype.card D : ℚ) ^ R₁.tape * (Fintype.card C : ℚ) ^ (len2 R₁ R₂ + N))
      ≤ R₁.boundS + R₂.boundS + 1 / (Fintype.card Fmac : ℚ)
        + N * max (max R₁.fsCoefficientS R₂.fsCoefficientS) (1 / (Fintype.card Fmac : ℚ))
        + 2 * (((R₁.tape * (len2 R₁ R₂ + N) : ℕ) : ℚ) / 2 ^ R₁.params.digestBits) := by
  classical
  set S := setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂ with hS
  choose LigD₁ ML₁ hacc₁ hesc₁ hbq₁ using S₁.hlig
  choose LigD₂ ML₂ hacc₂ hesc₂ hbq₂ using S₂.hlig
  have hCpos : 0 < Fintype.card C := Fintype.card_pos
  have hFpos₁ : 0 < R₁.params.row.fieldSize := by rw [← hF₁]; exact Fintype.card_pos
  have hFpos₂ : 0 < R₂.params.row.fieldSize := by rw [← hF₂]; exact Fintype.card_pos
  set bp₁ := pairBudget (Fintype.card C) R₁.params.row.fieldSize
  set bi₁ := inBudget (Fintype.card C) R₁.params.row.fieldSize
  set bl₁ := ligBudget R₁.params.row (Fintype.card C)
  set bq₁ := queryBudget R₁.params.row (Fintype.card C)
  set bp₂ := pairBudget (Fintype.card C) R₂.params.row.fieldSize
  set bi₂ := inBudget (Fintype.card C) R₂.params.row.fieldSize
  set bl₂ := ligBudget R₂.params.row (Fintype.card C)
  set bq₂ := queryBudget R₂.params.row (Fintype.card C)
  have hB₁ : ∀ σ (hσ : ∀ cand, ¬ S₁.Sat σ cand),
      MsgBudgets (S₁.field σ) (ML₁ σ hσ) bp₁ bp₁ bi₁ bl₁ bq₁ := by
    intro σ hσ
    have ep : 2 * Fintype.card C / Fintype.card F₁ = bp₁ := by rw [hF₁]; rfl
    have ei : Fintype.card C / Fintype.card F₁ = bi₁ := by rw [hF₁]; rfl
    obtain ⟨hp0, hp1, hr, hi⟩ := (S₁.hexact σ).field_budgets
    obtain ⟨-, -, hchal, hqq⟩ := S₁.hexact σ
    refine ⟨hp0.trans_eq ep, hp1.trans_eq ep, hr.trans_eq ep, hi.trans_eq ei,
      LigeroV1LayerStep.mul_le_floor (add_nonneg (LigeroV1LayerStep.fail_nonneg _)
        (LigeroV1LayerStep.arith_nonneg _)) (hesc₁ σ hσ) hchal, ?_⟩
    rw [hbq₁ σ hσ]
    exact LigeroV1LayerStep.queryBudget_le hqq
  have hB₂ : ∀ σ (hσ : ∀ cand, ¬ S₂.Sat σ cand),
      MsgBudgets (S₂.field σ) (ML₂ σ hσ) bp₂ bp₂ bi₂ bl₂ bq₂ := by
    intro σ hσ
    have ep : 2 * Fintype.card C / Fintype.card F₂ = bp₂ := by rw [hF₂]; rfl
    have ei : Fintype.card C / Fintype.card F₂ = bi₂ := by rw [hF₂]; rfl
    obtain ⟨hp0, hp1, hr, hi⟩ := (S₂.hexact σ).field_budgets
    obtain ⟨-, -, hchal, hqq⟩ := S₂.hexact σ
    refine ⟨hp0.trans_eq ep, hp1.trans_eq ep, hr.trans_eq ep, hi.trans_eq ei,
      LigeroV1LayerStep.mul_le_floor (add_nonneg (LigeroV1LayerStep.fail_nonneg _)
        (LigeroV1LayerStep.arith_nonneg _)) (hesc₂ σ hσ) hchal, ?_⟩
    rw [hbq₂ σ hσ]
    exact LigeroV1LayerStep.queryBudget_le hqq
  obtain ⟨Bad, hBad⟩ : ∃ Bad : (D × D) × List (Enc × D) →
      Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds R₂.params.rounds → C → Prop,
      Bad = fun κ q c => Sum.elim (fun _ => aP κ + decode c = 0)
        (Sum.elim
          (fun p => ∃ hσ : (∀ cand, ¬ S₁.Sat (κ, p.ctx.2.1, p.ctx.2.2) cand),
            DoomedAt (S₁.field (κ, p.ctx.2.1, p.ctx.2.2)) (S₁.MD (κ, p.ctx.2.1, p.ctx.2.2))
              (ML₁ (κ, p.ctx.2.1, p.ctx.2.2) hσ) dflt p ∧
            EscapesAt (S₁.field (κ, p.ctx.2.1, p.ctx.2.2)) (S₁.MD (κ, p.ctx.2.1, p.ctx.2.2))
              (ML₁ (κ, p.ctx.2.1, p.ctx.2.2) hσ) dflt p c)
          (fun p => ∃ hσ : (∀ cand, ¬ S₂.Sat (κ, p.ctx.2.1, p.ctx.2.2) cand),
            DoomedAt (S₂.field (κ, p.ctx.2.1, p.ctx.2.2)) (S₂.MD (κ, p.ctx.2.1, p.ctx.2.2))
              (ML₂ (κ, p.ctx.2.1, p.ctx.2.2) hσ) dflt p ∧
            EscapesAt (S₂.field (κ, p.ctx.2.1, p.ctx.2.2)) (S₂.MD (κ, p.ctx.2.1, p.ctx.2.2))
              (ML₂ (κ, p.ctx.2.1, p.ctx.2.2) hσ) dflt p c)) q := ⟨_, rfl⟩
  -- the mixed per-point budget
  let beta : Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds R₂.params.rounds →
      ℕ := Sum.elim (fun _ => kmac) (Sum.elim
    (fun p => mixedBudget (nl := R₁.params.nl) (w := R₁.params.rounds) (Fintype.card Cand₁)
      bp₁ bp₁ bi₁ bl₁ bq₁ p.role)
    (fun p => mixedBudget (nl := R₂.params.nl) (w := R₂.params.rounds) (Fintype.card Cand₂)
      bp₂ bp₂ bi₂ bl₂ bq₂ p.role))
  have hbad : ∀ κ q, (univ.filter fun c : C => Bad κ q c).card ≤ beta q := by
    intro κ q
    rcases q with r | p | p
    · refine le_trans (Finset.card_le_card ?_) (hbal (-aP κ))
      intro c hc
      simp only [mem_filter, mem_univ, true_and, hBad, Sum.elim_inl] at hc ⊢
      linear_combination hc
    · by_cases hσ : ∀ cand, ¬ S₁.Sat (κ, p.ctx.2.1, p.ctx.2.2) cand
      · by_cases hd : DoomedAt (S₁.field (κ, p.ctx.2.1, p.ctx.2.2)) (S₁.MD (κ, p.ctx.2.1, p.ctx.2.2))
            (ML₁ (κ, p.ctx.2.1, p.ctx.2.2) hσ) dflt p
        · refine le_trans (Finset.card_le_card ?_)
            (RbrSplitS.escapesAt_cardS (S₁.field _) (S₁.MD _) (ML₁ _ hσ) (hB₁ _ hσ) dflt p hd)
          intro c hc
          simp only [mem_filter, mem_univ, true_and, hBad, Sum.elim_inr, Sum.elim_inl] at hc ⊢
          obtain ⟨_, _, he⟩ := hc
          exact he
        · refine le_trans (Finset.card_le_card (t := (∅ : Finset C)) ?_) (by simp)
          intro c hc
          simp only [mem_filter, mem_univ, true_and, hBad, Sum.elim_inr, Sum.elim_inl] at hc
          obtain ⟨_, hd', _⟩ := hc
          exact absurd hd' hd
      · refine le_trans (Finset.card_le_card (t := (∅ : Finset C)) ?_) (by simp)
        intro c hc
        simp only [mem_filter, mem_univ, true_and, hBad, Sum.elim_inr, Sum.elim_inl] at hc
        obtain ⟨hσ', _⟩ := hc
        exact absurd hσ' hσ
    · by_cases hσ : ∀ cand, ¬ S₂.Sat (κ, p.ctx.2.1, p.ctx.2.2) cand
      · by_cases hd : DoomedAt (S₂.field (κ, p.ctx.2.1, p.ctx.2.2)) (S₂.MD (κ, p.ctx.2.1, p.ctx.2.2))
            (ML₂ (κ, p.ctx.2.1, p.ctx.2.2) hσ) dflt p
        · refine le_trans (Finset.card_le_card ?_)
            (RbrSplitS.escapesAt_cardS (S₂.field _) (S₂.MD _) (ML₂ _ hσ) (hB₂ _ hσ) dflt p hd)
          intro c hc
          simp only [mem_filter, mem_univ, true_and, hBad, Sum.elim_inr] at hc ⊢
          obtain ⟨_, _, he⟩ := hc
          exact he
        · refine le_trans (Finset.card_le_card (t := (∅ : Finset C)) ?_) (by simp)
          intro c hc
          simp only [mem_filter, mem_univ, true_and, hBad, Sum.elim_inr] at hc
          obtain ⟨_, hd', _⟩ := hc
          exact absurd hd' hd
      · refine le_trans (Finset.card_le_card (t := (∅ : Finset C)) ?_) (by simp)
        intro c hc
        simp only [mem_filter, mem_univ, true_and, hBad, Sum.elim_inr] at hc
        obtain ⟨hσ', _⟩ := hc
        exact absurd hσ' hσ
  set βmax := max kmac (max
    (NizkGrinding.maxBudget (Fintype.card Cand₁ * bp₁) (Fintype.card Cand₁ * bp₁)
      (Fintype.card Cand₁ * bi₁) bl₁ bq₁)
    (NizkGrinding.maxBudget (Fintype.card Cand₂ * bp₂) (Fintype.card Cand₂ * bp₂)
      (Fintype.card Cand₂ * bi₂) bl₂ bq₂)) with hβmax
  have hmax : ∀ q, beta q ≤ βmax := by
    intro q
    rcases q with r | p | p
    · exact le_max_left _ _
    · exact le_trans (classBudget_le_max p.role) (le_trans (le_max_left _ _) (le_max_right _ _))
    · exact le_trans (classBudget_le_max p.role) (le_trans (le_max_right _ _) (le_max_right _ _))
  let g : ℕ → ℕ := fun k =>
    if k = 0 then kmac
    else if k < 1 + Rounds.Role.length R₁.params.nl R₁.params.rounds then
      mixedBudget (nl := R₁.params.nl) (w := R₁.params.rounds) (Fintype.card Cand₁)
        bp₁ bp₁ bi₁ bl₁ bq₁ (roleAt (k - 1))
    else
      mixedBudget (nl := R₂.params.nl) (w := R₂.params.rounds) (Fintype.card Cand₂)
        bp₂ bp₂ bi₂ bl₂ bq₂ (roleAt (k - 1 - Rounds.Role.length R₁.params.nl R₁.params.rounds))
  let slotBeta : Fin (len2 R₁ R₂) → ℕ := fun i => g i.val
  have hslot : ∀ (out : Out) (i : Fin (len2 R₁ R₂)) (cp : Fin i.val → C),
      beta (S.hashInput out i.val cp) ≤ slotBeta i := by
    intro out i cp
    show beta (hash2 rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂ out i.val cp) ≤ g i.val
    unfold hash2
    simp only [g]
    split_ifs <;> exact le_rfl
  have hsum : ∑ i, slotBeta i
      = kmac + (Fintype.card Cand₁ * (R₁.params.nl * bp₁
          + (∑ i ∈ Finset.range R₁.params.nl, R₁.params.rounds i) * bp₁ + bi₁) + bl₁ + bq₁)
        + (Fintype.card Cand₂ * (R₂.params.nl * bp₂
          + (∑ i ∈ Finset.range R₂.params.nl, R₂.params.rounds i) * bp₂ + bi₂) + bl₂ + bq₂) := by
    rw [show (∑ i, slotBeta i) = ∑ i : Fin (len2 R₁ R₂), g i.val from rfl,
      Fin.sum_univ_eq_sum_range g, len2, Finset.sum_range_add, Finset.sum_range_add,
      Finset.sum_range_one]
    have e0 : g 0 = kmac := by simp only [g, if_pos rfl]
    have e1 : ∑ x ∈ range (Rounds.Role.length R₁.params.nl R₁.params.rounds), g (1 + x)
        = ∑ x ∈ range (Rounds.Role.length R₁.params.nl R₁.params.rounds),
          mixedBudget (nl := R₁.params.nl) (w := R₁.params.rounds) (Fintype.card Cand₁)
            bp₁ bp₁ bi₁ bl₁ bq₁ (roleAt x) := by
      refine Finset.sum_congr rfl fun x hx => ?_
      have hx' := Finset.mem_range.mp hx
      simp only [g]
      rw [if_neg (by omega), if_pos (by omega), show 1 + x - 1 = x by omega]
    have e2 : ∑ x ∈ range (Rounds.Role.length R₂.params.nl R₂.params.rounds),
          g (1 + Rounds.Role.length R₁.params.nl R₁.params.rounds + x)
        = ∑ x ∈ range (Rounds.Role.length R₂.params.nl R₂.params.rounds),
          mixedBudget (nl := R₂.params.nl) (w := R₂.params.rounds) (Fintype.card Cand₂)
            bp₂ bp₂ bi₂ bl₂ bq₂ (roleAt x) := by
      refine Finset.sum_congr rfl fun x hx => ?_
      simp only [g]
      rw [if_neg (by omega), if_neg (by omega),
        show 1 + Rounds.Role.length R₁.params.nl R₁.params.rounds + x - 1
          - Rounds.Role.length R₁.params.nl R₁.params.rounds = x by omega]
    rw [e0, e1, e2, sum_roleAt, sum_roleAt, mixed_budget_sum, mixed_budget_sum]
  have hchain : ∀ (mt : Fin R₁.tape → D) (ct : Fin (len2 R₁ R₂ + N) → C),
      (JointAccepts K₁ codec₁ S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ claimOf₁
          statementOf₁ responseOf₁ challengeOf₁ queryOf₁ mt ct ∧
        JointAccepts K₂ codec₂ S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ claimOf₂
          statementOf₂ responseOf₂ challengeOf₂ queryOf₂ mt ct) →
      S.Explains dec₁ Prod.fst claimOf₁ mt ct → S.Explains dec₂ Prod.snd claimOf₂ mt ct →
      (¬ ∃ a₁ a₂,
        S₁.Good (S.context mt ct, S.challenges mt ct ⟨0, by omega⟩, pubOf (S.proof mt ct)) a₁ ∧
        S₂.Good (S.context mt ct, S.challenges mt ct ⟨0, by omega⟩, pubOf (S.proof mt ct)) a₂ ∧
        common₁ a₁ = common₂ a₂) →
      (S.grinding mt Bad beta hbad).RoundBad ct := by
    intro mt ct hacc hex₁ hex₂ hcomp
    set out := S.proof mt ct with hout
    set c₀ := S.challenges mt ct ⟨0, by omega⟩ with hc₀
    set σ := (S.context mt ct, c₀, pubOf out) with hσdef
    by_cases hσ₁ : ∀ cand, ¬ S₁.Sat σ cand
    · have hlayerStep := hright₁ mt ct hσ₁ hacc.1 hex₁
      rw [← hacc₁ σ hσ₁] at hlayerStep
      let ch₁ : Fin (Rounds.Role.length R₁.params.nl R₁.params.rounds) → C :=
        fun i => S.challenges mt ct ⟨1 + i.val, by omega⟩
      let hR := layerStepRbr (nl := R₁.params.nl) (w := R₁.params.rounds) (S₁.field σ) (S₁.MD σ)
        (ML₁ σ hσ₁) (hB₁ σ hσ₁) (Fails := ∀ cand, ¬ S₁.Sat σ cand) (fun h => h) (msgOf₁ out)
      obtain ⟨k₁, hd, he⟩ := hR.exists_escape ch₁ (hR.doomed_start hσ₁ _)
        (hR.accepts_undoomed ch₁ hlayerStep)
      obtain ⟨hdq, hesq⟩ := link_at (S₁.field σ) (S₁.MD σ) (ML₁ σ hσ₁) dflt
        ((rootOf₁ out, rootOf₂ out), c₀, pubOf out) msgOf₁ out k₁.val
        (Sumcheck.extract_prefix ch₁ k₁) (ch₁ k₁) k₁.isLt hd he
      refine ⟨⟨1 + k₁.val, by omega⟩, ?_⟩
      have hpt : (S.grinding mt Bad beta hbad).point ct ⟨1 + k₁.val, by omega⟩
          = Sum.inr (Sum.inl (hashPoint ((rootOf₁ out, rootOf₂ out), c₀, pubOf out) msgOf₁ out
              k₁.val (Sumcheck.extract_prefix ch₁ k₁))) := by
        show hash2 rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂ (S.output mt ct).1 (1 + k₁.val)
          (fun j => (S.output mt ct).2 j.val) = _
        exact hash2_side1 rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂ _ k₁.isLt _
      rw [hpt]
      subst hBad
      exact ⟨hσ₁, hdq, hesq⟩
    by_cases hσ₂ : ∀ cand, ¬ S₂.Sat σ cand
    · have hlayerStep := hright₂ mt ct hσ₂ hacc.2 hex₂
      rw [← hacc₂ σ hσ₂] at hlayerStep
      let ch₂ : Fin (Rounds.Role.length R₂.params.nl R₂.params.rounds) → C :=
        fun i => S.challenges mt ct
          ⟨1 + Rounds.Role.length R₁.params.nl R₁.params.rounds + i.val, by omega⟩
      let hR := layerStepRbr (nl := R₂.params.nl) (w := R₂.params.rounds) (S₂.field σ) (S₂.MD σ)
        (ML₂ σ hσ₂) (hB₂ σ hσ₂) (Fails := ∀ cand, ¬ S₂.Sat σ cand) (fun h => h) (msgOf₂ out)
      obtain ⟨k₂, hd, he⟩ := hR.exists_escape ch₂ (hR.doomed_start hσ₂ _)
        (hR.accepts_undoomed ch₂ hlayerStep)
      obtain ⟨hdq, hesq⟩ := link_at (S₂.field σ) (S₂.MD σ) (ML₂ σ hσ₂) dflt
        ((rootOf₁ out, rootOf₂ out), c₀, pubOf out) msgOf₂ out k₂.val
        (Sumcheck.extract_prefix ch₂ k₂) (ch₂ k₂) k₂.isLt hd he
      refine ⟨⟨1 + Rounds.Role.length R₁.params.nl R₁.params.rounds + k₂.val, by omega⟩, ?_⟩
      have hpt : (S.grinding mt Bad beta hbad).point ct
            ⟨1 + Rounds.Role.length R₁.params.nl R₁.params.rounds + k₂.val, by omega⟩
          = Sum.inr (Sum.inr (hashPoint ((rootOf₁ out, rootOf₂ out), c₀, pubOf out) msgOf₂ out
              k₂.val (Sumcheck.extract_prefix ch₂ k₂))) := by
        show hash2 rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂ (S.output mt ct).1
          (1 + Rounds.Role.length R₁.params.nl R₁.params.rounds + k₂.val)
          (fun j => (S.output mt ct).2 j.val) = _
        exact hash2_side2 rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂ _ _
      rw [hpt]
      subst hBad
      exact ⟨hσ₂, hdq, hesq⟩
    push Not at hσ₁ hσ₂
    obtain ⟨cand₁, hs₁⟩ := hσ₁
    obtain ⟨cand₂, hs₂⟩ := hσ₂
    have hne : common₁ ((S₁.field σ).wOf cand₁) ≠ common₂ ((S₂.field σ).wOf cand₂) :=
      fun heq => hcomp ⟨_, _, ⟨cand₁, hs₁, rfl⟩, ⟨cand₂, hs₂, rfl⟩, heq⟩
    have hm₁ := hrow₁ mt ct _ hacc.1 ⟨cand₁, hs₁, rfl⟩
    have hm₂ := hrow₂ mt ct _ hacc.2 ⟨cand₂, hs₂, rfl⟩
    have hzero := macTag_collision hne (hm₁.trans hm₂.symm)
    refine ⟨⟨0, by omega⟩, ?_⟩
    have hpt : (S.grinding mt Bad beta hbad).point ct ⟨0, by omega⟩
        = Sum.inl (rootOf₁ out, rootOf₂ out) := by
      show hash2 rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂ (S.output mt ct).1 0
        (fun j => (S.output mt ct).2 j.val) = _
      exact hash2_zero rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂ _ _
    rw [hpt]
    subst hBad
    exact hzero
  have hcheck₁ : ∀ (H : Enc → D) (out : Out),
      ∀ qa ∈ ((checkPass codec₁ n₁ (claimOf₁ out).I (claimOf₁ out).a (claimOf₁ out).pf (2 * n₁)
          fun _ => default).run H).2,
        qa ∈ ((check2 codec₁ claimOf₁ codec₂ claimOf₂ out).run H).2 := by
    intro H out qa hqa
    rw [check2, Tree.run_bind]
    exact List.mem_append_left _ (lfCheck_trace codec₁ claimOf₁ H out qa hqa)
  have hcheck₂ : ∀ (H : Enc → D) (out : Out),
      ∀ qa ∈ ((checkPass codec₂ n₂ (claimOf₂ out).I (claimOf₂ out).a (claimOf₂ out).pf (2 * n₂)
          fun _ => default).run H).2,
        qa ∈ ((check2 codec₁ claimOf₁ codec₂ claimOf₂ out).run H).2 := by
    intro H out qa hqa
    rw [check2, Tree.run_bind]
    exact List.mem_append_right _ (lfCheck_trace codec₂ claimOf₂ H out qa hqa)
  have hroom := Row.fuel_room h₁
  have hgen := S.ratio_le_two codec₁ dec₁ codec₂ dec₂ (check2 codec₁ claimOf₁ codec₂ claimOf₂)
    Prod.fst Prod.snd claimOf₁ claimOf₂ hcheck₁ hcheck₂ Bad beta hbad βmax hmax slotBeta hslot
    (by omega) (by omega) htape (by omega) le_rfl
    (fun mt ct => JointAccepts K₁ codec₁ S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁
        claimOf₁ statementOf₁ responseOf₁ challengeOf₁ queryOf₁ mt ct ∧
      JointAccepts K₂ codec₂ S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ claimOf₂
        statementOf₂ responseOf₂ challengeOf₂ queryOf₂ mt ct)
    (fun mt ct => ¬ ∃ a₁ a₂,
      S₁.Good (S.context mt ct, S.challenges mt ct ⟨0, by omega⟩, pubOf (S.proof mt ct)) a₁ ∧
      S₂.Good (S.context mt ct, S.challenges mt ct ⟨0, by omega⟩, pubOf (S.proof mt ct)) a₂ ∧
      common₁ a₁ = common₂ a₂)
    (fun mt ct h => h.1.2.1) (fun mt ct h => h.2.2.1) hchain
  refine le_trans (div_le_div_of_nonneg_right (Nat.cast_le.mpr (Finset.card_le_card ?_))
    (by positivity)) (le_trans hgen ?_)
  · intro ω hω
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
    exact ⟨⟨hω.1, hω.2.1⟩, hω.2.2⟩
  -- the densities
  rw [hsum]
  have hc : (0 : ℚ) < (Fintype.card C : ℚ) := by exact_mod_cast hCpos
  have hDpos : (0 : ℚ) < (Fintype.card D : ℚ) := by exact_mod_cast Fintype.card_pos
  have hseq₁ := budgets_le_boundS R₁ hCpos hFpos₁ (cardCand := Fintype.card Cand₁) hD₁
  have hseq₂ := budgets_le_boundS R₂ hCpos hFpos₂ (cardCand := Fintype.card Cand₂) hD₂
  have hb₁ : R₁.boundS = R₁.params.nizkBoundS (Fintype.card Cand₁) R₁.commitFuel R₁.tape := by
    rw [hcand₁]; rfl
  have hb₂ : R₂.boundS = R₂.params.nizkBoundS (Fintype.card Cand₂) R₂.commitFuel R₂.tape := by
    rw [hcand₂]; rfl
  have hmacq := Lfzk.TwoFieldV1.mac_term_le (C := C) hmac
  set M := max (max R₁.fsCoefficientS R₂.fsCoefficientS) (1 / (Fintype.card Fmac : ℚ)) with hM
  have hβ : (βmax : ℚ) / (Fintype.card C : ℚ) ≤ M := by
    rw [div_le_iff₀ hc, hβmax]
    push_cast
    have hk : (kmac : ℚ) ≤ M * Fintype.card C := by
      have h := (div_le_iff₀ hc).mp hmacq
      have hle : 1 / (Fintype.card Fmac : ℚ) ≤ M := le_max_right _ _
      nlinarith
    have h1 : ((NizkGrinding.maxBudget (Fintype.card Cand₁ * bp₁) (Fintype.card Cand₁ * bp₁)
          (Fintype.card Cand₁ * bi₁) bl₁ bq₁ : ℕ) : ℚ) ≤ M * Fintype.card C := by
      have hmd := maxBudget_le_densityS R₁ hCpos hFpos₁ (cardCand := Fintype.card Cand₁)
      have hκ : R₁.fsCoefficientS = R₁.maxDensityAt (Fintype.card Cand₁) := by
        unfold Row.fsCoefficientS; rw [hcand₁]
      have hle : R₁.fsCoefficientS ≤ M := le_trans (le_max_left _ _) (le_max_left _ _)
      rw [← hκ] at hmd
      nlinarith
    have h2 : ((NizkGrinding.maxBudget (Fintype.card Cand₂ * bp₂) (Fintype.card Cand₂ * bp₂)
          (Fintype.card Cand₂ * bi₂) bl₂ bq₂ : ℕ) : ℚ) ≤ M * Fintype.card C := by
      have hmd := maxBudget_le_densityS R₂ hCpos hFpos₂ (cardCand := Fintype.card Cand₂)
      have hκ : R₂.fsCoefficientS = R₂.maxDensityAt (Fintype.card Cand₂) := by
        unfold Row.fsCoefficientS; rw [hcand₂]
      have hle : R₂.fsCoefficientS ≤ M := le_trans (le_max_right _ _) (le_max_left _ _)
      rw [← hκ] at hmd
      nlinarith
    exact max_le hk (max_le h1 h2)
  have hDq : (Fintype.card D : ℚ) = 2 ^ R₁.params.digestBits := by rw [hD₁]; push_cast; rfl
  have hnum₁ := adaptiveNumerator_le (Lfs := len2 R₁ R₂ + N) htA₁ htape
  have hnum₂ := adaptiveNumerator_le (Lfs := len2 R₁ R₂ + N) htA₂ (htape₂ ▸ htape)
  have hnumq₁ : (adaptiveNumerator (2 * n₂ + 2 * n₁) tA (len2 R₁ R₂ + N) : ℚ)
        / (Fintype.card D : ℚ)
      ≤ (merkleNumerator R₁.commitFuel R₁.tape : ℚ) / (Fintype.card D : ℚ)
        + ((R₁.tape * (len2 R₁ R₂ + N) : ℕ) : ℚ) / 2 ^ R₁.params.digestBits := by
    rw [← hDq, ← add_div]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hnum₁) hDpos.le
  have hnumq₂ : (adaptiveNumerator (2 * n₂ + 2 * n₁) tA (len2 R₁ R₂ + N) : ℚ)
        / (Fintype.card D : ℚ)
      ≤ (merkleNumerator R₂.commitFuel R₂.tape : ℚ) / (Fintype.card D : ℚ)
        + ((R₁.tape * (len2 R₁ R₂ + N) : ℕ) : ℚ) / 2 ^ R₁.params.digestBits := by
    rw [← hDq, ← add_div, htape₂]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hnum₂) hDpos.le
  have hsplit : ((N * βmax + (kmac + (Fintype.card Cand₁ * (R₁.params.nl * bp₁
          + (∑ i ∈ Finset.range R₁.params.nl, R₁.params.rounds i) * bp₁ + bi₁) + bl₁ + bq₁)
        + (Fintype.card Cand₂ * (R₂.params.nl * bp₂
          + (∑ i ∈ Finset.range R₂.params.nl, R₂.params.rounds i) * bp₂ + bi₂) + bl₂ + bq₂)) : ℕ)
          : ℚ) / (Fintype.card C : ℚ)
      = N * ((βmax : ℚ) / (Fintype.card C : ℚ)) + (kmac : ℚ) / (Fintype.card C : ℚ)
        + ((Fintype.card Cand₁ * (R₁.params.nl * bp₁
          + (∑ i ∈ Finset.range R₁.params.nl, R₁.params.rounds i) * bp₁ + bi₁) + bl₁ + bq₁ : ℕ)
            : ℚ) / (Fintype.card C : ℚ)
        + ((Fintype.card Cand₂ * (R₂.params.nl * bp₂
          + (∑ i ∈ Finset.range R₂.params.nl, R₂.params.rounds i) * bp₂ + bi₂) + bl₂ + bq₂ : ℕ)
            : ℚ) / (Fintype.card C : ℚ) := by
    push_cast
    ring
  rw [hsplit, hb₁, hb₂]
  have hN : (0 : ℚ) ≤ N := Nat.cast_nonneg N
  have := mul_le_mul_of_nonneg_left hβ hN
  linarith

end ComposeS

/-! ## 5. At `p256sha` -/

open Lfzk.TwoFieldV1Rows

/-- **The mixed composed bound plus the two cut-trace extractions at `N = 0`**: at most
`2^-115`. -/
theorem p256sha_adaptive_slack_boundS :
    p256sha.ecdsa.boundS + p256sha.sha.boundS + 1 / (p256sha.macFieldSize : ℚ)
        + 2 * (((p256sha.ecdsa.tape * len2 p256sha.ecdsa p256sha.sha : ℕ) : ℚ)
          / 2 ^ p256sha.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ 115 := by
  native_decide

/-- **The mixed per-query coefficient fits**: the worst role — the `GF(2^128)` side's Ligero
challenge slot, `2^-116.94` — plus `2 · tape / 2^256` is at most `2^-116`. -/
theorem p256sha_adaptive_slack_coeffS :
    max (max p256sha.ecdsa.fsCoefficientS p256sha.sha.fsCoefficientS)
        (1 / (p256sha.macFieldSize : ℚ))
      + 2 * ((p256sha.ecdsa.tape : ℚ) / 2 ^ p256sha.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ 116 := by
  native_decide

/-- `115` is the mixed composed bound's exact integer bit level at `p256sha`. -/
theorem p256sha_boundS_sharp :
    ¬ p256sha.ecdsa.boundS + p256sha.sha.boundS + 1 / (p256sha.macFieldSize : ℚ)
        ≤ (1 : ℚ) / 2 ^ 116 := by
  native_decide

/-- **`p256sha`'s numerals at the mixed accounting**: within `2^-115 + N · 2^-116`. -/
theorem p256sha_adaptive_rhs_leS {Fmac : Type} [Fintype Fmac] (N : ℕ)
    (hFmac : Fintype.card Fmac = 2 ^ 128) :
    p256sha.ecdsa.boundS + p256sha.sha.boundS + 1 / (Fintype.card Fmac : ℚ)
        + N * max (max p256sha.ecdsa.fsCoefficientS p256sha.sha.fsCoefficientS)
            (1 / (Fintype.card Fmac : ℚ))
        + 2 * (((p256sha.ecdsa.tape * (len2 p256sha.ecdsa p256sha.sha + N) : ℕ) : ℚ)
          / 2 ^ p256sha.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 116) := by
  have hsb := p256sha_adaptive_slack_boundS
  have hsc := p256sha_adaptive_slack_coeffS
  have hmf : (Fintype.card Fmac : ℚ) = (p256sha.macFieldSize : ℚ) := by
    rw [hFmac]; rfl
  rw [hmf]
  have hsplit : 2 * (((p256sha.ecdsa.tape * (len2 p256sha.ecdsa p256sha.sha + N) : ℕ) : ℚ)
        / 2 ^ p256sha.ecdsa.params.digestBits)
      = 2 * (((p256sha.ecdsa.tape * len2 p256sha.ecdsa p256sha.sha : ℕ) : ℚ)
          / 2 ^ p256sha.ecdsa.params.digestBits)
        + N * (2 * ((p256sha.ecdsa.tape : ℚ) / 2 ^ p256sha.ecdsa.params.digestBits)) := by
    push_cast
    ring
  rw [hsplit]
  have hN : (0 : ℚ) ≤ N := Nat.cast_nonneg N
  have := mul_le_mul_of_nonneg_left hsc hN
  nlinarith

end Lfzk.NizkAdaptiveTwoField
