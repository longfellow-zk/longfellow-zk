import Lfzk.NizkZk

/-!
# Two-field Longfellow at the zero-knowledge LayerStep, against one re-committing prover

`Lfzk.NizkAdaptiveTwoField.twofield_adaptive_ratio_le` (and its mixed-accounting twin
`twofield_adaptive_ratio_leS`) composes two **clear-verifier** sides through the MAC.  This file
composes two **zero-knowledge** sides (`Lfzk.RbrZkSplit`): the transcript is the same (`hash2`,
`setup2`: the MAC-key point `H(root₁, root₂)` at round `0`, then each side's rounds with the raw key
answer and the public data in the side context), and the bad events per slot are

* the key point: `aP κ + decode c = 0`, budget `kmac`;
* a side point: the side's zero-knowledge LayerStep, in the side context `σ = (κ, c₀, pub)`, is doomed
  and `c` escapes, budget `mixedBudget cardCand … role` (`NizkZk.escapesAt_cardG`).

```text
Pr[ both sides' verifiers accept  ∧  no two good witnesses agree on the common value ]
    ≤  R₁.zkBound logv₁ + R₂.zkBound logv₂ + 1/|Fmac|
       +  N · max(R₁.zkCoefficient logv₁, R₂.zkCoefficient logv₂, 1/|Fmac|)
       +  2 · tape · (1 + L₁ + L₂ + N) / 2^digestBits                   twofield_zk_adaptive_ratio_le
```

## A zero-knowledge side (`ZkSide`)

Per side context `σ`: the verifier's code `V σ` (its public binding reads the MAC key and the
public data, so it is per context), the candidates `Lift σ` (at most `cardCand`), the honest values,
the candidates' assignments and witnesses, the satisfaction predicate, the field data with exactly
balanced decoders, and the Ligero half with the row's densities.  A **good witness** is the witness
of a satisfying candidate.

## What is still a hypothesis

Per side: the `ZkSide` data, `hright` (the side's compiled acceptance, with the side's cut-trace
extraction explaining it, implies its zero-knowledge LayerStep accepts at its slice of the recomputed
answers) and `hrow` (the MAC row: a good witness of an accepting side satisfies the MAC equation at
the hashed key and the proof's tag); the MAC data `aP`, `decode`, `hbal`, `hmac`; the instance's
numbers.  `Lfzk.CompiledZkTwoField` discharges `hright` at the deployed verifiers.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.NizkZkTwoField

open Finset Bcs Bcs.AdaptiveCommit Merkle Merkle.MH Merkle.RandomOracle
  Merkle.RandomOracle.TwoOracleTree RbrLongfellow Lfzk.NizkGrinding Lfzk.NizkAdaptive
  Lfzk.NizkAdaptiveTwoField Lfzk.CertifiedV1 Lfzk.Mac Lfzk.RbrLayerStepS Lfzk.RbrZkLongfellow
  Lfzk.RbrZkSplit Lfzk.NizkZk
open scoped Classical

/-! ## 1. A zero-knowledge side -/

/-- **One zero-knowledge side's data, per side context.** -/
structure ZkSide (R : Row) (logv : ℕ) (Sig C : Type) [Fintype C] (F X Q Msg Witness : Type)
    [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F] [Fintype X] [DecidableEq X]
    [Fintype Q] [DecidableEq Q] (M ninp logw logc : ℕ) where
  /-- The verifier's code, per side context (its public binding reads the key and the tag). -/
  V : Sig → ZkCode C F X Q Msg (Fin logv → F) M ninp logw logc
  /-- The candidates, per side context. -/
  Lift : Sig → Type
  fin : ∀ σ, Fintype (Lift σ)
  hcand : ∀ σ, @Fintype.card (Lift σ) (fin σ) ≤ R.cardCand
  /-- The honest values. -/
  H : ∀ σ, ZkHonest F (Lift σ) logw logc
  /-- The candidates' assignments. -/
  asg : ∀ σ, Lift σ → LigeroAssignment ninp M F
  /-- The candidates' witnesses (what the MAC binds). -/
  wit : ∀ σ, Lift σ → Witness
  /-- Which candidates satisfy the side's circuit. -/
  Sat : ∀ σ, Lift σ → Prop
  /-- The field half. -/
  FD : ∀ σ, ZkFieldData C F X Q Msg (Fin logv → F) (Lift σ) M ninp logw logc R.params.nl
    R.params.rounds (V σ) (H σ) (asg σ) (Sat σ)
  hexact : ∀ σ, (FD σ).ExactAt
  /-- The Ligero half. -/
  LD : ∀ σ, ZkLigeroData C X Q Msg (V σ) (asg σ)
  hesc : ∀ σ sys, Fits (V σ) sys → NoSat (asg σ) sys →
    (((LD σ).escaping sys).card : ℚ) ≤ (R.params.row.fail + R.params.row.arith) * Fintype.card X
  hbq : ∀ σ, (LD σ).bq ≤ LigeroV1LayerStep.queryCount R.params.row
  hQ : Fintype.card Q = R.params.row.n.choose R.params.row.openings

attribute [instance] ZkSide.fin

namespace ZkSide

variable {R : Row} {logv : ℕ} {Sig C : Type} [Fintype C] {F X Q Msg Witness : Type}
  [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F] [Fintype X] [DecidableEq X]
  [Fintype Q] [DecidableEq Q] {M ninp logw logc : ℕ}
variable (S : ZkSide R logv Sig C F X Q Msg Witness M ninp logw logc)

/-- A good witness: the witness of a satisfying candidate. -/
def Good (σ : Sig) (a : Witness) : Prop := ∃ ℓ : S.Lift σ, S.Sat σ ℓ ∧ S.wit σ ℓ = a

/-- The side's zero-knowledge chain at a context and a message sequence. -/
noncomputable def chainAt (σ : Sig) (ms : ℕ → Msg) :
    Bcs.ClaimChain C (Rounds.Role.length R.params.nl R.params.rounds)
      (ZkState M ninp logw logc F X) (Option (S.Lift σ)) :=
  chain (nl := R.params.nl) (w := R.params.rounds) (S.V σ) (S.H σ) (S.asg σ) (S.Sat σ) (S.LD σ) ms

theorem budgets (hF : Fintype.card F = R.params.row.fieldSize) (σ : Sig) :
    ZkBudgets (S.FD σ) (S.LD σ) (zkPairBudget (Fintype.card C) R.params.row.fieldSize logv)
      (pairBudget (Fintype.card C) R.params.row.fieldSize)
      (inBudget (Fintype.card C) R.params.row.fieldSize)
      (ligBudget R.params.row (Fintype.card C)) (queryBudget R.params.row (Fintype.card C)) := by
  obtain ⟨hbin, hini, hpr, hk, hch, hqq⟩ := S.hexact σ
  have hF' : 0 < Fintype.card F := Fintype.card_pos
  obtain ⟨e0, e1, e2, e3⟩ := zk_field_budgets (cardC := Fintype.card C) hF' hbin hini hpr hk
  have ez : zkPairBudget (Fintype.card C) (Fintype.card F) logv
      = zkPairBudget (Fintype.card C) R.params.row.fieldSize logv := by rw [hF]
  have ep : pairBudget (Fintype.card C) (Fintype.card F)
      = pairBudget (Fintype.card C) R.params.row.fieldSize := by rw [hF]
  have ei : inBudget (Fintype.card C) (Fintype.card F)
      = inBudget (Fintype.card C) R.params.row.fieldSize := by rw [hF]
  refine ⟨e0.trans_eq ez, e1.trans_eq ez, e2.trans_eq ep, e3.trans_eq ei,
    fun sys hf hn => ?_, ?_⟩
  · exact LigeroV1LayerStep.mul_le_floor (add_nonneg (LigeroV1LayerStep.fail_nonneg _)
      (LigeroV1LayerStep.arith_nonneg _)) (S.hesc σ sys hf hn) hch
  · refine le_trans (Nat.mul_le_mul_left _ (S.hbq σ)) ?_
    refine LigeroV1LayerStep.mul_le_floor (cardY := R.params.row.n.choose R.params.row.openings)
      (LigeroV1LayerStep.cover_nonneg _) ?_ (by rw [← S.hQ]; exact hqq)
    exact Nat.floor_le (mul_nonneg (LigeroV1LayerStep.cover_nonneg _) (Nat.cast_nonneg _))

end ZkSide

/-! ## 2. Two zero-knowledge sides, one prover, one hashed MAC key -/

section Compose

variable {R₁ R₂ : Row} {logv₁ logv₂ : ℕ}
variable {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]
variable {D : Type} [Fintype D] [DecidableEq D] [Inhabited D]
variable {Enc X Out : Type} [DecidableEq Enc]
variable {Fmac : Type} [Field Fmac] [Fintype Fmac] [DecidableEq Fmac] {nblk : ℕ}
variable {F₁ X₁ Q₁ Msg₁ Witness₁ : Type} [Field F₁] [Fintype F₁] [DecidableEq F₁]
  [SumcheckInterp F₁] [Fintype X₁] [DecidableEq X₁] [Fintype Q₁] [DecidableEq Q₁]
  [Inhabited Msg₁] [DecidableEq Msg₁] {M₁ ninp₁ logw₁ logc₁ : ℕ}
variable {F₂ X₂ Q₂ Msg₂ Witness₂ : Type} [Field F₂] [Fintype F₂] [DecidableEq F₂]
  [SumcheckInterp F₂] [Fintype X₂] [DecidableEq X₂] [Fintype Q₂] [DecidableEq Q₂]
  [Inhabited Msg₂] [DecidableEq Msg₂] {M₂ ninp₂ logw₂ logc₂ : ℕ}
variable {Statement₁ Oracle₁ Challenge₁ Response₁ Query₁ : Type} {Opening₁ : Query₁ → Type}
variable {Statement₂ Oracle₂ Challenge₂ Response₂ Query₂ : Type} {Opening₂ : Query₂ → Type}
variable {Salt₁ Mc₁ Salt₂ Mc₂ : Type} [Inhabited Salt₁] [Inhabited Mc₁] [Inhabited Salt₂]
  [Inhabited Mc₂] {n₁ n₂ : ℕ}

omit [DecidableEq Msg₁] [DecidableEq Msg₂] in
/--
**Two-field Longfellow at the zero-knowledge LayerStep, against one re-committing Fiat–Shamir
prover with a hashed MAC key.**

```text
Pr[ both compiled verifiers accept  ∧  no two good witnesses agree on the common value ]
    ≤  R₁.zkBound logv₁ + R₂.zkBound logv₂ + 1/|Fmac|
       +  N · max(R₁.zkCoefficient logv₁, R₂.zkCoefficient logv₂, 1/|Fmac|)
       +  2 · R₁.tape · (1 + L₁ + L₂ + N) / 2^digestBits
```

The side context is `σ = (κ, c₀, pubOf out)`.  **Every premise**: per side a `ZkSide` and
`|F| = row.fieldSize`; per side `hright` and `hrow`; the MAC data; `|D|`; the Merkle budget.
-/
theorem twofield_zk_adaptive_ratio_le (h₁ : R₁.Valid) {tA N : ℕ}
    {codec₁ : Codec Salt₁ Mc₁ D Enc} (dec₁ : RoleDecoders codec₁)
    {codec₂ : Codec Salt₂ Mc₂ D Enc} (dec₂ : RoleDecoders codec₂)
    (K₁ : Compiler Statement₁ Oracle₁ Challenge₁ Response₁ Query₁ Opening₁ Mc₁ n₁)
    (K₂ : Compiler Statement₂ Oracle₂ Challenge₂ Response₂ Query₂ Opening₂ Mc₂ n₂)
    (body : TwoOracleTree Enc D (Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds
      R₂.params.rounds) C Out tA N)
    (dflt : C) (rootOf₁ rootOf₂ : Out → D) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim n₁ Salt₁ Mc₁ D) (claimOf₂ : Out → OpeningClaim n₂ Salt₂ Mc₂ D)
    (statementOf₁ : Out → (Fin (len2 R₁ R₂) → C) → Statement₁) (responseOf₁ : Out → Response₁)
    (challengeOf₁ : Out → (Fin (len2 R₁ R₂) → C) → Challenge₁)
    (queryOf₁ : Out → (Fin (len2 R₁ R₂) → C) → Query₁)
    (statementOf₂ : Out → (Fin (len2 R₁ R₂) → C) → Statement₂) (responseOf₂ : Out → Response₂)
    (challengeOf₂ : Out → (Fin (len2 R₁ R₂) → C) → Challenge₂)
    (queryOf₂ : Out → (Fin (len2 R₁ R₂) → C) → Query₂)
    (S₁ : ZkSide R₁ logv₁ (((D × D) × List (Enc × D)) × C × X) C F₁ X₁ Q₁ Msg₁ Witness₁
      M₁ ninp₁ logw₁ logc₁)
    (S₂ : ZkSide R₂ logv₂ (((D × D) × List (Enc × D)) × C × X) C F₂ X₂ Q₂ Msg₂ Witness₂
      M₂ ninp₂ logw₂ logc₂)
    (hF₁ : Fintype.card F₁ = R₁.params.row.fieldSize)
    (hF₂ : Fintype.card F₂ = R₂.params.row.fieldSize)
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
      JointAccepts K₁ codec₁ S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ claimOf₁
        statementOf₁ responseOf₁ challengeOf₁ queryOf₁ mt ct →
      S.Explains dec₁ Prod.fst claimOf₁ mt ct →
      ZkLayerStepAccepts .accepted .start
        (steps (nl := R₁.params.nl) (w := R₁.params.rounds) (S₁.V σ) (S₁.LD σ)
          (msgOf₁ (S.proof mt ct)))
        (fun i => S.challenges mt ct ⟨1 + i.val, by omega⟩))
    (hright₂ : ∀ (mt : Fin R₁.tape → D) (ct : Fin (len2 R₁ R₂ + N) → C),
      let S := setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂
      let σ := (S.context mt ct, S.challenges mt ct ⟨0, by omega⟩, pubOf (S.proof mt ct))
      JointAccepts K₂ codec₂ S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ claimOf₂
        statementOf₂ responseOf₂ challengeOf₂ queryOf₂ mt ct →
      S.Explains dec₂ Prod.snd claimOf₂ mt ct →
      ZkLayerStepAccepts .accepted .start
        (steps (nl := R₂.params.nl) (w := R₂.params.rounds) (S₂.V σ) (S₂.LD σ)
          (msgOf₂ (S.proof mt ct)))
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
      ≤ R₁.zkBound logv₁ + R₂.zkBound logv₂ + 1 / (Fintype.card Fmac : ℚ)
        + N * max (max (R₁.zkCoefficient logv₁) (R₂.zkCoefficient logv₂))
            (1 / (Fintype.card Fmac : ℚ))
        + 2 * (((R₁.tape * (len2 R₁ R₂ + N) : ℕ) : ℚ) / 2 ^ R₁.params.digestBits) := by
  set S := setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂ with hS
  have hCpos : 0 < Fintype.card C := Fintype.card_pos
  have hFpos₁ : 0 < R₁.params.row.fieldSize := by rw [← hF₁]; exact Fintype.card_pos
  have hFpos₂ : 0 < R₂.params.row.fieldSize := by rw [← hF₂]; exact Fintype.card_pos
  set bz₁ := zkPairBudget (Fintype.card C) R₁.params.row.fieldSize logv₁
  set bp₁ := pairBudget (Fintype.card C) R₁.params.row.fieldSize
  set bi₁ := inBudget (Fintype.card C) R₁.params.row.fieldSize
  set bl₁ := ligBudget R₁.params.row (Fintype.card C)
  set bq₁ := queryBudget R₁.params.row (Fintype.card C)
  set bz₂ := zkPairBudget (Fintype.card C) R₂.params.row.fieldSize logv₂
  set bp₂ := pairBudget (Fintype.card C) R₂.params.row.fieldSize
  set bi₂ := inBudget (Fintype.card C) R₂.params.row.fieldSize
  set bl₂ := ligBudget R₂.params.row (Fintype.card C)
  set bq₂ := queryBudget R₂.params.row (Fintype.card C)
  have hB₁ := S₁.budgets hF₁
  have hB₂ := S₂.budgets hF₂
  have hloc₁ : ∀ σ, MsgLocal (S₁.chainAt σ) := fun σ =>
    zkChain_msgLocal (S₁.V σ) (S₁.H σ) (S₁.asg σ) (S₁.Sat σ) (S₁.LD σ)
  have hloc₂ : ∀ σ, MsgLocal (S₂.chainAt σ) := fun σ =>
    zkChain_msgLocal (S₂.V σ) (S₂.H σ) (S₂.asg σ) (S₂.Sat σ) (S₂.LD σ)
  -- the bad event at a point, by role
  obtain ⟨Bad, hBad⟩ : ∃ Bad : (D × D) × List (Enc × D) →
      Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds R₂.params.rounds → C → Prop,
      Bad = fun κ q c => Sum.elim (fun _ => aP κ + decode c = 0)
        (Sum.elim
          (fun p => ZkFails S₁.Sat (κ, p.ctx.2.1, p.ctx.2.2) ∧
            DoomedAtG (S₁.chainAt (κ, p.ctx.2.1, p.ctx.2.2)) dflt p ∧
            EscapesAtG (S₁.chainAt (κ, p.ctx.2.1, p.ctx.2.2)) dflt p c)
          (fun p => ZkFails S₂.Sat (κ, p.ctx.2.1, p.ctx.2.2) ∧
            DoomedAtG (S₂.chainAt (κ, p.ctx.2.1, p.ctx.2.2)) dflt p ∧
            EscapesAtG (S₂.chainAt (κ, p.ctx.2.1, p.ctx.2.2)) dflt p c)) q := ⟨_, rfl⟩
  let beta : Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds R₂.params.rounds →
      ℕ := Sum.elim (fun _ => kmac) (Sum.elim
    (fun p => mixedBudget (nl := R₁.params.nl) (w := R₁.params.rounds) R₁.cardCand
      bz₁ bp₁ bi₁ bl₁ bq₁ p.role)
    (fun p => mixedBudget (nl := R₂.params.nl) (w := R₂.params.rounds) R₂.cardCand
      bz₂ bp₂ bi₂ bl₂ bq₂ p.role))
  have hbad : ∀ κ q, (univ.filter fun c : C => Bad κ q c).card ≤ beta q := by
    intro κ q
    rcases q with r | p | p
    · refine le_trans (Finset.card_le_card ?_) (hbal (-aP κ))
      intro c hc
      simp only [mem_filter, mem_univ, true_and, hBad, Sum.elim_inl] at hc ⊢
      linear_combination hc
    · by_cases hd : DoomedAtG (S₁.chainAt (κ, p.ctx.2.1, p.ctx.2.2)) dflt p
      · refine le_trans (Finset.card_le_card ?_) (le_trans (escapesAt_cardG
          (mixedBudget (nl := R₁.params.nl) (w := R₁.params.rounds)
            (Fintype.card (S₁.Lift (κ, p.ctx.2.1, p.ctx.2.2))) bz₁ bp₁ bi₁ bl₁ bq₁)
          (fun ms i pref hd' => (S₁.FD _).doom_preserved_chain (S₁.LD _) (hB₁ _) ms i pref hd')
          dflt p hd) (mixedBudget_mono (S₁.hcand _) _ _ _ _ _ _))
        intro c hc
        simp only [mem_filter, mem_univ, true_and, hBad, Sum.elim_inr, Sum.elim_inl] at hc ⊢
        exact hc.2.2
      · refine le_trans (Finset.card_le_card (t := (∅ : Finset C)) ?_) (by simp)
        intro c hc
        simp only [mem_filter, mem_univ, true_and, hBad, Sum.elim_inr, Sum.elim_inl] at hc
        exact absurd hc.2.1 hd
    · by_cases hd : DoomedAtG (S₂.chainAt (κ, p.ctx.2.1, p.ctx.2.2)) dflt p
      · refine le_trans (Finset.card_le_card ?_) (le_trans (escapesAt_cardG
          (mixedBudget (nl := R₂.params.nl) (w := R₂.params.rounds)
            (Fintype.card (S₂.Lift (κ, p.ctx.2.1, p.ctx.2.2))) bz₂ bp₂ bi₂ bl₂ bq₂)
          (fun ms i pref hd' => (S₂.FD _).doom_preserved_chain (S₂.LD _) (hB₂ _) ms i pref hd')
          dflt p hd) (mixedBudget_mono (S₂.hcand _) _ _ _ _ _ _))
        intro c hc
        simp only [mem_filter, mem_univ, true_and, hBad, Sum.elim_inr] at hc ⊢
        exact hc.2.2
      · refine le_trans (Finset.card_le_card (t := (∅ : Finset C)) ?_) (by simp)
        intro c hc
        simp only [mem_filter, mem_univ, true_and, hBad, Sum.elim_inr] at hc
        exact absurd hc.2.1 hd
  set βmax := max kmac (max
    (NizkGrinding.maxBudget (R₁.cardCand * bz₁) (R₁.cardCand * bp₁) (R₁.cardCand * bi₁) bl₁ bq₁)
    (NizkGrinding.maxBudget (R₂.cardCand * bz₂) (R₂.cardCand * bp₂) (R₂.cardCand * bi₂) bl₂ bq₂))
    with hβmax
  have hmax : ∀ q, beta q ≤ βmax := by
    intro q
    rcases q with r | p | p
    · exact le_max_left _ _
    · exact le_trans (classBudget_le_max p.role) (le_trans (le_max_left _ _) (le_max_right _ _))
    · exact le_trans (classBudget_le_max p.role) (le_trans (le_max_right _ _) (le_max_right _ _))
  let g : ℕ → ℕ := fun k =>
    if k = 0 then kmac
    else if k < 1 + Rounds.Role.length R₁.params.nl R₁.params.rounds then
      mixedBudget (nl := R₁.params.nl) (w := R₁.params.rounds) R₁.cardCand
        bz₁ bp₁ bi₁ bl₁ bq₁ (roleAt (k - 1))
    else
      mixedBudget (nl := R₂.params.nl) (w := R₂.params.rounds) R₂.cardCand
        bz₂ bp₂ bi₂ bl₂ bq₂ (roleAt (k - 1 - Rounds.Role.length R₁.params.nl R₁.params.rounds))
  let slotBeta : Fin (len2 R₁ R₂) → ℕ := fun i => g i.val
  have hslot : ∀ (out : Out) (i : Fin (len2 R₁ R₂)) (cp : Fin i.val → C),
      beta (S.hashInput out i.val cp) ≤ slotBeta i := by
    intro out i cp
    show beta (hash2 rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂ out i.val cp) ≤ g i.val
    unfold hash2
    simp only [g]
    split_ifs <;> exact le_rfl
  have hsum : ∑ i, slotBeta i
      = kmac + (R₁.cardCand * (R₁.params.nl * bz₁
          + (∑ i ∈ Finset.range R₁.params.nl, R₁.params.rounds i) * bp₁ + bi₁) + bl₁ + bq₁)
        + (R₂.cardCand * (R₂.params.nl * bz₂
          + (∑ i ∈ Finset.range R₂.params.nl, R₂.params.rounds i) * bp₂ + bi₂) + bl₂ + bq₂) := by
    rw [show (∑ i, slotBeta i) = ∑ i : Fin (len2 R₁ R₂), g i.val from rfl,
      Fin.sum_univ_eq_sum_range g, len2, Finset.sum_range_add, Finset.sum_range_add,
      Finset.sum_range_one]
    have e0 : g 0 = kmac := by simp only [g, if_pos rfl]
    have e1 : ∑ x ∈ range (Rounds.Role.length R₁.params.nl R₁.params.rounds), g (1 + x)
        = ∑ x ∈ range (Rounds.Role.length R₁.params.nl R₁.params.rounds),
          mixedBudget (nl := R₁.params.nl) (w := R₁.params.rounds) R₁.cardCand
            bz₁ bp₁ bi₁ bl₁ bq₁ (roleAt x) := by
      refine Finset.sum_congr rfl fun x hx => ?_
      have hx' := Finset.mem_range.mp hx
      simp only [g]
      rw [if_neg (by omega), if_pos (by omega), show 1 + x - 1 = x by omega]
    have e2 : ∑ x ∈ range (Rounds.Role.length R₂.params.nl R₂.params.rounds),
          g (1 + Rounds.Role.length R₁.params.nl R₁.params.rounds + x)
        = ∑ x ∈ range (Rounds.Role.length R₂.params.nl R₂.params.rounds),
          mixedBudget (nl := R₂.params.nl) (w := R₂.params.rounds) R₂.cardCand
            bz₂ bp₂ bi₂ bl₂ bq₂ (roleAt x) := by
      refine Finset.sum_congr rfl fun x hx => ?_
      simp only [g]
      rw [if_neg (by omega), if_neg (by omega),
        show 1 + Rounds.Role.length R₁.params.nl R₁.params.rounds + x - 1
          - Rounds.Role.length R₁.params.nl R₁.params.rounds = x by omega]
    rw [e0, e1, e2, sum_roleAt, sum_roleAt, mixed_budget_sum, mixed_budget_sum]
  -- the chain: the three-way split of the composed failure
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
    by_cases hσ₁ : ZkFails S₁.Sat
      (S.context mt ct, S.challenges mt ct ⟨0, by omega⟩, pubOf (S.proof mt ct))
    · have hz := hright₁ mt ct hacc.1 hex₁
      obtain ⟨k₁, hd, he⟩ := (S₁.FD _).exists_escape_chain (S₁.LD _) (hB₁ _)
        (msgOf₁ (S.proof mt ct)) _ hσ₁ hz
      obtain ⟨hdq, hesq⟩ := link_atG (hloc₁ _) dflt
        ((rootOf₁ (S.proof mt ct), rootOf₂ (S.proof mt ct)), S.challenges mt ct ⟨0, by omega⟩,
          pubOf (S.proof mt ct)) msgOf₁ (S.proof mt ct) k₁.val
        (Sumcheck.extract_prefix (fun i : Fin (Rounds.Role.length R₁.params.nl R₁.params.rounds) =>
          S.challenges mt ct ⟨1 + i.val, by omega⟩) k₁)
        (S.challenges mt ct ⟨1 + k₁.val, by omega⟩) k₁.isLt hd he
      refine ⟨⟨1 + k₁.val, by omega⟩, ?_⟩
      have hpt : (S.grinding mt Bad beta hbad).point ct ⟨1 + k₁.val, by omega⟩
          = Sum.inr (Sum.inl (hashPoint ((rootOf₁ (S.proof mt ct), rootOf₂ (S.proof mt ct)),
              S.challenges mt ct ⟨0, by omega⟩, pubOf (S.proof mt ct)) msgOf₁ (S.proof mt ct)
              k₁.val (Sumcheck.extract_prefix
                (fun i : Fin (Rounds.Role.length R₁.params.nl R₁.params.rounds) =>
                  S.challenges mt ct ⟨1 + i.val, by omega⟩) k₁))) := by
        show hash2 rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂ (S.output mt ct).1 (1 + k₁.val)
          (fun j => (S.output mt ct).2 j.val) = _
        exact hash2_side1 rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂ _ k₁.isLt _
      rw [hpt]
      subst hBad
      exact ⟨hσ₁, hdq, hesq⟩
    by_cases hσ₂ : ZkFails S₂.Sat
      (S.context mt ct, S.challenges mt ct ⟨0, by omega⟩, pubOf (S.proof mt ct))
    · have hz := hright₂ mt ct hacc.2 hex₂
      obtain ⟨k₂, hd, he⟩ := (S₂.FD _).exists_escape_chain (S₂.LD _) (hB₂ _)
        (msgOf₂ (S.proof mt ct)) _ hσ₂ hz
      obtain ⟨hdq, hesq⟩ := link_atG (hloc₂ _) dflt
        ((rootOf₁ (S.proof mt ct), rootOf₂ (S.proof mt ct)), S.challenges mt ct ⟨0, by omega⟩,
          pubOf (S.proof mt ct)) msgOf₂ (S.proof mt ct) k₂.val
        (Sumcheck.extract_prefix (fun i : Fin (Rounds.Role.length R₂.params.nl R₂.params.rounds) =>
          S.challenges mt ct
            ⟨1 + Rounds.Role.length R₁.params.nl R₁.params.rounds + i.val, by omega⟩) k₂)
        (S.challenges mt ct
          ⟨1 + Rounds.Role.length R₁.params.nl R₁.params.rounds + k₂.val, by omega⟩)
        k₂.isLt hd he
      refine ⟨⟨1 + Rounds.Role.length R₁.params.nl R₁.params.rounds + k₂.val, by omega⟩, ?_⟩
      have hpt : (S.grinding mt Bad beta hbad).point ct
            ⟨1 + Rounds.Role.length R₁.params.nl R₁.params.rounds + k₂.val, by omega⟩
          = Sum.inr (Sum.inr (hashPoint ((rootOf₁ (S.proof mt ct), rootOf₂ (S.proof mt ct)),
              S.challenges mt ct ⟨0, by omega⟩, pubOf (S.proof mt ct)) msgOf₂ (S.proof mt ct)
              k₂.val (Sumcheck.extract_prefix
                (fun i : Fin (Rounds.Role.length R₂.params.nl R₂.params.rounds) =>
                  S.challenges mt ct
                    ⟨1 + Rounds.Role.length R₁.params.nl R₁.params.rounds + i.val, by omega⟩)
                k₂))) := by
        show hash2 rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂ (S.output mt ct).1
          (1 + Rounds.Role.length R₁.params.nl R₁.params.rounds + k₂.val)
          (fun j => (S.output mt ct).2 j.val) = _
        exact hash2_side2 rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂ _ _
      rw [hpt]
      subst hBad
      exact ⟨hσ₂, hdq, hesq⟩
    -- both sides have good witnesses, which disagree: the MAC rows kill the multiplier
    simp only [ZkFails, not_forall, not_not] at hσ₁ hσ₂
    obtain ⟨ℓ₁, hs₁⟩ := hσ₁
    obtain ⟨ℓ₂, hs₂⟩ := hσ₂
    have hne : common₁ (S₁.wit _ ℓ₁) ≠ common₂ (S₂.wit _ ℓ₂) :=
      fun heq => hcomp ⟨_, _, ⟨ℓ₁, hs₁, rfl⟩, ⟨ℓ₂, hs₂, rfl⟩, heq⟩
    have hm₁ := hrow₁ mt ct _ hacc.1 ⟨ℓ₁, hs₁, rfl⟩
    have hm₂ := hrow₂ mt ct _ hacc.2 ⟨ℓ₂, hs₂, rfl⟩
    have hzero := macTag_collision hne (hm₁.trans hm₂.symm)
    refine ⟨⟨0, by omega⟩, ?_⟩
    have hpt : (S.grinding mt Bad beta hbad).point ct ⟨0, by omega⟩
        = Sum.inl (rootOf₁ (S.proof mt ct), rootOf₂ (S.proof mt ct)) := by
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
  have hseq₁ := budgets_le_zkBound R₁ logv₁ hCpos hFpos₁ (cardCand := R₁.cardCand) hD₁
  have hseq₂ := budgets_le_zkBound R₂ logv₂ hCpos hFpos₂ (cardCand := R₂.cardCand) hD₂
  have hb₁ : R₁.zkBound logv₁ = zkBoundAt R₁ logv₁ R₁.cardCand := rfl
  have hb₂ : R₂.zkBound logv₂ = zkBoundAt R₂ logv₂ R₂.cardCand := rfl
  have hmacq := Lfzk.TwoFieldV1.mac_term_le (C := C) hmac
  set MM := max (max (R₁.zkCoefficient logv₁) (R₂.zkCoefficient logv₂))
    (1 / (Fintype.card Fmac : ℚ)) with hMM
  have hβ : (βmax : ℚ) / (Fintype.card C : ℚ) ≤ MM := by
    rw [div_le_iff₀ hc, hβmax]
    push_cast
    have hk : (kmac : ℚ) ≤ MM * Fintype.card C := by
      have h := (div_le_iff₀ hc).mp hmacq
      have hle : 1 / (Fintype.card Fmac : ℚ) ≤ MM := le_max_right _ _
      nlinarith
    have h1 : ((NizkGrinding.maxBudget (R₁.cardCand * bz₁) (R₁.cardCand * bp₁)
          (R₁.cardCand * bi₁) bl₁ bq₁ : ℕ) : ℚ) ≤ MM * Fintype.card C := by
      have hmd := maxBudget_le_zkDensity R₁ logv₁ hCpos hFpos₁ (cardCand := R₁.cardCand)
      have hle : R₁.zkCoefficient logv₁ ≤ MM := le_trans (le_max_left _ _) (le_max_left _ _)
      have hκ : R₁.zkCoefficient logv₁ = zkMaxDensityAt R₁ logv₁ R₁.cardCand := rfl
      rw [← hκ] at hmd
      nlinarith
    have h2 : ((NizkGrinding.maxBudget (R₂.cardCand * bz₂) (R₂.cardCand * bp₂)
          (R₂.cardCand * bi₂) bl₂ bq₂ : ℕ) : ℚ) ≤ MM * Fintype.card C := by
      have hmd := maxBudget_le_zkDensity R₂ logv₂ hCpos hFpos₂ (cardCand := R₂.cardCand)
      have hle : R₂.zkCoefficient logv₂ ≤ MM := le_trans (le_max_right _ _) (le_max_left _ _)
      have hκ : R₂.zkCoefficient logv₂ = zkMaxDensityAt R₂ logv₂ R₂.cardCand := rfl
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
  have hsplit : ((N * βmax + (kmac + (R₁.cardCand * (R₁.params.nl * bz₁
          + (∑ i ∈ Finset.range R₁.params.nl, R₁.params.rounds i) * bp₁ + bi₁) + bl₁ + bq₁)
        + (R₂.cardCand * (R₂.params.nl * bz₂
          + (∑ i ∈ Finset.range R₂.params.nl, R₂.params.rounds i) * bp₂ + bi₂) + bl₂ + bq₂)) : ℕ)
          : ℚ) / (Fintype.card C : ℚ)
      = N * ((βmax : ℚ) / (Fintype.card C : ℚ)) + (kmac : ℚ) / (Fintype.card C : ℚ)
        + ((R₁.cardCand * (R₁.params.nl * bz₁
          + (∑ i ∈ Finset.range R₁.params.nl, R₁.params.rounds i) * bp₁ + bi₁) + bl₁ + bq₁ : ℕ)
            : ℚ) / (Fintype.card C : ℚ)
        + ((R₂.cardCand * (R₂.params.nl * bz₂
          + (∑ i ∈ Finset.range R₂.params.nl, R₂.params.rounds i) * bp₂ + bi₂) + bl₂ + bq₂ : ℕ)
            : ℚ) / (Fintype.card C : ℚ) := by
    push_cast
    ring
  rw [hsplit, hb₁, hb₂]
  have hN : (0 : ℚ) ≤ N := Nat.cast_nonneg N
  have := mul_le_mul_of_nonneg_left hβ hN
  linarith

end Compose

end Lfzk.NizkZkTwoField
