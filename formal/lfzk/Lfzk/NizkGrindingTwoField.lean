import Lfzk.NizkGrinding
import Lfzk.TwoFieldV1Rows

/-!
# Two-field Longfellow against grinding Fiat–Shamir adversaries

`Lfzk.TwoFieldV1` composes two `CertifiedV1` sides through the MAC on one merged tape, each side a
`V1Family` in the **sequential** model.  This file is the same composition with each side a grinding
Fiat–Shamir side (`FSFamily`): side `i`'s search makes at most `Nᵢ` queries against its own challenge
oracle, whose lazy tape has `Lᵢ + Nᵢ` slots, and its single-field bound is
`Lfzk.CertifiedV1.Row.fs_ratio_le_bound`'s `Rᵢ.bound + Nᵢ · Rᵢ.fsCoefficient`.

```text
Pr over (pre, tape) [ both compiled verifiers accept  ∧  the composed extractor fails ]
    ≤  (R₁.bound + N₁ · κ₁)  +  (R₂.bound + N₂ · κ₂)  +  kmac / |C|          twofield_fs_ratio_le
```

At `p256sha` (`p256sha_fs_ratio_le_keyFirst`) the sequential part is the row's certified `2^-114`, and
the two coefficients are certified here: `κ₁ ≤ 2^-121` on the `P-256` side, `κ₂ ≤ 2^-115` on the
`GF(2^128)` side.

## What carries over, and what does not

The composition is `TwoFieldBridge.twofield_merged_ratio_le` verbatim: an `FSFamily` is a
`TwoFieldBridge.SideBound` (`FSFamily.sideBound`) at the side's challenge tape of `Lᵢ + Nᵢ` slots.
`TwoFieldLongfellow`'s and `TwoFieldV1`'s caveats apply unchanged: the merged experiment is the
conjunction of two side verifiers on one sample space, each side's adversary is a family indexed by
the coordinates it does not read (here: the other side's whole challenge tape and the MAC key coin),
and there is no formal two-field driver.  The key coin is a uniform slot of the merged tape, as in
`TwoFieldV1`; it is not itself derived by a grinding search.  Each side inherits
`Lfzk.NizkGrinding`'s restrictions (one commitment, the Ligero statement fixed per commitment, hash
inputs carrying the raw earlier answers, no Merkle queries during the search).

**What each side still assumes** is `Row.fs_ratio_le_bound`'s list at every absorbed `z` (the fields
of `FSFamily`), and the composition keeps the MAC rows `hrow₁`, `hrow₂` (the arithmetization
assumption `assert_mac`) and the MAC slot's `decode`, `hbal`, `hmac`, `|Fmac| = 2^128`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.NizkGrindingTwoField

open Finset Bcs Merkle Merkle.MH Merkle.RandomOracle
open scoped Classical
open Lfzk.Mac Lfzk.TwoField Lfzk.TwoFieldNizk Lfzk.TwoFieldBridge Lfzk.CertifiedV1
open Lfzk.NizkGrinding Lfzk.TwoFieldV1Rows

/-! ## 1. One side, at a hash tape of variable length -/

/-- **`Row.fs_ratio_le_bound` at a hash tape of length `tlen = R.tape`**, so that two rows can share
one hash tape. -/
theorem side_fs_ratio_le {R : Row} (h : R.Valid) {tlen : ℕ} (htl : R.tape = tlen)
    {C Cand : Type} [Fintype C] [DecidableEq C] [Nonempty C] [Fintype Cand] [Nonempty Cand]
    {F Equations Witness : Type} [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F]
    [Fintype Equations] [DecidableEq Equations]
    {logw logc nc nv : ℕ}
    {Statement Oracle Challenge Response Query : Type} {Opening : Query → Type}
    {Enc D Salt M Aux Aux' : Type} {n respondFuel revealFuel : ℕ}
    [Fintype D] [DecidableEq D] [Inhabited D] [DecidableEq Enc] [Inhabited Salt] [Inhabited M]
    {Ctx Msg Out : Type} [DecidableEq Ctx] [DecidableEq Msg] [Inhabited Msg] {N : ℕ}
    {codec : Codec Salt M D Enc} (dec : RoleDecoders codec)
    (K : Compiler Statement Oracle Challenge Response Query Opening M n)
    (A : Adversary Enc D Salt M Challenge Response Query Aux Aux'
      n R.commitFuel respondFuel revealFuel)
    (adv : Aux → Tree (Point Ctx Msg C R.params.nl R.params.rounds) C Out N)
    (dflt : C) (ctxOf : Aux → Ctx) (msgOf : Out → ℕ → Msg)
    (challengeOf : Aux → (Fin (R.fsLen N) → C) → Challenge)
    (queryOf : Aux → (Fin (R.fsLen N) → C) → Query)
    (statement : (Fin tlen → D) × (Fin (R.fsLen N) → C) → Statement)
    {Fails : (Fin tlen → D) → Prop}
    (hF : Fintype.card F = R.params.row.fieldSize)
    (dom : LigeroFamily.ReedSolomon.Domain F R.params.row.openings R.params.q R.params.row.n)
    (lig : ∀ _pre : Fin tlen → D,
      LigeroV1LayerStep.Instance R.params.row F Equations R.params.nw R.params.nq R.params.q)
    (hfalse : ∀ pre : Fin tlen → D, Fails pre → ¬ (lig pre).statement.Language)
    (H : ∀ _pre : Fin tlen → D, RbrLongfellow.Honest F Cand logw logc)
    (Sat : (Fin tlen → D) → Cand → Prop)
    (Ffam : ∀ pre : Fin tlen → D,
      RbrSplit.FieldData C F (LigeroV1LayerStep.Chal F Equations R.params.nw R.params.nq)
        (LigeroV1LayerStep.Qry R.params.row) Cand Witness nc nv logw logc (H pre) (Sat pre))
    (hexact : ∀ pre : Fin tlen → D, (Ffam pre).Exact)
    (MD : ∀ pre : Fin tlen → D, MsgData C Msg (H pre))
    (hfail : ∀ pre : Fin tlen → D, Fails pre → ∀ cand : Cand, ¬ Sat pre cand)
    (hright : ∀ pre : Fin tlen → D, Fails pre → ∀ ct : Fin (R.fsLen N) → C,
        (CompiledAccepts K A codec (statement (pre, ct))
            (challengeOf (A.auxOf pre) ct) (queryOf (A.auxOf pre) ct) pre ∧
          ExtractionExplains codec dec n R.commitFuel (revealFuel + respondFuel) tlen A.commit
            (A.openingStage (challengeOf (A.auxOf pre) ct) (queryOf (A.auxOf pre) ct)) pre) →
        RbrSplit.LayerStepAccepts
          (RbrSplit.stepsOf (nl := R.params.nl) (w := R.params.rounds)
            (withMsgs (Ffam pre) (MD pre)
              (msgOf (fsProof (adv (A.auxOf pre)) dflt (ctxOf (A.auxOf pre)) msgOf ct)))
            (fun _ _ => LigeroV1LayerStep.accepting (Row.rowValid h) dom (Row.hkrow h) (lig pre)))
          (fsChallenges (adv (A.auxOf pre)) dflt (ctxOf (A.auxOf pre)) msgOf ct))
    (ht₁ : R.commitFuel ≤ tlen)
    (hT : 2 * n + (revealFuel + respondFuel) + R.commitFuel ≤ tlen) (hT1 : 1 ≤ tlen)
    (hcand : Fintype.card Cand = R.cardCand)
    (hD : Fintype.card D = 2 ^ R.params.digestBits) :
    ((univ.filter fun omega : (Fin tlen → D) × (Fin (R.fsLen N) → C) =>
        CompiledAccepts K A codec (statement omega)
            (challengeOf (A.auxOf omega.1) omega.2) (queryOf (A.auxOf omega.1) omega.2) omega.1 ∧
          Fails omega.1).card : ℚ)
        / (Fintype.card (Fin tlen → D) * (Fintype.card C : ℚ) ^ R.fsLen N)
      ≤ R.bound + N * R.fsCoefficient := by
  subst htl
  exact Row.fs_ratio_le_bound h dec K A adv dflt ctxOf msgOf challengeOf queryOf statement hF dom
    lig hfalse H Sat Ffam hexact MD hfail hright ht₁ hT hT1 hcand hD

/-! ## 2. One side, as a family over the absorbed coordinate -/

/--
**One grinding Fiat–Shamir Longfellow side of a two-field argument.**

`TwoFieldV1.V1Family` with the sequential coin tape replaced by the side's challenge tape of
`R.fsLen N` slots, and with the Fiat–Shamir search `adv`, its proof reading `msgOf`, the hash
inputs' context `ctxOf` and the message data `MD` added.  Everything the prover chooses is a function
of the absorbed coordinate `z`; the fields after `MD` are `Row.fs_ratio_le_bound`'s premises at every
`z`, with `Fails pre := ∀ cand, ¬ Sat z pre cand`.
-/
structure FSFamily (R : Row) (hR : R.Valid) (Z : Type) (C : Type) [Fintype C] [DecidableEq C]
    (Cand F Equations Witness : Type) [Fintype Cand] [Field F] [Fintype F] [DecidableEq F]
    [SumcheckInterp F] [Fintype Equations] [DecidableEq Equations]
    (nc nv logw logc : ℕ)
    {Statement Oracle Challenge Response Query : Type} {Opening : Query → Type}
    {Enc D Salt M : Type} [Fintype D] [Inhabited D] [DecidableEq D] [DecidableEq Enc]
    [Inhabited Salt] [Inhabited M]
    (Ctx Msg Out : Type) [DecidableEq Ctx] [DecidableEq Msg] [Inhabited Msg] (N : ℕ)
    (Aux Aux' : Type) (tlen n respondFuel revealFuel : ℕ)
    {codec : Codec Salt M D Enc} (dec : RoleDecoders codec)
    (K : Compiler Statement Oracle Challenge Response Query Opening M n)
    (dom : LigeroFamily.ReedSolomon.Domain F R.params.row.openings R.params.q R.params.row.n) where
  /-- The side's Merkle adversary, at each value of the coordinates it does not read. -/
  A : Z → Adversary Enc D Salt M Challenge Response Query Aux Aux'
    n R.commitFuel respondFuel revealFuel
  /-- The side's Fiat–Shamir search, run after the commitment. -/
  adv : Z → Aux → Tree (Point Ctx Msg C R.params.nl R.params.rounds) C Out N
  /-- The answer an out-of-range slot would give; never read. -/
  dflt : C
  /-- The hash inputs' commitment context. -/
  ctxOf : Z → Aux → Ctx
  /-- The proof's per-round messages. -/
  msgOf : Z → Out → ℕ → Msg
  /-- The compiled verifier's Ligero challenge, read after the commitment. -/
  challengeOf : Z → Aux → (Fin (R.fsLen N) → C) → Challenge
  /-- The compiled verifier's Ligero query, read after the commitment. -/
  queryOf : Z → Aux → (Fin (R.fsLen N) → C) → Query
  /-- The side's statement — in a two-field argument it includes the MAC key and tag. -/
  statement : Z → (Fin tlen → D) × (Fin (R.fsLen N) → C) → Statement
  /-- The commitment's Ligero V1 instance: statement and IPCP prover. -/
  lig : Z → (Fin tlen → D) →
    LigeroV1LayerStep.Instance R.params.row F Equations R.params.nw R.params.nq R.params.q
  /-- LayerStep's honest values, per commitment. -/
  H : Z → (Fin tlen → D) → RbrLongfellow.Honest F Cand logw logc
  /-- Which candidates satisfy the side's circuit, per commitment. -/
  Sat : Z → (Fin tlen → D) → Cand → Prop
  /-- The field half of LayerStep, per commitment. -/
  field : ∀ (z : Z) (pre : Fin tlen → D),
    RbrSplit.FieldData C F (LigeroV1LayerStep.Chal F Equations R.params.nw R.params.nq)
      (LigeroV1LayerStep.Qry R.params.row) Cand Witness nc nv logw logc (H z pre) (Sat z pre)
  /-- Its decoders are exactly balanced. -/
  hexact : ∀ (z : Z) (pre : Fin tlen → D), (field z pre).Exact
  /-- How a round's message fixes LayerStep's prover data at that round. -/
  MD : ∀ (z : Z) (pre : Fin tlen → D), MsgData C Msg (H z pre)
  /-- **Ligero's extractor**: no satisfying candidate means a false Ligero statement. -/
  hfalse : ∀ (z : Z) (pre : Fin tlen → D), (∀ cand : Cand, ¬ Sat z pre cand) →
    ¬ (lig z pre).statement.Language
  /-- **The Fiat–Shamir transliteration**: compiled acceptance at the recomputed Ligero rounds, with
  extraction explaining it, means LayerStep on the proof's messages accepts at the recomputed
  challenges. -/
  hright : ∀ (z : Z) (pre : Fin tlen → D), (∀ cand : Cand, ¬ Sat z pre cand) →
    ∀ ct : Fin (R.fsLen N) → C,
      (CompiledAccepts K (A z) codec (statement z (pre, ct))
          (challengeOf z ((A z).auxOf pre) ct) (queryOf z ((A z).auxOf pre) ct) pre ∧
        ExtractionExplains codec dec n R.commitFuel (revealFuel + respondFuel) tlen (A z).commit
          ((A z).openingStage (challengeOf z ((A z).auxOf pre) ct)
            (queryOf z ((A z).auxOf pre) ct)) pre) →
      RbrSplit.LayerStepAccepts
        (RbrSplit.stepsOf (nl := R.params.nl) (w := R.params.rounds)
          (withMsgs (field z pre) (MD z pre)
            (msgOf z (fsProof (adv z ((A z).auxOf pre)) dflt (ctxOf z ((A z).auxOf pre))
              (msgOf z) ct)))
          (fun _ _ => LigeroV1LayerStep.accepting (Row.rowValid hR) dom (Row.hkrow hR) (lig z pre)))
        (fsChallenges (adv z ((A z).auxOf pre)) dflt (ctxOf z ((A z).auxOf pre)) (msgOf z) ct)
  /-- The side's row and the shared hash tape agree on its length. -/
  htape : R.tape = tlen
  hF : Fintype.card F = R.params.row.fieldSize
  hcand : Fintype.card Cand = R.cardCand
  hD : Fintype.card D = 2 ^ R.params.digestBits
  /-- The Merkle extractor's fuels. -/
  ht₁ : R.commitFuel ≤ tlen
  hT : 2 * n + (revealFuel + respondFuel) + R.commitFuel ≤ tlen
  hT1 : 1 ≤ tlen

namespace FSFamily

variable {R : Row} {hR : R.Valid} {Z : Type} {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]
variable {Cand F Equations Witness : Type} [Fintype Cand] [Nonempty Cand] [Field F] [Fintype F]
  [DecidableEq F] [SumcheckInterp F] [Fintype Equations] [DecidableEq Equations]
variable {nc nv logw logc : ℕ}
variable {Statement Oracle Challenge Response Query : Type} {Opening : Query → Type}
variable {Enc D Salt M : Type} [Fintype D] [DecidableEq D] [Inhabited D] [DecidableEq Enc]
  [Inhabited Salt] [Inhabited M]
variable {Ctx Msg Out : Type} [DecidableEq Ctx] [DecidableEq Msg] [Inhabited Msg] {N : ℕ}
variable {Aux Aux' : Type} {tlen n respondFuel revealFuel : ℕ}
variable {codec : Codec Salt M D Enc} {dec : RoleDecoders codec}
variable {K : Compiler Statement Oracle Challenge Response Query Opening M n}
variable {dom : LigeroFamily.ReedSolomon.Domain F R.params.row.openings R.params.q R.params.row.n}
variable (L : FSFamily R hR Z C Cand F Equations Witness nc nv logw logc Ctx Msg Out N Aux Aux'
  tlen n respondFuel revealFuel dec K dom)

/-- The side's **compiled** verifier at absorbed coordinate `z`, at the recomputed Ligero rounds. -/
def accepts (z : Z) (x : (Fin tlen → D) × (Fin (R.fsLen N) → C)) : Prop :=
  CompiledAccepts K (L.A z) codec (L.statement z x) (L.challengeOf z ((L.A z).auxOf x.1) x.2)
    (L.queryOf z ((L.A z).auxOf x.1) x.2) x.1

/-- A good witness: the witness of a candidate that satisfies the side's circuit. -/
def good (z : Z) (x : (Fin tlen → D) × (Fin (R.fsLen N) → C)) (a : Witness) : Prop :=
  ∃ cand : Cand, L.Sat z x.1 cand ∧ (L.field z x.1).wOf cand = a

omit [Nonempty C] [Nonempty Cand] in
theorem good_iff (z : Z) (x : (Fin tlen → D) × (Fin (R.fsLen N) → C)) :
    (∀ a, ¬ L.good z x a) ↔ ∀ cand : Cand, ¬ L.Sat z x.1 cand := by
  constructor
  · intro h cand hsat
    exact h _ ⟨cand, hsat, rfl⟩
  · rintro h a ⟨cand, hsat, _⟩
    exact h cand hsat

/-- **The single-field grinding bound, at every absorbed coordinate.** -/
theorem ratio_le (z : Z) :
    ((univ.filter fun omega : (Fin tlen → D) × (Fin (R.fsLen N) → C) =>
        L.accepts z omega ∧ ∀ cand : Cand, ¬ L.Sat z omega.1 cand).card : ℚ)
        / (Fintype.card (Fin tlen → D) * (Fintype.card C : ℚ) ^ R.fsLen N)
      ≤ R.bound + N * R.fsCoefficient := by
  refine le_trans (le_of_eq ?_) (side_fs_ratio_le hR L.htape dec K (L.A z) (L.adv z) L.dflt
    (L.ctxOf z) (L.msgOf z) (L.challengeOf z) (L.queryOf z) (L.statement z)
    (Fails := fun pre => ∀ cand : Cand, ¬ L.Sat z pre cand) L.hF dom (L.lig z) (L.hfalse z)
    (L.H z) (L.Sat z) (L.field z) (L.hexact z) (L.MD z) (fun _ h => h) (L.hright z)
    L.ht₁ L.hT L.hT1 L.hcand L.hD)
  congr 3
  ext x
  simp only [Finset.mem_filter]
  rfl

/-- **The side, as a `SideBound`**, with bound `R.bound + N · R.fsCoefficient`. -/
noncomputable def sideBound :
    SideBound Z (Fin tlen → D) C (R.fsLen N) Witness where
  accepts := L.accepts
  good := L.good
  bound := R.bound + N * R.fsCoefficient
  sound z := by
    refine le_trans (le_of_eq ?_) (L.ratio_le z)
    congr 3
    exact Finset.filter_congr (fun x _ => and_congr_right fun _ => L.good_iff z x)

@[simp] theorem sideBound_bound : L.sideBound.bound = R.bound + N * R.fsCoefficient := rfl

end FSFamily

/-! ## 3. Two sides on one merged tape -/

section Compose

variable {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]
variable {D : Type} [Fintype D] [DecidableEq D] [Inhabited D]
variable {Fmac : Type} [Field Fmac] {nblk tlen T : ℕ}
variable {R₁ R₂ : Row} {h₁ : R₁.Valid} {h₂ : R₂.Valid} {N₁ N₂ : ℕ}
variable {Cand₁ F₁ Equations₁ Witness₁ : Type} [Fintype Cand₁] [Nonempty Cand₁] [Field F₁]
  [Fintype F₁] [DecidableEq F₁] [SumcheckInterp F₁] [Fintype Equations₁] [DecidableEq Equations₁]
variable {nc₁ nv₁ logw₁ logc₁ : ℕ}
variable {Statement₁ Oracle₁ Challenge₁ Response₁ Query₁ : Type} {Opening₁ : Query₁ → Type}
variable {Enc₁ Salt₁ M₁ : Type} [DecidableEq Enc₁] [Inhabited Salt₁] [Inhabited M₁]
variable {Ctx₁ Msg₁ Out₁ : Type} [DecidableEq Ctx₁] [DecidableEq Msg₁] [Inhabited Msg₁]
variable {Aux₁ Aux₁' : Type} {n₁ respondFuel₁ revealFuel₁ : ℕ}
variable {codec₁ : Codec Salt₁ M₁ D Enc₁} {dec₁ : RoleDecoders codec₁}
variable {K₁ : Compiler Statement₁ Oracle₁ Challenge₁ Response₁ Query₁ Opening₁ M₁ n₁}
variable {dom₁ : LigeroFamily.ReedSolomon.Domain F₁ R₁.params.row.openings R₁.params.q
  R₁.params.row.n}
variable {Cand₂ F₂ Equations₂ Witness₂ : Type} [Fintype Cand₂] [Nonempty Cand₂] [Field F₂]
  [Fintype F₂] [DecidableEq F₂] [SumcheckInterp F₂] [Fintype Equations₂] [DecidableEq Equations₂]
variable {nc₂ nv₂ logw₂ logc₂ : ℕ}
variable {Statement₂ Oracle₂ Challenge₂ Response₂ Query₂ : Type} {Opening₂ : Query₂ → Type}
variable {Enc₂ Salt₂ M₂ : Type} [DecidableEq Enc₂] [Inhabited Salt₂] [Inhabited M₂]
variable {Ctx₂ Msg₂ Out₂ : Type} [DecidableEq Ctx₂] [DecidableEq Msg₂] [Inhabited Msg₂]
variable {Aux₂ Aux₂' : Type} {n₂ respondFuel₂ revealFuel₂ : ℕ}
variable {codec₂ : Codec Salt₂ M₂ D Enc₂} {dec₂ : RoleDecoders codec₂}
variable {K₂ : Compiler Statement₂ Oracle₂ Challenge₂ Response₂ Query₂ Opening₂ M₂ n₂}
variable {dom₂ : LigeroFamily.ReedSolomon.Domain F₂ R₂.params.row.openings R₂.params.q
  R₂.params.row.n}

/--
**Two grinding Fiat–Shamir Longfellow sides and one MAC slot.**

`TwoFieldBridge.twofield_merged_ratio_le` at two `FSFamily.sideBound`s:

```text
Pr over (pre, tape) [ both compiled verifiers accept  ∧  the composed extractor fails ]
    ≤  (R₁.bound + N₁ · κ₁)  +  (R₂.bound + N₂ · κ₂)  +  kmac / |C|
```

`hrowᵢ` is side `i`'s MAC row, in `SideBound`'s form: a good witness of an accepting side satisfies
the MAC equation at the shared key and tag.
-/
theorem twofield_fs_ratio_le [Nonempty (Fin tlen → D)]
    (sch : Schedule (R₁.fsLen N₁) (R₂.fsLen N₂) T)
    (L₁ : FSFamily R₁ h₁ (Rest sch.ι₁ → C) C Cand₁ F₁ Equations₁ Witness₁ nc₁ nv₁ logw₁ logc₁
      Ctx₁ Msg₁ Out₁ N₁ Aux₁ Aux₁' tlen n₁ respondFuel₁ revealFuel₁ dec₁ K₁ dom₁)
    (L₂ : FSFamily R₂ h₂ (Rest sch.ι₂ → C) C Cand₂ F₂ Equations₂ Witness₂ nc₂ nv₂ logw₂ logc₂
      Ctx₂ Msg₂ Out₂ N₂ Aux₂ Aux₂' tlen n₂ respondFuel₂ revealFuel₂ dec₂ K₂ dom₂)
    (decode : C → Fmac) (aP : (Fin tlen → D) → Fmac) (kmac : ℕ)
    (hbal : ∀ x : Fmac, (univ.filter fun c : C => decode c = x).card ≤ kmac)
    {keyB tag : (Fin tlen → D) × (Fin T → C) → Fin nblk → Fmac}
    (common₁ : Witness₁ → Fin nblk → Fmac)
    (hrow₁ : ∀ (ω : (Fin tlen → D) × (Fin T → C)) (a : Witness₁),
      L₁.sideBound.mergedAccepts ω → L₁.sideBound.mergedGood ω a →
      macTag (aP ω.1 + decode (ω.2 sch.s)) (keyB ω) (common₁ a) = tag ω)
    (common₂ : Witness₂ → Fin nblk → Fmac)
    (hrow₂ : ∀ (ω : (Fin tlen → D) × (Fin T → C)) (a : Witness₂),
      L₂.sideBound.mergedAccepts ω → L₂.sideBound.mergedGood ω a →
      macTag (aP ω.1 + decode (ω.2 sch.s)) (keyB ω) (common₂ a) = tag ω)
    (hT : 1 ≤ T) :
    ((univ.filter fun ω : (Fin tlen → D) × (Fin T → C) =>
        (L₁.sideBound.toMacBound common₁ hrow₁).accepts ω ∧
          (L₂.sideBound.toMacBound common₂ hrow₂).accepts ω ∧
          composedE (L₁.sideBound.toMacBound common₁ hrow₁)
            (L₂.sideBound.toMacBound common₂ hrow₂) ω = none).card : ℚ)
        / (Fintype.card (Fin tlen → D) * (Fintype.card C : ℚ) ^ T)
      ≤ (R₁.bound + N₁ * R₁.fsCoefficient) + (R₂.bound + N₂ * R₂.fsCoefficient)
        + (kmac : ℚ) / (Fintype.card C : ℚ) :=
  twofield_merged_ratio_le sch decode aP kmac hbal L₁.sideBound common₁ hrow₁
    L₂.sideBound common₂ hrow₂ hT

end Compose

/-! ## 4. At `p256sha` -/

/-- **The `P-256` side's work-normalized coefficient is at most `2^-121`.** -/
theorem p256sha_ecdsa_fsCoefficient : p256sha.ecdsa.fsCoefficient ≤ (1 : ℚ) / 2 ^ 121 := by
  native_decide

/-- …and `121` is its exact integer bit level. -/
theorem p256sha_ecdsa_fsCoefficient_sharp :
    ¬ p256sha.ecdsa.fsCoefficient ≤ (1 : ℚ) / 2 ^ 122 := by
  native_decide

/-- **The `GF(2^128)` side's work-normalized coefficient is at most `2^-115`.** -/
theorem p256sha_sha_fsCoefficient : p256sha.sha.fsCoefficient ≤ (1 : ℚ) / 2 ^ 115 := by
  native_decide

/-- …and `115` is its exact integer bit level. -/
theorem p256sha_sha_fsCoefficient_sharp : ¬ p256sha.sha.fsCoefficient ≤ (1 : ℚ) / 2 ^ 116 := by
  native_decide

section Headline

variable {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]
variable {D : Type} [Fintype D] [DecidableEq D] [Inhabited D]
variable {Fmac : Type} [Field Fmac] [Fintype Fmac] {nblk tlen : ℕ} {N₁ N₂ : ℕ}
variable {Cand₁ F₁ Equations₁ Witness₁ : Type} [Fintype Cand₁] [Nonempty Cand₁] [Field F₁]
  [Fintype F₁] [DecidableEq F₁] [SumcheckInterp F₁] [Fintype Equations₁] [DecidableEq Equations₁]
variable {nc₁ nv₁ logw₁ logc₁ : ℕ}
variable {Statement₁ Oracle₁ Challenge₁ Response₁ Query₁ : Type} {Opening₁ : Query₁ → Type}
variable {Enc₁ Salt₁ M₁ : Type} [DecidableEq Enc₁] [Inhabited Salt₁] [Inhabited M₁]
variable {Ctx₁ Msg₁ Out₁ : Type} [DecidableEq Ctx₁] [DecidableEq Msg₁] [Inhabited Msg₁]
variable {Aux₁ Aux₁' : Type} {n₁ respondFuel₁ revealFuel₁ : ℕ}
variable {codec₁ : Codec Salt₁ M₁ D Enc₁} {dec₁ : RoleDecoders codec₁}
variable {K₁ : Compiler Statement₁ Oracle₁ Challenge₁ Response₁ Query₁ Opening₁ M₁ n₁}
variable {Cand₂ F₂ Equations₂ Witness₂ : Type} [Fintype Cand₂] [Nonempty Cand₂] [Field F₂]
  [Fintype F₂] [DecidableEq F₂] [SumcheckInterp F₂] [Fintype Equations₂] [DecidableEq Equations₂]
variable {nc₂ nv₂ logw₂ logc₂ : ℕ}
variable {Statement₂ Oracle₂ Challenge₂ Response₂ Query₂ : Type} {Opening₂ : Query₂ → Type}
variable {Enc₂ Salt₂ M₂ : Type} [DecidableEq Enc₂] [Inhabited Salt₂] [Inhabited M₂]
variable {Ctx₂ Msg₂ Out₂ : Type} [DecidableEq Ctx₂] [DecidableEq Msg₂] [Inhabited Msg₂]
variable {Aux₂ Aux₂' : Type} {n₂ respondFuel₂ revealFuel₂ : ℕ}
variable {codec₂ : Codec Salt₂ M₂ D Enc₂} {dec₂ : RoleDecoders codec₂}
variable {K₂ : Compiler Statement₂ Oracle₂ Challenge₂ Response₂ Query₂ Opening₂ M₂ n₂}

/-- The merged tape at `p256sha` under Protocol 3.8's schedule: the key slot, then each side's
challenge tape of `Lᵢ + Nᵢ` slots. -/
abbrev fsKeyFirstLen (N₁ N₂ : ℕ) : ℕ := 1 + p256sha.ecdsa.fsLen N₁ + p256sha.sha.fsLen N₂

/--
**Two-field Longfellow at `p256sha`, against grinding Fiat–Shamir adversaries.**

ECDSA over `P-256`'s base field and SHA-256 over `GF(2^128)`, each at its deployed v8 circuit profile
proved with Ligero V1 at 132 openings, composed through the MAC over a field of `2^128` elements, at
Protocol 3.8's schedule; side `i`'s search makes at most `Nᵢ` queries:

```text
Pr [ both compiled verifiers accept  ∧  the composed extractor fails ]
    ≤  2^-114  +  N₁ · 2^-121  +  N₂ · 2^-115
```

`2^-114` is the sequential row's certified composed bound (`p256sha_valid`), and the two coefficients
are certified above.  The premises are `twofield_fs_ratio_le`'s: per side an `FSFamily` (whose fields
are `Row.fs_ratio_le_bound`'s premises at every absorbed coordinate), the MAC slot's `decode`,
`hbal`, `hmac`, `|Fmac| = 2^128`, and the MAC rows `hrow₁`, `hrow₂`.
-/
theorem p256sha_fs_ratio_le_keyFirst
    (hFmac : Fintype.card Fmac = 2 ^ 128)
    {dom₁ : LigeroFamily.ReedSolomon.Domain F₁ p256sha.ecdsa.params.row.openings
      p256sha.ecdsa.params.q p256sha.ecdsa.params.row.n}
    {dom₂ : LigeroFamily.ReedSolomon.Domain F₂ p256sha.sha.params.row.openings
      p256sha.sha.params.q p256sha.sha.params.row.n}
    (L₁ : FSFamily p256sha.ecdsa (TwoFieldRowV1.ecdsa_valid p256sha_valid)
      (Rest (Schedule.keyFirst (p256sha.ecdsa.fsLen N₁) (p256sha.sha.fsLen N₂)).ι₁ → C)
      C Cand₁ F₁ Equations₁ Witness₁ nc₁ nv₁ logw₁ logc₁ Ctx₁ Msg₁ Out₁ N₁ Aux₁ Aux₁' tlen n₁
      respondFuel₁ revealFuel₁ dec₁ K₁ dom₁)
    (L₂ : FSFamily p256sha.sha (TwoFieldRowV1.sha_valid p256sha_valid)
      (Rest (Schedule.keyFirst (p256sha.ecdsa.fsLen N₁) (p256sha.sha.fsLen N₂)).ι₂ → C)
      C Cand₂ F₂ Equations₂ Witness₂ nc₂ nv₂ logw₂ logc₂ Ctx₂ Msg₂ Out₂ N₂ Aux₂ Aux₂' tlen n₂
      respondFuel₂ revealFuel₂ dec₂ K₂ dom₂)
    (decode : C → Fmac) (aP : (Fin tlen → D) → Fmac) (kmac : ℕ)
    (hbal : ∀ x : Fmac, (univ.filter fun c : C => decode c = x).card ≤ kmac)
    (hmac : kmac * Fintype.card Fmac ≤ Fintype.card C)
    {keyB tag : (Fin tlen → D) × (Fin (fsKeyFirstLen N₁ N₂) → C) → Fin nblk → Fmac}
    (common₁ : Witness₁ → Fin nblk → Fmac)
    (hrow₁ : ∀ (ω : (Fin tlen → D) × (Fin (fsKeyFirstLen N₁ N₂) → C)) (a : Witness₁),
      L₁.sideBound.mergedAccepts ω → L₁.sideBound.mergedGood ω a →
      macTag (aP ω.1 + decode (ω.2 (Schedule.keyFirst _ _).s)) (keyB ω) (common₁ a) = tag ω)
    (common₂ : Witness₂ → Fin nblk → Fmac)
    (hrow₂ : ∀ (ω : (Fin tlen → D) × (Fin (fsKeyFirstLen N₁ N₂) → C)) (a : Witness₂),
      L₂.sideBound.mergedAccepts ω → L₂.sideBound.mergedGood ω a →
      macTag (aP ω.1 + decode (ω.2 (Schedule.keyFirst _ _).s)) (keyB ω) (common₂ a) = tag ω) :
    ((univ.filter fun ω : (Fin tlen → D) × (Fin (fsKeyFirstLen N₁ N₂) → C) =>
        (L₁.sideBound.toMacBound common₁ hrow₁).accepts ω ∧
          (L₂.sideBound.toMacBound common₂ hrow₂).accepts ω ∧
          composedE (L₁.sideBound.toMacBound common₁ hrow₁)
            (L₂.sideBound.toMacBound common₂ hrow₂) ω = none).card : ℚ)
        / (Fintype.card (Fin tlen → D) * (Fintype.card C : ℚ) ^ fsKeyFirstLen N₁ N₂)
      ≤ (1 : ℚ) / 2 ^ 114 + N₁ * ((1 : ℚ) / 2 ^ 121) + N₂ * ((1 : ℚ) / 2 ^ 115) := by
  haveI : Nonempty (Fin tlen → D) := inferInstance
  refine le_trans (twofield_fs_ratio_le (Schedule.keyFirst _ _) L₁ L₂ decode aP kmac hbal
    common₁ hrow₁ common₂ hrow₂ (by omega)) ?_
  have hmacq := Lfzk.TwoFieldV1.mac_term_le (C := C) hmac
  have ht := TwoFieldRowV1.target p256sha_valid
  unfold TwoFieldRowV1.bound at ht
  rw [hFmac] at hmacq
  have hlam : p256sha.lam = 114 := rfl
  have hmacsize : p256sha.macFieldSize = 2 ^ 128 := rfl
  rw [hlam, hmacsize] at ht
  push_cast at hmacq ht
  have h1 := mul_le_mul_of_nonneg_left p256sha_ecdsa_fsCoefficient (Nat.cast_nonneg (α := ℚ) N₁)
  have h2 := mul_le_mul_of_nonneg_left p256sha_sha_fsCoefficient (Nat.cast_nonneg (α := ℚ) N₂)
  linarith

end Headline

end Lfzk.NizkGrindingTwoField
