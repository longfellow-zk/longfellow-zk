import Lfzk.CompiledLongfellow
import Lfzk.NizkGrindingTwoField

/-!
# Two-field Longfellow at the compiled verifier

`Lfzk.NizkGrindingTwoField.FSFamily` is one grinding Fiat–Shamir side of a two-field argument, over an
abstract compiled verifier `K` with abstract `challengeOf`, `queryOf`, `statement`, `lig` and the
acceptance bridge `hright`.  `CompiledFSFamily` is the same side at the compiled Longfellow verifier
of `Lfzk.CompiledLongfellow`: `K` is `guarded (v1K …)`, the challenge and query are the decoded
recomputed Ligero rounds, the Ligero instance is the Merkle-extracted one, and `hright` is the
theorem `CompiledLongfellow.hright_v1`.  `toFSFamily` builds the `FSFamily`, so the two-field
composition applies verbatim.

The side's verifier code `V` and proof parsing `msgOf` are parameters of the family, fixed across
the absorbed coordinate `z`; its Ligero statement `stmt z` may read `z`, because a two-field side's
statement carries the MAC key, which is a coin of the merged tape.

`p256sha_compiled_fs_ratio_le_keyFirst` is `NizkGrindingTwoField.p256sha_fs_ratio_le_keyFirst` at two
compiled families, numerals unchanged; `toMacBound_accepts_iff` says its event's side acceptances are
the compiled verifiers on the merged tape.  What remains a hypothesis is listed there.  Which
verifier `Accepts` is (the non-ZK-path sumcheck checks with a commitment-fixed Ligero statement, not
the deployed zero-knowledge verifier), and the residual refinement claim, are in
`Lfzk.CompiledLongfellow`'s module docstring; they apply to each side.  Not imported by `Lfzk.lean`,
as `Lfzk.NizkGrindingTwoField` is not.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.CompiledLongfellowTwoField

open Finset Bcs Merkle Merkle.MH Merkle.RandomOracle
open scoped Classical
open Lfzk.Mac Lfzk.TwoField Lfzk.TwoFieldNizk Lfzk.TwoFieldBridge Lfzk.CertifiedV1
open Lfzk.NizkGrinding Lfzk.TwoFieldV1Rows Lfzk.NizkGrindingTwoField Lfzk.CompiledLongfellow

/--
**One grinding Fiat–Shamir side at the compiled Longfellow verifier.**

`FSFamily` without `challengeOf`, `queryOf`, `statement`, `lig` and `hright`, with the Ligero
statement `stmt` and the matching premise `hmatch` in their place.  The verifier is
`Accepts (v1K …) V … msgOf (stmt z)`, at the code `V`, the parsing `msgOf` and the domain `dom`.
-/
structure CompiledFSFamily (R : Row) (hR : R.Valid) (hr : 0 < R.params.row.openings)
    (Z : Type) (C : Type) [Fintype C] [DecidableEq C]
    (Cand F Equations Witness : Type) [Fintype Cand] [Field F] [Fintype F] [DecidableEq F]
    [SumcheckInterp F] [Fintype Equations] [DecidableEq Equations]
    (nc nv logw logc : ℕ)
    {Enc D Salt : Type} [Fintype D] [Inhabited D] [DecidableEq D] [DecidableEq Enc]
    [Inhabited Salt]
    (Ctx Msg Out : Type) [DecidableEq Ctx] [DecidableEq Msg] [Inhabited Msg] (N : ℕ)
    (Aux Aux' : Type) (tlen respondFuel revealFuel : ℕ)
    {codec : Codec Salt (Col F R.params.nw R.params.nq) D Enc} (dec : RoleDecoders codec)
    (dom : LigeroFamily.ReedSolomon.Domain F R.params.row.openings R.params.q R.params.row.n)
    (V : Code C F (LigeroV1LayerStep.Chal F Equations R.params.nw R.params.nq)
      (LigeroV1LayerStep.Qry R.params.row) Msg logw logc)
    (msgOf : Out → ℕ → Msg) where
  /-- The side's Merkle adversary, at each value of the coordinates it does not read. -/
  A : Z → Adversary Enc D Salt (Col F R.params.nw R.params.nq)
    (LigeroV1LayerStep.Chal F Equations R.params.nw R.params.nq)
    (LigeroFamily.Response F R.params.row.openings R.params.q R.params.row.n 1)
    (LigeroV1LayerStep.Qry R.params.row) Aux Aux' R.params.row.n R.commitFuel respondFuel revealFuel
  /-- The side's Fiat–Shamir search, run after the commitment. -/
  adv : Z → Aux → Tree (Point Ctx Msg C R.params.nl R.params.rounds) C Out N
  /-- The answer an out-of-range slot would give; never read. -/
  dflt : C
  /-- The hash inputs' commitment context. -/
  ctxOf : Z → Aux → Ctx
  /-- The side's Ligero statement — in a two-field argument it includes the MAC key and tag. -/
  stmt : Z → (Fin tlen → D) →
    LigeroFamily.ConstraintSystem F R.params.nw R.params.nq R.params.q Equations
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
  /-- **LayerStep data describes the verifier** (`CompiledLongfellow.Matches`). -/
  hmatch : ∀ (z : Z) (pre : Fin tlen → D), Matches V (field z pre) (MD z pre)
  /-- **Ligero's extractor**: no satisfying candidate means a false Ligero statement. -/
  hfalse : ∀ (z : Z) (pre : Fin tlen → D), (∀ cand : Cand, ¬ Sat z pre cand) →
    ¬ (stmt z pre).Language
  /-- The side's row and the shared hash tape agree on its length. -/
  htape : R.tape = tlen
  hF : Fintype.card F = R.params.row.fieldSize
  hcand : Fintype.card Cand = R.cardCand
  hD : Fintype.card D = 2 ^ R.params.digestBits
  /-- The Merkle extractor's fuels. -/
  ht₁ : R.commitFuel ≤ tlen
  hT : 2 * R.params.row.n + (revealFuel + respondFuel) + R.commitFuel ≤ tlen
  hT1 : 1 ≤ tlen

namespace CompiledFSFamily

variable {R : Row} {hR : R.Valid} {hr : 0 < R.params.row.openings} {Z : Type} {C : Type}
  [Fintype C] [DecidableEq C] [Nonempty C]
variable {Cand F Equations Witness : Type} [Fintype Cand] [Nonempty Cand] [Field F] [Fintype F]
  [DecidableEq F] [SumcheckInterp F] [Fintype Equations] [DecidableEq Equations]
variable {nc nv logw logc : ℕ}
variable {Enc D Salt : Type} [Fintype D] [DecidableEq D] [Inhabited D] [DecidableEq Enc]
  [Inhabited Salt]
variable {Ctx Msg Out : Type} [DecidableEq Ctx] [DecidableEq Msg] [Inhabited Msg] {N : ℕ}
variable {Aux Aux' : Type} {tlen respondFuel revealFuel : ℕ}
variable {codec : Codec Salt (Col F R.params.nw R.params.nq) D Enc} {dec : RoleDecoders codec}
variable {dom : LigeroFamily.ReedSolomon.Domain F R.params.row.openings R.params.q R.params.row.n}
variable {V : Code C F (LigeroV1LayerStep.Chal F Equations R.params.nw R.params.nq)
  (LigeroV1LayerStep.Qry R.params.row) Msg logw logc} {msgOf : Out → ℕ → Msg}
variable (L : CompiledFSFamily R hR hr Z C Cand F Equations Witness nc nv logw logc Ctx Msg Out N
  Aux Aux' tlen respondFuel revealFuel dec dom V msgOf)

/-- The side's compiled verifier at absorbed coordinate `z`. -/
def accepts (z : Z) (x : (Fin tlen → D) × (Fin (R.fsLen N) → C)) : Prop :=
  Accepts (v1K (Row.rowValid hR) dom (Row.hkrow hR) hr) V (L.A z) codec (L.adv z) L.dflt (L.ctxOf z)
    msgOf (L.stmt z) x

/-- **The `FSFamily` the compiled side is.**  `K := guarded (v1K …)`; `challengeOf`, `queryOf`,
`statement` and `lig` are `CompiledLongfellow`'s; `hright` is `hright_v1`. -/
noncomputable def toFSFamily :
    FSFamily (Enc := Enc) (D := D) (Salt := Salt) (M := Col F R.params.nw R.params.nq)
      R hR Z C Cand F Equations Witness nc nv logw logc Ctx Msg Out N Aux Aux' tlen
      R.params.row.n respondFuel revealFuel dec
      (guarded (v1K (Equations := Equations) (nw := R.params.nw) (nq := R.params.nq)
        (Row.rowValid hR) dom (Row.hkrow hR) hr)) dom where
  A := L.A
  adv := L.adv
  dflt := L.dflt
  ctxOf := L.ctxOf
  msgOf _ := msgOf
  challengeOf z := challengeOf V (L.adv z) L.dflt (L.ctxOf z) msgOf
  queryOf z := queryOf V (L.adv z) L.dflt (L.ctxOf z) msgOf
  statement z := guardedStatement V (L.A z) (L.adv z) L.dflt (L.ctxOf z) msgOf (L.stmt z)
  lig z := extractedInstance (Row.rowValid hR) dom (Row.hkrow hR) hr dec (L.A z) (L.stmt z)
  H := L.H
  Sat := L.Sat
  field := L.field
  hexact := L.hexact
  MD := L.MD
  hfalse := L.hfalse
  hright z pre _ ct := hright_v1 (Row.rowValid hR) dom (Row.hkrow hR) hr dec V (L.A z) (L.adv z)
    L.dflt (L.ctxOf z) msgOf (L.stmt z) (L.field z pre) (L.MD z pre) (L.hmatch z pre) pre ct
  htape := L.htape
  hF := L.hF
  hcand := L.hcand
  hD := L.hD
  ht₁ := L.ht₁
  hT := L.hT
  hT1 := L.hT1

omit [Nonempty C] [Nonempty Cand] in
/-- **The built family's verifier is the compiled verifier.** -/
theorem toFSFamily_accepts_iff (z : Z) (x : (Fin tlen → D) × (Fin (R.fsLen N) → C)) :
    L.toFSFamily.accepts z x ↔ L.accepts z x :=
  (accepts_iff_guarded _ V (L.A z) codec (L.adv z) L.dflt (L.ctxOf z) msgOf (L.stmt z) x).symm

end CompiledFSFamily

/-! ## At `p256sha` -/

section Headline

variable {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]
variable {D : Type} [Fintype D] [DecidableEq D] [Inhabited D]
variable {Fmac : Type} [Field Fmac] [Fintype Fmac] {nblk tlen : ℕ} {N₁ N₂ : ℕ}
variable {Cand₁ F₁ Equations₁ Witness₁ : Type} [Fintype Cand₁] [Nonempty Cand₁] [Field F₁]
  [Fintype F₁] [DecidableEq F₁] [SumcheckInterp F₁] [Fintype Equations₁] [DecidableEq Equations₁]
variable {nc₁ nv₁ logw₁ logc₁ : ℕ}
variable {Enc₁ Salt₁ : Type} [DecidableEq Enc₁] [Inhabited Salt₁]
variable {Ctx₁ Msg₁ Out₁ : Type} [DecidableEq Ctx₁] [DecidableEq Msg₁] [Inhabited Msg₁]
variable {Aux₁ Aux₁' : Type} {respondFuel₁ revealFuel₁ : ℕ}
variable {Cand₂ F₂ Equations₂ Witness₂ : Type} [Fintype Cand₂] [Nonempty Cand₂] [Field F₂]
  [Fintype F₂] [DecidableEq F₂] [SumcheckInterp F₂] [Fintype Equations₂] [DecidableEq Equations₂]
variable {nc₂ nv₂ logw₂ logc₂ : ℕ}
variable {Enc₂ Salt₂ : Type} [DecidableEq Enc₂] [Inhabited Salt₂]
variable {Ctx₂ Msg₂ Out₂ : Type} [DecidableEq Ctx₂] [DecidableEq Msg₂] [Inhabited Msg₂]
variable {Aux₂ Aux₂' : Type} {respondFuel₂ revealFuel₂ : ℕ}

/-- The `P-256` side opens `140` columns. -/
theorem p256sha_ecdsa_openings_pos : 0 < p256sha.ecdsa.params.row.openings := by decide

/-- The `GF(2^128)` side opens `140` columns. -/
theorem p256sha_sha_openings_pos : 0 < p256sha.sha.params.row.openings := by decide

/-- The merged tape's schedule at `p256sha`: Protocol 3.8's key slot first. -/
abbrev keyFirstSch (N₁ N₂ : ℕ) :=
  Schedule.keyFirst (p256sha.ecdsa.fsLen N₁) (p256sha.sha.fsLen N₂)

omit [Fintype Fmac] in
/-- **A side's merged acceptance is its compiled verifier on its own coordinates.**  The event of
`p256sha_compiled_fs_ratio_le_keyFirst` reads `(toFSFamily.sideBound.toMacBound …).accepts`; at
`ω` it is `Accepts (v1K …) V …` at the absorbed coordinate `restOf ι ω.2` and the side's tape
`ω.2 ∘ ι`. -/
theorem toMacBound_accepts_iff {R : Row} {hR : R.Valid} {hr : 0 < R.params.row.openings}
    {Tm : ℕ} {ι : Fin (R.fsLen N₁) → Fin Tm}
    {codec₁ : Codec Salt₁ (Col F₁ R.params.nw R.params.nq) D Enc₁} {dec₁ : RoleDecoders codec₁}
    {dom₁ : LigeroFamily.ReedSolomon.Domain F₁ R.params.row.openings R.params.q R.params.row.n}
    {V₁ : Code C F₁ (LigeroV1LayerStep.Chal F₁ Equations₁ R.params.nw R.params.nq)
      (LigeroV1LayerStep.Qry R.params.row) Msg₁ logw₁ logc₁} {msgOf₁ : Out₁ → ℕ → Msg₁}
    (L : CompiledFSFamily R hR hr (Rest ι → C) C Cand₁ F₁ Equations₁ Witness₁ nc₁ nv₁ logw₁ logc₁
      Ctx₁ Msg₁ Out₁ N₁ Aux₁ Aux₁' tlen respondFuel₁ revealFuel₁ dec₁ dom₁ V₁ msgOf₁)
    {keyA : (Fin tlen → D) × (Fin Tm → C) → Fmac}
    {keyB tag : (Fin tlen → D) × (Fin Tm → C) → Fin nblk → Fmac}
    (common : Witness₁ → Fin nblk → Fmac)
    (hrow : ∀ (ω : (Fin tlen → D) × (Fin Tm → C)) (a : Witness₁),
      L.toFSFamily.sideBound.mergedAccepts ω → L.toFSFamily.sideBound.mergedGood ω a →
      macTag (keyA ω) (keyB ω) (common a) = tag ω)
    (ω : (Fin tlen → D) × (Fin Tm → C)) :
    (L.toFSFamily.sideBound.toMacBound common hrow).accepts ω ↔
      L.accepts (restOf ι ω.2) (ω.1, ω.2 ∘ ι) :=
  L.toFSFamily_accepts_iff (restOf ι ω.2) (ω.1, ω.2 ∘ ι)

/--
**Two-field Longfellow at `p256sha`, at the compiled verifiers, against grinding Fiat–Shamir
adversaries.**

`NizkGrindingTwoField.p256sha_fs_ratio_le_keyFirst` at `L₁.toFSFamily` and `L₂.toFSFamily`, numerals
unchanged:

```text
Pr [ both compiled verifiers accept  ∧  the composed extractor fails ]
    ≤  2^-114  +  N₁ · 2^-121  +  N₂ · 2^-115
```

Each side's acceptance is `CompiledFSFamily.accepts`, the compiled Longfellow verifier
(`toMacBound_accepts_iff`).  **Every premise:** per side a `CompiledFSFamily` (whose fields are
`CompiledLongfellow.row_fs_ratio_le_v1`'s premises at every absorbed coordinate, `hmatch` among
them and `hright` not), the MAC slot's `decode`, `hbal`, `hmac`, `|Fmac| = 2^128`, and the MAC rows
`hrow₁`, `hrow₂` (the arithmetization assumption `assert_mac`).
-/
theorem p256sha_compiled_fs_ratio_le_keyFirst
    (hFmac : Fintype.card Fmac = 2 ^ 128)
    {codec₁ : Codec Salt₁ (Col F₁ p256sha.ecdsa.params.nw p256sha.ecdsa.params.nq) D Enc₁}
    {dec₁ : RoleDecoders codec₁}
    {dom₁ : LigeroFamily.ReedSolomon.Domain F₁ p256sha.ecdsa.params.row.openings
      p256sha.ecdsa.params.q p256sha.ecdsa.params.row.n}
    {V₁ : Code C F₁ (LigeroV1LayerStep.Chal F₁ Equations₁ p256sha.ecdsa.params.nw
      p256sha.ecdsa.params.nq) (LigeroV1LayerStep.Qry p256sha.ecdsa.params.row) Msg₁ logw₁ logc₁}
    {msgOf₁ : Out₁ → ℕ → Msg₁}
    {codec₂ : Codec Salt₂ (Col F₂ p256sha.sha.params.nw p256sha.sha.params.nq) D Enc₂}
    {dec₂ : RoleDecoders codec₂}
    {dom₂ : LigeroFamily.ReedSolomon.Domain F₂ p256sha.sha.params.row.openings
      p256sha.sha.params.q p256sha.sha.params.row.n}
    {V₂ : Code C F₂ (LigeroV1LayerStep.Chal F₂ Equations₂ p256sha.sha.params.nw
      p256sha.sha.params.nq) (LigeroV1LayerStep.Qry p256sha.sha.params.row) Msg₂ logw₂ logc₂}
    {msgOf₂ : Out₂ → ℕ → Msg₂}
    (L₁ : CompiledFSFamily p256sha.ecdsa (TwoFieldRowV1.ecdsa_valid p256sha_valid)
      p256sha_ecdsa_openings_pos (Rest (keyFirstSch N₁ N₂).ι₁ → C) C Cand₁ F₁ Equations₁ Witness₁
      nc₁ nv₁ logw₁ logc₁ Ctx₁ Msg₁ Out₁ N₁ Aux₁ Aux₁' tlen respondFuel₁ revealFuel₁ dec₁ dom₁ V₁
      msgOf₁)
    (L₂ : CompiledFSFamily p256sha.sha (TwoFieldRowV1.sha_valid p256sha_valid)
      p256sha_sha_openings_pos (Rest (keyFirstSch N₁ N₂).ι₂ → C) C Cand₂ F₂ Equations₂ Witness₂
      nc₂ nv₂ logw₂ logc₂ Ctx₂ Msg₂ Out₂ N₂ Aux₂ Aux₂' tlen respondFuel₂ revealFuel₂ dec₂ dom₂ V₂
      msgOf₂)
    (decode : C → Fmac) (aP : (Fin tlen → D) → Fmac) (kmac : ℕ)
    (hbal : ∀ x : Fmac, (univ.filter fun c : C => decode c = x).card ≤ kmac)
    (hmac : kmac * Fintype.card Fmac ≤ Fintype.card C)
    {keyB tag : (Fin tlen → D) × (Fin (fsKeyFirstLen N₁ N₂) → C) → Fin nblk → Fmac}
    (common₁ : Witness₁ → Fin nblk → Fmac)
    (hrow₁ : ∀ (ω : (Fin tlen → D) × (Fin (fsKeyFirstLen N₁ N₂) → C)) (a : Witness₁),
      L₁.toFSFamily.sideBound.mergedAccepts ω → L₁.toFSFamily.sideBound.mergedGood ω a →
      macTag (aP ω.1 + decode (ω.2 (keyFirstSch N₁ N₂).s)) (keyB ω) (common₁ a) = tag ω)
    (common₂ : Witness₂ → Fin nblk → Fmac)
    (hrow₂ : ∀ (ω : (Fin tlen → D) × (Fin (fsKeyFirstLen N₁ N₂) → C)) (a : Witness₂),
      L₂.toFSFamily.sideBound.mergedAccepts ω → L₂.toFSFamily.sideBound.mergedGood ω a →
      macTag (aP ω.1 + decode (ω.2 (keyFirstSch N₁ N₂).s)) (keyB ω) (common₂ a) = tag ω) :
    ((univ.filter fun ω : (Fin tlen → D) × (Fin (fsKeyFirstLen N₁ N₂) → C) =>
        (L₁.toFSFamily.sideBound.toMacBound common₁ hrow₁).accepts ω ∧
          (L₂.toFSFamily.sideBound.toMacBound common₂ hrow₂).accepts ω ∧
          composedE (L₁.toFSFamily.sideBound.toMacBound common₁ hrow₁)
            (L₂.toFSFamily.sideBound.toMacBound common₂ hrow₂) ω = none).card : ℚ)
        / (Fintype.card (Fin tlen → D) * (Fintype.card C : ℚ) ^ fsKeyFirstLen N₁ N₂)
      ≤ (1 : ℚ) / 2 ^ 114 + N₁ * ((1 : ℚ) / 2 ^ 121) + N₂ * ((1 : ℚ) / 2 ^ 115) :=
  p256sha_fs_ratio_le_keyFirst hFmac L₁.toFSFamily L₂.toFSFamily decode aP kmac hbal hmac common₁
    hrow₁ common₂ hrow₂

end Headline

end Lfzk.CompiledLongfellowTwoField
