import Lfzk.CompiledLongfellowZkTwoField
import Lfzk.LigeroV1RowsV7

/-!
# Zero knowledge at the deployed v7 geometries

The numerals of `Lfzk.CompiledLongfellowZk.compiled_longfellow_zk_bits256` and
`Lfzk.CompiledLongfellowZkTwoField.twofield_zk` at the rows `Lfzk.CertifiedV7` certifies for
soundness (`Lfzk.LigeroV1Rows.v7Sig`, `v7Hash1 … v7Hash4`): the same `(n, openings)`, and the
statements are about **the rows' own Reed–Solomon codes** (`LigeroV1Rows.Row.code`), so the
soundness and zero-knowledge theorems speak about one object.

At 32-byte nonces and SHA-256 digests the single-side term is

```
zkEps n r f = (4n² + (2n−1)(2n−2) + 2(n−r)·f) / 2^256
```

| component | `n` | `4n² + (2n−1)(2n−2)` | `2(n − 132)` | at `f = 2^115` |
|---|---|---|---|---|
| v7 signature | 3187 | 81236632 | 6110 | `≤ 2^-128` |
| v7 hash, 1 attribute | 3230 | 83443822 | 6196 | `≤ 2^-128` |
| v7 hash, 2 attributes | 3318 | 88053086 | 6372 | `≤ 2^-128` |
| v7 hash, 3 attributes | 3352 | 89867122 | 6440 | `≤ 2^-128` |
| v7 hash, 4 attributes | 3436 | 94428154 | 6608 | `≤ 2^-128` |

and the two-field proof (signature + any hash variant) is `≤ 2^-127` against `2^115` Merkle-oracle
queries (`v7_twofield_zk_q115`).  All of this is exact rational arithmetic (`norm_num`), with no
`native_decide`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace Lfzk.CompiledLongfellowZkV7

open Merkle Merkle.MH LigeroFamily
open Lfzk.ZkAdaptiveV1 Lfzk.CompiledLongfellowZk Lfzk.CompiledLongfellowZkTwoField Lfzk.Mac
open Lfzk.CompiledLigeroZk (Bits256 card_Bits256)

/-- The single-side zero-knowledge error at 32-byte nonces and digests, `n` columns, `r` opened,
`f` Merkle-oracle queries. -/
noncomputable def zkEps (n r f : ℕ) : ℚ :=
  ((4 * n ^ 2 + 2 * (n - r) * f + (2 * n - 1) * (2 * n - 2) : ℕ) : ℚ) / 2 ^ 256

theorem zkEps_le_q115 (n r : ℕ) (hn : 0 < n) (hn' : n ≤ 2 ^ 12) (hr : 0 < r) :
    zkEps n r (2 ^ 115) ≤ 1 / 2 ^ 128 := by
  have h := openingEps_bits256_q115 n r 1 hn hn' hr one_pos
  rwa [openingEps_bits256 n (2 ^ 115) 1 (n - r) hn one_pos] at h

/-! ## The rows' numerals -/

open Lfzk.LigeroV1Rows in
theorem v7Sig_zkEps (f : ℕ) :
    zkEps v7Sig.n v7Sig.openings f = ((81236632 + 6110 * f : ℕ) : ℚ) / 2 ^ 256 := by
  simp only [zkEps, Row.n, Row.openings, v7Sig]
  congr 2
  ring

open Lfzk.LigeroV1Rows in
theorem v7Hash1_zkEps (f : ℕ) :
    zkEps v7Hash1.n v7Hash1.openings f = ((83443822 + 6196 * f : ℕ) : ℚ) / 2 ^ 256 := by
  simp only [zkEps, Row.n, Row.openings, v7Hash1]
  congr 2
  ring

open Lfzk.LigeroV1Rows in
theorem v7Hash2_zkEps (f : ℕ) :
    zkEps v7Hash2.n v7Hash2.openings f = ((88053086 + 6372 * f : ℕ) : ℚ) / 2 ^ 256 := by
  simp only [zkEps, Row.n, Row.openings, v7Hash2]
  congr 2
  ring

open Lfzk.LigeroV1Rows in
theorem v7Hash3_zkEps (f : ℕ) :
    zkEps v7Hash3.n v7Hash3.openings f = ((89867122 + 6440 * f : ℕ) : ℚ) / 2 ^ 256 := by
  simp only [zkEps, Row.n, Row.openings, v7Hash3]
  congr 2
  ring

open Lfzk.LigeroV1Rows in
theorem v7Hash4_zkEps (f : ℕ) :
    zkEps v7Hash4.n v7Hash4.openings f = ((94428154 + 6608 * f : ℕ) : ℚ) / 2 ^ 256 := by
  simp only [zkEps, Row.n, Row.openings, v7Hash4]
  congr 2
  ring

/-- Every v7 row has at most `2^12` columns and opens at least one. -/
theorem v7_rows_small :
    ∀ row ∈ [LigeroV1Rows.v7Sig, LigeroV1Rows.v7Hash1, LigeroV1Rows.v7Hash2, LigeroV1Rows.v7Hash3,
      LigeroV1Rows.v7Hash4], 0 < row.n ∧ row.n ≤ 2 ^ 12 ∧ 0 < row.openings := by
  decide

/-! ## Single side, at a row's own code -/

section Single

variable {F Equations : Type} [Field F] [Fintype F] [DecidableEq F]
variable [Fintype Equations] [DecidableEq Equations]
variable {w nw nq reps : ℕ}
variable {Enc Coin LQ Ctx Wit Blind Tr RO V : Type}
variable [DecidableEq Enc] [Fintype Coin] [DecidableEq Coin] [Nonempty Coin]
variable [Fintype LQ] [DecidableEq LQ] [Fintype Blind] [Fintype Tr] [Fintype RO] [DecidableEq V]

/--
**Compiled Longfellow zero knowledge at a certified row's code**: `zkEps row.n row.openings f`,
for the V1 code `row.code h D hkrow` the soundness rows are stated at.
-/
theorem row_compiled_zk (row : LigeroV1Rows.Row) (h : row.Valid)
    (D : ReedSolomon.Domain F row.openings w row.n) (hkrow : row.openings + w = row.k)
    (Cod : Codec Bits256 (Col F nw nq reps) Bits256 Enc) (hinjC : Cod.Inj)
    (dec₁ : Coin → Ligero.V1.Challenge F nw nq reps Equations)
    (dec₂ : Coin → QuerySet row.n row.openings)
    (FE : Frontend F nw nq w Equations Ctx Wit Blind Tr RO) (ctx : Bits256 → Ctx)
    (pts : Points Ctx Tr Coin (LigeroFamily.Response F row.openings w row.n reps) LQ) (wit : Wit)
    (hvalid : ∀ root, FE.Valid wit (ctx root)) (hn : 0 < row.n) {T f : ℕ}
    (hT : 2 * row.n - 1 + f ≤ T)
    (dist : Distinguisher F row.openings w row.n nw nq reps Bits256 Bits256 Enc Tr Coin LQ RO V f) :
    StatClose (zkEps row.n row.openings f)
      (realExp (row.code h D hkrow) Cod dec₁ dec₂ FE ctx pts wit (T := T) dist)
      (simExp (row.code h D hkrow) Cod dec₁ dec₂ FE.stmt ctx pts (T := T) dist) :=
  compiled_longfellow_zk_bits256 (row.code h D hkrow) Cod hinjC dec₁ dec₂ FE ctx pts wit hvalid hn
    hT dist

/-- **The v7 signature component**: `(81236632 + 6110·f) / 2^256`. -/
theorem v7Sig_compiled_zk (h : LigeroV1Rows.v7Sig.Valid)
    (D : ReedSolomon.Domain F LigeroV1Rows.v7Sig.openings w LigeroV1Rows.v7Sig.n)
    (hkrow : LigeroV1Rows.v7Sig.openings + w = LigeroV1Rows.v7Sig.k)
    (Cod : Codec Bits256 (Col F nw nq reps) Bits256 Enc) (hinjC : Cod.Inj)
    (dec₁ : Coin → Ligero.V1.Challenge F nw nq reps Equations)
    (dec₂ : Coin → QuerySet LigeroV1Rows.v7Sig.n LigeroV1Rows.v7Sig.openings)
    (FE : Frontend F nw nq w Equations Ctx Wit Blind Tr RO) (ctx : Bits256 → Ctx)
    (pts : Points Ctx Tr Coin
      (LigeroFamily.Response F LigeroV1Rows.v7Sig.openings w LigeroV1Rows.v7Sig.n reps) LQ)
    (wit : Wit) (hvalid : ∀ root, FE.Valid wit (ctx root)) {T f : ℕ}
    (hT : 2 * LigeroV1Rows.v7Sig.n - 1 + f ≤ T)
    (dist : Distinguisher F LigeroV1Rows.v7Sig.openings w LigeroV1Rows.v7Sig.n nw nq reps
      Bits256 Bits256 Enc Tr Coin LQ RO V f) :
    StatClose (((81236632 + 6110 * f : ℕ) : ℚ) / 2 ^ 256)
      (realExp (LigeroV1Rows.v7Sig.code h D hkrow) Cod dec₁ dec₂ FE ctx pts wit (T := T) dist)
      (simExp (LigeroV1Rows.v7Sig.code h D hkrow) Cod dec₁ dec₂ FE.stmt ctx pts (T := T) dist) := by
  rw [← v7Sig_zkEps]
  exact row_compiled_zk _ h D hkrow Cod hinjC dec₁ dec₂ FE ctx pts wit hvalid (by decide) hT dist

/-- **The v7 hash component, 4 attributes** (the largest): `(94428154 + 6608·f) / 2^256`. -/
theorem v7Hash4_compiled_zk (h : LigeroV1Rows.v7Hash4.Valid)
    (D : ReedSolomon.Domain F LigeroV1Rows.v7Hash4.openings w LigeroV1Rows.v7Hash4.n)
    (hkrow : LigeroV1Rows.v7Hash4.openings + w = LigeroV1Rows.v7Hash4.k)
    (Cod : Codec Bits256 (Col F nw nq reps) Bits256 Enc) (hinjC : Cod.Inj)
    (dec₁ : Coin → Ligero.V1.Challenge F nw nq reps Equations)
    (dec₂ : Coin → QuerySet LigeroV1Rows.v7Hash4.n LigeroV1Rows.v7Hash4.openings)
    (FE : Frontend F nw nq w Equations Ctx Wit Blind Tr RO) (ctx : Bits256 → Ctx)
    (pts : Points Ctx Tr Coin
      (LigeroFamily.Response F LigeroV1Rows.v7Hash4.openings w LigeroV1Rows.v7Hash4.n reps) LQ)
    (wit : Wit) (hvalid : ∀ root, FE.Valid wit (ctx root)) {T f : ℕ}
    (hT : 2 * LigeroV1Rows.v7Hash4.n - 1 + f ≤ T)
    (dist : Distinguisher F LigeroV1Rows.v7Hash4.openings w LigeroV1Rows.v7Hash4.n nw nq reps
      Bits256 Bits256 Enc Tr Coin LQ RO V f) :
    StatClose (((94428154 + 6608 * f : ℕ) : ℚ) / 2 ^ 256)
      (realExp (LigeroV1Rows.v7Hash4.code h D hkrow) Cod dec₁ dec₂ FE ctx pts wit (T := T) dist)
      (simExp (LigeroV1Rows.v7Hash4.code h D hkrow) Cod dec₁ dec₂ FE.stmt ctx pts (T := T)
        dist) := by
  rw [← v7Hash4_zkEps]
  exact row_compiled_zk _ h D hkrow Cod hinjC dec₁ dec₂ FE ctx pts wit hvalid (by decide) hT dist

end Single

/-! ## The two-field proof at 32-byte nonces and digests -/

section TwoField

variable {F₁ E₁ F₂ E₂ : Type} [Field F₁] [Fintype F₁] [DecidableEq F₁] [Fintype E₁]
  [DecidableEq E₁] [Field F₂] [Fintype F₂] [DecidableEq F₂] [Fintype E₂] [DecidableEq E₂]
variable {r₁ w₁ n₁ nw₁ nq₁ reps₁ r₂ w₂ n₂ nw₂ nq₂ reps₂ : ℕ}
variable {Enc₁ Enc₂ Coin₁ Coin₂ LQ₁ LQ₂ Ctx₁ Ctx₂ Wit₁ Wit₂ B₁ B₂ Tr₁ Tr₂ RO₁ RO₂ V : Type}
variable [DecidableEq Enc₁] [DecidableEq Enc₂] [DecidableEq LQ₁] [DecidableEq LQ₂]
variable [Fintype Coin₁] [DecidableEq Coin₁] [Nonempty Coin₁] [Fintype Coin₂] [DecidableEq Coin₂]
  [Nonempty Coin₂] [Fintype LQ₁] [Fintype LQ₂] [Fintype B₁] [Fintype B₂] [Fintype Tr₁]
  [Fintype Tr₂] [Fintype RO₁] [Fintype RO₂] [DecidableEq V]
variable {Fmac : Type} [Field Fmac] [Fintype Fmac] [DecidableEq Fmac] {nblk : ℕ}

/--
**The two-field proof at 32-byte nonces and digests**: `zkEps n₁ r₁ f + zkEps n₂ r₂ f`.
-/
theorem twofield_zk_bits256
    (P₁ : Side F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ E₁ Bits256 Bits256 Enc₁ Coin₁ LQ₁ Ctx₁ Wit₁ B₁ Tr₁ RO₁)
    (P₂ : Side F₂ r₂ w₂ n₂ nw₂ nq₂ reps₂ E₂ Bits256 Bits256 Enc₂ Coin₂ LQ₂ Ctx₂ Wit₂ B₂ Tr₂ RO₂)
    (ctx₁ : Bits256 → Bits256 → Fmac → Tag Fmac nblk → Ctx₁)
    (ctx₂ : Bits256 → Bits256 → Fmac → Tag Fmac nblk →
      LProof F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ Bits256 Bits256 Tr₁ Coin₁ → Ctx₂)
    (wit₁ : Tag Fmac nblk → Wit₁) (wit₂ : Tag Fmac nblk → Wit₂) (msg : Fin nblk → Fmac)
    (hinj₁ : P₁.Cod.Inj) (hinj₂ : P₂.Cod.Inj)
    (hvalid₁ : ∀ ap root₁ root₂ av, P₁.FE.Valid (wit₁ ap) (ctx₁ root₁ root₂ av (macTag av ap msg)))
    (hvalid₂ : ∀ ap root₁ root₂ av pf₁,
      P₂.FE.Valid (wit₂ ap) (ctx₂ root₁ root₂ av (macTag av ap msg) pf₁))
    (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) {T₁ T₂ f : ℕ} (hT₁ : 2 * n₁ - 1 + f ≤ T₁)
    (hT₂ : 2 * n₂ - 1 + f ≤ T₂)
    (dist : TwoDistinguisher F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ F₂ r₂ w₂ n₂ nw₂ nq₂ reps₂
      Bits256 Bits256 Enc₁ Enc₂ Tr₁ Tr₂ Coin₁ Coin₂ LQ₁ LQ₂ RO₁ RO₂ Fmac nblk V f) :
    StatClose (zkEps n₁ r₁ f + zkEps n₂ r₂ f)
      (realExp2 P₁ P₂ ctx₁ ctx₂ wit₁ wit₂ msg (T₁ := T₁) (T₂ := T₂) dist)
      (simExp2 P₁ P₂ ctx₁ ctx₂ (T₁ := T₁) (T₂ := T₂) dist) := by
  have h := twofield_zk P₁ P₂ ctx₁ ctx₂ wit₁ wit₂ msg hinj₁ hinj₂ hvalid₁ hvalid₂ hn₁ hn₂ hT₁ hT₂
    dist
  rwa [openingEps_bits256 n₁ f T₁ (n₁ - r₁) hn₁ (by omega),
    openingEps_bits256 n₂ f T₂ (n₂ - r₂) hn₂ (by omega)] at h

/--
**At `2^115` Merkle-oracle queries the two-field proof is `≤ 2^-127`**, at every pair of
geometries with at most `2^12` columns per side and at least one opened column — in particular
the v7 signature row (`n = 3187`) with any v7 hash row (`n = 3230 … 3436`), 132 openings each
(`v7_rows_small`).
-/
theorem v7_twofield_zk_q115
    (P₁ : Side F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ E₁ Bits256 Bits256 Enc₁ Coin₁ LQ₁ Ctx₁ Wit₁ B₁ Tr₁ RO₁)
    (P₂ : Side F₂ r₂ w₂ n₂ nw₂ nq₂ reps₂ E₂ Bits256 Bits256 Enc₂ Coin₂ LQ₂ Ctx₂ Wit₂ B₂ Tr₂ RO₂)
    (ctx₁ : Bits256 → Bits256 → Fmac → Tag Fmac nblk → Ctx₁)
    (ctx₂ : Bits256 → Bits256 → Fmac → Tag Fmac nblk →
      LProof F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ Bits256 Bits256 Tr₁ Coin₁ → Ctx₂)
    (wit₁ : Tag Fmac nblk → Wit₁) (wit₂ : Tag Fmac nblk → Wit₂) (msg : Fin nblk → Fmac)
    (hinj₁ : P₁.Cod.Inj) (hinj₂ : P₂.Cod.Inj)
    (hvalid₁ : ∀ ap root₁ root₂ av, P₁.FE.Valid (wit₁ ap) (ctx₁ root₁ root₂ av (macTag av ap msg)))
    (hvalid₂ : ∀ ap root₁ root₂ av pf₁,
      P₂.FE.Valid (wit₂ ap) (ctx₂ root₁ root₂ av (macTag av ap msg) pf₁))
    (hn₁ : 0 < n₁) (hn₁' : n₁ ≤ 2 ^ 12) (hr₁ : 0 < r₁) (hn₂ : 0 < n₂) (hn₂' : n₂ ≤ 2 ^ 12)
    (hr₂ : 0 < r₂) {T₁ T₂ : ℕ} (hT₁ : 2 * n₁ - 1 + 2 ^ 115 ≤ T₁)
    (hT₂ : 2 * n₂ - 1 + 2 ^ 115 ≤ T₂)
    (dist : TwoDistinguisher F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ F₂ r₂ w₂ n₂ nw₂ nq₂ reps₂
      Bits256 Bits256 Enc₁ Enc₂ Tr₁ Tr₂ Coin₁ Coin₂ LQ₁ LQ₂ RO₁ RO₂ Fmac nblk V (2 ^ 115)) :
    StatClose (1 / 2 ^ 127)
      (realExp2 P₁ P₂ ctx₁ ctx₂ wit₁ wit₂ msg (T₁ := T₁) (T₂ := T₂) dist)
      (simExp2 P₁ P₂ ctx₁ ctx₂ (T₁ := T₁) (T₂ := T₂) dist) := by
  have h := twofield_zk_bits256 P₁ P₂ ctx₁ ctx₂ wit₁ wit₂ msg hinj₁ hinj₂ hvalid₁ hvalid₂ hn₁ hn₂
    hT₁ hT₂ dist
  refine h.mono ?_
  have h1 := zkEps_le_q115 n₁ r₁ hn₁ hn₁' hr₁
  have h2 := zkEps_le_q115 n₂ r₂ hn₂ hn₂' hr₂
  calc zkEps n₁ r₁ (2 ^ 115) + zkEps n₂ r₂ (2 ^ 115) ≤ 1 / 2 ^ 128 + 1 / 2 ^ 128 :=
        add_le_add h1 h2
    _ = 1 / 2 ^ 127 := by norm_num

end TwoField

end Lfzk.CompiledLongfellowZkV7
