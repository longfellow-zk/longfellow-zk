import Lfzk.CompiledZkTwoField

/-!
# Two-field Longfellow at the deployed zero-knowledge verifiers, at the certified pairs

`CompiledZk.twofield_zk_compiled_ratio_le` at each certified two-field pair, with each side's
output dimension `logv` (`lfzk/scripts/v7-circuit-profiles.json` for v7: the signature
circuit's `logv` is `8` in v7 and `3` in v8; the hash circuit's is `3, 4, 4, 5` for 1–4 attributes
in v7, and `5` for the 4-attribute v8 circuit that `p256sha.sha` models), and the pair's numerals
certified by `native_decide` with the MAC term and both re-commitment terms absorbed:

| pair | `logv₁`, `logv₂` | bound at `N = 0` | coefficient | headline |
|---|---|---|---|---|
| `v7P256Sha1` | 8, 3 | `2^-115.66` | `2^-117.08` | `2^-115 + N · 2^-117` |
| `v7P256Sha2` | 8, 4 | `2^-115.62` | `2^-117.09` | `2^-115 + N · 2^-117` |
| `v7P256Sha3` | 8, 4 | `2^-115.64` | `2^-117.13` | `2^-115 + N · 2^-117` |
| `v7P256Sha4` | 8, 5 | `2^-115.61` | `2^-117.13` | `2^-115 + N · 2^-117` |
| `p256sha` | 3, 5 | `2^-115.44` | `2^-116.94` | `2^-115 + N · 2^-116` |

(the bound column is `zkBound₁ + zkBound₂ + 2^-128 + 2·tape·len2/2^256`, the coefficient column
`max(κ₁, κ₂, 2^-128) + 2·tape/2^256`).  The premises are `twofield_zk_compiled_ratio_le`'s, with
`hr₁`, `hr₂`, the second `|D|` equation and the tape equation discharged.

What is still a hypothesis: per side the `CompiledZkSide` data — in particular the analysis data
`ZkHonest` (with the pending-assertion predicate), `ZkBoundary` and `hinit`, see
`Lfzk.RbrZkLongfellow` — the MAC data and rows, and `|D|`, `|Fmac|`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.TwoFieldV1Rows

open Lfzk.NizkAdaptiveTwoField Lfzk.CertifiedV1 Lfzk.NizkZk

/-- **The two-field re-committing right-hand side at the zero-knowledge accounting, from two slack
numerals.** -/
theorem TwoFieldRowV1.zk_rhs_le_of_slack {R : TwoFieldRowV1} {logv₁ logv₂ a b : ℕ}
    {Fmac : Type} [Fintype Fmac] (hFmac : Fintype.card Fmac = R.macFieldSize)
    (hsb : R.ecdsa.zkBound logv₁ + R.sha.zkBound logv₂ + 1 / (R.macFieldSize : ℚ)
        + 2 * (((R.ecdsa.tape * len2 R.ecdsa R.sha : ℕ) : ℚ) / 2 ^ R.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ a)
    (hsc : max (max (R.ecdsa.zkCoefficient logv₁) (R.sha.zkCoefficient logv₂))
          (1 / (R.macFieldSize : ℚ))
        + 2 * ((R.ecdsa.tape : ℚ) / 2 ^ R.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ b)
    (N : ℕ) :
    R.ecdsa.zkBound logv₁ + R.sha.zkBound logv₂ + 1 / (Fintype.card Fmac : ℚ)
        + N * max (max (R.ecdsa.zkCoefficient logv₁) (R.sha.zkCoefficient logv₂))
            (1 / (Fintype.card Fmac : ℚ))
        + 2 * (((R.ecdsa.tape * (len2 R.ecdsa R.sha + N) : ℕ) : ℚ)
          / 2 ^ R.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ a + N * ((1 : ℚ) / 2 ^ b) := by
  have hmf : (Fintype.card Fmac : ℚ) = (R.macFieldSize : ℚ) := by rw [hFmac]
  rw [hmf]
  have hsplit : 2 * (((R.ecdsa.tape * (len2 R.ecdsa R.sha + N) : ℕ) : ℚ)
        / 2 ^ R.ecdsa.params.digestBits)
      = 2 * (((R.ecdsa.tape * len2 R.ecdsa R.sha : ℕ) : ℚ) / 2 ^ R.ecdsa.params.digestBits)
        + N * (2 * ((R.ecdsa.tape : ℚ) / 2 ^ R.ecdsa.params.digestBits)) := by
    push_cast
    ring
  rw [hsplit]
  have hN : (0 : ℚ) ≤ N := Nat.cast_nonneg N
  have := mul_le_mul_of_nonneg_left hsc hN
  nlinarith

/-- `v7P256Sha1` at the zero-knowledge accounting (`logv = 8, 3`), at `N = 0`: at most `2^-115`. -/
theorem v7P256Sha1_zk_slack_bound :
    v7P256Sha1.ecdsa.zkBound 8 + v7P256Sha1.sha.zkBound 3 + 1 / (v7P256Sha1.macFieldSize : ℚ)
        + 2 * (((v7P256Sha1.ecdsa.tape * len2 v7P256Sha1.ecdsa v7P256Sha1.sha : ℕ) : ℚ)
          / 2 ^ v7P256Sha1.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ 115 := by
  native_decide

/-- `v7P256Sha1`'s worst zero-knowledge coefficient plus the per-query term: at most `2^-117`. -/
theorem v7P256Sha1_zk_slack_coeff :
    max (max (v7P256Sha1.ecdsa.zkCoefficient 8) (v7P256Sha1.sha.zkCoefficient 3))
        (1 / (v7P256Sha1.macFieldSize : ℚ))
      + 2 * ((v7P256Sha1.ecdsa.tape : ℚ) / 2 ^ v7P256Sha1.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ 117 := by
  native_decide

/-- **`v7P256Sha1`'s zero-knowledge numerals**: within `2^-115 + N · 2^-117`. -/
theorem v7P256Sha1_zk_rhs_le (N : ℕ) {Fmac : Type} [Fintype Fmac]
    (hFmac : Fintype.card Fmac = 2 ^ 128) :
    v7P256Sha1.ecdsa.zkBound 8 + v7P256Sha1.sha.zkBound 3 + 1 / (Fintype.card Fmac : ℚ)
        + N * max (max (v7P256Sha1.ecdsa.zkCoefficient 8) (v7P256Sha1.sha.zkCoefficient 3))
            (1 / (Fintype.card Fmac : ℚ))
        + 2 * (((v7P256Sha1.ecdsa.tape * (len2 v7P256Sha1.ecdsa v7P256Sha1.sha + N) : ℕ) : ℚ)
          / 2 ^ v7P256Sha1.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 117) :=
  TwoFieldRowV1.zk_rhs_le_of_slack hFmac v7P256Sha1_zk_slack_bound v7P256Sha1_zk_slack_coeff N

/-- `v7P256Sha2` at the zero-knowledge accounting (`logv = 8, 4`), at `N = 0`: at most `2^-115`. -/
theorem v7P256Sha2_zk_slack_bound :
    v7P256Sha2.ecdsa.zkBound 8 + v7P256Sha2.sha.zkBound 4 + 1 / (v7P256Sha2.macFieldSize : ℚ)
        + 2 * (((v7P256Sha2.ecdsa.tape * len2 v7P256Sha2.ecdsa v7P256Sha2.sha : ℕ) : ℚ)
          / 2 ^ v7P256Sha2.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ 115 := by
  native_decide

/-- `v7P256Sha2`'s worst zero-knowledge coefficient plus the per-query term: at most `2^-117`. -/
theorem v7P256Sha2_zk_slack_coeff :
    max (max (v7P256Sha2.ecdsa.zkCoefficient 8) (v7P256Sha2.sha.zkCoefficient 4))
        (1 / (v7P256Sha2.macFieldSize : ℚ))
      + 2 * ((v7P256Sha2.ecdsa.tape : ℚ) / 2 ^ v7P256Sha2.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ 117 := by
  native_decide

/-- **`v7P256Sha2`'s zero-knowledge numerals**: within `2^-115 + N · 2^-117`. -/
theorem v7P256Sha2_zk_rhs_le (N : ℕ) {Fmac : Type} [Fintype Fmac]
    (hFmac : Fintype.card Fmac = 2 ^ 128) :
    v7P256Sha2.ecdsa.zkBound 8 + v7P256Sha2.sha.zkBound 4 + 1 / (Fintype.card Fmac : ℚ)
        + N * max (max (v7P256Sha2.ecdsa.zkCoefficient 8) (v7P256Sha2.sha.zkCoefficient 4))
            (1 / (Fintype.card Fmac : ℚ))
        + 2 * (((v7P256Sha2.ecdsa.tape * (len2 v7P256Sha2.ecdsa v7P256Sha2.sha + N) : ℕ) : ℚ)
          / 2 ^ v7P256Sha2.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 117) :=
  TwoFieldRowV1.zk_rhs_le_of_slack hFmac v7P256Sha2_zk_slack_bound v7P256Sha2_zk_slack_coeff N

/-- `v7P256Sha3` at the zero-knowledge accounting (`logv = 8, 4`), at `N = 0`: at most `2^-115`. -/
theorem v7P256Sha3_zk_slack_bound :
    v7P256Sha3.ecdsa.zkBound 8 + v7P256Sha3.sha.zkBound 4 + 1 / (v7P256Sha3.macFieldSize : ℚ)
        + 2 * (((v7P256Sha3.ecdsa.tape * len2 v7P256Sha3.ecdsa v7P256Sha3.sha : ℕ) : ℚ)
          / 2 ^ v7P256Sha3.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ 115 := by
  native_decide

/-- `v7P256Sha3`'s worst zero-knowledge coefficient plus the per-query term: at most `2^-117`. -/
theorem v7P256Sha3_zk_slack_coeff :
    max (max (v7P256Sha3.ecdsa.zkCoefficient 8) (v7P256Sha3.sha.zkCoefficient 4))
        (1 / (v7P256Sha3.macFieldSize : ℚ))
      + 2 * ((v7P256Sha3.ecdsa.tape : ℚ) / 2 ^ v7P256Sha3.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ 117 := by
  native_decide

/-- **`v7P256Sha3`'s zero-knowledge numerals**: within `2^-115 + N · 2^-117`. -/
theorem v7P256Sha3_zk_rhs_le (N : ℕ) {Fmac : Type} [Fintype Fmac]
    (hFmac : Fintype.card Fmac = 2 ^ 128) :
    v7P256Sha3.ecdsa.zkBound 8 + v7P256Sha3.sha.zkBound 4 + 1 / (Fintype.card Fmac : ℚ)
        + N * max (max (v7P256Sha3.ecdsa.zkCoefficient 8) (v7P256Sha3.sha.zkCoefficient 4))
            (1 / (Fintype.card Fmac : ℚ))
        + 2 * (((v7P256Sha3.ecdsa.tape * (len2 v7P256Sha3.ecdsa v7P256Sha3.sha + N) : ℕ) : ℚ)
          / 2 ^ v7P256Sha3.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 117) :=
  TwoFieldRowV1.zk_rhs_le_of_slack hFmac v7P256Sha3_zk_slack_bound v7P256Sha3_zk_slack_coeff N

/-- `v7P256Sha4` at the zero-knowledge accounting (`logv = 8, 5`), at `N = 0`: at most `2^-115`. -/
theorem v7P256Sha4_zk_slack_bound :
    v7P256Sha4.ecdsa.zkBound 8 + v7P256Sha4.sha.zkBound 5 + 1 / (v7P256Sha4.macFieldSize : ℚ)
        + 2 * (((v7P256Sha4.ecdsa.tape * len2 v7P256Sha4.ecdsa v7P256Sha4.sha : ℕ) : ℚ)
          / 2 ^ v7P256Sha4.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ 115 := by
  native_decide

/-- `v7P256Sha4`'s worst zero-knowledge coefficient plus the per-query term: at most `2^-117`. -/
theorem v7P256Sha4_zk_slack_coeff :
    max (max (v7P256Sha4.ecdsa.zkCoefficient 8) (v7P256Sha4.sha.zkCoefficient 5))
        (1 / (v7P256Sha4.macFieldSize : ℚ))
      + 2 * ((v7P256Sha4.ecdsa.tape : ℚ) / 2 ^ v7P256Sha4.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ 117 := by
  native_decide

/-- **`v7P256Sha4`'s zero-knowledge numerals**: within `2^-115 + N · 2^-117`. -/
theorem v7P256Sha4_zk_rhs_le (N : ℕ) {Fmac : Type} [Fintype Fmac]
    (hFmac : Fintype.card Fmac = 2 ^ 128) :
    v7P256Sha4.ecdsa.zkBound 8 + v7P256Sha4.sha.zkBound 5 + 1 / (Fintype.card Fmac : ℚ)
        + N * max (max (v7P256Sha4.ecdsa.zkCoefficient 8) (v7P256Sha4.sha.zkCoefficient 5))
            (1 / (Fintype.card Fmac : ℚ))
        + 2 * (((v7P256Sha4.ecdsa.tape * (len2 v7P256Sha4.ecdsa v7P256Sha4.sha + N) : ℕ) : ℚ)
          / 2 ^ v7P256Sha4.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 117) :=
  TwoFieldRowV1.zk_rhs_le_of_slack hFmac v7P256Sha4_zk_slack_bound v7P256Sha4_zk_slack_coeff N

/-- `p256sha` at the zero-knowledge accounting (`logv = 3, 5`), at `N = 0`: at most `2^-115`. -/
theorem p256sha_zk_slack_bound :
    p256sha.ecdsa.zkBound 3 + p256sha.sha.zkBound 5 + 1 / (p256sha.macFieldSize : ℚ)
        + 2 * (((p256sha.ecdsa.tape * len2 p256sha.ecdsa p256sha.sha : ℕ) : ℚ)
          / 2 ^ p256sha.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ 115 := by
  native_decide

/-- `p256sha`'s worst zero-knowledge coefficient plus the per-query term: at most `2^-116`. -/
theorem p256sha_zk_slack_coeff :
    max (max (p256sha.ecdsa.zkCoefficient 3) (p256sha.sha.zkCoefficient 5))
        (1 / (p256sha.macFieldSize : ℚ))
      + 2 * ((p256sha.ecdsa.tape : ℚ) / 2 ^ p256sha.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ 116 := by
  native_decide

/-- **`p256sha`'s zero-knowledge numerals**: within `2^-115 + N · 2^-116`. -/
theorem p256sha_zk_rhs_le (N : ℕ) {Fmac : Type} [Fintype Fmac]
    (hFmac : Fintype.card Fmac = 2 ^ 128) :
    p256sha.ecdsa.zkBound 3 + p256sha.sha.zkBound 5 + 1 / (Fintype.card Fmac : ℚ)
        + N * max (max (p256sha.ecdsa.zkCoefficient 3) (p256sha.sha.zkCoefficient 5))
            (1 / (Fintype.card Fmac : ℚ))
        + 2 * (((p256sha.ecdsa.tape * (len2 p256sha.ecdsa p256sha.sha + N) : ℕ) : ℚ)
          / 2 ^ p256sha.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 116) :=
  TwoFieldRowV1.zk_rhs_le_of_slack hFmac p256sha_zk_slack_bound p256sha_zk_slack_coeff N

end Lfzk.TwoFieldV1Rows

namespace Lfzk.CompiledZk

open Finset Bcs Bcs.AdaptiveCommit Merkle Merkle.MH Merkle.RandomOracle
  Merkle.RandomOracle.TwoOracleTree RbrLongfellow Lfzk.NizkGrinding Lfzk.NizkAdaptive
  Lfzk.RbrLayerStepS Lfzk.RbrZkLongfellow Lfzk.RbrZkSplit Lfzk.NizkZk Lfzk.ZkLigeroV1
  Lfzk.CompiledLongfellow Lfzk.CompiledLongfellowAdaptive Lfzk.NizkAdaptiveTwoField
  Lfzk.NizkZkTwoField Lfzk.CertifiedV1 Lfzk.Mac Lfzk.TwoFieldV1Rows
open scoped Classical

section Rows

variable {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]
variable {D : Type} [Fintype D] [DecidableEq D] [Inhabited D]
variable {Enc X Out : Type} [DecidableEq Enc]
variable {Fmac : Type} [Field Fmac] [Fintype Fmac] [DecidableEq Fmac] {nblk : ℕ}
variable {F₁ Msg₁ Witness₁ : Type} [Field F₁] [Fintype F₁] [DecidableEq F₁] [SumcheckInterp F₁]
  [DecidableEq Msg₁] [Inhabited Msg₁] {M₁ ninp₁ nt₁ nlin₁ logw₁ logc₁ : ℕ}
variable {F₂ Msg₂ Witness₂ : Type} [Field F₂] [Fintype F₂] [DecidableEq F₂] [SumcheckInterp F₂]
  [DecidableEq Msg₂] [Inhabited Msg₂] {M₂ ninp₂ nt₂ nlin₂ logw₂ logc₂ : ℕ}
variable {Salt₁ Salt₂ : Type} [Inhabited Salt₁] [Inhabited Salt₂]

omit [DecidableEq Msg₁] [DecidableEq Msg₂] in
/--
**Two-field Longfellow at `v7P256Sha1`, at the deployed zero-knowledge verifiers, against one
re-committing Fiat–Shamir prover with a hashed MAC key.**

`twofield_zk_compiled_ratio_le` at `TwoFieldV1Rows.v7P256Sha1` (the deployed v7 pair for 1 attribute: ECDSA over `P-256`'s base field (`CertifiedV1.v7Sig`) and SHA-256 over `GF(2^128)` (`CertifiedV1.v7Hash1`), Ligero V1 at 132
openings, the MAC over a field of `2^128` elements), output dimensions `logv = 8, 3`, with the
numerals `TwoFieldV1Rows.v7P256Sha1_zk_rhs_le`: against one adaptive program making at most `tA ≤ 2^60`
Merkle-oracle and `N` challenge-oracle queries,

```text
Pr [ both deployed verifiers accept  ∧  no two good witnesses agree on the common value ]
    ≤  2^-115  +  N · 2^-117
```

The premises are `twofield_zk_compiled_ratio_le`'s; `hr₁`, `hr₂` are discharged.
-/
theorem v7P256Sha1_zk_compiled_ratio_le {tA N : ℕ} (hFmac : Fintype.card Fmac = 2 ^ 128)
    {codec₁ : Codec Salt₁ (Col F₁ v7P256Sha1.ecdsa.params.nw v7P256Sha1.ecdsa.params.nq) D Enc}
    {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ v7P256Sha1.sha.params.nw v7P256Sha1.sha.params.nq) D Enc}
    {dec₂ : RoleDecoders codec₂}
    (L₁ : CompiledZkSide v7P256Sha1.ecdsa (TwoFieldRowV1.ecdsa_valid v7P256Sha1_valid) v7P256Sha1_ecdsa_openings_pos 8 C F₁ Msg₁ Witness₁
      M₁ ninp₁ nt₁ nlin₁ logw₁ logc₁ X dec₁ Prod.fst)
    (L₂ : CompiledZkSide v7P256Sha1.sha (TwoFieldRowV1.sha_valid v7P256Sha1_valid) v7P256Sha1_sha_openings_pos 3 C F₂ Msg₂ Witness₂
      M₂ ninp₂ nt₂ nlin₂ logw₂ logc₂ X dec₂ Prod.snd)
    (body : TwoOracleTree Enc D (Pt2 D C X Msg₁ Msg₂ v7P256Sha1.ecdsa.params.nl
      v7P256Sha1.sha.params.nl v7P256Sha1.ecdsa.params.rounds v7P256Sha1.sha.params.rounds) C Out tA N)
    (dflt : C) (rootOf₁ rootOf₂ : Out → D) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim v7P256Sha1.ecdsa.params.row.n Salt₁
      (Col F₁ v7P256Sha1.ecdsa.params.nw v7P256Sha1.ecdsa.params.nq) D)
    (claimOf₂ : Out → OpeningClaim v7P256Sha1.sha.params.row.n Salt₂
      (Col F₂ v7P256Sha1.sha.params.nw v7P256Sha1.sha.params.nq) D)
    (hD : Fintype.card D = 2 ^ v7P256Sha1.ecdsa.params.digestBits)
    (aP : (D × D) × List (Enc × D) → Fmac) (decode : C → Fmac) (kmac : ℕ)
    (hbal : ∀ x : Fmac, (univ.filter fun c : C => decode c = x).card ≤ kmac)
    (hmac : kmac * Fintype.card Fmac ≤ Fintype.card C)
    (keyB tagOf : Out → Fin nblk → Fmac)
    (common₁ : Witness₁ → Fin nblk → Fmac) (common₂ : Witness₂ → Fin nblk → Fmac)
    (hrow₁ : ∀ (mt : Fin v7P256Sha1.ecdsa.tape → D)
      (ct : Fin (len2 v7P256Sha1.ecdsa v7P256Sha1.sha + N) → C) (a : Witness₁),
      let S := setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂
      L₁.accepts S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ pubOf
        (len2_pos _ _) (slice1 v7P256Sha1.ecdsa v7P256Sha1.sha) mt ct →
      L₁.Good (sideCtx S pubOf (len2_pos _ _) mt ct) a →
      macTag (aP (S.context mt ct) + decode (S.challenges mt ct ⟨0, len2_pos _ _⟩))
        (keyB (S.proof mt ct)) (common₁ a) = tagOf (S.proof mt ct))
    (hrow₂ : ∀ (mt : Fin v7P256Sha1.ecdsa.tape → D)
      (ct : Fin (len2 v7P256Sha1.ecdsa v7P256Sha1.sha + N) → C) (a : Witness₂),
      let S := setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂
      L₂.accepts S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ pubOf
        (len2_pos _ _) (slice2 v7P256Sha1.ecdsa v7P256Sha1.sha) mt ct →
      L₂.Good (sideCtx S pubOf (len2_pos _ _) mt ct) a →
      macTag (aP (S.context mt ct) + decode (S.challenges mt ct ⟨0, len2_pos _ _⟩))
        (keyB (S.proof mt ct)) (common₂ a) = tagOf (S.proof mt ct))
    (htA : tA ≤ 2 ^ 60)
    (htape : 2 * v7P256Sha1.sha.params.row.n + 2 * v7P256Sha1.ecdsa.params.row.n + tA ≤ 2 ^ 62) :
    ((univ.filter fun ω : (Fin v7P256Sha1.ecdsa.tape → D) ×
          (Fin (len2 v7P256Sha1.ecdsa v7P256Sha1.sha + N) → C) =>
        L₁.accepts (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ pubOf (len2_pos _ _)
            (slice1 v7P256Sha1.ecdsa v7P256Sha1.sha) ω.1 ω.2 ∧
          L₂.accepts (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ pubOf (len2_pos _ _)
            (slice2 v7P256Sha1.ecdsa v7P256Sha1.sha) ω.1 ω.2 ∧
          ¬ ∃ a₁ a₂,
            L₁.Good (sideCtx (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂) pubOf
              (len2_pos _ _) ω.1 ω.2) a₁ ∧
            L₂.Good (sideCtx (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂) pubOf
              (len2_pos _ _) ω.1 ω.2) a₂ ∧
            common₁ a₁ = common₂ a₂).card : ℚ)
        / ((Fintype.card D : ℚ) ^ v7P256Sha1.ecdsa.tape *
            (Fintype.card C : ℚ) ^ (len2 v7P256Sha1.ecdsa v7P256Sha1.sha + N))
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 117) :=
  le_trans
    (twofield_zk_compiled_ratio_le (TwoFieldRowV1.ecdsa_valid v7P256Sha1_valid) (TwoFieldRowV1.sha_valid v7P256Sha1_valid) v7P256Sha1_ecdsa_openings_pos v7P256Sha1_sha_openings_pos
      L₁ L₂ body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂ claimOf₁ claimOf₂ hD hD
      aP decode kmac hbal hmac keyB tagOf common₁ common₂ hrow₁ hrow₂ htA htA htape rfl)
    (v7P256Sha1_zk_rhs_le N hFmac)

omit [DecidableEq Msg₁] [DecidableEq Msg₂] in
/--
**Two-field Longfellow at `v7P256Sha2`, at the deployed zero-knowledge verifiers, against one
re-committing Fiat–Shamir prover with a hashed MAC key.**

`twofield_zk_compiled_ratio_le` at `TwoFieldV1Rows.v7P256Sha2` (the deployed v7 pair for 2 attributes: ECDSA over `P-256`'s base field (`CertifiedV1.v7Sig`) and SHA-256 over `GF(2^128)` (`CertifiedV1.v7Hash2`), Ligero V1 at 132
openings, the MAC over a field of `2^128` elements), output dimensions `logv = 8, 4`, with the
numerals `TwoFieldV1Rows.v7P256Sha2_zk_rhs_le`: against one adaptive program making at most `tA ≤ 2^60`
Merkle-oracle and `N` challenge-oracle queries,

```text
Pr [ both deployed verifiers accept  ∧  no two good witnesses agree on the common value ]
    ≤  2^-115  +  N · 2^-117
```

The premises are `twofield_zk_compiled_ratio_le`'s; `hr₁`, `hr₂` are discharged.
-/
theorem v7P256Sha2_zk_compiled_ratio_le {tA N : ℕ} (hFmac : Fintype.card Fmac = 2 ^ 128)
    {codec₁ : Codec Salt₁ (Col F₁ v7P256Sha2.ecdsa.params.nw v7P256Sha2.ecdsa.params.nq) D Enc}
    {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ v7P256Sha2.sha.params.nw v7P256Sha2.sha.params.nq) D Enc}
    {dec₂ : RoleDecoders codec₂}
    (L₁ : CompiledZkSide v7P256Sha2.ecdsa (TwoFieldRowV1.ecdsa_valid v7P256Sha2_valid) v7P256Sha2_ecdsa_openings_pos 8 C F₁ Msg₁ Witness₁
      M₁ ninp₁ nt₁ nlin₁ logw₁ logc₁ X dec₁ Prod.fst)
    (L₂ : CompiledZkSide v7P256Sha2.sha (TwoFieldRowV1.sha_valid v7P256Sha2_valid) v7P256Sha2_sha_openings_pos 4 C F₂ Msg₂ Witness₂
      M₂ ninp₂ nt₂ nlin₂ logw₂ logc₂ X dec₂ Prod.snd)
    (body : TwoOracleTree Enc D (Pt2 D C X Msg₁ Msg₂ v7P256Sha2.ecdsa.params.nl
      v7P256Sha2.sha.params.nl v7P256Sha2.ecdsa.params.rounds v7P256Sha2.sha.params.rounds) C Out tA N)
    (dflt : C) (rootOf₁ rootOf₂ : Out → D) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim v7P256Sha2.ecdsa.params.row.n Salt₁
      (Col F₁ v7P256Sha2.ecdsa.params.nw v7P256Sha2.ecdsa.params.nq) D)
    (claimOf₂ : Out → OpeningClaim v7P256Sha2.sha.params.row.n Salt₂
      (Col F₂ v7P256Sha2.sha.params.nw v7P256Sha2.sha.params.nq) D)
    (hD : Fintype.card D = 2 ^ v7P256Sha2.ecdsa.params.digestBits)
    (aP : (D × D) × List (Enc × D) → Fmac) (decode : C → Fmac) (kmac : ℕ)
    (hbal : ∀ x : Fmac, (univ.filter fun c : C => decode c = x).card ≤ kmac)
    (hmac : kmac * Fintype.card Fmac ≤ Fintype.card C)
    (keyB tagOf : Out → Fin nblk → Fmac)
    (common₁ : Witness₁ → Fin nblk → Fmac) (common₂ : Witness₂ → Fin nblk → Fmac)
    (hrow₁ : ∀ (mt : Fin v7P256Sha2.ecdsa.tape → D)
      (ct : Fin (len2 v7P256Sha2.ecdsa v7P256Sha2.sha + N) → C) (a : Witness₁),
      let S := setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂
      L₁.accepts S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ pubOf
        (len2_pos _ _) (slice1 v7P256Sha2.ecdsa v7P256Sha2.sha) mt ct →
      L₁.Good (sideCtx S pubOf (len2_pos _ _) mt ct) a →
      macTag (aP (S.context mt ct) + decode (S.challenges mt ct ⟨0, len2_pos _ _⟩))
        (keyB (S.proof mt ct)) (common₁ a) = tagOf (S.proof mt ct))
    (hrow₂ : ∀ (mt : Fin v7P256Sha2.ecdsa.tape → D)
      (ct : Fin (len2 v7P256Sha2.ecdsa v7P256Sha2.sha + N) → C) (a : Witness₂),
      let S := setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂
      L₂.accepts S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ pubOf
        (len2_pos _ _) (slice2 v7P256Sha2.ecdsa v7P256Sha2.sha) mt ct →
      L₂.Good (sideCtx S pubOf (len2_pos _ _) mt ct) a →
      macTag (aP (S.context mt ct) + decode (S.challenges mt ct ⟨0, len2_pos _ _⟩))
        (keyB (S.proof mt ct)) (common₂ a) = tagOf (S.proof mt ct))
    (htA : tA ≤ 2 ^ 60)
    (htape : 2 * v7P256Sha2.sha.params.row.n + 2 * v7P256Sha2.ecdsa.params.row.n + tA ≤ 2 ^ 62) :
    ((univ.filter fun ω : (Fin v7P256Sha2.ecdsa.tape → D) ×
          (Fin (len2 v7P256Sha2.ecdsa v7P256Sha2.sha + N) → C) =>
        L₁.accepts (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ pubOf (len2_pos _ _)
            (slice1 v7P256Sha2.ecdsa v7P256Sha2.sha) ω.1 ω.2 ∧
          L₂.accepts (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ pubOf (len2_pos _ _)
            (slice2 v7P256Sha2.ecdsa v7P256Sha2.sha) ω.1 ω.2 ∧
          ¬ ∃ a₁ a₂,
            L₁.Good (sideCtx (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂) pubOf
              (len2_pos _ _) ω.1 ω.2) a₁ ∧
            L₂.Good (sideCtx (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂) pubOf
              (len2_pos _ _) ω.1 ω.2) a₂ ∧
            common₁ a₁ = common₂ a₂).card : ℚ)
        / ((Fintype.card D : ℚ) ^ v7P256Sha2.ecdsa.tape *
            (Fintype.card C : ℚ) ^ (len2 v7P256Sha2.ecdsa v7P256Sha2.sha + N))
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 117) :=
  le_trans
    (twofield_zk_compiled_ratio_le (TwoFieldRowV1.ecdsa_valid v7P256Sha2_valid) (TwoFieldRowV1.sha_valid v7P256Sha2_valid) v7P256Sha2_ecdsa_openings_pos v7P256Sha2_sha_openings_pos
      L₁ L₂ body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂ claimOf₁ claimOf₂ hD hD
      aP decode kmac hbal hmac keyB tagOf common₁ common₂ hrow₁ hrow₂ htA htA htape rfl)
    (v7P256Sha2_zk_rhs_le N hFmac)

omit [DecidableEq Msg₁] [DecidableEq Msg₂] in
/--
**Two-field Longfellow at `v7P256Sha3`, at the deployed zero-knowledge verifiers, against one
re-committing Fiat–Shamir prover with a hashed MAC key.**

`twofield_zk_compiled_ratio_le` at `TwoFieldV1Rows.v7P256Sha3` (the deployed v7 pair for 3 attributes: ECDSA over `P-256`'s base field (`CertifiedV1.v7Sig`) and SHA-256 over `GF(2^128)` (`CertifiedV1.v7Hash3`), Ligero V1 at 132
openings, the MAC over a field of `2^128` elements), output dimensions `logv = 8, 4`, with the
numerals `TwoFieldV1Rows.v7P256Sha3_zk_rhs_le`: against one adaptive program making at most `tA ≤ 2^60`
Merkle-oracle and `N` challenge-oracle queries,

```text
Pr [ both deployed verifiers accept  ∧  no two good witnesses agree on the common value ]
    ≤  2^-115  +  N · 2^-117
```

The premises are `twofield_zk_compiled_ratio_le`'s; `hr₁`, `hr₂` are discharged.
-/
theorem v7P256Sha3_zk_compiled_ratio_le {tA N : ℕ} (hFmac : Fintype.card Fmac = 2 ^ 128)
    {codec₁ : Codec Salt₁ (Col F₁ v7P256Sha3.ecdsa.params.nw v7P256Sha3.ecdsa.params.nq) D Enc}
    {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ v7P256Sha3.sha.params.nw v7P256Sha3.sha.params.nq) D Enc}
    {dec₂ : RoleDecoders codec₂}
    (L₁ : CompiledZkSide v7P256Sha3.ecdsa (TwoFieldRowV1.ecdsa_valid v7P256Sha3_valid) v7P256Sha3_ecdsa_openings_pos 8 C F₁ Msg₁ Witness₁
      M₁ ninp₁ nt₁ nlin₁ logw₁ logc₁ X dec₁ Prod.fst)
    (L₂ : CompiledZkSide v7P256Sha3.sha (TwoFieldRowV1.sha_valid v7P256Sha3_valid) v7P256Sha3_sha_openings_pos 4 C F₂ Msg₂ Witness₂
      M₂ ninp₂ nt₂ nlin₂ logw₂ logc₂ X dec₂ Prod.snd)
    (body : TwoOracleTree Enc D (Pt2 D C X Msg₁ Msg₂ v7P256Sha3.ecdsa.params.nl
      v7P256Sha3.sha.params.nl v7P256Sha3.ecdsa.params.rounds v7P256Sha3.sha.params.rounds) C Out tA N)
    (dflt : C) (rootOf₁ rootOf₂ : Out → D) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim v7P256Sha3.ecdsa.params.row.n Salt₁
      (Col F₁ v7P256Sha3.ecdsa.params.nw v7P256Sha3.ecdsa.params.nq) D)
    (claimOf₂ : Out → OpeningClaim v7P256Sha3.sha.params.row.n Salt₂
      (Col F₂ v7P256Sha3.sha.params.nw v7P256Sha3.sha.params.nq) D)
    (hD : Fintype.card D = 2 ^ v7P256Sha3.ecdsa.params.digestBits)
    (aP : (D × D) × List (Enc × D) → Fmac) (decode : C → Fmac) (kmac : ℕ)
    (hbal : ∀ x : Fmac, (univ.filter fun c : C => decode c = x).card ≤ kmac)
    (hmac : kmac * Fintype.card Fmac ≤ Fintype.card C)
    (keyB tagOf : Out → Fin nblk → Fmac)
    (common₁ : Witness₁ → Fin nblk → Fmac) (common₂ : Witness₂ → Fin nblk → Fmac)
    (hrow₁ : ∀ (mt : Fin v7P256Sha3.ecdsa.tape → D)
      (ct : Fin (len2 v7P256Sha3.ecdsa v7P256Sha3.sha + N) → C) (a : Witness₁),
      let S := setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂
      L₁.accepts S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ pubOf
        (len2_pos _ _) (slice1 v7P256Sha3.ecdsa v7P256Sha3.sha) mt ct →
      L₁.Good (sideCtx S pubOf (len2_pos _ _) mt ct) a →
      macTag (aP (S.context mt ct) + decode (S.challenges mt ct ⟨0, len2_pos _ _⟩))
        (keyB (S.proof mt ct)) (common₁ a) = tagOf (S.proof mt ct))
    (hrow₂ : ∀ (mt : Fin v7P256Sha3.ecdsa.tape → D)
      (ct : Fin (len2 v7P256Sha3.ecdsa v7P256Sha3.sha + N) → C) (a : Witness₂),
      let S := setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂
      L₂.accepts S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ pubOf
        (len2_pos _ _) (slice2 v7P256Sha3.ecdsa v7P256Sha3.sha) mt ct →
      L₂.Good (sideCtx S pubOf (len2_pos _ _) mt ct) a →
      macTag (aP (S.context mt ct) + decode (S.challenges mt ct ⟨0, len2_pos _ _⟩))
        (keyB (S.proof mt ct)) (common₂ a) = tagOf (S.proof mt ct))
    (htA : tA ≤ 2 ^ 60)
    (htape : 2 * v7P256Sha3.sha.params.row.n + 2 * v7P256Sha3.ecdsa.params.row.n + tA ≤ 2 ^ 62) :
    ((univ.filter fun ω : (Fin v7P256Sha3.ecdsa.tape → D) ×
          (Fin (len2 v7P256Sha3.ecdsa v7P256Sha3.sha + N) → C) =>
        L₁.accepts (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ pubOf (len2_pos _ _)
            (slice1 v7P256Sha3.ecdsa v7P256Sha3.sha) ω.1 ω.2 ∧
          L₂.accepts (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ pubOf (len2_pos _ _)
            (slice2 v7P256Sha3.ecdsa v7P256Sha3.sha) ω.1 ω.2 ∧
          ¬ ∃ a₁ a₂,
            L₁.Good (sideCtx (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂) pubOf
              (len2_pos _ _) ω.1 ω.2) a₁ ∧
            L₂.Good (sideCtx (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂) pubOf
              (len2_pos _ _) ω.1 ω.2) a₂ ∧
            common₁ a₁ = common₂ a₂).card : ℚ)
        / ((Fintype.card D : ℚ) ^ v7P256Sha3.ecdsa.tape *
            (Fintype.card C : ℚ) ^ (len2 v7P256Sha3.ecdsa v7P256Sha3.sha + N))
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 117) :=
  le_trans
    (twofield_zk_compiled_ratio_le (TwoFieldRowV1.ecdsa_valid v7P256Sha3_valid) (TwoFieldRowV1.sha_valid v7P256Sha3_valid) v7P256Sha3_ecdsa_openings_pos v7P256Sha3_sha_openings_pos
      L₁ L₂ body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂ claimOf₁ claimOf₂ hD hD
      aP decode kmac hbal hmac keyB tagOf common₁ common₂ hrow₁ hrow₂ htA htA htape rfl)
    (v7P256Sha3_zk_rhs_le N hFmac)

omit [DecidableEq Msg₁] [DecidableEq Msg₂] in
/--
**Two-field Longfellow at `v7P256Sha4`, at the deployed zero-knowledge verifiers, against one
re-committing Fiat–Shamir prover with a hashed MAC key.**

`twofield_zk_compiled_ratio_le` at `TwoFieldV1Rows.v7P256Sha4` (the deployed v7 pair for 4 attributes: ECDSA over `P-256`'s base field (`CertifiedV1.v7Sig`) and SHA-256 over `GF(2^128)` (`CertifiedV1.v7Hash4`), Ligero V1 at 132
openings, the MAC over a field of `2^128` elements), output dimensions `logv = 8, 5`, with the
numerals `TwoFieldV1Rows.v7P256Sha4_zk_rhs_le`: against one adaptive program making at most `tA ≤ 2^60`
Merkle-oracle and `N` challenge-oracle queries,

```text
Pr [ both deployed verifiers accept  ∧  no two good witnesses agree on the common value ]
    ≤  2^-115  +  N · 2^-117
```

The premises are `twofield_zk_compiled_ratio_le`'s; `hr₁`, `hr₂` are discharged.
-/
theorem v7P256Sha4_zk_compiled_ratio_le {tA N : ℕ} (hFmac : Fintype.card Fmac = 2 ^ 128)
    {codec₁ : Codec Salt₁ (Col F₁ v7P256Sha4.ecdsa.params.nw v7P256Sha4.ecdsa.params.nq) D Enc}
    {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ v7P256Sha4.sha.params.nw v7P256Sha4.sha.params.nq) D Enc}
    {dec₂ : RoleDecoders codec₂}
    (L₁ : CompiledZkSide v7P256Sha4.ecdsa (TwoFieldRowV1.ecdsa_valid v7P256Sha4_valid) v7P256Sha4_ecdsa_openings_pos 8 C F₁ Msg₁ Witness₁
      M₁ ninp₁ nt₁ nlin₁ logw₁ logc₁ X dec₁ Prod.fst)
    (L₂ : CompiledZkSide v7P256Sha4.sha (TwoFieldRowV1.sha_valid v7P256Sha4_valid) v7P256Sha4_sha_openings_pos 5 C F₂ Msg₂ Witness₂
      M₂ ninp₂ nt₂ nlin₂ logw₂ logc₂ X dec₂ Prod.snd)
    (body : TwoOracleTree Enc D (Pt2 D C X Msg₁ Msg₂ v7P256Sha4.ecdsa.params.nl
      v7P256Sha4.sha.params.nl v7P256Sha4.ecdsa.params.rounds v7P256Sha4.sha.params.rounds) C Out tA N)
    (dflt : C) (rootOf₁ rootOf₂ : Out → D) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim v7P256Sha4.ecdsa.params.row.n Salt₁
      (Col F₁ v7P256Sha4.ecdsa.params.nw v7P256Sha4.ecdsa.params.nq) D)
    (claimOf₂ : Out → OpeningClaim v7P256Sha4.sha.params.row.n Salt₂
      (Col F₂ v7P256Sha4.sha.params.nw v7P256Sha4.sha.params.nq) D)
    (hD : Fintype.card D = 2 ^ v7P256Sha4.ecdsa.params.digestBits)
    (aP : (D × D) × List (Enc × D) → Fmac) (decode : C → Fmac) (kmac : ℕ)
    (hbal : ∀ x : Fmac, (univ.filter fun c : C => decode c = x).card ≤ kmac)
    (hmac : kmac * Fintype.card Fmac ≤ Fintype.card C)
    (keyB tagOf : Out → Fin nblk → Fmac)
    (common₁ : Witness₁ → Fin nblk → Fmac) (common₂ : Witness₂ → Fin nblk → Fmac)
    (hrow₁ : ∀ (mt : Fin v7P256Sha4.ecdsa.tape → D)
      (ct : Fin (len2 v7P256Sha4.ecdsa v7P256Sha4.sha + N) → C) (a : Witness₁),
      let S := setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂
      L₁.accepts S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ pubOf
        (len2_pos _ _) (slice1 v7P256Sha4.ecdsa v7P256Sha4.sha) mt ct →
      L₁.Good (sideCtx S pubOf (len2_pos _ _) mt ct) a →
      macTag (aP (S.context mt ct) + decode (S.challenges mt ct ⟨0, len2_pos _ _⟩))
        (keyB (S.proof mt ct)) (common₁ a) = tagOf (S.proof mt ct))
    (hrow₂ : ∀ (mt : Fin v7P256Sha4.ecdsa.tape → D)
      (ct : Fin (len2 v7P256Sha4.ecdsa v7P256Sha4.sha + N) → C) (a : Witness₂),
      let S := setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂
      L₂.accepts S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ pubOf
        (len2_pos _ _) (slice2 v7P256Sha4.ecdsa v7P256Sha4.sha) mt ct →
      L₂.Good (sideCtx S pubOf (len2_pos _ _) mt ct) a →
      macTag (aP (S.context mt ct) + decode (S.challenges mt ct ⟨0, len2_pos _ _⟩))
        (keyB (S.proof mt ct)) (common₂ a) = tagOf (S.proof mt ct))
    (htA : tA ≤ 2 ^ 60)
    (htape : 2 * v7P256Sha4.sha.params.row.n + 2 * v7P256Sha4.ecdsa.params.row.n + tA ≤ 2 ^ 62) :
    ((univ.filter fun ω : (Fin v7P256Sha4.ecdsa.tape → D) ×
          (Fin (len2 v7P256Sha4.ecdsa v7P256Sha4.sha + N) → C) =>
        L₁.accepts (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ pubOf (len2_pos _ _)
            (slice1 v7P256Sha4.ecdsa v7P256Sha4.sha) ω.1 ω.2 ∧
          L₂.accepts (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ pubOf (len2_pos _ _)
            (slice2 v7P256Sha4.ecdsa v7P256Sha4.sha) ω.1 ω.2 ∧
          ¬ ∃ a₁ a₂,
            L₁.Good (sideCtx (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂) pubOf
              (len2_pos _ _) ω.1 ω.2) a₁ ∧
            L₂.Good (sideCtx (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂) pubOf
              (len2_pos _ _) ω.1 ω.2) a₂ ∧
            common₁ a₁ = common₂ a₂).card : ℚ)
        / ((Fintype.card D : ℚ) ^ v7P256Sha4.ecdsa.tape *
            (Fintype.card C : ℚ) ^ (len2 v7P256Sha4.ecdsa v7P256Sha4.sha + N))
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 117) :=
  le_trans
    (twofield_zk_compiled_ratio_le (TwoFieldRowV1.ecdsa_valid v7P256Sha4_valid) (TwoFieldRowV1.sha_valid v7P256Sha4_valid) v7P256Sha4_ecdsa_openings_pos v7P256Sha4_sha_openings_pos
      L₁ L₂ body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂ claimOf₁ claimOf₂ hD hD
      aP decode kmac hbal hmac keyB tagOf common₁ common₂ hrow₁ hrow₂ htA htA htape rfl)
    (v7P256Sha4_zk_rhs_le N hFmac)

omit [DecidableEq Msg₁] [DecidableEq Msg₂] in
/--
**Two-field Longfellow at `p256sha`, at the deployed zero-knowledge verifiers, against one
re-committing Fiat–Shamir prover with a hashed MAC key.**

`twofield_zk_compiled_ratio_le` at `TwoFieldV1Rows.p256sha` (the v8 pair (4 attributes): ECDSA over `P-256`'s base field and SHA-256 over `GF(2^128)` at the v8 circuit profiles, Ligero V1 at 132
openings, the MAC over a field of `2^128` elements), output dimensions `logv = 3, 5`, with the
numerals `TwoFieldV1Rows.p256sha_zk_rhs_le`: against one adaptive program making at most `tA ≤ 2^60`
Merkle-oracle and `N` challenge-oracle queries,

```text
Pr [ both deployed verifiers accept  ∧  no two good witnesses agree on the common value ]
    ≤  2^-115  +  N · 2^-116
```

The premises are `twofield_zk_compiled_ratio_le`'s; `hr₁`, `hr₂` are discharged.
-/
theorem p256sha_zk_compiled_ratio_le {tA N : ℕ} (hFmac : Fintype.card Fmac = 2 ^ 128)
    {codec₁ : Codec Salt₁ (Col F₁ p256sha.ecdsa.params.nw p256sha.ecdsa.params.nq) D Enc}
    {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ p256sha.sha.params.nw p256sha.sha.params.nq) D Enc}
    {dec₂ : RoleDecoders codec₂}
    (L₁ : CompiledZkSide p256sha.ecdsa (TwoFieldRowV1.ecdsa_valid p256sha_valid) p256sha_ecdsa_openings_pos 3 C F₁ Msg₁ Witness₁
      M₁ ninp₁ nt₁ nlin₁ logw₁ logc₁ X dec₁ Prod.fst)
    (L₂ : CompiledZkSide p256sha.sha (TwoFieldRowV1.sha_valid p256sha_valid) p256sha_sha_openings_pos 5 C F₂ Msg₂ Witness₂
      M₂ ninp₂ nt₂ nlin₂ logw₂ logc₂ X dec₂ Prod.snd)
    (body : TwoOracleTree Enc D (Pt2 D C X Msg₁ Msg₂ p256sha.ecdsa.params.nl
      p256sha.sha.params.nl p256sha.ecdsa.params.rounds p256sha.sha.params.rounds) C Out tA N)
    (dflt : C) (rootOf₁ rootOf₂ : Out → D) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim p256sha.ecdsa.params.row.n Salt₁
      (Col F₁ p256sha.ecdsa.params.nw p256sha.ecdsa.params.nq) D)
    (claimOf₂ : Out → OpeningClaim p256sha.sha.params.row.n Salt₂
      (Col F₂ p256sha.sha.params.nw p256sha.sha.params.nq) D)
    (hD : Fintype.card D = 2 ^ p256sha.ecdsa.params.digestBits)
    (aP : (D × D) × List (Enc × D) → Fmac) (decode : C → Fmac) (kmac : ℕ)
    (hbal : ∀ x : Fmac, (univ.filter fun c : C => decode c = x).card ≤ kmac)
    (hmac : kmac * Fintype.card Fmac ≤ Fintype.card C)
    (keyB tagOf : Out → Fin nblk → Fmac)
    (common₁ : Witness₁ → Fin nblk → Fmac) (common₂ : Witness₂ → Fin nblk → Fmac)
    (hrow₁ : ∀ (mt : Fin p256sha.ecdsa.tape → D)
      (ct : Fin (len2 p256sha.ecdsa p256sha.sha + N) → C) (a : Witness₁),
      let S := setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂
      L₁.accepts S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ pubOf
        (len2_pos _ _) (slice1 p256sha.ecdsa p256sha.sha) mt ct →
      L₁.Good (sideCtx S pubOf (len2_pos _ _) mt ct) a →
      macTag (aP (S.context mt ct) + decode (S.challenges mt ct ⟨0, len2_pos _ _⟩))
        (keyB (S.proof mt ct)) (common₁ a) = tagOf (S.proof mt ct))
    (hrow₂ : ∀ (mt : Fin p256sha.ecdsa.tape → D)
      (ct : Fin (len2 p256sha.ecdsa p256sha.sha + N) → C) (a : Witness₂),
      let S := setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂
      L₂.accepts S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ pubOf
        (len2_pos _ _) (slice2 p256sha.ecdsa p256sha.sha) mt ct →
      L₂.Good (sideCtx S pubOf (len2_pos _ _) mt ct) a →
      macTag (aP (S.context mt ct) + decode (S.challenges mt ct ⟨0, len2_pos _ _⟩))
        (keyB (S.proof mt ct)) (common₂ a) = tagOf (S.proof mt ct))
    (htA : tA ≤ 2 ^ 60)
    (htape : 2 * p256sha.sha.params.row.n + 2 * p256sha.ecdsa.params.row.n + tA ≤ 2 ^ 62) :
    ((univ.filter fun ω : (Fin p256sha.ecdsa.tape → D) ×
          (Fin (len2 p256sha.ecdsa p256sha.sha + N) → C) =>
        L₁.accepts (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ pubOf (len2_pos _ _)
            (slice1 p256sha.ecdsa p256sha.sha) ω.1 ω.2 ∧
          L₂.accepts (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ pubOf (len2_pos _ _)
            (slice2 p256sha.ecdsa p256sha.sha) ω.1 ω.2 ∧
          ¬ ∃ a₁ a₂,
            L₁.Good (sideCtx (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂) pubOf
              (len2_pos _ _) ω.1 ω.2) a₁ ∧
            L₂.Good (sideCtx (setup2 body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂) pubOf
              (len2_pos _ _) ω.1 ω.2) a₂ ∧
            common₁ a₁ = common₂ a₂).card : ℚ)
        / ((Fintype.card D : ℚ) ^ p256sha.ecdsa.tape *
            (Fintype.card C : ℚ) ^ (len2 p256sha.ecdsa p256sha.sha + N))
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 116) :=
  le_trans
    (twofield_zk_compiled_ratio_le (TwoFieldRowV1.ecdsa_valid p256sha_valid) (TwoFieldRowV1.sha_valid p256sha_valid) p256sha_ecdsa_openings_pos p256sha_sha_openings_pos
      L₁ L₂ body dflt rootOf₁ rootOf₂ pubOf msgOf₁ msgOf₂ claimOf₁ claimOf₂ hD hD
      aP decode kmac hbal hmac keyB tagOf common₁ common₂ hrow₁ hrow₂ htA htA htape rfl)
    (p256sha_zk_rhs_le N hFmac)

end Rows

end Lfzk.CompiledZk
