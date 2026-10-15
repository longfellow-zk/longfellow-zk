import Lfzk.CompiledZk

/-!
# The deployed zero-knowledge verifier at the certified rows

`CompiledZk.row_zk_compiled_ratio_le` at each certified row, with the output dimension `logv` of
the row's circuit (`lfzk/scripts/v7-circuit-profiles.json` for v7; the v8 circuits' own `logv` for
v8) and the row's numerals,
certified by `native_decide` with the re-commitment terms absorbed:

| row | `logv` | `zkBound` | coefficient | headline |
|---|---|---|---|---|
| `v7Hash1` | 3 | `2^-115.67` | `2^-117.08` | `2^-115 + N · 2^-117` |
| `v7Hash2` | 4 | `2^-115.63` | `2^-117.09` | `2^-115 + N · 2^-117` |
| `v7Hash3` | 4 | `2^-115.65` | `2^-117.13` | `2^-115 + N · 2^-117` |
| `v7Hash4` | 5 | `2^-115.62` | `2^-117.13` | `2^-115 + N · 2^-117` |
| `v7Sig` | 8 | `2^-123.01` | `2^-123.01` | `2^-123 + N · 2^-123` |
| `v8Hash` | 5 | `2^-115.45` | `2^-116.94` | `2^-115 + N · 2^-116` |
| `v8Sig` | 3 | `2^-122.69` | `2^-122.69` | `2^-122 + N · 2^-122` |

(the `zkBound` and coefficient columns include the re-commitment slack `tape·L/2^256`, resp.
`tape/2^256`).  The premises are `row_zk_compiled_ratio_le`'s; `hr` is discharged.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.CompiledZk

open Finset Bcs Bcs.AdaptiveCommit Merkle Merkle.MH Merkle.RandomOracle
  Merkle.RandomOracle.TwoOracleTree RbrLongfellow Lfzk.NizkGrinding Lfzk.NizkAdaptive
  Lfzk.RbrLayerStepS Lfzk.RbrZkLongfellow Lfzk.RbrZkSplit Lfzk.NizkZk Lfzk.ZkLigeroV1
  Lfzk.CompiledLongfellow Lfzk.CompiledLongfellowAdaptive Lfzk.CertifiedV1
open scoped Classical

/-! ## The numerals -/

/-- **A re-committing right-hand side from two slack numerals**, for any bound `B` and
coefficient `K`. -/
theorem zk_rhs_le_of_slack {B K : ℚ} {T L d a b : ℕ}
    (hsb : B + ((T * L : ℕ) : ℚ) / 2 ^ d ≤ (1 : ℚ) / 2 ^ a)
    (hsc : K + (T : ℚ) / 2 ^ d ≤ (1 : ℚ) / 2 ^ b) (N : ℕ) :
    B + N * K + ((T * (L + N) : ℕ) : ℚ) / 2 ^ d ≤ (1 : ℚ) / 2 ^ a + N * ((1 : ℚ) / 2 ^ b) := by
  have hsplit : ((T * (L + N) : ℕ) : ℚ) / 2 ^ d
      = ((T * L : ℕ) : ℚ) / 2 ^ d + N * ((T : ℚ) / 2 ^ d) := by
    push_cast
    ring
  rw [hsplit]
  have hN : (0 : ℚ) ≤ N := Nat.cast_nonneg N
  have := mul_le_mul_of_nonneg_left hsc hN
  nlinarith

/-- `v7Hash1`'s zero-knowledge bound at `logv = 3` plus the re-commitment term at `N = 0`: at most
`2^-115`. -/
theorem v7Hash1_zk_slack_bound :
    v7Hash1.zkBound 3
        + ((v7Hash1.tape * Rounds.Role.length v7Hash1.params.nl v7Hash1.params.rounds : ℕ) : ℚ)
          / 2 ^ v7Hash1.params.digestBits
      ≤ (1 : ℚ) / 2 ^ 115 := by
  native_decide

/-- `v7Hash1`'s zero-knowledge coefficient plus the per-query re-commitment term: at most `2^-117`. -/
theorem v7Hash1_zk_slack_coeff :
    v7Hash1.zkCoefficient 3 + (v7Hash1.tape : ℚ) / 2 ^ v7Hash1.params.digestBits ≤ (1 : ℚ) / 2 ^ 117 := by
  native_decide

/-- `115` is the zero-knowledge bound's exact integer bit level at `v7Hash1`. -/
theorem v7Hash1_zkBound_sharp : ¬ v7Hash1.zkBound 3 ≤ (1 : ℚ) / 2 ^ 116 := by
  native_decide

/-- **`v7Hash1`'s zero-knowledge numerals**: within `2^-115 + N · 2^-117`. -/
theorem v7Hash1_zk_rhs_le (N : ℕ) :
    v7Hash1.zkBound 3 + N * v7Hash1.zkCoefficient 3
        + ((v7Hash1.tape * (Rounds.Role.length v7Hash1.params.nl v7Hash1.params.rounds + N) : ℕ) : ℚ)
          / 2 ^ v7Hash1.params.digestBits
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 117) :=
  zk_rhs_le_of_slack v7Hash1_zk_slack_bound v7Hash1_zk_slack_coeff N

/-- `v7Hash2`'s zero-knowledge bound at `logv = 4` plus the re-commitment term at `N = 0`: at most
`2^-115`. -/
theorem v7Hash2_zk_slack_bound :
    v7Hash2.zkBound 4
        + ((v7Hash2.tape * Rounds.Role.length v7Hash2.params.nl v7Hash2.params.rounds : ℕ) : ℚ)
          / 2 ^ v7Hash2.params.digestBits
      ≤ (1 : ℚ) / 2 ^ 115 := by
  native_decide

/-- `v7Hash2`'s zero-knowledge coefficient plus the per-query re-commitment term: at most `2^-117`. -/
theorem v7Hash2_zk_slack_coeff :
    v7Hash2.zkCoefficient 4 + (v7Hash2.tape : ℚ) / 2 ^ v7Hash2.params.digestBits ≤ (1 : ℚ) / 2 ^ 117 := by
  native_decide

/-- `115` is the zero-knowledge bound's exact integer bit level at `v7Hash2`. -/
theorem v7Hash2_zkBound_sharp : ¬ v7Hash2.zkBound 4 ≤ (1 : ℚ) / 2 ^ 116 := by
  native_decide

/-- **`v7Hash2`'s zero-knowledge numerals**: within `2^-115 + N · 2^-117`. -/
theorem v7Hash2_zk_rhs_le (N : ℕ) :
    v7Hash2.zkBound 4 + N * v7Hash2.zkCoefficient 4
        + ((v7Hash2.tape * (Rounds.Role.length v7Hash2.params.nl v7Hash2.params.rounds + N) : ℕ) : ℚ)
          / 2 ^ v7Hash2.params.digestBits
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 117) :=
  zk_rhs_le_of_slack v7Hash2_zk_slack_bound v7Hash2_zk_slack_coeff N

/-- `v7Hash3`'s zero-knowledge bound at `logv = 4` plus the re-commitment term at `N = 0`: at most
`2^-115`. -/
theorem v7Hash3_zk_slack_bound :
    v7Hash3.zkBound 4
        + ((v7Hash3.tape * Rounds.Role.length v7Hash3.params.nl v7Hash3.params.rounds : ℕ) : ℚ)
          / 2 ^ v7Hash3.params.digestBits
      ≤ (1 : ℚ) / 2 ^ 115 := by
  native_decide

/-- `v7Hash3`'s zero-knowledge coefficient plus the per-query re-commitment term: at most `2^-117`. -/
theorem v7Hash3_zk_slack_coeff :
    v7Hash3.zkCoefficient 4 + (v7Hash3.tape : ℚ) / 2 ^ v7Hash3.params.digestBits ≤ (1 : ℚ) / 2 ^ 117 := by
  native_decide

/-- `115` is the zero-knowledge bound's exact integer bit level at `v7Hash3`. -/
theorem v7Hash3_zkBound_sharp : ¬ v7Hash3.zkBound 4 ≤ (1 : ℚ) / 2 ^ 116 := by
  native_decide

/-- **`v7Hash3`'s zero-knowledge numerals**: within `2^-115 + N · 2^-117`. -/
theorem v7Hash3_zk_rhs_le (N : ℕ) :
    v7Hash3.zkBound 4 + N * v7Hash3.zkCoefficient 4
        + ((v7Hash3.tape * (Rounds.Role.length v7Hash3.params.nl v7Hash3.params.rounds + N) : ℕ) : ℚ)
          / 2 ^ v7Hash3.params.digestBits
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 117) :=
  zk_rhs_le_of_slack v7Hash3_zk_slack_bound v7Hash3_zk_slack_coeff N

/-- `v7Hash4`'s zero-knowledge bound at `logv = 5` plus the re-commitment term at `N = 0`: at most
`2^-115`. -/
theorem v7Hash4_zk_slack_bound :
    v7Hash4.zkBound 5
        + ((v7Hash4.tape * Rounds.Role.length v7Hash4.params.nl v7Hash4.params.rounds : ℕ) : ℚ)
          / 2 ^ v7Hash4.params.digestBits
      ≤ (1 : ℚ) / 2 ^ 115 := by
  native_decide

/-- `v7Hash4`'s zero-knowledge coefficient plus the per-query re-commitment term: at most `2^-117`. -/
theorem v7Hash4_zk_slack_coeff :
    v7Hash4.zkCoefficient 5 + (v7Hash4.tape : ℚ) / 2 ^ v7Hash4.params.digestBits ≤ (1 : ℚ) / 2 ^ 117 := by
  native_decide

/-- `115` is the zero-knowledge bound's exact integer bit level at `v7Hash4`. -/
theorem v7Hash4_zkBound_sharp : ¬ v7Hash4.zkBound 5 ≤ (1 : ℚ) / 2 ^ 116 := by
  native_decide

/-- **`v7Hash4`'s zero-knowledge numerals**: within `2^-115 + N · 2^-117`. -/
theorem v7Hash4_zk_rhs_le (N : ℕ) :
    v7Hash4.zkBound 5 + N * v7Hash4.zkCoefficient 5
        + ((v7Hash4.tape * (Rounds.Role.length v7Hash4.params.nl v7Hash4.params.rounds + N) : ℕ) : ℚ)
          / 2 ^ v7Hash4.params.digestBits
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 117) :=
  zk_rhs_le_of_slack v7Hash4_zk_slack_bound v7Hash4_zk_slack_coeff N

/-- `v7Sig`'s zero-knowledge bound at `logv = 8` plus the re-commitment term at `N = 0`: at most
`2^-123`. -/
theorem v7Sig_zk_slack_bound :
    v7Sig.zkBound 8
        + ((v7Sig.tape * Rounds.Role.length v7Sig.params.nl v7Sig.params.rounds : ℕ) : ℚ)
          / 2 ^ v7Sig.params.digestBits
      ≤ (1 : ℚ) / 2 ^ 123 := by
  native_decide

/-- `v7Sig`'s zero-knowledge coefficient plus the per-query re-commitment term: at most `2^-123`. -/
theorem v7Sig_zk_slack_coeff :
    v7Sig.zkCoefficient 8 + (v7Sig.tape : ℚ) / 2 ^ v7Sig.params.digestBits ≤ (1 : ℚ) / 2 ^ 123 := by
  native_decide

/-- `123` is the zero-knowledge bound's exact integer bit level at `v7Sig`. -/
theorem v7Sig_zkBound_sharp : ¬ v7Sig.zkBound 8 ≤ (1 : ℚ) / 2 ^ 124 := by
  native_decide

/-- **`v7Sig`'s zero-knowledge numerals**: within `2^-123 + N · 2^-123`. -/
theorem v7Sig_zk_rhs_le (N : ℕ) :
    v7Sig.zkBound 8 + N * v7Sig.zkCoefficient 8
        + ((v7Sig.tape * (Rounds.Role.length v7Sig.params.nl v7Sig.params.rounds + N) : ℕ) : ℚ)
          / 2 ^ v7Sig.params.digestBits
      ≤ (1 : ℚ) / 2 ^ 123 + N * ((1 : ℚ) / 2 ^ 123) :=
  zk_rhs_le_of_slack v7Sig_zk_slack_bound v7Sig_zk_slack_coeff N

/-- `v8Hash`'s zero-knowledge bound at `logv = 5` plus the re-commitment term at `N = 0`: at most
`2^-115`. -/
theorem v8Hash_zk_slack_bound :
    v8Hash.zkBound 5
        + ((v8Hash.tape * Rounds.Role.length v8Hash.params.nl v8Hash.params.rounds : ℕ) : ℚ)
          / 2 ^ v8Hash.params.digestBits
      ≤ (1 : ℚ) / 2 ^ 115 := by
  native_decide

/-- `v8Hash`'s zero-knowledge coefficient plus the per-query re-commitment term: at most `2^-116`. -/
theorem v8Hash_zk_slack_coeff :
    v8Hash.zkCoefficient 5 + (v8Hash.tape : ℚ) / 2 ^ v8Hash.params.digestBits ≤ (1 : ℚ) / 2 ^ 116 := by
  native_decide

/-- `115` is the zero-knowledge bound's exact integer bit level at `v8Hash`. -/
theorem v8Hash_zkBound_sharp : ¬ v8Hash.zkBound 5 ≤ (1 : ℚ) / 2 ^ 116 := by
  native_decide

/-- **`v8Hash`'s zero-knowledge numerals**: within `2^-115 + N · 2^-116`. -/
theorem v8Hash_zk_rhs_le (N : ℕ) :
    v8Hash.zkBound 5 + N * v8Hash.zkCoefficient 5
        + ((v8Hash.tape * (Rounds.Role.length v8Hash.params.nl v8Hash.params.rounds + N) : ℕ) : ℚ)
          / 2 ^ v8Hash.params.digestBits
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 116) :=
  zk_rhs_le_of_slack v8Hash_zk_slack_bound v8Hash_zk_slack_coeff N

/-- `v8Sig`'s zero-knowledge bound at `logv = 3` plus the re-commitment term at `N = 0`: at most
`2^-122`. -/
theorem v8Sig_zk_slack_bound :
    v8Sig.zkBound 3
        + ((v8Sig.tape * Rounds.Role.length v8Sig.params.nl v8Sig.params.rounds : ℕ) : ℚ)
          / 2 ^ v8Sig.params.digestBits
      ≤ (1 : ℚ) / 2 ^ 122 := by
  native_decide

/-- `v8Sig`'s zero-knowledge coefficient plus the per-query re-commitment term: at most `2^-122`. -/
theorem v8Sig_zk_slack_coeff :
    v8Sig.zkCoefficient 3 + (v8Sig.tape : ℚ) / 2 ^ v8Sig.params.digestBits ≤ (1 : ℚ) / 2 ^ 122 := by
  native_decide

/-- `122` is the zero-knowledge bound's exact integer bit level at `v8Sig`. -/
theorem v8Sig_zkBound_sharp : ¬ v8Sig.zkBound 3 ≤ (1 : ℚ) / 2 ^ 123 := by
  native_decide

/-- **`v8Sig`'s zero-knowledge numerals**: within `2^-122 + N · 2^-122`. -/
theorem v8Sig_zk_rhs_le (N : ℕ) :
    v8Sig.zkBound 3 + N * v8Sig.zkCoefficient 3
        + ((v8Sig.tape * (Rounds.Role.length v8Sig.params.nl v8Sig.params.rounds + N) : ℕ) : ℚ)
          / 2 ^ v8Sig.params.digestBits
      ≤ (1 : ℚ) / 2 ^ 122 + N * ((1 : ℚ) / 2 ^ 122) :=
  zk_rhs_le_of_slack v8Sig_zk_slack_bound v8Sig_zk_slack_coeff N

/-- The v8 signature row opens `132` columns. -/
theorem v8Sig_zk_openings_pos : 0 < v8Sig.params.row.openings := by decide

/-! ## The headlines -/

section Rows

variable {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F]
variable {ninp M nt nlin logw logc : ℕ}
variable {Enc D Salt : Type} [Fintype D] [DecidableEq D] [Inhabited D] [DecidableEq Enc]
  [Inhabited Salt]
variable {Msg Out : Type} [DecidableEq Msg] [Inhabited Msg] {tA N : ℕ}

/--
**v7Hash1 at the deployed zero-knowledge verifier, against a re-committing Fiat–Shamir prover:
`2^-115 + N · 2^-117`.**  `row_zk_compiled_ratio_le` at `CertifiedV1.v7Hash1` — the deployed v7
1-attribute hash row (17 layers, 566 sumcheck slots, `GF(2^128)`, Ligero V1 at `n = 3230`, `k =
461`, 132 openings), output dimension `logv = 3` — with the numerals `v7Hash1_zk_rhs_le`.  The
premises are `row_zk_compiled_ratio_le`'s; `hr` is discharged.
-/
theorem v7Hash1_zk_compiled_ratio_le
    (pl : Encode.Placement ninp M v7Hash1.params.q v7Hash1.params.nw v7Hash1.params.nq nt)
    {codec : Codec Salt (Col F v7Hash1.params.nw v7Hash1.params.nq) D Enc} (dec : RoleDecoders codec)
    (V : ZkCode C F (ZkLigeroV1.Chal F v7Hash1.params.nw v7Hash1.params.nq nlin nt)
      (LigeroV1LayerStep.Qry v7Hash1.params.row) Msg (Fin 3 → F) M ninp logw logc)
    (hnlin : V.nlin = nlin) (hnt : V.nt = nt)
    (dom : LigeroFamily.ReedSolomon.Domain F v7Hash1.params.row.openings v7Hash1.params.q v7Hash1.params.row.n)
    (respOf : Msg → LigeroFamily.Response F v7Hash1.params.row.openings v7Hash1.params.q v7Hash1.params.row.n 1)
    (body : TwoOracleTree Enc D (Point D Msg C v7Hash1.params.nl v7Hash1.params.rounds) C Out tA N)
    (dflt : C) (rootOf : Out → D) (msgOf : Out → ℕ → Msg)
    (claimOf : Out → OpeningClaim v7Hash1.params.row.n Salt (Col F v7Hash1.params.nw v7Hash1.params.nq) D)
    (hF : Fintype.card F = v7Hash1.params.row.fieldSize)
    (H : ∀ κ : D × List (Enc × D), ZkHonest F
      (ZkLigeroV1.Lift (Row.rowValid v7Hash1_valid) dom (Row.hkrow v7Hash1_valid)
        (extOracle nlin nt (Row.rowValid v7Hash1_valid) dom (Row.hkrow v7Hash1_valid) v7Hash1_openings_pos dec κ))
      logw logc)
    (Sat : ∀ κ : D × List (Enc × D),
      ZkLigeroV1.Lift (Row.rowValid v7Hash1_valid) dom (Row.hkrow v7Hash1_valid)
        (extOracle nlin nt (Row.rowValid v7Hash1_valid) dom (Row.hkrow v7Hash1_valid) v7Hash1_openings_pos dec κ) → Prop)
    (FD : ∀ κ : D × List (Enc × D), ZkFieldData C F (ZkLigeroV1.Chal F v7Hash1.params.nw v7Hash1.params.nq nlin nt)
      (LigeroV1LayerStep.Qry v7Hash1.params.row) Msg (Fin 3 → F)
      (ZkLigeroV1.Lift (Row.rowValid v7Hash1_valid) dom (Row.hkrow v7Hash1_valid)
        (extOracle nlin nt (Row.rowValid v7Hash1_valid) dom (Row.hkrow v7Hash1_valid) v7Hash1_openings_pos dec κ))
      M ninp logw logc v7Hash1.params.nl v7Hash1.params.rounds V (H κ) (asgOf pl) (Sat κ))
    (hexact : ∀ κ, (FD κ).ExactAt)
    (htA : tA ≤ v7Hash1.commitFuel) (htape : 2 * v7Hash1.params.row.n + tA ≤ v7Hash1.tape)
    (hD : Fintype.card D = 2 ^ v7Hash1.params.digestBits) :
    ((univ.filter fun ω : (Fin v7Hash1.tape → D) × (Fin (v7Hash1.fsLen N) → C) =>
        AcceptsZk (nl := v7Hash1.params.nl) (w := v7Hash1.params.rounds)
            (v1K (Equations := Fin nlin ⊕ (Fin nt × Encode.QSide)) (Row.rowValid v7Hash1_valid) dom
              (Row.hkrow v7Hash1_valid) v7Hash1_openings_pos) V codec
            (lfSetup body dflt rootOf msgOf) (lfCheck codec claimOf) rootOf msgOf claimOf
            (stmtOf pl nlin) respOf ω.1 ω.2 ∧
          ZkFails Sat ((lfSetup body dflt rootOf msgOf).context ω.1 ω.2)).card : ℚ)
        / ((Fintype.card D : ℚ) ^ v7Hash1.tape * (Fintype.card C : ℚ) ^ v7Hash1.fsLen N)
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 117) :=
  le_trans
    (row_zk_compiled_ratio_le v7Hash1_valid v7Hash1_openings_pos 3 pl dec V hnlin hnt dom respOf body
      dflt rootOf msgOf claimOf hF H Sat FD hexact htA htape hD)
    (v7Hash1_zk_rhs_le N)

/--
**v7Hash2 at the deployed zero-knowledge verifier, against a re-committing Fiat–Shamir prover:
`2^-115 + N · 2^-117`.**  `row_zk_compiled_ratio_le` at `CertifiedV1.v7Hash2` — the deployed v7
2-attribute hash row (17 layers, 570 sumcheck slots, `GF(2^128)`, Ligero V1 at `n = 3318`, `k =
474`), `logv = 4` — with the numerals `v7Hash2_zk_rhs_le`.  The premises are
`row_zk_compiled_ratio_le`'s; `hr` is discharged.
-/
theorem v7Hash2_zk_compiled_ratio_le
    (pl : Encode.Placement ninp M v7Hash2.params.q v7Hash2.params.nw v7Hash2.params.nq nt)
    {codec : Codec Salt (Col F v7Hash2.params.nw v7Hash2.params.nq) D Enc} (dec : RoleDecoders codec)
    (V : ZkCode C F (ZkLigeroV1.Chal F v7Hash2.params.nw v7Hash2.params.nq nlin nt)
      (LigeroV1LayerStep.Qry v7Hash2.params.row) Msg (Fin 4 → F) M ninp logw logc)
    (hnlin : V.nlin = nlin) (hnt : V.nt = nt)
    (dom : LigeroFamily.ReedSolomon.Domain F v7Hash2.params.row.openings v7Hash2.params.q v7Hash2.params.row.n)
    (respOf : Msg → LigeroFamily.Response F v7Hash2.params.row.openings v7Hash2.params.q v7Hash2.params.row.n 1)
    (body : TwoOracleTree Enc D (Point D Msg C v7Hash2.params.nl v7Hash2.params.rounds) C Out tA N)
    (dflt : C) (rootOf : Out → D) (msgOf : Out → ℕ → Msg)
    (claimOf : Out → OpeningClaim v7Hash2.params.row.n Salt (Col F v7Hash2.params.nw v7Hash2.params.nq) D)
    (hF : Fintype.card F = v7Hash2.params.row.fieldSize)
    (H : ∀ κ : D × List (Enc × D), ZkHonest F
      (ZkLigeroV1.Lift (Row.rowValid v7Hash2_valid) dom (Row.hkrow v7Hash2_valid)
        (extOracle nlin nt (Row.rowValid v7Hash2_valid) dom (Row.hkrow v7Hash2_valid) v7Hash2_openings_pos dec κ))
      logw logc)
    (Sat : ∀ κ : D × List (Enc × D),
      ZkLigeroV1.Lift (Row.rowValid v7Hash2_valid) dom (Row.hkrow v7Hash2_valid)
        (extOracle nlin nt (Row.rowValid v7Hash2_valid) dom (Row.hkrow v7Hash2_valid) v7Hash2_openings_pos dec κ) → Prop)
    (FD : ∀ κ : D × List (Enc × D), ZkFieldData C F (ZkLigeroV1.Chal F v7Hash2.params.nw v7Hash2.params.nq nlin nt)
      (LigeroV1LayerStep.Qry v7Hash2.params.row) Msg (Fin 4 → F)
      (ZkLigeroV1.Lift (Row.rowValid v7Hash2_valid) dom (Row.hkrow v7Hash2_valid)
        (extOracle nlin nt (Row.rowValid v7Hash2_valid) dom (Row.hkrow v7Hash2_valid) v7Hash2_openings_pos dec κ))
      M ninp logw logc v7Hash2.params.nl v7Hash2.params.rounds V (H κ) (asgOf pl) (Sat κ))
    (hexact : ∀ κ, (FD κ).ExactAt)
    (htA : tA ≤ v7Hash2.commitFuel) (htape : 2 * v7Hash2.params.row.n + tA ≤ v7Hash2.tape)
    (hD : Fintype.card D = 2 ^ v7Hash2.params.digestBits) :
    ((univ.filter fun ω : (Fin v7Hash2.tape → D) × (Fin (v7Hash2.fsLen N) → C) =>
        AcceptsZk (nl := v7Hash2.params.nl) (w := v7Hash2.params.rounds)
            (v1K (Equations := Fin nlin ⊕ (Fin nt × Encode.QSide)) (Row.rowValid v7Hash2_valid) dom
              (Row.hkrow v7Hash2_valid) v7Hash2_openings_pos) V codec
            (lfSetup body dflt rootOf msgOf) (lfCheck codec claimOf) rootOf msgOf claimOf
            (stmtOf pl nlin) respOf ω.1 ω.2 ∧
          ZkFails Sat ((lfSetup body dflt rootOf msgOf).context ω.1 ω.2)).card : ℚ)
        / ((Fintype.card D : ℚ) ^ v7Hash2.tape * (Fintype.card C : ℚ) ^ v7Hash2.fsLen N)
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 117) :=
  le_trans
    (row_zk_compiled_ratio_le v7Hash2_valid v7Hash2_openings_pos 4 pl dec V hnlin hnt dom respOf body
      dflt rootOf msgOf claimOf hF H Sat FD hexact htA htape hD)
    (v7Hash2_zk_rhs_le N)

/--
**v7Hash3 at the deployed zero-knowledge verifier, against a re-committing Fiat–Shamir prover:
`2^-115 + N · 2^-117`.**  `row_zk_compiled_ratio_le` at `CertifiedV1.v7Hash3` — the deployed v7
3-attribute hash row (17 layers, 574 sumcheck slots, `GF(2^128)`, Ligero V1 at `n = 3352`, `k =
478`), `logv = 4` — with the numerals `v7Hash3_zk_rhs_le`.  The premises are
`row_zk_compiled_ratio_le`'s; `hr` is discharged.
-/
theorem v7Hash3_zk_compiled_ratio_le
    (pl : Encode.Placement ninp M v7Hash3.params.q v7Hash3.params.nw v7Hash3.params.nq nt)
    {codec : Codec Salt (Col F v7Hash3.params.nw v7Hash3.params.nq) D Enc} (dec : RoleDecoders codec)
    (V : ZkCode C F (ZkLigeroV1.Chal F v7Hash3.params.nw v7Hash3.params.nq nlin nt)
      (LigeroV1LayerStep.Qry v7Hash3.params.row) Msg (Fin 4 → F) M ninp logw logc)
    (hnlin : V.nlin = nlin) (hnt : V.nt = nt)
    (dom : LigeroFamily.ReedSolomon.Domain F v7Hash3.params.row.openings v7Hash3.params.q v7Hash3.params.row.n)
    (respOf : Msg → LigeroFamily.Response F v7Hash3.params.row.openings v7Hash3.params.q v7Hash3.params.row.n 1)
    (body : TwoOracleTree Enc D (Point D Msg C v7Hash3.params.nl v7Hash3.params.rounds) C Out tA N)
    (dflt : C) (rootOf : Out → D) (msgOf : Out → ℕ → Msg)
    (claimOf : Out → OpeningClaim v7Hash3.params.row.n Salt (Col F v7Hash3.params.nw v7Hash3.params.nq) D)
    (hF : Fintype.card F = v7Hash3.params.row.fieldSize)
    (H : ∀ κ : D × List (Enc × D), ZkHonest F
      (ZkLigeroV1.Lift (Row.rowValid v7Hash3_valid) dom (Row.hkrow v7Hash3_valid)
        (extOracle nlin nt (Row.rowValid v7Hash3_valid) dom (Row.hkrow v7Hash3_valid) v7Hash3_openings_pos dec κ))
      logw logc)
    (Sat : ∀ κ : D × List (Enc × D),
      ZkLigeroV1.Lift (Row.rowValid v7Hash3_valid) dom (Row.hkrow v7Hash3_valid)
        (extOracle nlin nt (Row.rowValid v7Hash3_valid) dom (Row.hkrow v7Hash3_valid) v7Hash3_openings_pos dec κ) → Prop)
    (FD : ∀ κ : D × List (Enc × D), ZkFieldData C F (ZkLigeroV1.Chal F v7Hash3.params.nw v7Hash3.params.nq nlin nt)
      (LigeroV1LayerStep.Qry v7Hash3.params.row) Msg (Fin 4 → F)
      (ZkLigeroV1.Lift (Row.rowValid v7Hash3_valid) dom (Row.hkrow v7Hash3_valid)
        (extOracle nlin nt (Row.rowValid v7Hash3_valid) dom (Row.hkrow v7Hash3_valid) v7Hash3_openings_pos dec κ))
      M ninp logw logc v7Hash3.params.nl v7Hash3.params.rounds V (H κ) (asgOf pl) (Sat κ))
    (hexact : ∀ κ, (FD κ).ExactAt)
    (htA : tA ≤ v7Hash3.commitFuel) (htape : 2 * v7Hash3.params.row.n + tA ≤ v7Hash3.tape)
    (hD : Fintype.card D = 2 ^ v7Hash3.params.digestBits) :
    ((univ.filter fun ω : (Fin v7Hash3.tape → D) × (Fin (v7Hash3.fsLen N) → C) =>
        AcceptsZk (nl := v7Hash3.params.nl) (w := v7Hash3.params.rounds)
            (v1K (Equations := Fin nlin ⊕ (Fin nt × Encode.QSide)) (Row.rowValid v7Hash3_valid) dom
              (Row.hkrow v7Hash3_valid) v7Hash3_openings_pos) V codec
            (lfSetup body dflt rootOf msgOf) (lfCheck codec claimOf) rootOf msgOf claimOf
            (stmtOf pl nlin) respOf ω.1 ω.2 ∧
          ZkFails Sat ((lfSetup body dflt rootOf msgOf).context ω.1 ω.2)).card : ℚ)
        / ((Fintype.card D : ℚ) ^ v7Hash3.tape * (Fintype.card C : ℚ) ^ v7Hash3.fsLen N)
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 117) :=
  le_trans
    (row_zk_compiled_ratio_le v7Hash3_valid v7Hash3_openings_pos 4 pl dec V hnlin hnt dom respOf body
      dflt rootOf msgOf claimOf hF H Sat FD hexact htA htape hD)
    (v7Hash3_zk_rhs_le N)

/--
**v7Hash4 at the deployed zero-knowledge verifier, against a re-committing Fiat–Shamir prover:
`2^-115 + N · 2^-117`.**  `row_zk_compiled_ratio_le` at `CertifiedV1.v7Hash4` — the deployed v7
4-attribute hash row (17 layers, 574 sumcheck slots, `GF(2^128)`, Ligero V1 at `n = 3436`, `k =
490`), `logv = 5` — with the numerals `v7Hash4_zk_rhs_le`.  The premises are
`row_zk_compiled_ratio_le`'s; `hr` is discharged.
-/
theorem v7Hash4_zk_compiled_ratio_le
    (pl : Encode.Placement ninp M v7Hash4.params.q v7Hash4.params.nw v7Hash4.params.nq nt)
    {codec : Codec Salt (Col F v7Hash4.params.nw v7Hash4.params.nq) D Enc} (dec : RoleDecoders codec)
    (V : ZkCode C F (ZkLigeroV1.Chal F v7Hash4.params.nw v7Hash4.params.nq nlin nt)
      (LigeroV1LayerStep.Qry v7Hash4.params.row) Msg (Fin 5 → F) M ninp logw logc)
    (hnlin : V.nlin = nlin) (hnt : V.nt = nt)
    (dom : LigeroFamily.ReedSolomon.Domain F v7Hash4.params.row.openings v7Hash4.params.q v7Hash4.params.row.n)
    (respOf : Msg → LigeroFamily.Response F v7Hash4.params.row.openings v7Hash4.params.q v7Hash4.params.row.n 1)
    (body : TwoOracleTree Enc D (Point D Msg C v7Hash4.params.nl v7Hash4.params.rounds) C Out tA N)
    (dflt : C) (rootOf : Out → D) (msgOf : Out → ℕ → Msg)
    (claimOf : Out → OpeningClaim v7Hash4.params.row.n Salt (Col F v7Hash4.params.nw v7Hash4.params.nq) D)
    (hF : Fintype.card F = v7Hash4.params.row.fieldSize)
    (H : ∀ κ : D × List (Enc × D), ZkHonest F
      (ZkLigeroV1.Lift (Row.rowValid v7Hash4_valid) dom (Row.hkrow v7Hash4_valid)
        (extOracle nlin nt (Row.rowValid v7Hash4_valid) dom (Row.hkrow v7Hash4_valid) v7Hash4_openings_pos dec κ))
      logw logc)
    (Sat : ∀ κ : D × List (Enc × D),
      ZkLigeroV1.Lift (Row.rowValid v7Hash4_valid) dom (Row.hkrow v7Hash4_valid)
        (extOracle nlin nt (Row.rowValid v7Hash4_valid) dom (Row.hkrow v7Hash4_valid) v7Hash4_openings_pos dec κ) → Prop)
    (FD : ∀ κ : D × List (Enc × D), ZkFieldData C F (ZkLigeroV1.Chal F v7Hash4.params.nw v7Hash4.params.nq nlin nt)
      (LigeroV1LayerStep.Qry v7Hash4.params.row) Msg (Fin 5 → F)
      (ZkLigeroV1.Lift (Row.rowValid v7Hash4_valid) dom (Row.hkrow v7Hash4_valid)
        (extOracle nlin nt (Row.rowValid v7Hash4_valid) dom (Row.hkrow v7Hash4_valid) v7Hash4_openings_pos dec κ))
      M ninp logw logc v7Hash4.params.nl v7Hash4.params.rounds V (H κ) (asgOf pl) (Sat κ))
    (hexact : ∀ κ, (FD κ).ExactAt)
    (htA : tA ≤ v7Hash4.commitFuel) (htape : 2 * v7Hash4.params.row.n + tA ≤ v7Hash4.tape)
    (hD : Fintype.card D = 2 ^ v7Hash4.params.digestBits) :
    ((univ.filter fun ω : (Fin v7Hash4.tape → D) × (Fin (v7Hash4.fsLen N) → C) =>
        AcceptsZk (nl := v7Hash4.params.nl) (w := v7Hash4.params.rounds)
            (v1K (Equations := Fin nlin ⊕ (Fin nt × Encode.QSide)) (Row.rowValid v7Hash4_valid) dom
              (Row.hkrow v7Hash4_valid) v7Hash4_openings_pos) V codec
            (lfSetup body dflt rootOf msgOf) (lfCheck codec claimOf) rootOf msgOf claimOf
            (stmtOf pl nlin) respOf ω.1 ω.2 ∧
          ZkFails Sat ((lfSetup body dflt rootOf msgOf).context ω.1 ω.2)).card : ℚ)
        / ((Fintype.card D : ℚ) ^ v7Hash4.tape * (Fintype.card C : ℚ) ^ v7Hash4.fsLen N)
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 117) :=
  le_trans
    (row_zk_compiled_ratio_le v7Hash4_valid v7Hash4_openings_pos 5 pl dec V hnlin hnt dom respOf body
      dflt rootOf msgOf claimOf hF H Sat FD hexact htA htape hD)
    (v7Hash4_zk_rhs_le N)

/--
**v7Sig at the deployed zero-knowledge verifier, against a re-committing Fiat–Shamir prover: `2^-123
+ N · 2^-123`.**  `row_zk_compiled_ratio_le` at `CertifiedV1.v7Sig` — the deployed v7 signature row
(21 layers, 542 sumcheck slots, P-256's base field, Ligero V1 at `n = 3187`, `k = 455`), `logv = 8`
— with the numerals `v7Sig_zk_rhs_le`.  The premises are `row_zk_compiled_ratio_le`'s; `hr` is
discharged.
-/
theorem v7Sig_zk_compiled_ratio_le
    (pl : Encode.Placement ninp M v7Sig.params.q v7Sig.params.nw v7Sig.params.nq nt)
    {codec : Codec Salt (Col F v7Sig.params.nw v7Sig.params.nq) D Enc} (dec : RoleDecoders codec)
    (V : ZkCode C F (ZkLigeroV1.Chal F v7Sig.params.nw v7Sig.params.nq nlin nt)
      (LigeroV1LayerStep.Qry v7Sig.params.row) Msg (Fin 8 → F) M ninp logw logc)
    (hnlin : V.nlin = nlin) (hnt : V.nt = nt)
    (dom : LigeroFamily.ReedSolomon.Domain F v7Sig.params.row.openings v7Sig.params.q v7Sig.params.row.n)
    (respOf : Msg → LigeroFamily.Response F v7Sig.params.row.openings v7Sig.params.q v7Sig.params.row.n 1)
    (body : TwoOracleTree Enc D (Point D Msg C v7Sig.params.nl v7Sig.params.rounds) C Out tA N)
    (dflt : C) (rootOf : Out → D) (msgOf : Out → ℕ → Msg)
    (claimOf : Out → OpeningClaim v7Sig.params.row.n Salt (Col F v7Sig.params.nw v7Sig.params.nq) D)
    (hF : Fintype.card F = v7Sig.params.row.fieldSize)
    (H : ∀ κ : D × List (Enc × D), ZkHonest F
      (ZkLigeroV1.Lift (Row.rowValid v7Sig_valid) dom (Row.hkrow v7Sig_valid)
        (extOracle nlin nt (Row.rowValid v7Sig_valid) dom (Row.hkrow v7Sig_valid) v7Sig_openings_pos dec κ))
      logw logc)
    (Sat : ∀ κ : D × List (Enc × D),
      ZkLigeroV1.Lift (Row.rowValid v7Sig_valid) dom (Row.hkrow v7Sig_valid)
        (extOracle nlin nt (Row.rowValid v7Sig_valid) dom (Row.hkrow v7Sig_valid) v7Sig_openings_pos dec κ) → Prop)
    (FD : ∀ κ : D × List (Enc × D), ZkFieldData C F (ZkLigeroV1.Chal F v7Sig.params.nw v7Sig.params.nq nlin nt)
      (LigeroV1LayerStep.Qry v7Sig.params.row) Msg (Fin 8 → F)
      (ZkLigeroV1.Lift (Row.rowValid v7Sig_valid) dom (Row.hkrow v7Sig_valid)
        (extOracle nlin nt (Row.rowValid v7Sig_valid) dom (Row.hkrow v7Sig_valid) v7Sig_openings_pos dec κ))
      M ninp logw logc v7Sig.params.nl v7Sig.params.rounds V (H κ) (asgOf pl) (Sat κ))
    (hexact : ∀ κ, (FD κ).ExactAt)
    (htA : tA ≤ v7Sig.commitFuel) (htape : 2 * v7Sig.params.row.n + tA ≤ v7Sig.tape)
    (hD : Fintype.card D = 2 ^ v7Sig.params.digestBits) :
    ((univ.filter fun ω : (Fin v7Sig.tape → D) × (Fin (v7Sig.fsLen N) → C) =>
        AcceptsZk (nl := v7Sig.params.nl) (w := v7Sig.params.rounds)
            (v1K (Equations := Fin nlin ⊕ (Fin nt × Encode.QSide)) (Row.rowValid v7Sig_valid) dom
              (Row.hkrow v7Sig_valid) v7Sig_openings_pos) V codec
            (lfSetup body dflt rootOf msgOf) (lfCheck codec claimOf) rootOf msgOf claimOf
            (stmtOf pl nlin) respOf ω.1 ω.2 ∧
          ZkFails Sat ((lfSetup body dflt rootOf msgOf).context ω.1 ω.2)).card : ℚ)
        / ((Fintype.card D : ℚ) ^ v7Sig.tape * (Fintype.card C : ℚ) ^ v7Sig.fsLen N)
      ≤ (1 : ℚ) / 2 ^ 123 + N * ((1 : ℚ) / 2 ^ 123) :=
  le_trans
    (row_zk_compiled_ratio_le v7Sig_valid v7Sig_openings_pos 8 pl dec V hnlin hnt dom respOf body
      dflt rootOf msgOf claimOf hF H Sat FD hexact htA htape hD)
    (v7Sig_zk_rhs_le N)

/--
**v8Hash at the deployed zero-knowledge verifier, against a re-committing Fiat–Shamir prover:
`2^-115 + N · 2^-116`.**  `row_zk_compiled_ratio_le` at `CertifiedV1.v8Hash` — the v8 hash row (20
layers, 610 sumcheck slots, `GF(2^128)`, Ligero V1 at `n = 4088`, `k = 584`), `logv = 5` — with the
numerals `v8Hash_zk_rhs_le`.  The premises are `row_zk_compiled_ratio_le`'s; `hr` is discharged.
-/
theorem v8Hash_zk_compiled_ratio_le
    (pl : Encode.Placement ninp M v8Hash.params.q v8Hash.params.nw v8Hash.params.nq nt)
    {codec : Codec Salt (Col F v8Hash.params.nw v8Hash.params.nq) D Enc} (dec : RoleDecoders codec)
    (V : ZkCode C F (ZkLigeroV1.Chal F v8Hash.params.nw v8Hash.params.nq nlin nt)
      (LigeroV1LayerStep.Qry v8Hash.params.row) Msg (Fin 5 → F) M ninp logw logc)
    (hnlin : V.nlin = nlin) (hnt : V.nt = nt)
    (dom : LigeroFamily.ReedSolomon.Domain F v8Hash.params.row.openings v8Hash.params.q v8Hash.params.row.n)
    (respOf : Msg → LigeroFamily.Response F v8Hash.params.row.openings v8Hash.params.q v8Hash.params.row.n 1)
    (body : TwoOracleTree Enc D (Point D Msg C v8Hash.params.nl v8Hash.params.rounds) C Out tA N)
    (dflt : C) (rootOf : Out → D) (msgOf : Out → ℕ → Msg)
    (claimOf : Out → OpeningClaim v8Hash.params.row.n Salt (Col F v8Hash.params.nw v8Hash.params.nq) D)
    (hF : Fintype.card F = v8Hash.params.row.fieldSize)
    (H : ∀ κ : D × List (Enc × D), ZkHonest F
      (ZkLigeroV1.Lift (Row.rowValid v8Hash_valid) dom (Row.hkrow v8Hash_valid)
        (extOracle nlin nt (Row.rowValid v8Hash_valid) dom (Row.hkrow v8Hash_valid) v8Hash_openings_pos dec κ))
      logw logc)
    (Sat : ∀ κ : D × List (Enc × D),
      ZkLigeroV1.Lift (Row.rowValid v8Hash_valid) dom (Row.hkrow v8Hash_valid)
        (extOracle nlin nt (Row.rowValid v8Hash_valid) dom (Row.hkrow v8Hash_valid) v8Hash_openings_pos dec κ) → Prop)
    (FD : ∀ κ : D × List (Enc × D), ZkFieldData C F (ZkLigeroV1.Chal F v8Hash.params.nw v8Hash.params.nq nlin nt)
      (LigeroV1LayerStep.Qry v8Hash.params.row) Msg (Fin 5 → F)
      (ZkLigeroV1.Lift (Row.rowValid v8Hash_valid) dom (Row.hkrow v8Hash_valid)
        (extOracle nlin nt (Row.rowValid v8Hash_valid) dom (Row.hkrow v8Hash_valid) v8Hash_openings_pos dec κ))
      M ninp logw logc v8Hash.params.nl v8Hash.params.rounds V (H κ) (asgOf pl) (Sat κ))
    (hexact : ∀ κ, (FD κ).ExactAt)
    (htA : tA ≤ v8Hash.commitFuel) (htape : 2 * v8Hash.params.row.n + tA ≤ v8Hash.tape)
    (hD : Fintype.card D = 2 ^ v8Hash.params.digestBits) :
    ((univ.filter fun ω : (Fin v8Hash.tape → D) × (Fin (v8Hash.fsLen N) → C) =>
        AcceptsZk (nl := v8Hash.params.nl) (w := v8Hash.params.rounds)
            (v1K (Equations := Fin nlin ⊕ (Fin nt × Encode.QSide)) (Row.rowValid v8Hash_valid) dom
              (Row.hkrow v8Hash_valid) v8Hash_openings_pos) V codec
            (lfSetup body dflt rootOf msgOf) (lfCheck codec claimOf) rootOf msgOf claimOf
            (stmtOf pl nlin) respOf ω.1 ω.2 ∧
          ZkFails Sat ((lfSetup body dflt rootOf msgOf).context ω.1 ω.2)).card : ℚ)
        / ((Fintype.card D : ℚ) ^ v8Hash.tape * (Fintype.card C : ℚ) ^ v8Hash.fsLen N)
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 116) :=
  le_trans
    (row_zk_compiled_ratio_le v8Hash_valid v8Hash_openings_pos 5 pl dec V hnlin hnt dom respOf body
      dflt rootOf msgOf claimOf hF H Sat FD hexact htA htape hD)
    (v8Hash_zk_rhs_le N)

/--
**v8Sig at the deployed zero-knowledge verifier, against a re-committing Fiat–Shamir prover: `2^-122
+ N · 2^-122`.**  `row_zk_compiled_ratio_le` at `CertifiedV1.v8Sig` — the v8 signature row (21
layers, 520 sumcheck slots, P-256's base field, Ligero V1 at `n = 3458`, `k = 494`), `logv = 3` —
with the numerals `v8Sig_zk_rhs_le`.  The premises are `row_zk_compiled_ratio_le`'s; `hr` is
discharged.
-/
theorem v8Sig_zk_compiled_ratio_le
    (pl : Encode.Placement ninp M v8Sig.params.q v8Sig.params.nw v8Sig.params.nq nt)
    {codec : Codec Salt (Col F v8Sig.params.nw v8Sig.params.nq) D Enc} (dec : RoleDecoders codec)
    (V : ZkCode C F (ZkLigeroV1.Chal F v8Sig.params.nw v8Sig.params.nq nlin nt)
      (LigeroV1LayerStep.Qry v8Sig.params.row) Msg (Fin 3 → F) M ninp logw logc)
    (hnlin : V.nlin = nlin) (hnt : V.nt = nt)
    (dom : LigeroFamily.ReedSolomon.Domain F v8Sig.params.row.openings v8Sig.params.q v8Sig.params.row.n)
    (respOf : Msg → LigeroFamily.Response F v8Sig.params.row.openings v8Sig.params.q v8Sig.params.row.n 1)
    (body : TwoOracleTree Enc D (Point D Msg C v8Sig.params.nl v8Sig.params.rounds) C Out tA N)
    (dflt : C) (rootOf : Out → D) (msgOf : Out → ℕ → Msg)
    (claimOf : Out → OpeningClaim v8Sig.params.row.n Salt (Col F v8Sig.params.nw v8Sig.params.nq) D)
    (hF : Fintype.card F = v8Sig.params.row.fieldSize)
    (H : ∀ κ : D × List (Enc × D), ZkHonest F
      (ZkLigeroV1.Lift (Row.rowValid v8Sig_valid) dom (Row.hkrow v8Sig_valid)
        (extOracle nlin nt (Row.rowValid v8Sig_valid) dom (Row.hkrow v8Sig_valid) v8Sig_zk_openings_pos dec κ))
      logw logc)
    (Sat : ∀ κ : D × List (Enc × D),
      ZkLigeroV1.Lift (Row.rowValid v8Sig_valid) dom (Row.hkrow v8Sig_valid)
        (extOracle nlin nt (Row.rowValid v8Sig_valid) dom (Row.hkrow v8Sig_valid) v8Sig_zk_openings_pos dec κ) → Prop)
    (FD : ∀ κ : D × List (Enc × D), ZkFieldData C F (ZkLigeroV1.Chal F v8Sig.params.nw v8Sig.params.nq nlin nt)
      (LigeroV1LayerStep.Qry v8Sig.params.row) Msg (Fin 3 → F)
      (ZkLigeroV1.Lift (Row.rowValid v8Sig_valid) dom (Row.hkrow v8Sig_valid)
        (extOracle nlin nt (Row.rowValid v8Sig_valid) dom (Row.hkrow v8Sig_valid) v8Sig_zk_openings_pos dec κ))
      M ninp logw logc v8Sig.params.nl v8Sig.params.rounds V (H κ) (asgOf pl) (Sat κ))
    (hexact : ∀ κ, (FD κ).ExactAt)
    (htA : tA ≤ v8Sig.commitFuel) (htape : 2 * v8Sig.params.row.n + tA ≤ v8Sig.tape)
    (hD : Fintype.card D = 2 ^ v8Sig.params.digestBits) :
    ((univ.filter fun ω : (Fin v8Sig.tape → D) × (Fin (v8Sig.fsLen N) → C) =>
        AcceptsZk (nl := v8Sig.params.nl) (w := v8Sig.params.rounds)
            (v1K (Equations := Fin nlin ⊕ (Fin nt × Encode.QSide)) (Row.rowValid v8Sig_valid) dom
              (Row.hkrow v8Sig_valid) v8Sig_zk_openings_pos) V codec
            (lfSetup body dflt rootOf msgOf) (lfCheck codec claimOf) rootOf msgOf claimOf
            (stmtOf pl nlin) respOf ω.1 ω.2 ∧
          ZkFails Sat ((lfSetup body dflt rootOf msgOf).context ω.1 ω.2)).card : ℚ)
        / ((Fintype.card D : ℚ) ^ v8Sig.tape * (Fintype.card C : ℚ) ^ v8Sig.fsLen N)
      ≤ (1 : ℚ) / 2 ^ 122 + N * ((1 : ℚ) / 2 ^ 122) :=
  le_trans
    (row_zk_compiled_ratio_le v8Sig_valid v8Sig_zk_openings_pos 3 pl dec V hnlin hnt dom respOf body
      dflt rootOf msgOf claimOf hF H Sat FD hexact htA htape hD)
    (v8Sig_zk_rhs_le N)

end Rows

end Lfzk.CompiledZk
