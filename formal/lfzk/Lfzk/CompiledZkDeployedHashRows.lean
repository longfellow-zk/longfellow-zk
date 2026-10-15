import Lfzk.CompiledZkDeployedHash
import Lfzk.CompiledZkRows
import Lfzk.CompiledZkTwoFieldRows

/-!
# The deployed zero-knowledge verifier with deployed hash inputs, at the v7 rows

`CompiledZkDeployedHash.row_zk_deployed_ratio_le` and
`CompiledZkDeployedHash.twofield_zk_deployed_ratio_le` at the registered v7 rows and pairs.  The
verifier is the deployed zero-knowledge verifier (`CompiledZk`), and the Fiat–Shamir hash inputs are
the deployed ones: context, role and the prover's message prefix, with no challenge re-absorbed
(`Bcs.TotalOracle`).  So `N` counts **deployed** hash queries.  The right-hand sides are
`CompiledZk`'s, so the certified numerals are `CompiledZkRows`' and `CompiledZkTwoFieldRows`'
(`_zk_rhs_le`), unchanged:

| row | `logv` | headline |
|---|---|---|
| `v7Hash1` … `v7Hash4` | 3, 4, 4, 5 | `2^-115 + N · 2^-117` |
| `v7Sig` | 8 | `2^-123 + N · 2^-123` |
| `v7P256Sha1` … `v7P256Sha4` (hash side first) | 3/4/4/5, 8 | `2^-115 + N · 2^-117` |

The two-field pairs are instantiated in the deployed transcript order: the `GF(2^128)` hash circuit
is proved first, then the `P-256` signature circuit on the same transcript, and the MAC-key share
`av` is checked against the oracle's answer at the key point (the two roots).  The ECDSA-first
numerals are moved over by `twofield_zk_rhs_swap`.

The premises are the abstract theorems' (listed in `Lfzk.CompiledZkDeployedHash`); `hr`, the second
`|D|` equation and the tape equation are discharged.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.CompiledZkDeployedHash

open Finset Bcs Merkle Merkle.MH Merkle.RandomOracle Merkle.RandomOracle.TwoOracleTree
  RbrLongfellow Lfzk.NizkDeployedHash Lfzk.NizkDeployedHashAdaptive Lfzk.RbrZkLongfellow
  Lfzk.RbrZkSplit Lfzk.NizkZk Lfzk.ZkLigeroV1 Lfzk.CompiledZk Lfzk.CertifiedV1
open Lfzk.CompiledLongfellow (Col v1K)
open scoped Classical

/-! ## 1. One field -/

section Rows

variable {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]
variable {F : Type} [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F]
variable {ninp M nt nlin logw logc : ℕ}
variable {Enc D Salt : Type} [Fintype D] [DecidableEq D] [Inhabited D] [DecidableEq Enc]
  [Inhabited Salt]
variable {Msg Out : Type} [Fintype Msg] [DecidableEq Msg] [Inhabited Msg] {tA N : ℕ}

/--
**v7Hash1 at the deployed zero-knowledge verifier, with deployed hash inputs: `2^-115 + N · 2^-117`.**
`row_zk_deployed_ratio_le` at `CertifiedV1.v7Hash1` — the deployed v7 1-attribute hash row (17 layers, 566 sumcheck slots, `GF(2^128)`, Ligero V1 at `n = 3230`, `k = 461`, 132 openings), output dimension `logv = 3` — with the
numerals `CompiledZk.v7Hash1_zk_rhs_le`.  `N` counts deployed (message-prefix) hash queries.
-/
theorem v7Hash1_zk_deployed_ratio_le
    (pl : Encode.Placement ninp M v7Hash1.params.q v7Hash1.params.nw v7Hash1.params.nq nt)
    {codec : Codec Salt (Col F v7Hash1.params.nw v7Hash1.params.nq) D Enc} (dec : RoleDecoders codec)
    (V : ZkCode C F (ZkLigeroV1.Chal F v7Hash1.params.nw v7Hash1.params.nq nlin nt)
      (LigeroV1LayerStep.Qry v7Hash1.params.row) Msg (Fin 3 → F) M ninp logw logc)
    (hnlin : V.nlin = nlin) (hnt : V.nt = nt)
    (dom : LigeroFamily.ReedSolomon.Domain F v7Hash1.params.row.openings v7Hash1.params.q
      v7Hash1.params.row.n)
    (respOf : Msg → LigeroFamily.Response F v7Hash1.params.row.openings v7Hash1.params.q
      v7Hash1.params.row.n 1)
    (body : TwoOracleTree Enc D (MPoint D Msg v7Hash1.params.nl v7Hash1.params.rounds) C Out tA N)
    (rootOf : Out → D) (msgOf : Out → ℕ → Msg)
    (claimOf : Out → OpeningClaim v7Hash1.params.row.n Salt (Col F v7Hash1.params.nw v7Hash1.params.nq) D)
    (hF : Fintype.card F = v7Hash1.params.row.fieldSize)
    (H : ∀ κ : D × List (Enc × D), ZkHonest F
      (ZkLigeroV1.Lift (Row.rowValid v7Hash1_valid) dom (Row.hkrow v7Hash1_valid)
        (extOracle nlin nt (Row.rowValid v7Hash1_valid) dom (Row.hkrow v7Hash1_valid) v7Hash1_openings_pos dec κ))
      logw logc)
    (Sat : ∀ κ : D × List (Enc × D),
      ZkLigeroV1.Lift (Row.rowValid v7Hash1_valid) dom (Row.hkrow v7Hash1_valid)
        (extOracle nlin nt (Row.rowValid v7Hash1_valid) dom (Row.hkrow v7Hash1_valid) v7Hash1_openings_pos dec κ) → Prop)
    (FD : ∀ κ : D × List (Enc × D), ZkFieldData C F
      (ZkLigeroV1.Chal F v7Hash1.params.nw v7Hash1.params.nq nlin nt)
      (LigeroV1LayerStep.Qry v7Hash1.params.row) Msg (Fin 3 → F)
      (ZkLigeroV1.Lift (Row.rowValid v7Hash1_valid) dom (Row.hkrow v7Hash1_valid)
        (extOracle nlin nt (Row.rowValid v7Hash1_valid) dom (Row.hkrow v7Hash1_valid) v7Hash1_openings_pos dec κ))
      M ninp logw logc v7Hash1.params.nl v7Hash1.params.rounds V (H κ) (asgOf pl) (Sat κ))
    (hexact : ∀ κ, (FD κ).ExactAt)
    (htA : tA ≤ v7Hash1.commitFuel) (htape : 2 * v7Hash1.params.row.n + tA ≤ v7Hash1.tape)
    (hD : Fintype.card D = 2 ^ v7Hash1.params.digestBits) :
    ((univ.filter fun ω : (Fin v7Hash1.tape → D) × (MPoint D Msg v7Hash1.params.nl v7Hash1.params.rounds → C) =>
        AcceptsZkDH (nl := v7Hash1.params.nl) (w := v7Hash1.params.rounds)
            (v1K (Equations := Fin nlin ⊕ (Fin nt × Encode.QSide)) (Row.rowValid v7Hash1_valid) dom
              (Row.hkrow v7Hash1_valid) v7Hash1_openings_pos) V codec
            (lfSetup body rootOf msgOf) (NizkAdaptive.lfCheck codec claimOf) rootOf msgOf claimOf
            (stmtOf pl nlin) respOf ω.1 ω.2 ∧
          ZkFails Sat ((lfSetup body rootOf msgOf).context ω.1 ω.2)).card : ℚ)
        / ((Fintype.card D : ℚ) ^ v7Hash1.tape
            * (Fintype.card C : ℚ) ^ Fintype.card (MPoint D Msg v7Hash1.params.nl v7Hash1.params.rounds))
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 117) :=
  le_trans
    (row_zk_deployed_ratio_le v7Hash1_valid v7Hash1_openings_pos 3 pl dec V hnlin hnt dom respOf body
      rootOf msgOf claimOf hF H Sat FD hexact htA htape hD)
    (v7Hash1_zk_rhs_le N)

/--
**v7Hash2 at the deployed zero-knowledge verifier, with deployed hash inputs: `2^-115 + N · 2^-117`.**
`row_zk_deployed_ratio_le` at `CertifiedV1.v7Hash2` — the deployed v7 2-attribute hash row (17 layers, 570 sumcheck slots, `GF(2^128)`, Ligero V1 at `n = 3318`, `k = 474`, 132 openings), output dimension `logv = 4` — with the
numerals `CompiledZk.v7Hash2_zk_rhs_le`.  `N` counts deployed (message-prefix) hash queries.
-/
theorem v7Hash2_zk_deployed_ratio_le
    (pl : Encode.Placement ninp M v7Hash2.params.q v7Hash2.params.nw v7Hash2.params.nq nt)
    {codec : Codec Salt (Col F v7Hash2.params.nw v7Hash2.params.nq) D Enc} (dec : RoleDecoders codec)
    (V : ZkCode C F (ZkLigeroV1.Chal F v7Hash2.params.nw v7Hash2.params.nq nlin nt)
      (LigeroV1LayerStep.Qry v7Hash2.params.row) Msg (Fin 4 → F) M ninp logw logc)
    (hnlin : V.nlin = nlin) (hnt : V.nt = nt)
    (dom : LigeroFamily.ReedSolomon.Domain F v7Hash2.params.row.openings v7Hash2.params.q
      v7Hash2.params.row.n)
    (respOf : Msg → LigeroFamily.Response F v7Hash2.params.row.openings v7Hash2.params.q
      v7Hash2.params.row.n 1)
    (body : TwoOracleTree Enc D (MPoint D Msg v7Hash2.params.nl v7Hash2.params.rounds) C Out tA N)
    (rootOf : Out → D) (msgOf : Out → ℕ → Msg)
    (claimOf : Out → OpeningClaim v7Hash2.params.row.n Salt (Col F v7Hash2.params.nw v7Hash2.params.nq) D)
    (hF : Fintype.card F = v7Hash2.params.row.fieldSize)
    (H : ∀ κ : D × List (Enc × D), ZkHonest F
      (ZkLigeroV1.Lift (Row.rowValid v7Hash2_valid) dom (Row.hkrow v7Hash2_valid)
        (extOracle nlin nt (Row.rowValid v7Hash2_valid) dom (Row.hkrow v7Hash2_valid) v7Hash2_openings_pos dec κ))
      logw logc)
    (Sat : ∀ κ : D × List (Enc × D),
      ZkLigeroV1.Lift (Row.rowValid v7Hash2_valid) dom (Row.hkrow v7Hash2_valid)
        (extOracle nlin nt (Row.rowValid v7Hash2_valid) dom (Row.hkrow v7Hash2_valid) v7Hash2_openings_pos dec κ) → Prop)
    (FD : ∀ κ : D × List (Enc × D), ZkFieldData C F
      (ZkLigeroV1.Chal F v7Hash2.params.nw v7Hash2.params.nq nlin nt)
      (LigeroV1LayerStep.Qry v7Hash2.params.row) Msg (Fin 4 → F)
      (ZkLigeroV1.Lift (Row.rowValid v7Hash2_valid) dom (Row.hkrow v7Hash2_valid)
        (extOracle nlin nt (Row.rowValid v7Hash2_valid) dom (Row.hkrow v7Hash2_valid) v7Hash2_openings_pos dec κ))
      M ninp logw logc v7Hash2.params.nl v7Hash2.params.rounds V (H κ) (asgOf pl) (Sat κ))
    (hexact : ∀ κ, (FD κ).ExactAt)
    (htA : tA ≤ v7Hash2.commitFuel) (htape : 2 * v7Hash2.params.row.n + tA ≤ v7Hash2.tape)
    (hD : Fintype.card D = 2 ^ v7Hash2.params.digestBits) :
    ((univ.filter fun ω : (Fin v7Hash2.tape → D) × (MPoint D Msg v7Hash2.params.nl v7Hash2.params.rounds → C) =>
        AcceptsZkDH (nl := v7Hash2.params.nl) (w := v7Hash2.params.rounds)
            (v1K (Equations := Fin nlin ⊕ (Fin nt × Encode.QSide)) (Row.rowValid v7Hash2_valid) dom
              (Row.hkrow v7Hash2_valid) v7Hash2_openings_pos) V codec
            (lfSetup body rootOf msgOf) (NizkAdaptive.lfCheck codec claimOf) rootOf msgOf claimOf
            (stmtOf pl nlin) respOf ω.1 ω.2 ∧
          ZkFails Sat ((lfSetup body rootOf msgOf).context ω.1 ω.2)).card : ℚ)
        / ((Fintype.card D : ℚ) ^ v7Hash2.tape
            * (Fintype.card C : ℚ) ^ Fintype.card (MPoint D Msg v7Hash2.params.nl v7Hash2.params.rounds))
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 117) :=
  le_trans
    (row_zk_deployed_ratio_le v7Hash2_valid v7Hash2_openings_pos 4 pl dec V hnlin hnt dom respOf body
      rootOf msgOf claimOf hF H Sat FD hexact htA htape hD)
    (v7Hash2_zk_rhs_le N)

/--
**v7Hash3 at the deployed zero-knowledge verifier, with deployed hash inputs: `2^-115 + N · 2^-117`.**
`row_zk_deployed_ratio_le` at `CertifiedV1.v7Hash3` — the deployed v7 3-attribute hash row (`GF(2^128)`, Ligero V1, 132 openings), output dimension `logv = 4` — with the
numerals `CompiledZk.v7Hash3_zk_rhs_le`.  `N` counts deployed (message-prefix) hash queries.
-/
theorem v7Hash3_zk_deployed_ratio_le
    (pl : Encode.Placement ninp M v7Hash3.params.q v7Hash3.params.nw v7Hash3.params.nq nt)
    {codec : Codec Salt (Col F v7Hash3.params.nw v7Hash3.params.nq) D Enc} (dec : RoleDecoders codec)
    (V : ZkCode C F (ZkLigeroV1.Chal F v7Hash3.params.nw v7Hash3.params.nq nlin nt)
      (LigeroV1LayerStep.Qry v7Hash3.params.row) Msg (Fin 4 → F) M ninp logw logc)
    (hnlin : V.nlin = nlin) (hnt : V.nt = nt)
    (dom : LigeroFamily.ReedSolomon.Domain F v7Hash3.params.row.openings v7Hash3.params.q
      v7Hash3.params.row.n)
    (respOf : Msg → LigeroFamily.Response F v7Hash3.params.row.openings v7Hash3.params.q
      v7Hash3.params.row.n 1)
    (body : TwoOracleTree Enc D (MPoint D Msg v7Hash3.params.nl v7Hash3.params.rounds) C Out tA N)
    (rootOf : Out → D) (msgOf : Out → ℕ → Msg)
    (claimOf : Out → OpeningClaim v7Hash3.params.row.n Salt (Col F v7Hash3.params.nw v7Hash3.params.nq) D)
    (hF : Fintype.card F = v7Hash3.params.row.fieldSize)
    (H : ∀ κ : D × List (Enc × D), ZkHonest F
      (ZkLigeroV1.Lift (Row.rowValid v7Hash3_valid) dom (Row.hkrow v7Hash3_valid)
        (extOracle nlin nt (Row.rowValid v7Hash3_valid) dom (Row.hkrow v7Hash3_valid) v7Hash3_openings_pos dec κ))
      logw logc)
    (Sat : ∀ κ : D × List (Enc × D),
      ZkLigeroV1.Lift (Row.rowValid v7Hash3_valid) dom (Row.hkrow v7Hash3_valid)
        (extOracle nlin nt (Row.rowValid v7Hash3_valid) dom (Row.hkrow v7Hash3_valid) v7Hash3_openings_pos dec κ) → Prop)
    (FD : ∀ κ : D × List (Enc × D), ZkFieldData C F
      (ZkLigeroV1.Chal F v7Hash3.params.nw v7Hash3.params.nq nlin nt)
      (LigeroV1LayerStep.Qry v7Hash3.params.row) Msg (Fin 4 → F)
      (ZkLigeroV1.Lift (Row.rowValid v7Hash3_valid) dom (Row.hkrow v7Hash3_valid)
        (extOracle nlin nt (Row.rowValid v7Hash3_valid) dom (Row.hkrow v7Hash3_valid) v7Hash3_openings_pos dec κ))
      M ninp logw logc v7Hash3.params.nl v7Hash3.params.rounds V (H κ) (asgOf pl) (Sat κ))
    (hexact : ∀ κ, (FD κ).ExactAt)
    (htA : tA ≤ v7Hash3.commitFuel) (htape : 2 * v7Hash3.params.row.n + tA ≤ v7Hash3.tape)
    (hD : Fintype.card D = 2 ^ v7Hash3.params.digestBits) :
    ((univ.filter fun ω : (Fin v7Hash3.tape → D) × (MPoint D Msg v7Hash3.params.nl v7Hash3.params.rounds → C) =>
        AcceptsZkDH (nl := v7Hash3.params.nl) (w := v7Hash3.params.rounds)
            (v1K (Equations := Fin nlin ⊕ (Fin nt × Encode.QSide)) (Row.rowValid v7Hash3_valid) dom
              (Row.hkrow v7Hash3_valid) v7Hash3_openings_pos) V codec
            (lfSetup body rootOf msgOf) (NizkAdaptive.lfCheck codec claimOf) rootOf msgOf claimOf
            (stmtOf pl nlin) respOf ω.1 ω.2 ∧
          ZkFails Sat ((lfSetup body rootOf msgOf).context ω.1 ω.2)).card : ℚ)
        / ((Fintype.card D : ℚ) ^ v7Hash3.tape
            * (Fintype.card C : ℚ) ^ Fintype.card (MPoint D Msg v7Hash3.params.nl v7Hash3.params.rounds))
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 117) :=
  le_trans
    (row_zk_deployed_ratio_le v7Hash3_valid v7Hash3_openings_pos 4 pl dec V hnlin hnt dom respOf body
      rootOf msgOf claimOf hF H Sat FD hexact htA htape hD)
    (v7Hash3_zk_rhs_le N)

/--
**v7Hash4 at the deployed zero-knowledge verifier, with deployed hash inputs: `2^-115 + N · 2^-117`.**
`row_zk_deployed_ratio_le` at `CertifiedV1.v7Hash4` — the deployed v7 4-attribute hash row (`GF(2^128)`, Ligero V1 at `n = 3436`, `k = 490`, 132 openings), output dimension `logv = 5` — with the
numerals `CompiledZk.v7Hash4_zk_rhs_le`.  `N` counts deployed (message-prefix) hash queries.
-/
theorem v7Hash4_zk_deployed_ratio_le
    (pl : Encode.Placement ninp M v7Hash4.params.q v7Hash4.params.nw v7Hash4.params.nq nt)
    {codec : Codec Salt (Col F v7Hash4.params.nw v7Hash4.params.nq) D Enc} (dec : RoleDecoders codec)
    (V : ZkCode C F (ZkLigeroV1.Chal F v7Hash4.params.nw v7Hash4.params.nq nlin nt)
      (LigeroV1LayerStep.Qry v7Hash4.params.row) Msg (Fin 5 → F) M ninp logw logc)
    (hnlin : V.nlin = nlin) (hnt : V.nt = nt)
    (dom : LigeroFamily.ReedSolomon.Domain F v7Hash4.params.row.openings v7Hash4.params.q
      v7Hash4.params.row.n)
    (respOf : Msg → LigeroFamily.Response F v7Hash4.params.row.openings v7Hash4.params.q
      v7Hash4.params.row.n 1)
    (body : TwoOracleTree Enc D (MPoint D Msg v7Hash4.params.nl v7Hash4.params.rounds) C Out tA N)
    (rootOf : Out → D) (msgOf : Out → ℕ → Msg)
    (claimOf : Out → OpeningClaim v7Hash4.params.row.n Salt (Col F v7Hash4.params.nw v7Hash4.params.nq) D)
    (hF : Fintype.card F = v7Hash4.params.row.fieldSize)
    (H : ∀ κ : D × List (Enc × D), ZkHonest F
      (ZkLigeroV1.Lift (Row.rowValid v7Hash4_valid) dom (Row.hkrow v7Hash4_valid)
        (extOracle nlin nt (Row.rowValid v7Hash4_valid) dom (Row.hkrow v7Hash4_valid) v7Hash4_openings_pos dec κ))
      logw logc)
    (Sat : ∀ κ : D × List (Enc × D),
      ZkLigeroV1.Lift (Row.rowValid v7Hash4_valid) dom (Row.hkrow v7Hash4_valid)
        (extOracle nlin nt (Row.rowValid v7Hash4_valid) dom (Row.hkrow v7Hash4_valid) v7Hash4_openings_pos dec κ) → Prop)
    (FD : ∀ κ : D × List (Enc × D), ZkFieldData C F
      (ZkLigeroV1.Chal F v7Hash4.params.nw v7Hash4.params.nq nlin nt)
      (LigeroV1LayerStep.Qry v7Hash4.params.row) Msg (Fin 5 → F)
      (ZkLigeroV1.Lift (Row.rowValid v7Hash4_valid) dom (Row.hkrow v7Hash4_valid)
        (extOracle nlin nt (Row.rowValid v7Hash4_valid) dom (Row.hkrow v7Hash4_valid) v7Hash4_openings_pos dec κ))
      M ninp logw logc v7Hash4.params.nl v7Hash4.params.rounds V (H κ) (asgOf pl) (Sat κ))
    (hexact : ∀ κ, (FD κ).ExactAt)
    (htA : tA ≤ v7Hash4.commitFuel) (htape : 2 * v7Hash4.params.row.n + tA ≤ v7Hash4.tape)
    (hD : Fintype.card D = 2 ^ v7Hash4.params.digestBits) :
    ((univ.filter fun ω : (Fin v7Hash4.tape → D) × (MPoint D Msg v7Hash4.params.nl v7Hash4.params.rounds → C) =>
        AcceptsZkDH (nl := v7Hash4.params.nl) (w := v7Hash4.params.rounds)
            (v1K (Equations := Fin nlin ⊕ (Fin nt × Encode.QSide)) (Row.rowValid v7Hash4_valid) dom
              (Row.hkrow v7Hash4_valid) v7Hash4_openings_pos) V codec
            (lfSetup body rootOf msgOf) (NizkAdaptive.lfCheck codec claimOf) rootOf msgOf claimOf
            (stmtOf pl nlin) respOf ω.1 ω.2 ∧
          ZkFails Sat ((lfSetup body rootOf msgOf).context ω.1 ω.2)).card : ℚ)
        / ((Fintype.card D : ℚ) ^ v7Hash4.tape
            * (Fintype.card C : ℚ) ^ Fintype.card (MPoint D Msg v7Hash4.params.nl v7Hash4.params.rounds))
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 117) :=
  le_trans
    (row_zk_deployed_ratio_le v7Hash4_valid v7Hash4_openings_pos 5 pl dec V hnlin hnt dom respOf body
      rootOf msgOf claimOf hF H Sat FD hexact htA htape hD)
    (v7Hash4_zk_rhs_le N)

/--
**v7Sig at the deployed zero-knowledge verifier, with deployed hash inputs: `2^-123 + N · 2^-123`.**
`row_zk_deployed_ratio_le` at `CertifiedV1.v7Sig` — the deployed v7 signature row (21 layers, 542 sumcheck slots, P-256's base field, Ligero V1 at `n = 3187`, `k = 455`, 132 openings), output dimension `logv = 8` — with the
numerals `CompiledZk.v7Sig_zk_rhs_le`.  `N` counts deployed (message-prefix) hash queries.
-/
theorem v7Sig_zk_deployed_ratio_le
    (pl : Encode.Placement ninp M v7Sig.params.q v7Sig.params.nw v7Sig.params.nq nt)
    {codec : Codec Salt (Col F v7Sig.params.nw v7Sig.params.nq) D Enc} (dec : RoleDecoders codec)
    (V : ZkCode C F (ZkLigeroV1.Chal F v7Sig.params.nw v7Sig.params.nq nlin nt)
      (LigeroV1LayerStep.Qry v7Sig.params.row) Msg (Fin 8 → F) M ninp logw logc)
    (hnlin : V.nlin = nlin) (hnt : V.nt = nt)
    (dom : LigeroFamily.ReedSolomon.Domain F v7Sig.params.row.openings v7Sig.params.q
      v7Sig.params.row.n)
    (respOf : Msg → LigeroFamily.Response F v7Sig.params.row.openings v7Sig.params.q
      v7Sig.params.row.n 1)
    (body : TwoOracleTree Enc D (MPoint D Msg v7Sig.params.nl v7Sig.params.rounds) C Out tA N)
    (rootOf : Out → D) (msgOf : Out → ℕ → Msg)
    (claimOf : Out → OpeningClaim v7Sig.params.row.n Salt (Col F v7Sig.params.nw v7Sig.params.nq) D)
    (hF : Fintype.card F = v7Sig.params.row.fieldSize)
    (H : ∀ κ : D × List (Enc × D), ZkHonest F
      (ZkLigeroV1.Lift (Row.rowValid v7Sig_valid) dom (Row.hkrow v7Sig_valid)
        (extOracle nlin nt (Row.rowValid v7Sig_valid) dom (Row.hkrow v7Sig_valid) v7Sig_openings_pos dec κ))
      logw logc)
    (Sat : ∀ κ : D × List (Enc × D),
      ZkLigeroV1.Lift (Row.rowValid v7Sig_valid) dom (Row.hkrow v7Sig_valid)
        (extOracle nlin nt (Row.rowValid v7Sig_valid) dom (Row.hkrow v7Sig_valid) v7Sig_openings_pos dec κ) → Prop)
    (FD : ∀ κ : D × List (Enc × D), ZkFieldData C F
      (ZkLigeroV1.Chal F v7Sig.params.nw v7Sig.params.nq nlin nt)
      (LigeroV1LayerStep.Qry v7Sig.params.row) Msg (Fin 8 → F)
      (ZkLigeroV1.Lift (Row.rowValid v7Sig_valid) dom (Row.hkrow v7Sig_valid)
        (extOracle nlin nt (Row.rowValid v7Sig_valid) dom (Row.hkrow v7Sig_valid) v7Sig_openings_pos dec κ))
      M ninp logw logc v7Sig.params.nl v7Sig.params.rounds V (H κ) (asgOf pl) (Sat κ))
    (hexact : ∀ κ, (FD κ).ExactAt)
    (htA : tA ≤ v7Sig.commitFuel) (htape : 2 * v7Sig.params.row.n + tA ≤ v7Sig.tape)
    (hD : Fintype.card D = 2 ^ v7Sig.params.digestBits) :
    ((univ.filter fun ω : (Fin v7Sig.tape → D) × (MPoint D Msg v7Sig.params.nl v7Sig.params.rounds → C) =>
        AcceptsZkDH (nl := v7Sig.params.nl) (w := v7Sig.params.rounds)
            (v1K (Equations := Fin nlin ⊕ (Fin nt × Encode.QSide)) (Row.rowValid v7Sig_valid) dom
              (Row.hkrow v7Sig_valid) v7Sig_openings_pos) V codec
            (lfSetup body rootOf msgOf) (NizkAdaptive.lfCheck codec claimOf) rootOf msgOf claimOf
            (stmtOf pl nlin) respOf ω.1 ω.2 ∧
          ZkFails Sat ((lfSetup body rootOf msgOf).context ω.1 ω.2)).card : ℚ)
        / ((Fintype.card D : ℚ) ^ v7Sig.tape
            * (Fintype.card C : ℚ) ^ Fintype.card (MPoint D Msg v7Sig.params.nl v7Sig.params.rounds))
      ≤ (1 : ℚ) / 2 ^ 123 + N * ((1 : ℚ) / 2 ^ 123) :=
  le_trans
    (row_zk_deployed_ratio_le v7Sig_valid v7Sig_openings_pos 8 pl dec V hnlin hnt dom respOf body
      rootOf msgOf claimOf hF H Sat FD hexact htA htape hD)
    (v7Sig_zk_rhs_le N)

end Rows

/-! ## 2. Two fields, hash side first -/

open Lfzk.NizkAdaptiveTwoField (check2 len2)
open Lfzk.NizkDeployedHashTwoField (Pt2 setup2 sideCtx)
open Lfzk.CompiledLongfellowAdaptive (slice1 slice2)
open Lfzk.TwoFieldV1Rows Lfzk.Mac

/-- **The two-field zero-knowledge right-hand side is symmetric in the sides** (at equal tapes and
digest lengths): it moves the ECDSA-first certified numerals to the deployed hash-first order. -/
theorem twofield_zk_rhs_swap (R₁ R₂ : Row) (l₁ l₂ : ℕ) (m : ℚ) (N : ℕ) (ht : R₁.tape = R₂.tape)
    (hd : R₁.params.digestBits = R₂.params.digestBits) :
    R₁.zkBound l₁ + R₂.zkBound l₂ + m
        + N * max (max (R₁.zkCoefficient l₁) (R₂.zkCoefficient l₂)) m
        + 2 * (((R₁.tape * (len2 R₁ R₂ + N) : ℕ) : ℚ) / 2 ^ R₁.params.digestBits)
      = R₂.zkBound l₂ + R₁.zkBound l₁ + m
        + N * max (max (R₂.zkCoefficient l₂) (R₁.zkCoefficient l₁)) m
        + 2 * (((R₂.tape * (len2 R₂ R₁ + N) : ℕ) : ℚ) / 2 ^ R₂.params.digestBits) := by
  have hl : len2 R₁ R₂ = len2 R₂ R₁ := by unfold len2; omega
  rw [max_comm (R₁.zkCoefficient l₁), ht, hd, hl]
  ring

section TwoField

variable {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]
variable {D : Type} [Fintype D] [DecidableEq D] [Inhabited D]
variable {Enc X Out : Type} [DecidableEq Enc] [Fintype X]
variable {Fmac : Type} [Field Fmac] [Fintype Fmac] [DecidableEq Fmac] {nblk : ℕ}
variable {F₁ Msg₁ Witness₁ : Type} [Field F₁] [Fintype F₁] [DecidableEq F₁] [SumcheckInterp F₁]
  [DecidableEq Msg₁] [Inhabited Msg₁] [Fintype Msg₁] {M₁ ninp₁ nt₁ nlin₁ logw₁ logc₁ : ℕ}
variable {F₂ Msg₂ Witness₂ : Type} [Field F₂] [Fintype F₂] [DecidableEq F₂] [SumcheckInterp F₂]
  [DecidableEq Msg₂] [Inhabited Msg₂] [Fintype Msg₂] {M₂ ninp₂ nt₂ nlin₂ logw₂ logc₂ : ℕ}
variable {Salt₁ Salt₂ : Type} [Inhabited Salt₁] [Inhabited Salt₂]

omit [DecidableEq Msg₁] [DecidableEq Msg₂] in
/--
**Two-field Longfellow at `v7P256Sha1` (`v7Hash1` hash side first, then `v7Sig`), at the deployed
zero-knowledge verifiers, with deployed hash inputs: `2^-115 + N · 2^-117`.**
`twofield_zk_deployed_ratio_le` with `TwoFieldV1Rows.v7P256Sha1_zk_rhs_le` (via `twofield_zk_rhs_swap`),
output dimensions `logv = 3` (hash) and `8` (signature):

```text
Pr[ both deployed verifiers accept  ∧  av = ro(key point)  ∧  no two good witnesses agree ]
    ≤  2^-115  +  N · 2^-117
```

against one adaptive program making at most `tA ≤ 2^60` Merkle-oracle queries and `N` deployed hash
queries over all three roles.
-/
theorem v7P256Sha1_zk_deployed_ratio_le {tA N : ℕ} (hFmac : Fintype.card Fmac = 2 ^ 128)
    {codec₁ : Codec Salt₁ (Col F₁ v7P256Sha1.sha.params.nw v7P256Sha1.sha.params.nq) D Enc}
    {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ v7P256Sha1.ecdsa.params.nw v7P256Sha1.ecdsa.params.nq) D Enc}
    {dec₂ : RoleDecoders codec₂}
    (L₁ : CompiledZkSide v7P256Sha1.sha (TwoFieldRowV1.sha_valid v7P256Sha1_valid) v7P256Sha1_sha_openings_pos 3
      C F₁ Msg₁ Witness₁ M₁ ninp₁ nt₁ nlin₁ logw₁ logc₁ X dec₁ Prod.fst)
    (L₂ : CompiledZkSide v7P256Sha1.ecdsa (TwoFieldRowV1.ecdsa_valid v7P256Sha1_valid) v7P256Sha1_ecdsa_openings_pos 8
      C F₂ Msg₂ Witness₂ M₂ ninp₂ nt₂ nlin₂ logw₂ logc₂ X dec₂ Prod.snd)
    (body : TwoOracleTree Enc D (Pt2 D C X Msg₁ Msg₂ v7P256Sha1.sha.params.nl v7P256Sha1.ecdsa.params.nl
          v7P256Sha1.sha.params.rounds v7P256Sha1.ecdsa.params.rounds) C Out tA N)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim v7P256Sha1.sha.params.row.n Salt₁
      (Col F₁ v7P256Sha1.sha.params.nw v7P256Sha1.sha.params.nq) D)
    (claimOf₂ : Out → OpeningClaim v7P256Sha1.ecdsa.params.row.n Salt₂
      (Col F₂ v7P256Sha1.ecdsa.params.nw v7P256Sha1.ecdsa.params.nq) D)
    (hD : Fintype.card D = 2 ^ v7P256Sha1.ecdsa.params.digestBits)
    (aP : (D × D) × List (Enc × D) → Fmac) (decode : C → Fmac) (kmac : ℕ)
    (hbal : ∀ x : Fmac, (univ.filter fun c : C => decode c = x).card ≤ kmac)
    (hmac : kmac * Fintype.card Fmac ≤ Fintype.card C)
    (keyB tagOf : Out → Fin nblk → Fmac)
    (common₁ : Witness₁ → Fin nblk → Fmac) (common₂ : Witness₂ → Fin nblk → Fmac)
    (hrow₁ : ∀ (mt : Fin v7P256Sha1.sha.tape → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7P256Sha1.sha.params.nl v7P256Sha1.ecdsa.params.nl
          v7P256Sha1.sha.params.rounds v7P256Sha1.ecdsa.params.rounds → C) (a : Witness₁),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      L₁.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf pubOf
        (slice1 v7P256Sha1.sha v7P256Sha1.ecdsa) mt ro →
      L₁.Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (keyB (S.proof mt ro)) (common₁ a) = tagOf (S.proof mt ro))
    (hrow₂ : ∀ (mt : Fin v7P256Sha1.sha.tape → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7P256Sha1.sha.params.nl v7P256Sha1.ecdsa.params.nl
          v7P256Sha1.sha.params.rounds v7P256Sha1.ecdsa.params.rounds → C) (a : Witness₂),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      L₂.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf pubOf
        (slice2 v7P256Sha1.sha v7P256Sha1.ecdsa) mt ro →
      L₂.Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (keyB (S.proof mt ro)) (common₂ a) = tagOf (S.proof mt ro))
    (htA : tA ≤ 2 ^ 60)
    (htape : 2 * v7P256Sha1.ecdsa.params.row.n + 2 * v7P256Sha1.sha.params.row.n + tA ≤ 2 ^ 62) :
    ((univ.filter fun ω : (Fin v7P256Sha1.sha.tape → D) ×
          (Pt2 D C X Msg₁ Msg₂ v7P256Sha1.sha.params.nl v7P256Sha1.ecdsa.params.nl
          v7P256Sha1.sha.params.rounds v7P256Sha1.ecdsa.params.rounds → C) =>
        L₁.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf pubOf
            (slice1 v7P256Sha1.sha v7P256Sha1.ecdsa) ω.1 ω.2 ∧
          L₂.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf pubOf
            (slice2 v7P256Sha1.sha v7P256Sha1.ecdsa) ω.1 ω.2 ∧
          (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).challenges ω.1 ω.2
              ⟨0, by omega⟩
            = avOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2) ∧
          ¬ ∃ a₁ a₂,
            L₁.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf pubOf
              ω.1 ω.2) a₁ ∧
            L₂.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf pubOf
              ω.1 ω.2) a₂ ∧
            common₁ a₁ = common₂ a₂).card : ℚ)
        / ((Fintype.card D : ℚ) ^ v7P256Sha1.sha.tape * (Fintype.card C : ℚ) ^ Fintype.card
            (Pt2 D C X Msg₁ Msg₂ v7P256Sha1.sha.params.nl v7P256Sha1.ecdsa.params.nl
          v7P256Sha1.sha.params.rounds v7P256Sha1.ecdsa.params.rounds))
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 117) := by
  have hv := v7P256Sha1_valid
  refine le_trans
    (twofield_zk_deployed_ratio_le (TwoFieldRowV1.sha_valid hv) (TwoFieldRowV1.ecdsa_valid hv)
      v7P256Sha1_sha_openings_pos v7P256Sha1_ecdsa_openings_pos L₁ L₂ body rootOf₁ rootOf₂ avOf pubOf
      msgOf₁ msgOf₂ claimOf₁ claimOf₂ (hD.trans (by rw [TwoFieldRowV1.digest_eq hv])) hD aP decode
      kmac hbal hmac keyB tagOf common₁ common₂ hrow₁ hrow₂ htA htA htape
      (TwoFieldRowV1.tape_eq hv).symm) ?_
  rw [twofield_zk_rhs_swap _ _ _ _ _ N (TwoFieldRowV1.tape_eq hv).symm
    (TwoFieldRowV1.digest_eq hv).symm]
  exact v7P256Sha1_zk_rhs_le N hFmac

omit [DecidableEq Msg₁] [DecidableEq Msg₂] in
/--
**Two-field Longfellow at `v7P256Sha2` (`v7Hash2` hash side first, then `v7Sig`), at the deployed
zero-knowledge verifiers, with deployed hash inputs: `2^-115 + N · 2^-117`.**
`twofield_zk_deployed_ratio_le` with `TwoFieldV1Rows.v7P256Sha2_zk_rhs_le` (via `twofield_zk_rhs_swap`),
output dimensions `logv = 4` (hash) and `8` (signature):

```text
Pr[ both deployed verifiers accept  ∧  av = ro(key point)  ∧  no two good witnesses agree ]
    ≤  2^-115  +  N · 2^-117
```

against one adaptive program making at most `tA ≤ 2^60` Merkle-oracle queries and `N` deployed hash
queries over all three roles.
-/
theorem v7P256Sha2_zk_deployed_ratio_le {tA N : ℕ} (hFmac : Fintype.card Fmac = 2 ^ 128)
    {codec₁ : Codec Salt₁ (Col F₁ v7P256Sha2.sha.params.nw v7P256Sha2.sha.params.nq) D Enc}
    {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ v7P256Sha2.ecdsa.params.nw v7P256Sha2.ecdsa.params.nq) D Enc}
    {dec₂ : RoleDecoders codec₂}
    (L₁ : CompiledZkSide v7P256Sha2.sha (TwoFieldRowV1.sha_valid v7P256Sha2_valid) v7P256Sha2_sha_openings_pos 4
      C F₁ Msg₁ Witness₁ M₁ ninp₁ nt₁ nlin₁ logw₁ logc₁ X dec₁ Prod.fst)
    (L₂ : CompiledZkSide v7P256Sha2.ecdsa (TwoFieldRowV1.ecdsa_valid v7P256Sha2_valid) v7P256Sha2_ecdsa_openings_pos 8
      C F₂ Msg₂ Witness₂ M₂ ninp₂ nt₂ nlin₂ logw₂ logc₂ X dec₂ Prod.snd)
    (body : TwoOracleTree Enc D (Pt2 D C X Msg₁ Msg₂ v7P256Sha2.sha.params.nl v7P256Sha2.ecdsa.params.nl
          v7P256Sha2.sha.params.rounds v7P256Sha2.ecdsa.params.rounds) C Out tA N)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim v7P256Sha2.sha.params.row.n Salt₁
      (Col F₁ v7P256Sha2.sha.params.nw v7P256Sha2.sha.params.nq) D)
    (claimOf₂ : Out → OpeningClaim v7P256Sha2.ecdsa.params.row.n Salt₂
      (Col F₂ v7P256Sha2.ecdsa.params.nw v7P256Sha2.ecdsa.params.nq) D)
    (hD : Fintype.card D = 2 ^ v7P256Sha2.ecdsa.params.digestBits)
    (aP : (D × D) × List (Enc × D) → Fmac) (decode : C → Fmac) (kmac : ℕ)
    (hbal : ∀ x : Fmac, (univ.filter fun c : C => decode c = x).card ≤ kmac)
    (hmac : kmac * Fintype.card Fmac ≤ Fintype.card C)
    (keyB tagOf : Out → Fin nblk → Fmac)
    (common₁ : Witness₁ → Fin nblk → Fmac) (common₂ : Witness₂ → Fin nblk → Fmac)
    (hrow₁ : ∀ (mt : Fin v7P256Sha2.sha.tape → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7P256Sha2.sha.params.nl v7P256Sha2.ecdsa.params.nl
          v7P256Sha2.sha.params.rounds v7P256Sha2.ecdsa.params.rounds → C) (a : Witness₁),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      L₁.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf pubOf
        (slice1 v7P256Sha2.sha v7P256Sha2.ecdsa) mt ro →
      L₁.Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (keyB (S.proof mt ro)) (common₁ a) = tagOf (S.proof mt ro))
    (hrow₂ : ∀ (mt : Fin v7P256Sha2.sha.tape → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7P256Sha2.sha.params.nl v7P256Sha2.ecdsa.params.nl
          v7P256Sha2.sha.params.rounds v7P256Sha2.ecdsa.params.rounds → C) (a : Witness₂),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      L₂.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf pubOf
        (slice2 v7P256Sha2.sha v7P256Sha2.ecdsa) mt ro →
      L₂.Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (keyB (S.proof mt ro)) (common₂ a) = tagOf (S.proof mt ro))
    (htA : tA ≤ 2 ^ 60)
    (htape : 2 * v7P256Sha2.ecdsa.params.row.n + 2 * v7P256Sha2.sha.params.row.n + tA ≤ 2 ^ 62) :
    ((univ.filter fun ω : (Fin v7P256Sha2.sha.tape → D) ×
          (Pt2 D C X Msg₁ Msg₂ v7P256Sha2.sha.params.nl v7P256Sha2.ecdsa.params.nl
          v7P256Sha2.sha.params.rounds v7P256Sha2.ecdsa.params.rounds → C) =>
        L₁.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf pubOf
            (slice1 v7P256Sha2.sha v7P256Sha2.ecdsa) ω.1 ω.2 ∧
          L₂.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf pubOf
            (slice2 v7P256Sha2.sha v7P256Sha2.ecdsa) ω.1 ω.2 ∧
          (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).challenges ω.1 ω.2
              ⟨0, by omega⟩
            = avOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2) ∧
          ¬ ∃ a₁ a₂,
            L₁.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf pubOf
              ω.1 ω.2) a₁ ∧
            L₂.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf pubOf
              ω.1 ω.2) a₂ ∧
            common₁ a₁ = common₂ a₂).card : ℚ)
        / ((Fintype.card D : ℚ) ^ v7P256Sha2.sha.tape * (Fintype.card C : ℚ) ^ Fintype.card
            (Pt2 D C X Msg₁ Msg₂ v7P256Sha2.sha.params.nl v7P256Sha2.ecdsa.params.nl
          v7P256Sha2.sha.params.rounds v7P256Sha2.ecdsa.params.rounds))
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 117) := by
  have hv := v7P256Sha2_valid
  refine le_trans
    (twofield_zk_deployed_ratio_le (TwoFieldRowV1.sha_valid hv) (TwoFieldRowV1.ecdsa_valid hv)
      v7P256Sha2_sha_openings_pos v7P256Sha2_ecdsa_openings_pos L₁ L₂ body rootOf₁ rootOf₂ avOf pubOf
      msgOf₁ msgOf₂ claimOf₁ claimOf₂ (hD.trans (by rw [TwoFieldRowV1.digest_eq hv])) hD aP decode
      kmac hbal hmac keyB tagOf common₁ common₂ hrow₁ hrow₂ htA htA htape
      (TwoFieldRowV1.tape_eq hv).symm) ?_
  rw [twofield_zk_rhs_swap _ _ _ _ _ N (TwoFieldRowV1.tape_eq hv).symm
    (TwoFieldRowV1.digest_eq hv).symm]
  exact v7P256Sha2_zk_rhs_le N hFmac

omit [DecidableEq Msg₁] [DecidableEq Msg₂] in
/--
**Two-field Longfellow at `v7P256Sha3` (`v7Hash3` hash side first, then `v7Sig`), at the deployed
zero-knowledge verifiers, with deployed hash inputs: `2^-115 + N · 2^-117`.**
`twofield_zk_deployed_ratio_le` with `TwoFieldV1Rows.v7P256Sha3_zk_rhs_le` (via `twofield_zk_rhs_swap`),
output dimensions `logv = 4` (hash) and `8` (signature):

```text
Pr[ both deployed verifiers accept  ∧  av = ro(key point)  ∧  no two good witnesses agree ]
    ≤  2^-115  +  N · 2^-117
```

against one adaptive program making at most `tA ≤ 2^60` Merkle-oracle queries and `N` deployed hash
queries over all three roles.
-/
theorem v7P256Sha3_zk_deployed_ratio_le {tA N : ℕ} (hFmac : Fintype.card Fmac = 2 ^ 128)
    {codec₁ : Codec Salt₁ (Col F₁ v7P256Sha3.sha.params.nw v7P256Sha3.sha.params.nq) D Enc}
    {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ v7P256Sha3.ecdsa.params.nw v7P256Sha3.ecdsa.params.nq) D Enc}
    {dec₂ : RoleDecoders codec₂}
    (L₁ : CompiledZkSide v7P256Sha3.sha (TwoFieldRowV1.sha_valid v7P256Sha3_valid) v7P256Sha3_sha_openings_pos 4
      C F₁ Msg₁ Witness₁ M₁ ninp₁ nt₁ nlin₁ logw₁ logc₁ X dec₁ Prod.fst)
    (L₂ : CompiledZkSide v7P256Sha3.ecdsa (TwoFieldRowV1.ecdsa_valid v7P256Sha3_valid) v7P256Sha3_ecdsa_openings_pos 8
      C F₂ Msg₂ Witness₂ M₂ ninp₂ nt₂ nlin₂ logw₂ logc₂ X dec₂ Prod.snd)
    (body : TwoOracleTree Enc D (Pt2 D C X Msg₁ Msg₂ v7P256Sha3.sha.params.nl v7P256Sha3.ecdsa.params.nl
          v7P256Sha3.sha.params.rounds v7P256Sha3.ecdsa.params.rounds) C Out tA N)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim v7P256Sha3.sha.params.row.n Salt₁
      (Col F₁ v7P256Sha3.sha.params.nw v7P256Sha3.sha.params.nq) D)
    (claimOf₂ : Out → OpeningClaim v7P256Sha3.ecdsa.params.row.n Salt₂
      (Col F₂ v7P256Sha3.ecdsa.params.nw v7P256Sha3.ecdsa.params.nq) D)
    (hD : Fintype.card D = 2 ^ v7P256Sha3.ecdsa.params.digestBits)
    (aP : (D × D) × List (Enc × D) → Fmac) (decode : C → Fmac) (kmac : ℕ)
    (hbal : ∀ x : Fmac, (univ.filter fun c : C => decode c = x).card ≤ kmac)
    (hmac : kmac * Fintype.card Fmac ≤ Fintype.card C)
    (keyB tagOf : Out → Fin nblk → Fmac)
    (common₁ : Witness₁ → Fin nblk → Fmac) (common₂ : Witness₂ → Fin nblk → Fmac)
    (hrow₁ : ∀ (mt : Fin v7P256Sha3.sha.tape → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7P256Sha3.sha.params.nl v7P256Sha3.ecdsa.params.nl
          v7P256Sha3.sha.params.rounds v7P256Sha3.ecdsa.params.rounds → C) (a : Witness₁),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      L₁.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf pubOf
        (slice1 v7P256Sha3.sha v7P256Sha3.ecdsa) mt ro →
      L₁.Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (keyB (S.proof mt ro)) (common₁ a) = tagOf (S.proof mt ro))
    (hrow₂ : ∀ (mt : Fin v7P256Sha3.sha.tape → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7P256Sha3.sha.params.nl v7P256Sha3.ecdsa.params.nl
          v7P256Sha3.sha.params.rounds v7P256Sha3.ecdsa.params.rounds → C) (a : Witness₂),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      L₂.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf pubOf
        (slice2 v7P256Sha3.sha v7P256Sha3.ecdsa) mt ro →
      L₂.Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (keyB (S.proof mt ro)) (common₂ a) = tagOf (S.proof mt ro))
    (htA : tA ≤ 2 ^ 60)
    (htape : 2 * v7P256Sha3.ecdsa.params.row.n + 2 * v7P256Sha3.sha.params.row.n + tA ≤ 2 ^ 62) :
    ((univ.filter fun ω : (Fin v7P256Sha3.sha.tape → D) ×
          (Pt2 D C X Msg₁ Msg₂ v7P256Sha3.sha.params.nl v7P256Sha3.ecdsa.params.nl
          v7P256Sha3.sha.params.rounds v7P256Sha3.ecdsa.params.rounds → C) =>
        L₁.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf pubOf
            (slice1 v7P256Sha3.sha v7P256Sha3.ecdsa) ω.1 ω.2 ∧
          L₂.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf pubOf
            (slice2 v7P256Sha3.sha v7P256Sha3.ecdsa) ω.1 ω.2 ∧
          (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).challenges ω.1 ω.2
              ⟨0, by omega⟩
            = avOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2) ∧
          ¬ ∃ a₁ a₂,
            L₁.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf pubOf
              ω.1 ω.2) a₁ ∧
            L₂.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf pubOf
              ω.1 ω.2) a₂ ∧
            common₁ a₁ = common₂ a₂).card : ℚ)
        / ((Fintype.card D : ℚ) ^ v7P256Sha3.sha.tape * (Fintype.card C : ℚ) ^ Fintype.card
            (Pt2 D C X Msg₁ Msg₂ v7P256Sha3.sha.params.nl v7P256Sha3.ecdsa.params.nl
          v7P256Sha3.sha.params.rounds v7P256Sha3.ecdsa.params.rounds))
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 117) := by
  have hv := v7P256Sha3_valid
  refine le_trans
    (twofield_zk_deployed_ratio_le (TwoFieldRowV1.sha_valid hv) (TwoFieldRowV1.ecdsa_valid hv)
      v7P256Sha3_sha_openings_pos v7P256Sha3_ecdsa_openings_pos L₁ L₂ body rootOf₁ rootOf₂ avOf pubOf
      msgOf₁ msgOf₂ claimOf₁ claimOf₂ (hD.trans (by rw [TwoFieldRowV1.digest_eq hv])) hD aP decode
      kmac hbal hmac keyB tagOf common₁ common₂ hrow₁ hrow₂ htA htA htape
      (TwoFieldRowV1.tape_eq hv).symm) ?_
  rw [twofield_zk_rhs_swap _ _ _ _ _ N (TwoFieldRowV1.tape_eq hv).symm
    (TwoFieldRowV1.digest_eq hv).symm]
  exact v7P256Sha3_zk_rhs_le N hFmac

omit [DecidableEq Msg₁] [DecidableEq Msg₂] in
/--
**Two-field Longfellow at `v7P256Sha4` (`v7Hash4` hash side first, then `v7Sig`), at the deployed
zero-knowledge verifiers, with deployed hash inputs: `2^-115 + N · 2^-117`.**
`twofield_zk_deployed_ratio_le` with `TwoFieldV1Rows.v7P256Sha4_zk_rhs_le` (via `twofield_zk_rhs_swap`),
output dimensions `logv = 5` (hash) and `8` (signature):

```text
Pr[ both deployed verifiers accept  ∧  av = ro(key point)  ∧  no two good witnesses agree ]
    ≤  2^-115  +  N · 2^-117
```

against one adaptive program making at most `tA ≤ 2^60` Merkle-oracle queries and `N` deployed hash
queries over all three roles.
-/
theorem v7P256Sha4_zk_deployed_ratio_le {tA N : ℕ} (hFmac : Fintype.card Fmac = 2 ^ 128)
    {codec₁ : Codec Salt₁ (Col F₁ v7P256Sha4.sha.params.nw v7P256Sha4.sha.params.nq) D Enc}
    {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ v7P256Sha4.ecdsa.params.nw v7P256Sha4.ecdsa.params.nq) D Enc}
    {dec₂ : RoleDecoders codec₂}
    (L₁ : CompiledZkSide v7P256Sha4.sha (TwoFieldRowV1.sha_valid v7P256Sha4_valid) v7P256Sha4_sha_openings_pos 5
      C F₁ Msg₁ Witness₁ M₁ ninp₁ nt₁ nlin₁ logw₁ logc₁ X dec₁ Prod.fst)
    (L₂ : CompiledZkSide v7P256Sha4.ecdsa (TwoFieldRowV1.ecdsa_valid v7P256Sha4_valid) v7P256Sha4_ecdsa_openings_pos 8
      C F₂ Msg₂ Witness₂ M₂ ninp₂ nt₂ nlin₂ logw₂ logc₂ X dec₂ Prod.snd)
    (body : TwoOracleTree Enc D (Pt2 D C X Msg₁ Msg₂ v7P256Sha4.sha.params.nl v7P256Sha4.ecdsa.params.nl
          v7P256Sha4.sha.params.rounds v7P256Sha4.ecdsa.params.rounds) C Out tA N)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim v7P256Sha4.sha.params.row.n Salt₁
      (Col F₁ v7P256Sha4.sha.params.nw v7P256Sha4.sha.params.nq) D)
    (claimOf₂ : Out → OpeningClaim v7P256Sha4.ecdsa.params.row.n Salt₂
      (Col F₂ v7P256Sha4.ecdsa.params.nw v7P256Sha4.ecdsa.params.nq) D)
    (hD : Fintype.card D = 2 ^ v7P256Sha4.ecdsa.params.digestBits)
    (aP : (D × D) × List (Enc × D) → Fmac) (decode : C → Fmac) (kmac : ℕ)
    (hbal : ∀ x : Fmac, (univ.filter fun c : C => decode c = x).card ≤ kmac)
    (hmac : kmac * Fintype.card Fmac ≤ Fintype.card C)
    (keyB tagOf : Out → Fin nblk → Fmac)
    (common₁ : Witness₁ → Fin nblk → Fmac) (common₂ : Witness₂ → Fin nblk → Fmac)
    (hrow₁ : ∀ (mt : Fin v7P256Sha4.sha.tape → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7P256Sha4.sha.params.nl v7P256Sha4.ecdsa.params.nl
          v7P256Sha4.sha.params.rounds v7P256Sha4.ecdsa.params.rounds → C) (a : Witness₁),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      L₁.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf pubOf
        (slice1 v7P256Sha4.sha v7P256Sha4.ecdsa) mt ro →
      L₁.Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (keyB (S.proof mt ro)) (common₁ a) = tagOf (S.proof mt ro))
    (hrow₂ : ∀ (mt : Fin v7P256Sha4.sha.tape → D)
        (ro : Pt2 D C X Msg₁ Msg₂ v7P256Sha4.sha.params.nl v7P256Sha4.ecdsa.params.nl
          v7P256Sha4.sha.params.rounds v7P256Sha4.ecdsa.params.rounds → C) (a : Witness₂),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      L₂.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf pubOf
        (slice2 v7P256Sha4.sha v7P256Sha4.ecdsa) mt ro →
      L₂.Good (sideCtx S avOf pubOf mt ro) a →
      macTag (aP (S.context mt ro) + decode (avOf (S.proof mt ro)))
        (keyB (S.proof mt ro)) (common₂ a) = tagOf (S.proof mt ro))
    (htA : tA ≤ 2 ^ 60)
    (htape : 2 * v7P256Sha4.ecdsa.params.row.n + 2 * v7P256Sha4.sha.params.row.n + tA ≤ 2 ^ 62) :
    ((univ.filter fun ω : (Fin v7P256Sha4.sha.tape → D) ×
          (Pt2 D C X Msg₁ Msg₂ v7P256Sha4.sha.params.nl v7P256Sha4.ecdsa.params.nl
          v7P256Sha4.sha.params.rounds v7P256Sha4.ecdsa.params.rounds → C) =>
        L₁.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁ avOf pubOf
            (slice1 v7P256Sha4.sha v7P256Sha4.ecdsa) ω.1 ω.2 ∧
          L₂.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂ avOf pubOf
            (slice2 v7P256Sha4.sha v7P256Sha4.ecdsa) ω.1 ω.2 ∧
          (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).challenges ω.1 ω.2
              ⟨0, by omega⟩
            = avOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2) ∧
          ¬ ∃ a₁ a₂,
            L₁.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf pubOf
              ω.1 ω.2) a₁ ∧
            L₂.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂) avOf pubOf
              ω.1 ω.2) a₂ ∧
            common₁ a₁ = common₂ a₂).card : ℚ)
        / ((Fintype.card D : ℚ) ^ v7P256Sha4.sha.tape * (Fintype.card C : ℚ) ^ Fintype.card
            (Pt2 D C X Msg₁ Msg₂ v7P256Sha4.sha.params.nl v7P256Sha4.ecdsa.params.nl
          v7P256Sha4.sha.params.rounds v7P256Sha4.ecdsa.params.rounds))
      ≤ (1 : ℚ) / 2 ^ 115 + N * ((1 : ℚ) / 2 ^ 117) := by
  have hv := v7P256Sha4_valid
  refine le_trans
    (twofield_zk_deployed_ratio_le (TwoFieldRowV1.sha_valid hv) (TwoFieldRowV1.ecdsa_valid hv)
      v7P256Sha4_sha_openings_pos v7P256Sha4_ecdsa_openings_pos L₁ L₂ body rootOf₁ rootOf₂ avOf pubOf
      msgOf₁ msgOf₂ claimOf₁ claimOf₂ (hD.trans (by rw [TwoFieldRowV1.digest_eq hv])) hD aP decode
      kmac hbal hmac keyB tagOf common₁ common₂ hrow₁ hrow₂ htA htA htape
      (TwoFieldRowV1.tape_eq hv).symm) ?_
  rw [twofield_zk_rhs_swap _ _ _ _ _ N (TwoFieldRowV1.tape_eq hv).symm
    (TwoFieldRowV1.digest_eq hv).symm]
  exact v7P256Sha4_zk_rhs_le N hFmac

end TwoField

end Lfzk.CompiledZkDeployedHash
