import Lfzk.CompiledZkTwoFieldRows

/-!
# The v7 pairs' numerals with the separate-MAC slot

`NizkZkDeployedHash.twofield_zk_deployed_adaptive_ratio_leT_sep` charges the MAC slot
`B₁ · B₂ / |Fmac|` instead of `1/|Fmac|`, where `Bₖ` bounds side `k`'s candidate list.  At the v7
pairs the candidates are the lift lists, `cardCand = 2` on both sides, so the slot costs
`4 / 2^128 = 2^-126` (`v7P256ShaK_sep_mac_eq`).  This file re-certifies the pairs' two slack
numerals (`CompiledZkTwoFieldRows`' `v7P256ShaK_zk_slack_bound`, `_slack_coeff`) with that slot, by
`native_decide`:

| pair | bound at `N = 0` | coefficient |
|---|---|---|
| `v7P256Sha1` … `v7P256Sha4` | `≤ 2^-115` | `≤ 2^-117` |

— the same integer levels as with `1/|Fmac|`.  The MAC slot is not the worst slot: `4/2^128` is
below both rows' `zkCoefficient` (`v7P256ShaK_sep_mac_le_coeff`, `κ_hash ≈ 2^-117.1`), so the
per-query coefficient `max(κ_sig, κ_hash, 4/2^128)` is exactly the old `max(κ_sig, κ_hash)`
(`v7P256ShaK_sep_coeff_eq`); only the constant term grows, by `3/2^128`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.TwoFieldV1Rows

open Lfzk.NizkAdaptiveTwoField Lfzk.CertifiedV1 Lfzk.NizkZk

/-- `v7P256Sha1`'s separate-MAC slot: `cardCand · cardCand / |Fmac| = 4 / 2^128`. -/
theorem v7P256Sha1_sep_mac_eq :
    (v7P256Sha1.sha.cardCand : ℚ) * v7P256Sha1.ecdsa.cardCand / (v7P256Sha1.macFieldSize : ℚ)
      = 4 / 2 ^ 128 := by
  native_decide

/-- `v7P256Sha1` with the separate-MAC slot (`logv = 8, 3`), at `N = 0`: at most `2^-115`. -/
theorem v7P256Sha1_sep_slack_bound :
    v7P256Sha1.ecdsa.zkBound 8 + v7P256Sha1.sha.zkBound 3
        + (v7P256Sha1.sha.cardCand : ℚ) * v7P256Sha1.ecdsa.cardCand / (v7P256Sha1.macFieldSize : ℚ)
        + 2 * (((v7P256Sha1.ecdsa.tape * len2 v7P256Sha1.ecdsa v7P256Sha1.sha : ℕ) : ℚ)
          / 2 ^ v7P256Sha1.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ 115 := by
  native_decide

/-- `v7P256Sha1`'s worst coefficient with the separate-MAC slot plus the per-query term: at most
`2^-117`. -/
theorem v7P256Sha1_sep_slack_coeff :
    max (max (v7P256Sha1.ecdsa.zkCoefficient 8) (v7P256Sha1.sha.zkCoefficient 3))
        ((v7P256Sha1.sha.cardCand : ℚ) * v7P256Sha1.ecdsa.cardCand / (v7P256Sha1.macFieldSize : ℚ))
      + 2 * ((v7P256Sha1.ecdsa.tape : ℚ) / 2 ^ v7P256Sha1.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ 117 := by
  native_decide

/-- At `v7P256Sha1` the separate-MAC slot is below both rows' worst slot. -/
theorem v7P256Sha1_sep_mac_le_coeff :
    (v7P256Sha1.sha.cardCand : ℚ) * v7P256Sha1.ecdsa.cardCand / (v7P256Sha1.macFieldSize : ℚ)
      ≤ max (v7P256Sha1.ecdsa.zkCoefficient 8) (v7P256Sha1.sha.zkCoefficient 3) := by
  native_decide

/-- So at `v7P256Sha1` the per-query coefficient with the separate-MAC slot is the old one without
it. -/
theorem v7P256Sha1_sep_coeff_eq :
    max (max (v7P256Sha1.ecdsa.zkCoefficient 8) (v7P256Sha1.sha.zkCoefficient 3))
        ((v7P256Sha1.sha.cardCand : ℚ) * v7P256Sha1.ecdsa.cardCand / (v7P256Sha1.macFieldSize : ℚ))
      = max (v7P256Sha1.ecdsa.zkCoefficient 8) (v7P256Sha1.sha.zkCoefficient 3) :=
  max_eq_left v7P256Sha1_sep_mac_le_coeff

/-- `v7P256Sha2`'s separate-MAC slot: `cardCand · cardCand / |Fmac| = 4 / 2^128`. -/
theorem v7P256Sha2_sep_mac_eq :
    (v7P256Sha2.sha.cardCand : ℚ) * v7P256Sha2.ecdsa.cardCand / (v7P256Sha2.macFieldSize : ℚ)
      = 4 / 2 ^ 128 := by
  native_decide

/-- `v7P256Sha2` with the separate-MAC slot (`logv = 8, 4`), at `N = 0`: at most `2^-115`. -/
theorem v7P256Sha2_sep_slack_bound :
    v7P256Sha2.ecdsa.zkBound 8 + v7P256Sha2.sha.zkBound 4
        + (v7P256Sha2.sha.cardCand : ℚ) * v7P256Sha2.ecdsa.cardCand / (v7P256Sha2.macFieldSize : ℚ)
        + 2 * (((v7P256Sha2.ecdsa.tape * len2 v7P256Sha2.ecdsa v7P256Sha2.sha : ℕ) : ℚ)
          / 2 ^ v7P256Sha2.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ 115 := by
  native_decide

/-- `v7P256Sha2`'s worst coefficient with the separate-MAC slot plus the per-query term: at most
`2^-117`. -/
theorem v7P256Sha2_sep_slack_coeff :
    max (max (v7P256Sha2.ecdsa.zkCoefficient 8) (v7P256Sha2.sha.zkCoefficient 4))
        ((v7P256Sha2.sha.cardCand : ℚ) * v7P256Sha2.ecdsa.cardCand / (v7P256Sha2.macFieldSize : ℚ))
      + 2 * ((v7P256Sha2.ecdsa.tape : ℚ) / 2 ^ v7P256Sha2.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ 117 := by
  native_decide

/-- At `v7P256Sha2` the separate-MAC slot is below both rows' worst slot. -/
theorem v7P256Sha2_sep_mac_le_coeff :
    (v7P256Sha2.sha.cardCand : ℚ) * v7P256Sha2.ecdsa.cardCand / (v7P256Sha2.macFieldSize : ℚ)
      ≤ max (v7P256Sha2.ecdsa.zkCoefficient 8) (v7P256Sha2.sha.zkCoefficient 4) := by
  native_decide

/-- So at `v7P256Sha2` the per-query coefficient with the separate-MAC slot is the old one without
it. -/
theorem v7P256Sha2_sep_coeff_eq :
    max (max (v7P256Sha2.ecdsa.zkCoefficient 8) (v7P256Sha2.sha.zkCoefficient 4))
        ((v7P256Sha2.sha.cardCand : ℚ) * v7P256Sha2.ecdsa.cardCand / (v7P256Sha2.macFieldSize : ℚ))
      = max (v7P256Sha2.ecdsa.zkCoefficient 8) (v7P256Sha2.sha.zkCoefficient 4) :=
  max_eq_left v7P256Sha2_sep_mac_le_coeff

/-- `v7P256Sha3`'s separate-MAC slot: `cardCand · cardCand / |Fmac| = 4 / 2^128`. -/
theorem v7P256Sha3_sep_mac_eq :
    (v7P256Sha3.sha.cardCand : ℚ) * v7P256Sha3.ecdsa.cardCand / (v7P256Sha3.macFieldSize : ℚ)
      = 4 / 2 ^ 128 := by
  native_decide

/-- `v7P256Sha3` with the separate-MAC slot (`logv = 8, 4`), at `N = 0`: at most `2^-115`. -/
theorem v7P256Sha3_sep_slack_bound :
    v7P256Sha3.ecdsa.zkBound 8 + v7P256Sha3.sha.zkBound 4
        + (v7P256Sha3.sha.cardCand : ℚ) * v7P256Sha3.ecdsa.cardCand / (v7P256Sha3.macFieldSize : ℚ)
        + 2 * (((v7P256Sha3.ecdsa.tape * len2 v7P256Sha3.ecdsa v7P256Sha3.sha : ℕ) : ℚ)
          / 2 ^ v7P256Sha3.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ 115 := by
  native_decide

/-- `v7P256Sha3`'s worst coefficient with the separate-MAC slot plus the per-query term: at most
`2^-117`. -/
theorem v7P256Sha3_sep_slack_coeff :
    max (max (v7P256Sha3.ecdsa.zkCoefficient 8) (v7P256Sha3.sha.zkCoefficient 4))
        ((v7P256Sha3.sha.cardCand : ℚ) * v7P256Sha3.ecdsa.cardCand / (v7P256Sha3.macFieldSize : ℚ))
      + 2 * ((v7P256Sha3.ecdsa.tape : ℚ) / 2 ^ v7P256Sha3.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ 117 := by
  native_decide

/-- At `v7P256Sha3` the separate-MAC slot is below both rows' worst slot. -/
theorem v7P256Sha3_sep_mac_le_coeff :
    (v7P256Sha3.sha.cardCand : ℚ) * v7P256Sha3.ecdsa.cardCand / (v7P256Sha3.macFieldSize : ℚ)
      ≤ max (v7P256Sha3.ecdsa.zkCoefficient 8) (v7P256Sha3.sha.zkCoefficient 4) := by
  native_decide

/-- So at `v7P256Sha3` the per-query coefficient with the separate-MAC slot is the old one without
it. -/
theorem v7P256Sha3_sep_coeff_eq :
    max (max (v7P256Sha3.ecdsa.zkCoefficient 8) (v7P256Sha3.sha.zkCoefficient 4))
        ((v7P256Sha3.sha.cardCand : ℚ) * v7P256Sha3.ecdsa.cardCand / (v7P256Sha3.macFieldSize : ℚ))
      = max (v7P256Sha3.ecdsa.zkCoefficient 8) (v7P256Sha3.sha.zkCoefficient 4) :=
  max_eq_left v7P256Sha3_sep_mac_le_coeff

/-- `v7P256Sha4`'s separate-MAC slot: `cardCand · cardCand / |Fmac| = 4 / 2^128`. -/
theorem v7P256Sha4_sep_mac_eq :
    (v7P256Sha4.sha.cardCand : ℚ) * v7P256Sha4.ecdsa.cardCand / (v7P256Sha4.macFieldSize : ℚ)
      = 4 / 2 ^ 128 := by
  native_decide

/-- `v7P256Sha4` with the separate-MAC slot (`logv = 8, 5`), at `N = 0`: at most `2^-115`. -/
theorem v7P256Sha4_sep_slack_bound :
    v7P256Sha4.ecdsa.zkBound 8 + v7P256Sha4.sha.zkBound 5
        + (v7P256Sha4.sha.cardCand : ℚ) * v7P256Sha4.ecdsa.cardCand / (v7P256Sha4.macFieldSize : ℚ)
        + 2 * (((v7P256Sha4.ecdsa.tape * len2 v7P256Sha4.ecdsa v7P256Sha4.sha : ℕ) : ℚ)
          / 2 ^ v7P256Sha4.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ 115 := by
  native_decide

/-- `v7P256Sha4`'s worst coefficient with the separate-MAC slot plus the per-query term: at most
`2^-117`. -/
theorem v7P256Sha4_sep_slack_coeff :
    max (max (v7P256Sha4.ecdsa.zkCoefficient 8) (v7P256Sha4.sha.zkCoefficient 5))
        ((v7P256Sha4.sha.cardCand : ℚ) * v7P256Sha4.ecdsa.cardCand / (v7P256Sha4.macFieldSize : ℚ))
      + 2 * ((v7P256Sha4.ecdsa.tape : ℚ) / 2 ^ v7P256Sha4.ecdsa.params.digestBits)
      ≤ (1 : ℚ) / 2 ^ 117 := by
  native_decide

/-- At `v7P256Sha4` the separate-MAC slot is below both rows' worst slot. -/
theorem v7P256Sha4_sep_mac_le_coeff :
    (v7P256Sha4.sha.cardCand : ℚ) * v7P256Sha4.ecdsa.cardCand / (v7P256Sha4.macFieldSize : ℚ)
      ≤ max (v7P256Sha4.ecdsa.zkCoefficient 8) (v7P256Sha4.sha.zkCoefficient 5) := by
  native_decide

/-- So at `v7P256Sha4` the per-query coefficient with the separate-MAC slot is the old one without
it. -/
theorem v7P256Sha4_sep_coeff_eq :
    max (max (v7P256Sha4.ecdsa.zkCoefficient 8) (v7P256Sha4.sha.zkCoefficient 5))
        ((v7P256Sha4.sha.cardCand : ℚ) * v7P256Sha4.ecdsa.cardCand / (v7P256Sha4.macFieldSize : ℚ))
      = max (v7P256Sha4.ecdsa.zkCoefficient 8) (v7P256Sha4.sha.zkCoefficient 5) :=
  max_eq_left v7P256Sha4_sep_mac_le_coeff

end Lfzk.TwoFieldV1Rows
