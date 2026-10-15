import Lfzk.CertifiedV7
import Lfzk.LigeroV1RowsHahn
import Lfzk.NizkZk

/-! The improved signature analysis at the unchanged v7 circuit profile. -/

namespace Lfzk.CertifiedV1

set_option maxHeartbeats 4000000

def v7SigHahn : Row :=
  { v7Sig with
    params := { v7Sig.params with row := Lfzk.LigeroV1Rows.v7SigHahn }
    lam := 126 }

theorem v7SigHahn_valid : v7SigHahn.Valid := by native_decide
theorem v7SigHahn_openings_pos : 0 < v7SigHahn.params.row.openings := by decide

end Lfzk.CertifiedV1

namespace Lfzk.CompiledZk

open Lfzk.CertifiedV1 Lfzk.NizkZk

set_option maxHeartbeats 4000000

/-- The exact core and worst-slot errors fit 127 bits; no fixed Merkle budget is included. -/
theorem v7SigHahn_core_le : zkCoreAt v7SigHahn 8 v7SigHahn.cardCand ≤ (1 : ℚ) / 2 ^ 127 := by
  native_decide

theorem v7SigHahn_coefficient_le : v7SigHahn.zkCoefficient 8 ≤ (1 : ℚ) / 2 ^ 127 := by
  native_decide

/-- The same core calculation does not certify 128 bits. This is not an attack lower bound. -/
theorem v7SigHahn_core_sharp : ¬ zkCoreAt v7SigHahn 8 v7SigHahn.cardCand ≤ (1 : ℚ) / 2 ^ 128 := by
  native_decide

/-- Constant, transcript-query, and Merkle-query slack at the nontrivial cutoff G = 2^127. -/
theorem v7SigHahn_tsec_slack :
    let R := v7SigHahn
    let fc := 2 * R.params.row.n
    let L := Rounds.Role.length R.params.nl R.params.rounds
    zkCoreAt R 8 R.cardCand + (fc * (1 + L) : ℕ) / (2 ^ 256 : ℚ) ≤ (1 : ℚ) / 2 ^ 127 ∧
      R.zkCoefficient 8 + (fc + 2 ^ 127 : ℕ) / (2 ^ 256 : ℚ) ≤ (1 : ℚ) / 2 ^ 127 ∧
      (3 * 2 ^ 127 + 2 * fc + 1 + L : ℕ) / (2 ^ 256 : ℚ) ≤ (1 : ℚ) / 2 ^ 127 := by
  native_decide

end Lfzk.CompiledZk
