import Lfzk.SoundnessAudit

/-!
# Limits of two proposed improvements to the current soundness accounting

These are bounds on the certified error expressions, not attacks or upper bounds on actual
protocol security. In particular, the singleton obstruction concerns the current query-cover
classifier; it does not rule out a different extraction or graded composition theorem.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.SoundnessOptionsAudit

open LigeroFamily Lfzk.LigeroV1Rows

/-- The current hash rows cut the integrated failure profile at the extraction radius itself.
The local clique optimization is already included; here it gives the outer line count. -/
theorem v7_failure_at_radius :
    ∀ row ∈ [v7Hash1, v7Hash2, v7Hash3, v7Hash4],
      row.failureThreshold + 1 = row.n - row.e ∧
        row.fail = (row.m - 1 : ℕ) / (row.fieldSize - (row.g + 1) : ℚ) := by
  native_decide

/-- The smallest cover the current classifier can have in the unique-decoding regime. -/
def uniqueCoverFloor (n d : ℕ) : ℕ := n - (d - 1) / 2 - 1

theorem uniqueCoverFloor_le_queryCover (row : Row) (hunique : 2 * (row.e + row.g) < row.d) :
    uniqueCoverFloor row.n row.d ≤ row.queryCover := by
  have he : row.e ≤ (row.d - 1) / 2 := by omega
  unfold uniqueCoverFloor Row.queryCover
  omega

theorem hypergeometricRatio_mono_cover {a b n r : ℕ} (hab : a ≤ b) :
    hypergeometricRatio a n r ≤ hypergeometricRatio b n r := by
  unfold hypergeometricRatio
  apply div_le_div_of_nonneg_right
  · exact_mod_cast Nat.choose_le_choose r hab
  · positivity

/-- This applies to every choice of the failure and arithmetic thresholds and residual `g`.
The unique candidate cannot be obtained for free by changing only the field-slot multiplier. -/
theorem unique_cover_lower_bound (row : Row) (hunique : 2 * (row.e + row.g) < row.d) :
    hypergeometricRatio (uniqueCoverFloor row.n row.d) row.n row.openings ≤ row.cover :=
  hypergeometricRatio_mono_cover (uniqueCoverFloor_le_queryCover row hunique)

/-- At every deployed v7 hash geometry, even the smallest possible singleton cover exceeds
the entire 115-bit error budget. All remaining charges are nonnegative. -/
theorem v7_unique_cover_floor_exceeds_115 :
    ∀ row ∈ [v7Hash1, v7Hash2, v7Hash3, v7Hash4],
      (1 : ℚ) / 2 ^ 115 <
        hypergeometricRatio (uniqueCoverFloor row.n row.d) row.n row.openings := by
  native_decide

/-- A parameter-independent obstruction at the deployed hash geometries, connected directly
to the query-cover budget used by `Row.rbr_soundness` and the current ZK composition. -/
theorem v7_unique_cover_exceeds_115 (row geometry : Row)
    (hgeometry : geometry ∈ [v7Hash1, v7Hash2, v7Hash3, v7Hash4])
    (hn : row.n = geometry.n) (hd : row.d = geometry.d)
    (hr : row.openings = geometry.openings)
    (hunique : 2 * (row.e + row.g) < row.d) :
    (1 : ℚ) / 2 ^ 115 < row.cover := by
  have h := v7_unique_cover_floor_exceeds_115 geometry hgeometry
  rw [← hn, ← hd, ← hr] at h
  exact h.trans_le (unique_cover_lower_bound row hunique)

/-! A numerical design target, not a new soundness theorem. If a future adaptive V1 composition
replaces the hash Ligero contribution by `(N + 2) / 2^119`, retaining the current two-candidate
field accounting, signature row and Merkle bound, all three 116-bit T-security inequalities fit.
This file does not establish that replacement. The pair's separate-MAC charge is included. -/

def target116Slack (R : Lfzk.CertifiedV1.Row) (logv : ℕ) : Prop :=
  let S := Lfzk.CertifiedV1.v7Sig
  let fc := 2 * R.params.row.n + 2 * S.params.row.n
  let L := 1 + Lfzk.Rounds.Role.length R.params.nl R.params.rounds +
    Lfzk.Rounds.Role.length S.params.nl S.params.rounds
  let fieldCore := (R.cardCand : ℚ) * Lfzk.NizkZk.zkFieldDensity R logv
  let fieldCoeff := (R.cardCand * (logv + 2) : ℕ) / (R.params.row.fieldSize : ℚ)
  let A := fieldCore + Lfzk.NizkZk.zkCoreAt S 8 S.cardCand + 4 / 2 ^ 128 + 2 / 2 ^ 119
  let K := max (max fieldCoeff (S.zkCoefficient 8)) (4 / 2 ^ 128) + 1 / 2 ^ 119
  A + 2 * (fc * (1 + L) : ℕ) / (2 ^ 256 : ℚ) ≤ (1 : ℚ) / 2 ^ 116 ∧
    K + 2 * (fc + 2 ^ 116 : ℕ) / (2 ^ 256 : ℚ) ≤ (1 : ℚ) / 2 ^ 116 ∧
    2 * (3 * 2 ^ 116 + 2 * fc + 1 + L : ℕ) / (2 ^ 256 : ℚ) ≤ (1 : ℚ) / 2 ^ 116

/-- Exact arithmetic for a proposed adaptive Ligero proof obligation. This does not assert
the obligation is true or supply a new verifier-soundness endpoint. -/
theorem v7_target116_slack :
    ∀ p ∈ [(Lfzk.CertifiedV1.v7Hash1, 3), (Lfzk.CertifiedV1.v7Hash2, 4),
      (Lfzk.CertifiedV1.v7Hash3, 4), (Lfzk.CertifiedV1.v7Hash4, 5)],
      target116Slack p.1 p.2 := by
  unfold target116Slack
  native_decide

end Lfzk.SoundnessOptionsAudit
