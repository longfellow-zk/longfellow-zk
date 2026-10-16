import Lfzk.V1StrongV7Mass
import Lfzk.ResponsePairMass

/-! The concrete V1 payload mass and its balanced raw-answer pair budget. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.V1StrongV7PairBudget

open Finset LigeroFamily Lfzk.V1StrongV7Numeric
open scoped Classical

private theorem highCover_eq_highCurve (i : Fin 4) (a : ℕ) :
    Lfzk.ResponsePairMass.highCover (cutoff (row i)) a
      (row i).n (row i).openings = (highCurve i).value a := by
  by_cases h : a ≤ cutoff (row i)
  · simp [Lfzk.ResponsePairMass.highCover, highCurve, h,
      show ¬ cutoff (row i) < a by omega]
  · simp [Lfzk.ResponsePairMass.highCover, highCurve, h,
      show cutoff (row i) < a by omega, cover]

/-- The concrete V1 payload proof supplies the exact mass used in pair counting. -/
theorem v7_v1_payload_high_cover_le (i : Fin 4)
    {F : Type} {Equations : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Fintype Equations] [DecidableEq Equations]
    {w nw nq : ℕ}
    (hrows : CoreRowsNonempty nw nq)
    (hfield : Fintype.card F = (row i).fieldSize)
    (D : ReedSolomon.Domain F (row i).openings w (row i).n)
    (hkrow : (row i).openings + w = (row i).k)
    (baseNodes : Fin (row i).k ↪
      Position (row i).openings w (row i).n)
    (responseNodes : Fin (2 * (row i).k - 1) ↪
      Position (row i).openings w (row i).n)
    (oracle : Ligero.V1.Oracle F nw nq (row i).n 1)
    (statement : ConstraintSystem F nw nq w Equations) :
    let R := row i
    let C := R.code (Lfzk.V1StrongV7Mass.row_valid i) D hkrow
    let policy := Ligero.V1.potentialFailedPolicy
      (e := R.e) (g := R.g) C oracle
    let decode := Lfzk.LigeroPayloadDecode.decode D baseNodes responseNodes
      (by fin_cases i <;> native_decide : R.openings ≤ R.k)
      (by fin_cases i <;> native_decide : R.k ≤ 2 * R.k - 1)
    (∑ challenge : Ligero.V1.Challenge F nw nq 1 Equations,
      ∑ payload : Lfzk.LigeroTranscriptInputs.ResponsePayload F
          R.k (2 * R.k - 1) R.openings,
        Lfzk.ResponsePairMass.highCover (cutoff R)
          (policyAcceptingCoordinates policy oracle statement challenge
            (decode payload)).card R.n R.openings) /
        Fintype.card (Ligero.V1.Challenge F nw nq 1 Equations) ≤
      highMass i := by
  have h := Lfzk.V1StrongV7Mass.v7_v1_payload_high_mass_le i
    hrows hfield D hkrow baseNodes responseNodes oracle statement
  simpa only [highCover_eq_highCurve] using h

/-- The high-agreement raw pair mass keeps the complete response sum inside
the extraction-derived envelope. -/
theorem pair_high_mass_of_mass (i : Fin 4)
    {Coin Challenge Response : Type*}
    [Fintype Coin] [Nonempty Coin]
    [Fintype Challenge] [DecidableEq Challenge] [Nonempty Challenge]
    [Fintype Response]
    (decodeChallenge : Coin → Challenge)
    (decodeQuery : Coin → QuerySet (row i).n (row i).openings)
    (good : Challenge → Response → Finset (Fin (row i).n))
    (accepts : Challenge → Response → QuerySet (row i).n (row i).openings → Prop)
    (hcover : ∀ challenge response query,
      accepts challenge response query →
        query.coordinates ⊆ good challenge response)
    (kchal kquery : ℕ)
    (hchal : ∀ challenge,
      (univ.filter fun c : Coin => decodeChallenge c = challenge).card ≤ kchal)
    (hqueryBalance : ∀ query,
      (univ.filter fun c : Coin => decodeQuery c = query).card ≤ kquery)
    (hkchal : kchal * Fintype.card Challenge ≤ Fintype.card Coin)
    (hkquery : kquery * Fintype.card
      (QuerySet (row i).n (row i).openings) ≤ Fintype.card Coin)
    (hmass : (∑ challenge : Challenge, ∑ response : Response,
      Lfzk.ResponsePairMass.highCover (cutoff (row i))
        (good challenge response).card (row i).n (row i).openings) /
        Fintype.card Challenge ≤ highMass i) :
    (∑ response : Response,
      ((univ.filter fun p : Coin × Coin =>
        Lfzk.ResponsePairMass.highEvent (cutoff := cutoff (row i))
          good accepts (decodeChallenge p.1) response
          (decodeQuery p.2)).card : ℚ) /
        (Fintype.card Coin : ℚ) ^ 2) ≤ highMass i := by
  have hrn : (row i).openings ≤ (row i).n := by
    fin_cases i <;> native_decide
  exact Lfzk.ResponsePairMass.high_cover_pair_ratio_le hrn
    decodeChallenge decodeQuery good accepts hcover
    kchal kquery hchal hqueryBalance hkchal hkquery (highMass i) hmass

/-- A checked `6/2^128` budget for two fresh, balanced hash answers. -/
theorem pair_budget_of_mass (i : Fin 4)
    {Coin Challenge Response : Type*}
    [Fintype Coin] [Nonempty Coin]
    [Fintype Challenge] [DecidableEq Challenge] [Nonempty Challenge]
    [Fintype Response]
    (decodeChallenge : Coin → Challenge)
    (decodeQuery : Coin → QuerySet (row i).n (row i).openings)
    (good : Challenge → Response → Finset (Fin (row i).n))
    (accepts : Challenge → Response → QuerySet (row i).n (row i).openings → Prop)
    (hcover : ∀ challenge response query,
      accepts challenge response query →
        query.coordinates ⊆ good challenge response)
    (kchal kquery : ℕ)
    (hchal : ∀ challenge,
      (univ.filter fun c : Coin => decodeChallenge c = challenge).card ≤ kchal)
    (hqueryBalance : ∀ query,
      (univ.filter fun c : Coin => decodeQuery c = query).card ≤ kquery)
    (hkchal : kchal * Fintype.card Challenge ≤ Fintype.card Coin)
    (hkquery : kquery * Fintype.card
      (QuerySet (row i).n (row i).openings) ≤ Fintype.card Coin)
    (hmass : (∑ challenge : Challenge, ∑ response : Response,
      Lfzk.ResponsePairMass.highCover (cutoff (row i))
        (good challenge response).card (row i).n (row i).openings) /
        Fintype.card Challenge ≤ highMass i) :
    cover (row i) (cutoff (row i)) +
      (∑ response : Response,
        ((univ.filter fun p : Coin × Coin =>
          Lfzk.ResponsePairMass.highEvent (cutoff := cutoff (row i))
            good accepts (decodeChallenge p.1) response
            (decodeQuery p.2)).card : ℚ) /
          (Fintype.card Coin : ℚ) ^ 2) <
      (6 : ℚ) / 2 ^ 128 := by
  have hpair := pair_high_mass_of_mass i
    decodeChallenge decodeQuery good accepts hcover
    kchal kquery hchal hqueryBalance hkchal hkquery hmass
  have hd := Lfzk.V1StrongV7Numeric.density_lt_six i
  unfold density at hd
  linarith

end Lfzk.V1StrongV7PairBudget
