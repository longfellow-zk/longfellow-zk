import Lfzk.V1StrongV7PairBudget

/-! A concrete balanced raw-answer pair bound for the V1 v7 hash rows. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Lfzk.V1StrongV7RawPair

open Finset LigeroFamily Lfzk.V1StrongV7Numeric
open scoped Classical

/-- For each v7 hash geometry, the V1 extraction-failing pair event has a
`6/2^128` local budget, provided the two raw-answer decoders satisfy the
stated balance conditions.  The response is the complete transmitted payload. -/
theorem v7_v1_raw_pair_lt_six (i : Fin 4)
    {F : Type} {Equations Coin : Type*}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype Equations] [DecidableEq Equations]
    [Fintype Coin] [Nonempty Coin]
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
    (statement : ConstraintSystem F nw nq w Equations)
    (decodeChallenge : Coin → Ligero.V1.Challenge F nw nq 1 Equations)
    (decodeQuery : Coin → QuerySet (row i).n (row i).openings)
    (kchal kquery : ℕ)
    (hchal : ∀ challenge,
      (univ.filter fun c : Coin => decodeChallenge c = challenge).card ≤ kchal)
    (hqueryBalance : ∀ query,
      (univ.filter fun c : Coin => decodeQuery c = query).card ≤ kquery)
    (hkchal : kchal * Fintype.card
      (Ligero.V1.Challenge F nw nq 1 Equations) ≤ Fintype.card Coin)
    (hkquery : kquery * Fintype.card
      (QuerySet (row i).n (row i).openings) ≤ Fintype.card Coin) :
    let R := row i
    let C := R.code (Lfzk.V1StrongV7Mass.row_valid i) D hkrow
    let policy := Ligero.V1.potentialFailedPolicy
      (e := R.e) (g := R.g) C oracle
    let decode := Lfzk.LigeroPayloadDecode.decode D baseNodes responseNodes
      (by fin_cases i <;> native_decide : R.openings ≤ R.k)
      (by fin_cases i <;> native_decide : R.k ≤ 2 * R.k - 1)
    cover R (cutoff R) +
      (∑ payload : Lfzk.LigeroTranscriptInputs.ResponsePayload F
          R.k (2 * R.k - 1) R.openings,
        ((univ.filter fun p : Coin × Coin =>
          Lfzk.ResponsePairMass.highEvent (cutoff := cutoff R)
            (fun challenge response =>
              policyAcceptingCoordinates policy oracle statement challenge
                (decode response))
            (fun challenge response query =>
              policy.accepts statement challenge (decode response) query
                (openSchemeOracle oracle query))
            (decodeChallenge p.1) payload (decodeQuery p.2)).card : ℚ) /
          (Fintype.card Coin : ℚ) ^ 2) <
      (6 : ℚ) / 2 ^ 128 := by
  let R := row i
  have hrb : R.openings ≤ R.k := by fin_cases i <;> native_decide
  have hbd : R.k ≤ 2 * R.k - 1 := by fin_cases i <;> native_decide
  let C := R.code (Lfzk.V1StrongV7Mass.row_valid i) D hkrow
  let policy := Ligero.V1.potentialFailedPolicy (Equations := Equations)
    (e := R.e) (g := R.g) C oracle
  let decode := Lfzk.LigeroPayloadDecode.decode D baseNodes responseNodes
    hrb hbd
  let good := fun challenge payload =>
    policyAcceptingCoordinates policy oracle statement challenge
      (decode payload)
  let accepts := fun challenge payload query =>
    policy.accepts statement challenge (decode payload) query
      (openSchemeOracle oracle query)
  have hcover : ∀ challenge payload query,
      accepts challenge payload query →
        query.coordinates ⊆ good challenge payload := by
    intro challenge payload query haccept
    exact query_subset_policyAcceptingCoordinates_of_accepts policy oracle
      statement challenge (decode payload) query haccept
  have hmass := Lfzk.V1StrongV7PairBudget.v7_v1_payload_high_cover_le i
    hrows hfield D hkrow baseNodes responseNodes oracle statement
  have hpair := Lfzk.V1StrongV7PairBudget.pair_budget_of_mass i
    decodeChallenge decodeQuery good accepts hcover
    kchal kquery hchal hqueryBalance hkchal hkquery
    (by simpa only [good, decode, policy, C, R] using hmass)
  simpa only [good, accepts, decode, policy, C, R] using hpair

end Lfzk.V1StrongV7RawPair
