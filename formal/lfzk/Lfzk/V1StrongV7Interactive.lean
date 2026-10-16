import Lfzk.V1StrongV7Terminal

/-! The direct two-coordinate V1 count also bounds an interactive prover
whose four-slice response depends on the first challenge. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Lfzk.V1StrongV7Interactive

open Finset LigeroFamily Lfzk.V1StrongV7Numeric
open scoped Classical

/-- The IOP prover sees the first raw challenge before choosing a complete
four-slice response. The second raw answer determines the column query.
The result bounds verifier acceptance with response-assisted extraction
failure, with no FS query multiplier. -/
theorem v7_v1_payload_iop_failure_le (i : Fin 4)
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
      (QuerySet (row i).n (row i).openings) ≤ Fintype.card Coin)
    (respond : Coin → Lfzk.V1StrongV7Terminal.Payload i F) :
    (∑ a : Coin, ∑ b : Coin,
      if Lfzk.V1StrongV7Terminal.accepts i D hkrow baseNodes responseNodes
        oracle statement (decodeChallenge a) (respond a) (decodeQuery b)
      then (1 : ℚ) else 0) /
        (Fintype.card Coin : ℚ) ^ 2 ≤ density i := by
  let lowAt := fun (a : Coin) (payload : Lfzk.V1StrongV7Terminal.Payload i F)
      (b : Coin) =>
    Lfzk.V1StrongV7Terminal.low i D hkrow baseNodes responseNodes
      oracle statement decodeChallenge decodeQuery payload a b
  let highAt := fun (a : Coin) (payload : Lfzk.V1StrongV7Terminal.Payload i F)
      (b : Coin) =>
    Lfzk.V1StrongV7Terminal.high i D hkrow baseNodes responseNodes
      oracle statement decodeChallenge decodeQuery payload a b
  have hlow (a : Coin) (payload : Lfzk.V1StrongV7Terminal.Payload i F) :
      ∑ b : Coin, (if lowAt a payload b then (1 : ℚ) else 0) ≤
        Fintype.card Coin * cover (row i) (cutoff (row i)) := by
    by_cases ha : (Lfzk.V1StrongV7Terminal.good i D hkrow baseNodes
        responseNodes oracle statement (decodeChallenge a) payload).card ≤
        cutoff (row i)
    · have h := Lfzk.V1StrongV7LowQuery.decoded_low_query_le i
        D hkrow oracle statement (decodeChallenge a)
        (Lfzk.V1StrongV7Terminal.decodePayload i D baseNodes responseNodes payload)
        decodeQuery kquery hqueryBalance hkquery ha
      simp only [lowAt, Lfzk.V1StrongV7Terminal.low, ha, true_and]
      exact h
    · have hcover : 0 ≤ cover (row i) (cutoff (row i)) := by
        unfold cover hypergeometricRatio
        positivity
      simpa only [lowAt, Lfzk.V1StrongV7Terminal.low, ha, false_and,
        ite_false, Finset.sum_const_zero]
        using mul_nonneg (by positivity : (0 : ℚ) ≤ Fintype.card Coin) hcover
  have hhigh :
      (∑ payload : Lfzk.V1StrongV7Terminal.Payload i F,
        ∑ a : Coin, ∑ b : Coin,
          if highAt a payload b then (1 : ℚ) else 0) ≤
        (Fintype.card Coin : ℚ) ^ 2 * highMass i := by
    exact Lfzk.V1StrongV7HighCount.v7_v1_high_count_le i
      hrows hfield D hkrow baseNodes responseNodes oracle statement
      decodeChallenge decodeQuery kchal kquery
      hchal hqueryBalance hkchal hkquery
  have hpair := Lfzk.ResponsePairMass.adaptive_response_pair_ratio_le
    lowAt highAt respond (cover (row i) (cutoff (row i)))
    (highMass i) hlow hhigh
  have heq :
      (∑ a : Coin, ∑ b : Coin,
        if Lfzk.V1StrongV7Terminal.accepts i D hkrow baseNodes
          responseNodes oracle statement (decodeChallenge a)
          (respond a) (decodeQuery b) then (1 : ℚ) else 0) =
      (∑ a : Coin, ∑ b : Coin,
        if lowAt a (respond a) b ∨ highAt a (respond a) b
          then (1 : ℚ) else 0) := by
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    rw [← Lfzk.V1StrongV7Terminal.low_or_high_iff_accepts i
      D hkrow baseNodes responseNodes oracle statement
      decodeChallenge decodeQuery (respond a) a b]
    by_cases h : lowAt a (respond a) b ∨ highAt a (respond a) b
    · simp [lowAt, highAt] at h ⊢
    · simp [lowAt, highAt] at h ⊢
  rw [heq]
  simpa only [density] using hpair

private theorem pair_duplicate_sum {A B : Type*} [Fintype A] [Fintype B]
    (f : A → B → ℚ) :
    (∑ p : A × B, ∑ q : A × B, f p.1 q.2) =
      (Fintype.card A : ℚ) * Fintype.card B *
        (∑ a : A, ∑ b : B, f a b) := by
  simp [Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul,
    mul_assoc, mul_comm]

private theorem fst_fiber {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq A] (a : A) :
    (Finset.univ.filter fun p : A × B => p.1 = a).card =
      Fintype.card B := by
  have hs : (Finset.univ.filter fun p : A × B => p.1 = a) =
      (Finset.univ.filter fun x : A => x = a) ×ˢ
        (Finset.univ : Finset B) := by
    ext p
    simp
  rw [hs, Finset.card_product]
  simp only [Finset.filter_eq', Finset.mem_univ, ite_true,
    Finset.card_singleton, one_mul, Finset.card_univ]

private theorem snd_fiber {A B : Type*}
    [Fintype A] [Fintype B] [DecidableEq B] (b : B) :
    (Finset.univ.filter fun p : A × B => p.2 = b).card =
      Fintype.card A := by
  have hs : (Finset.univ.filter fun p : A × B => p.2 = b) =
      (Finset.univ : Finset A) ×ˢ
        (Finset.univ.filter fun x : B => x = b) := by
    ext p
    simp
  rw [hs, Finset.card_product]
  simp only [Finset.filter_eq', Finset.mem_univ, ite_true,
    Finset.card_singleton, mul_one, Finset.card_univ]

/-- Uniform interactive sampling of the V1 combination challenge and column
query has the same density as the balanced raw-coin theorem. The prover's
four-slice payload may depend arbitrarily on the combination challenge. -/
theorem v7_v1_payload_iop_uniform_failure_le (i : Fin 4)
    {F : Type} {Equations : Type*}
    [Field F] [Fintype F] [DecidableEq F]
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
    (statement : ConstraintSystem F nw nq w Equations)
    (respond : Ligero.V1.Challenge F nw nq 1 Equations →
      Lfzk.V1StrongV7Terminal.Payload i F) :
    (∑ challenge : Ligero.V1.Challenge F nw nq 1 Equations,
      ∑ query : QuerySet (row i).n (row i).openings,
        if Lfzk.V1StrongV7Terminal.accepts i D hkrow baseNodes
          responseNodes oracle statement challenge
          (respond challenge) query then (1 : ℚ) else 0) /
      (Fintype.card (Ligero.V1.Challenge F nw nq 1 Equations) : ℚ) /
      (Fintype.card (QuerySet (row i).n (row i).openings) : ℚ) ≤
        density i := by
  letI : Nonempty (QuerySet (row i).n (row i).openings) :=
    QuerySet.nonempty (by fin_cases i <;> native_decide)
  let A := Ligero.V1.Challenge F nw nq 1 Equations
  let B := QuerySet (row i).n (row i).openings
  let f : A → B → ℚ := fun a b =>
    if Lfzk.V1StrongV7Terminal.accepts i D hkrow baseNodes
      responseNodes oracle statement a (respond a) b then 1 else 0
  have hchal (a : A) :
      (univ.filter fun p : A × B => p.1 = a).card ≤ Fintype.card B := by
    rw [fst_fiber]
  have hquery (b : B) :
      (univ.filter fun p : A × B => p.2 = b).card ≤ Fintype.card A := by
    rw [snd_fiber]
  have hkchal : Fintype.card B * Fintype.card A ≤
      Fintype.card (A × B) := by simp [Fintype.card_prod, Nat.mul_comm]
  have hkquery : Fintype.card A * Fintype.card B ≤
      Fintype.card (A × B) := by simp [Fintype.card_prod]
  have hraw := v7_v1_payload_iop_failure_le i
    hrows hfield D hkrow baseNodes responseNodes oracle statement
    (Coin := A × B) Prod.fst Prod.snd
    (Fintype.card B) (Fintype.card A)
    hchal hquery hkchal hkquery (fun p => respond p.1)
  have hA : (0 : ℚ) < Fintype.card A := by positivity
  have hB : (0 : ℚ) < Fintype.card B := by positivity
  have hsum := pair_duplicate_sum f
  dsimp only [f] at hsum
  calc
    _ = ((∑ p : A × B, ∑ q : A × B,
        if Lfzk.V1StrongV7Terminal.accepts i D hkrow baseNodes
          responseNodes oracle statement p.1 (respond p.1) q.2
        then (1 : ℚ) else 0) /
          (Fintype.card (A × B) : ℚ) ^ 2) := by
        rw [hsum]
        simp only [Fintype.card_prod, Nat.cast_mul]
        field_simp
        ring
    _ ≤ density i := hraw

/-- For a committed oracle with no satisfying decoded lift, the same direct
four-slice count bounds ordinary V1 IOP acceptance. -/
theorem v7_v1_payload_iop_uniform_acceptance_of_noDecoded_le (i : Fin 4)
    {F : Type} {Equations : Type*}
    [Field F] [Fintype F] [DecidableEq F]
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
    (statement : ConstraintSystem F nw nq w Equations)
    (respond : Ligero.V1.Challenge F nw nq 1 Equations →
      Lfzk.V1StrongV7Terminal.Payload i F)
    (hnd : NoDecodedSolution
      ((row i).code (Lfzk.V1StrongV7Mass.row_valid i) D hkrow)
      oracle ((row i).e + (row i).g) statement) :
    (∑ challenge : Ligero.V1.Challenge F nw nq 1 Equations,
      ∑ query : QuerySet (row i).n (row i).openings,
        if (SchemeVerifier.policy
          (Equations := Equations) (nw := nw) (nq := nq)
          (repetitions := 1)
          ((row i).code (Lfzk.V1StrongV7Mass.row_valid i) D hkrow)
          Ligero.V1.scheme).accepts statement challenge
            (Lfzk.V1StrongV7Terminal.decodePayload i D baseNodes
              responseNodes (respond challenge)) query
            (openSchemeOracle oracle query)
        then (1 : ℚ) else 0) /
      (Fintype.card (Ligero.V1.Challenge F nw nq 1 Equations) : ℚ) /
      (Fintype.card (QuerySet (row i).n (row i).openings) : ℚ) ≤
        density i := by
  have hcore := v7_v1_payload_iop_uniform_failure_le i hrows hfield D
    hkrow baseNodes responseNodes oracle statement respond
  have hsum :
      (∑ challenge : Ligero.V1.Challenge F nw nq 1 Equations,
        ∑ query : QuerySet (row i).n (row i).openings,
          if (SchemeVerifier.policy
            (Equations := Equations) (nw := nw) (nq := nq)
            (repetitions := 1)
            ((row i).code (Lfzk.V1StrongV7Mass.row_valid i) D hkrow)
            Ligero.V1.scheme).accepts statement challenge
              (Lfzk.V1StrongV7Terminal.decodePayload i D baseNodes
                responseNodes (respond challenge)) query
              (openSchemeOracle oracle query)
          then (1 : ℚ) else 0) =
      (∑ challenge : Ligero.V1.Challenge F nw nq 1 Equations,
        ∑ query : QuerySet (row i).n (row i).openings,
          if Lfzk.V1StrongV7Terminal.accepts i D hkrow baseNodes
            responseNodes oracle statement challenge (respond challenge)
            query then (1 : ℚ) else 0) := by
    apply Finset.sum_congr rfl
    intro challenge _
    apply Finset.sum_congr rfl
    intro query _
    rw [Lfzk.V1StrongV7Terminal.accepts_iff_of_noDecoded i D hkrow
      baseNodes responseNodes oracle statement challenge
      (respond challenge) query hnd]
  rw [hsum]
  exact hcore

end Lfzk.V1StrongV7Interactive
