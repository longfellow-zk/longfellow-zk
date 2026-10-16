import Lfzk.V1StrongV7Terminal
import Bcs.FinalQueryContext

/-! Terminal extraction-failure bound for Ligero V1 at each v7 geometry. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Lfzk.V1StrongV7ContextFinal

open Finset LigeroFamily Lfzk.V1StrongV7Numeric
open Bcs.TotalOracle Merkle.RandomOracle
open scoped Classical

/-- The terminal policy failure is charged even when the prover made zero
queries: the verifier's final query is the extra `+1`. -/
theorem v7_v1_context_final_density_le (i : Fin 4)
    {F : Type} {Equations : Type*} {Coin Q Prefix Out State : Type}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype Equations] [DecidableEq Equations]
    [Fintype Coin] [Nonempty Coin]
    [Fintype Q] [DecidableEq Q] [Fintype Prefix]
    {w nw nq N : ℕ}
    (hrows : CoreRowsNonempty nw nq)
    (hfield : Fintype.card F = (row i).fieldSize)
    (D : ReedSolomon.Domain F (row i).openings w (row i).n)
    (hkrow : (row i).openings + w = (row i).k)
    (baseNodes : Fin (row i).k ↪
      Position (row i).openings w (row i).n)
    (responseNodes : Fin (2 * (row i).k - 1) ↪
      Position (row i).openings w (row i).n)
    (tree : Tree Q Coin Out N)
    (selected : Out → Prefix × Lfzk.V1StrongV7Terminal.Payload i F)
    (parent : Prefix → Q)
    (child : Prefix → Lfzk.V1StrongV7Terminal.Payload i F → Q)
    (hparent : Function.Injective parent)
    (hchild : Function.Injective
      (fun pr : Prefix × Lfzk.V1StrongV7Terminal.Payload i F => child pr.1 pr.2))
    (hdisjoint : ∀ p p' payload, parent p ≠ child p' payload)
    (state : (Q → Coin) → State)
    (hstateOff : ∀ p payload (H H' : Q → Coin),
      (∀ z, z ≠ parent p → z ≠ child p payload → H z = H' z) →
      state H = state H')
    (oracle : State → Prefix → Ligero.V1.Oracle F nw nq (row i).n 1)
    (statement : State → Prefix → ConstraintSystem F nw nq w Equations)
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
    let failure := fun H : Q → Coin =>
      let pr := selected (tree.run H).1
      Lfzk.V1StrongV7Terminal.accepts i D hkrow baseNodes responseNodes
        (oracle (state H) pr.1) (statement (state H) pr.1) (decodeChallenge (H (parent pr.1)))
        pr.2 (decodeQuery (H (child pr.1 pr.2)))
    ((univ.filter failure).card : ℚ) /
        (Fintype.card Coin : ℚ) ^ Fintype.card Q ≤
      (N + 1 : ℕ) * density i := by
  let lowAt := fun s p payload a b =>
    Lfzk.V1StrongV7Terminal.low i D hkrow baseNodes responseNodes
      (oracle s p) (statement s p) decodeChallenge decodeQuery payload a b
  let highAt := fun s p payload a b =>
    Lfzk.V1StrongV7Terminal.high i D hkrow baseNodes responseNodes
      (oracle s p) (statement s p) decodeChallenge decodeQuery payload a b
  have hlow (s : State) (p : Prefix) (payload : Lfzk.V1StrongV7Terminal.Payload i F)
      (a : Coin) :
      ∑ b : Coin, (if lowAt s p payload a b then (1 : ℚ) else 0) ≤
        Fintype.card Coin * cover (row i) (cutoff (row i)) := by
    by_cases ha : (Lfzk.V1StrongV7Terminal.good i D hkrow baseNodes responseNodes
        (oracle s p) (statement s p) (decodeChallenge a) payload).card ≤
        cutoff (row i)
    · have h := Lfzk.V1StrongV7LowQuery.decoded_low_query_le i
        D hkrow (oracle s p) (statement s p) (decodeChallenge a)
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
  have hhigh (s : State) (p : Prefix) :
      ∑ payload : Lfzk.V1StrongV7Terminal.Payload i F,
        ∑ a : Coin, ∑ b : Coin,
        (if highAt s p payload a b then (1 : ℚ) else 0) ≤
        (Fintype.card Coin : ℚ) ^ 2 * highMass i := by
    exact Lfzk.V1StrongV7HighCount.v7_v1_high_count_le i
      hrows hfield D hkrow baseNodes responseNodes (oracle s p)
      (statement s p) decodeChallenge decodeQuery kchal kquery
      hchal hqueryBalance hkchal hkquery
  have hcover : 0 ≤ cover (row i) (cutoff (row i)) := by
    unfold cover hypergeometricRatio
    positivity
  have h := tree_two_scale_context_final_ratio_le tree selected parent child
    hparent hchild hdisjoint state hstateOff lowAt highAt
    (cover (row i) (cutoff (row i))) (highMass i)
    hcover (highMass_nonneg i) hlow hhigh
  have heq :
      (univ.filter (fun H : Q → Coin =>
        let pr := selected (tree.run H).1
        Lfzk.V1StrongV7Terminal.accepts i D hkrow baseNodes responseNodes
          (oracle (state H) pr.1) (statement (state H) pr.1) (decodeChallenge (H (parent pr.1)))
          pr.2 (decodeQuery (H (child pr.1 pr.2))))).card =
      (univ.filter (fun H : Q → Coin =>
        let pr := selected (tree.run H).1
        lowAt (state H) pr.1 pr.2 (H (parent pr.1)) (H (child pr.1 pr.2)) ∨
        highAt (state H) pr.1 pr.2 (H (parent pr.1)) (H (child pr.1 pr.2)))).card := by
    congr 1
    ext H
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact (Lfzk.V1StrongV7Terminal.low_or_high_iff_accepts i
      D hkrow baseNodes responseNodes
      (oracle (state H) (selected (tree.run H).1).1)
      (statement (state H) (selected (tree.run H).1).1)
      decodeChallenge decodeQuery
      (selected (tree.run H).1).2 (H (parent (selected (tree.run H).1).1))
      (H (child (selected (tree.run H).1).1 (selected (tree.run H).1).2))).symm
  dsimp only at ⊢ h
  rw [heq]
  simpa only [lowAt, highAt, density] using h

end Lfzk.V1StrongV7ContextFinal
