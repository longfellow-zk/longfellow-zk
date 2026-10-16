import Lfzk.V1StrongV7TwoSideFinal
import Lfzk.V1StrongV7LocalContextFinal

/-! V1 terminal extraction with a cut context local to the selected parent. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Lfzk.V1StrongV7TwoSideLocal

open Finset LigeroFamily Lfzk.V1StrongV7Numeric
open Bcs.TotalOracle Merkle.RandomOracle
open scoped Classical

/-- The compiled cut trace may depend on other transcript-oracle answers.
Only the selected V1 challenge and response-query answers must be fresh. -/
theorem v7_v1_two_side_local_final_le (i : Fin 4)
    {F : Type} {Equations : Type*} {D Coin X Other Msg₂ Out State : Type}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype Equations] [DecidableEq Equations]
    [Fintype D] [DecidableEq D]
    [Fintype Coin] [DecidableEq Coin] [Nonempty Coin]
    [Fintype X] [DecidableEq X]
    [Fintype Other] [DecidableEq Other] [Inhabited Other]
    [Fintype Msg₂] [DecidableEq Msg₂]
    {qw nw nq nl nl₂ N : ℕ} {rounds rounds₂ : ℕ → ℕ}
    (hrows : CoreRowsNonempty nw nq)
    (hfield : Fintype.card F = (row i).fieldSize)
    (dom : ReedSolomon.Domain F (row i).openings qw (row i).n)
    (hkrow : (row i).openings + qw = (row i).k)
    (baseNodes : Fin (row i).k ↪
      Position (row i).openings qw (row i).n)
    (responseNodes : Fin (2 * (row i).k - 1) ↪
      Position (row i).openings qw (row i).n)
    (tree : Tree (Lfzk.V1StrongV7TwoSideFinal.Point i D Coin X Other F Msg₂
      nl nl₂ rounds rounds₂) Coin Out N)
    (selected : Out → Lfzk.V1StrongV7TwoSideFinal.Prefix i D Coin X Other F
      nl rounds × Lfzk.V1StrongV7Terminal.Payload i F)
    (state : Lfzk.V1StrongV7TwoSideFinal.Prefix i D Coin X Other F
      nl rounds →
      (Lfzk.V1StrongV7TwoSideFinal.Point i D Coin X Other F Msg₂
        nl nl₂ rounds rounds₂ → Coin) → State)
    (hstateOff : ∀ p response (H H' :
        Lfzk.V1StrongV7TwoSideFinal.Point i D Coin X Other F Msg₂
          nl nl₂ rounds rounds₂ → Coin),
      (∀ z, z ≠ Lfzk.LigeroPairGeometryTwoSide.parent
          (Msg₂ := Msg₂) (nl₂ := nl₂) (w₂ := rounds₂) p →
        z ≠ Lfzk.LigeroPairGeometryTwoSide.child
          (Msg₂ := Msg₂) (nl₂ := nl₂) (w₂ := rounds₂) p response →
        H z = H' z) → state p H = state p H')
    (oracle : State → Lfzk.V1StrongV7TwoSideFinal.Prefix i D Coin X Other F
      nl rounds → Ligero.V1.Oracle F nw nq (row i).n 1)
    (statement : State → Lfzk.V1StrongV7TwoSideFinal.Prefix i D Coin X Other F
      nl rounds → ConstraintSystem F nw nq qw Equations)
    (decodeChallenge : State → Lfzk.V1StrongV7TwoSideFinal.Prefix i D Coin X Other F
      nl rounds → Coin → Ligero.V1.Challenge F nw nq 1 Equations)
    (decodeQuery : State → Lfzk.V1StrongV7TwoSideFinal.Prefix i D Coin X Other F
      nl rounds → Coin → QuerySet (row i).n (row i).openings)
    (kchal kquery : ℕ)
    (hchal : ∀ s p challenge,
      (univ.filter fun c : Coin => decodeChallenge s p c = challenge).card ≤ kchal)
    (hqueryBalance : ∀ s p query,
      (univ.filter fun c : Coin => decodeQuery s p c = query).card ≤ kquery)
    (hkchal : kchal * Fintype.card
      (Ligero.V1.Challenge F nw nq 1 Equations) ≤ Fintype.card Coin)
    (hkquery : kquery * Fintype.card
      (QuerySet (row i).n (row i).openings) ≤ Fintype.card Coin) :
    let failure := fun H : Lfzk.V1StrongV7TwoSideFinal.Point i D Coin X
        Other F Msg₂ nl nl₂ rounds rounds₂ → Coin =>
      let pr := selected (tree.run H).1
      Lfzk.V1StrongV7Terminal.accepts i dom hkrow baseNodes responseNodes
        (oracle (state pr.1 H) pr.1)
        (statement (state pr.1 H) pr.1)
        (decodeChallenge (state pr.1 H) pr.1
          (H (Lfzk.LigeroPairGeometryTwoSide.parent
            (Msg₂ := Msg₂) (nl₂ := nl₂) (w₂ := rounds₂) pr.1)))
        pr.2
        (decodeQuery (state pr.1 H) pr.1
          (H (Lfzk.LigeroPairGeometryTwoSide.child
            (Msg₂ := Msg₂) (nl₂ := nl₂) (w₂ := rounds₂) pr.1 pr.2)))
    ((univ.filter failure).card : ℚ) /
      (Fintype.card Coin : ℚ) ^
        Fintype.card (Lfzk.V1StrongV7TwoSideFinal.Point i D Coin X
          Other F Msg₂ nl nl₂ rounds rounds₂) ≤
      (N + 1 : ℕ) * density i := by
  exact Lfzk.V1StrongV7LocalContextFinal.v7_v1_local_context_final_density_le i
    hrows hfield dom hkrow baseNodes responseNodes tree selected
    Lfzk.LigeroPairGeometryTwoSide.parent
    Lfzk.LigeroPairGeometryTwoSide.child
    Lfzk.LigeroPairGeometryTwoSide.parent_injective
    Lfzk.LigeroPairGeometryTwoSide.child_injective
    Lfzk.LigeroPairGeometryTwoSide.parent_ne_child
    state hstateOff oracle statement decodeChallenge decodeQuery
    kchal kquery hchal hqueryBalance hkchal hkquery

end Lfzk.V1StrongV7TwoSideLocal
