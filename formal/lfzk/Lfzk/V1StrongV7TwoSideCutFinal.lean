import Lfzk.V1StrongV7TwoSideLocal
import Lfzk.V1StrongV7TwoSideCutContext

/-! The V1 pair bound with the actual adaptive committed cut trace. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Lfzk.V1StrongV7TwoSideCutFinal

open Finset LigeroFamily Lfzk.V1StrongV7Numeric
open Bcs.TotalOracle Merkle.RandomOracle
open scoped Classical

theorem v7_v1_two_side_cut_final_le (i : Fin 4)
    {F : Type} {Equations : Type*} {Enc D Coin X Other Msg₂ Out : Type}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype Equations] [DecidableEq Equations]
    [DecidableEq Enc]
    [Fintype D] [DecidableEq D] [Inhabited D]
    [Fintype Coin] [DecidableEq Coin] [Nonempty Coin]
    [Fintype X] [DecidableEq X]
    [Fintype Other] [DecidableEq Other] [Inhabited Other]
    [Fintype Msg₂] [DecidableEq Msg₂]
    {qw nw nq nl nl₂ N tA Lsch TM : ℕ} {rounds rounds₂ : ℕ → ℕ}
    (hrows : CoreRowsNonempty nw nq)
    (hfield : Fintype.card F = (row i).fieldSize)
    (dom : ReedSolomon.Domain F (row i).openings qw (row i).n)
    (hkrow : (row i).openings + qw = (row i).k)
    (baseNodes : Fin (row i).k ↪
      Position (row i).openings qw (row i).n)
    (responseNodes : Fin (2 * (row i).k - 1) ↪
      Position (row i).openings qw (row i).n)
    (S : Bcs.TotalOracleCommit.Setup Enc D
      (Lfzk.V1StrongV7TwoSideFinal.Point i D Coin X Other F Msg₂
        nl nl₂ rounds rounds₂) Coin Out (D × D) tA N Lsch)
    (hkey : ∀ p response,
      S.key (Lfzk.LigeroPairGeometryTwoSide.parent
        (Msg₂ := Msg₂) (nl₂ := nl₂) (w₂ := rounds₂) p) =
      S.key (Lfzk.LigeroPairGeometryTwoSide.child
        (Msg₂ := Msg₂) (nl₂ := nl₂) (w₂ := rounds₂) p response))
    (mt : Fin TM → D)
    (selected : Out → Lfzk.V1StrongV7TwoSideFinal.Prefix i D Coin X Other F
      nl rounds × Lfzk.V1StrongV7Terminal.Payload i F)
    (oracle : (Lfzk.V1StrongV7TwoSideCutContext.State
      (Enc := Enc) (D := D) (Coin := Coin) (X := X)
      (Other := Other) (F := F) (Msg₂ := Msg₂)
      (nl := nl) (nl₂ := nl₂) (block := (row i).k)
      (dblock := 2 * (row i).k - 1) (r := (row i).openings)
      (rounds := rounds) (rounds₂ := rounds₂)) →
      Lfzk.V1StrongV7TwoSideFinal.Prefix i D Coin X Other F nl rounds →
      Ligero.V1.Oracle F nw nq (row i).n 1)
    (statement : (Lfzk.V1StrongV7TwoSideCutContext.State
      (Enc := Enc) (D := D) (Coin := Coin) (X := X)
      (Other := Other) (F := F) (Msg₂ := Msg₂)
      (nl := nl) (nl₂ := nl₂) (block := (row i).k)
      (dblock := 2 * (row i).k - 1) (r := (row i).openings)
      (rounds := rounds) (rounds₂ := rounds₂)) →
      Lfzk.V1StrongV7TwoSideFinal.Prefix i D Coin X Other F nl rounds →
      ConstraintSystem F nw nq qw Equations)
    (decodeChallenge : (Lfzk.V1StrongV7TwoSideCutContext.State
      (Enc := Enc) (D := D) (Coin := Coin) (X := X)
      (Other := Other) (F := F) (Msg₂ := Msg₂)
      (nl := nl) (nl₂ := nl₂) (block := (row i).k)
      (dblock := 2 * (row i).k - 1) (r := (row i).openings)
      (rounds := rounds) (rounds₂ := rounds₂)) →
      Lfzk.V1StrongV7TwoSideFinal.Prefix i D Coin X Other F nl rounds →
      Coin → Ligero.V1.Challenge F nw nq 1 Equations)
    (decodeQuery : (Lfzk.V1StrongV7TwoSideCutContext.State
      (Enc := Enc) (D := D) (Coin := Coin) (X := X)
      (Other := Other) (F := F) (Msg₂ := Msg₂)
      (nl := nl) (nl₂ := nl₂) (block := (row i).k)
      (dblock := 2 * (row i).k - 1) (r := (row i).openings)
      (rounds := rounds) (rounds₂ := rounds₂)) →
      Lfzk.V1StrongV7TwoSideFinal.Prefix i D Coin X Other F nl rounds →
      Coin → QuerySet (row i).n (row i).openings)
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
      let pr := selected ((S.search mt).run H).1
      Lfzk.V1StrongV7Terminal.accepts i dom hkrow baseNodes responseNodes
        (oracle (Lfzk.V1StrongV7TwoSideCutContext.cutState S mt pr.1 H) pr.1)
        (statement (Lfzk.V1StrongV7TwoSideCutContext.cutState S mt pr.1 H) pr.1)
        (decodeChallenge (Lfzk.V1StrongV7TwoSideCutContext.cutState S mt pr.1 H)
          pr.1 (H (Lfzk.LigeroPairGeometryTwoSide.parent
            (Msg₂ := Msg₂) (nl₂ := nl₂) (w₂ := rounds₂) pr.1)))
        pr.2
        (decodeQuery (Lfzk.V1StrongV7TwoSideCutContext.cutState S mt pr.1 H)
          pr.1 (H (Lfzk.LigeroPairGeometryTwoSide.child
            (Msg₂ := Msg₂) (nl₂ := nl₂) (w₂ := rounds₂) pr.1 pr.2)))
    ((univ.filter failure).card : ℚ) /
      (Fintype.card Coin : ℚ) ^
        Fintype.card (Lfzk.V1StrongV7TwoSideFinal.Point i D Coin X
          Other F Msg₂ nl nl₂ rounds rounds₂) ≤
      (N + 1 : ℕ) * density i := by
  exact Lfzk.V1StrongV7TwoSideLocal.v7_v1_two_side_local_final_le i
    hrows hfield dom hkrow baseNodes responseNodes (S.search mt)
    selected (Lfzk.V1StrongV7TwoSideCutContext.cutState S mt)
    (Lfzk.V1StrongV7TwoSideCutContext.cutState_off S hkey mt)
    oracle statement decodeChallenge decodeQuery kchal kquery
    hchal hqueryBalance hkchal hkquery

end Lfzk.V1StrongV7TwoSideCutFinal
