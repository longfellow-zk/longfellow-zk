import Lfzk.V1StrongV7ContextFinal
import Lfzk.LigeroPairGeometryTwoSide

/-! The V1 terminal extraction charge on the full deployed two-side oracle. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Lfzk.V1StrongV7TwoSideFinal

open Finset LigeroFamily Lfzk.V1StrongV7Numeric
open Bcs.TotalOracle Merkle.RandomOracle
open scoped Classical

abbrev Point (i : Fin 4) (D Coin X Other F Msg₂ : Type)
    (nl nl₂ : ℕ) (w w₂ : ℕ → ℕ) :=
  Lfzk.LigeroPairGeometryTwoSide.Point
    (D := D) (C := Coin) (X := X) (Other := Other) (F := F)
    (Msg₂ := Msg₂) (nl := nl) (nl₂ := nl₂)
    (block := (row i).k) (dblock := 2 * (row i).k - 1)
    (r := (row i).openings) (w := w) (w₂ := w₂)

abbrev Prefix (i : Fin 4) (D Coin X Other F : Type)
    (nl : ℕ) (w : ℕ → ℕ) :=
  Lfzk.LigeroPairGeometryTwoSide.Prefix
    (D := D) (C := Coin) (X := X) (Other := Other) (F := F)
    (nl := nl) (block := (row i).k)
    (dblock := 2 * (row i).k - 1) (r := (row i).openings) (w := w)

abbrev Outside (i : Fin 4) (D Coin X Other F Msg₂ : Type)
    (nl nl₂ : ℕ) (w w₂ : ℕ → ℕ) :=
  Lfzk.LigeroPairGeometryTwoSide.OutsideTerminal
    (D := D) (C := Coin) (X := X) (Other := Other) (F := F)
    (Msg₂ := Msg₂) (nl := nl) (nl₂ := nl₂)
    (block := (row i).k) (dblock := 2 * (row i).k - 1)
    (r := (row i).openings) (w := w) (w₂ := w₂)

/-- The prover may query any key, first-side, or second-side hash point in
any order.  All answers outside the first side's final challenge/query roles
may determine its committed oracle and built statement. -/
theorem v7_v1_two_side_final_le (i : Fin 4)
    {F : Type} {Equations : Type*} {D Coin X Other Msg₂ Out : Type}
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
    (tree : Tree (Point i D Coin X Other F Msg₂ nl nl₂ rounds rounds₂)
      Coin Out N)
    (selected : Out → Prefix i D Coin X Other F nl rounds ×
      Lfzk.V1StrongV7Terminal.Payload i F)
    (oracle : (Outside i D Coin X Other F Msg₂ nl nl₂ rounds rounds₂ → Coin) →
      Prefix i D Coin X Other F nl rounds →
      Ligero.V1.Oracle F nw nq (row i).n 1)
    (statement : (Outside i D Coin X Other F Msg₂ nl nl₂ rounds rounds₂ → Coin) →
      Prefix i D Coin X Other F nl rounds →
      ConstraintSystem F nw nq qw Equations)
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
    let failure := fun H : Point i D Coin X Other F Msg₂ nl nl₂
        rounds rounds₂ → Coin =>
      let pr := selected (tree.run H).1
      Lfzk.V1StrongV7Terminal.accepts i dom hkrow baseNodes responseNodes
        (oracle (Lfzk.LigeroPairGeometryTwoSide.outsideTerminal H) pr.1)
        (statement (Lfzk.LigeroPairGeometryTwoSide.outsideTerminal H) pr.1)
        (decodeChallenge (H (Lfzk.LigeroPairGeometryTwoSide.parent
          (Msg₂ := Msg₂) (nl₂ := nl₂) (w₂ := rounds₂) pr.1)))
        pr.2
        (decodeQuery (H (Lfzk.LigeroPairGeometryTwoSide.child
          (Msg₂ := Msg₂) (nl₂ := nl₂) (w₂ := rounds₂) pr.1 pr.2)))
    ((univ.filter failure).card : ℚ) /
      (Fintype.card Coin : ℚ) ^
        Fintype.card (Point i D Coin X Other F Msg₂ nl nl₂ rounds rounds₂) ≤
      (N + 1 : ℕ) * density i := by
  exact Lfzk.V1StrongV7ContextFinal.v7_v1_context_final_density_le i
    hrows hfield dom hkrow baseNodes responseNodes tree selected
    Lfzk.LigeroPairGeometryTwoSide.parent
    Lfzk.LigeroPairGeometryTwoSide.child
    Lfzk.LigeroPairGeometryTwoSide.parent_injective
    Lfzk.LigeroPairGeometryTwoSide.child_injective
    Lfzk.LigeroPairGeometryTwoSide.parent_ne_child
    Lfzk.LigeroPairGeometryTwoSide.outsideTerminal
    (fun p response H H' h =>
      Lfzk.LigeroPairGeometryTwoSide.outsideTerminal_off p response H H' h)
    oracle statement decodeChallenge decodeQuery kchal kquery
    hchal hqueryBalance hkchal hkquery

end Lfzk.V1StrongV7TwoSideFinal
