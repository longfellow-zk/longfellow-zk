import Lfzk.V1StrongV7Terminal
import Lfzk.LigeroPairGeometry

/-! The V1 terminal policy bound at its actual prefix-only FS hash inputs. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Lfzk.V1StrongV7TranscriptTerminal

open Finset LigeroFamily Lfzk.V1StrongV7Numeric
open Bcs.TotalOracle Merkle.RandomOracle
open scoped Classical

abbrev Prefix (i : Fin 4) (Ctx Other F : Type)
    (nl : ℕ) (rounds : ℕ → ℕ) :=
  Lfzk.LigeroPairGeometry.ParentPrefix
    (Ctx := Ctx) (Other := Other) (F := F)
    (nl := nl) (block := (row i).k)
    (dblock := 2 * (row i).k - 1)
    (r := (row i).openings) (w := rounds)

abbrev Point (i : Fin 4) (Ctx Other F : Type)
    (nl : ℕ) (rounds : ℕ → ℕ) :=
  Lfzk.NizkDeployedHash.MPoint Ctx
    (Lfzk.LigeroTranscriptInputs.Message
      (Other := Other) (F := F)
      (block := (row i).k)
      (dblock := 2 * (row i).k - 1)
      (r := (row i).openings)) nl rounds

/-- The concrete parent/child hash-point geometry satisfies the one-query
adaptive terminal bound.  The actual verifier-to-policy implication remains
an obligation for the final FS extraction theorem. -/
theorem v7_v1_transcript_terminal_le (i : Fin 4)
    {F : Type} {Equations : Type*} {Ctx Other Coin Out : Type}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype Equations] [DecidableEq Equations]
    [Fintype Ctx] [DecidableEq Ctx]
    [Fintype Other] [DecidableEq Other] [Inhabited Other]
    [Fintype Coin] [Nonempty Coin]
    {w nw nq nl N : ℕ} {rounds : ℕ → ℕ}
    (hrows : CoreRowsNonempty nw nq)
    (hfield : Fintype.card F = (row i).fieldSize)
    (D : ReedSolomon.Domain F (row i).openings w (row i).n)
    (hkrow : (row i).openings + w = (row i).k)
    (baseNodes : Fin (row i).k ↪
      Position (row i).openings w (row i).n)
    (responseNodes : Fin (2 * (row i).k - 1) ↪
      Position (row i).openings w (row i).n)
    (tree : Tree (Point i Ctx Other F nl rounds) Coin Out N)
    (oracle : Prefix i Ctx Other F nl rounds →
      Ligero.V1.Oracle F nw nq (row i).n 1)
    (statement : Prefix i Ctx Other F nl rounds →
      ConstraintSystem F nw nq w Equations)
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
    let parent := Lfzk.LigeroPairGeometry.parent
      (Ctx := Ctx) (Other := Other) (F := F) (nl := nl)
      (block := (row i).k) (dblock := 2 * (row i).k - 1)
      (r := (row i).openings) (w := rounds)
    let child := Lfzk.LigeroPairGeometry.child
      (Ctx := Ctx) (Other := Other) (F := F) (nl := nl)
      (block := (row i).k) (dblock := 2 * (row i).k - 1)
      (r := (row i).openings) (w := rounds)
    (∑ H : Point i Ctx Other F nl rounds → Coin,
      ∑ p : Prefix i Ctx Other F nl rounds,
      ∑ payload : Lfzk.V1StrongV7Terminal.Payload i F,
      ((if child p payload ∈ queried tree H ∧
          Lfzk.V1StrongV7Terminal.low i D hkrow baseNodes responseNodes
            (oracle p) (statement p) decodeChallenge decodeQuery payload
            (H (parent p)) (H (child p payload)) then (1 : ℚ) else 0) +
      (if firstOfTwoOffResult tree (parent p) (child p payload)
          (Lfzk.LigeroPairGeometry.parent_ne_child p p payload)
          (fun z => H z.1) ≠ .neither ∧
          Lfzk.V1StrongV7Terminal.high i D hkrow baseNodes responseNodes
            (oracle p) (statement p) decodeChallenge decodeQuery payload
            (H (parent p)) (H (child p payload)) then (1 : ℚ) else 0))) /
        (Fintype.card Coin : ℚ) ^
          Fintype.card (Point i Ctx Other F nl rounds) ≤
      (N : ℚ) * density i := by
  exact Lfzk.V1StrongV7Terminal.v7_v1_terminal_density_le i
    hrows hfield D hkrow baseNodes responseNodes tree
    (Lfzk.LigeroPairGeometry.parent (Ctx := Ctx) (Other := Other)
      (F := F) (nl := nl) (block := (row i).k)
      (dblock := 2 * (row i).k - 1) (r := (row i).openings)
      (w := rounds))
    (Lfzk.LigeroPairGeometry.child (Ctx := Ctx) (Other := Other)
      (F := F) (nl := nl) (block := (row i).k)
      (dblock := 2 * (row i).k - 1) (r := (row i).openings)
      (w := rounds))
    Lfzk.LigeroPairGeometry.parent_injective
    Lfzk.LigeroPairGeometry.child_injective
    Lfzk.LigeroPairGeometry.parent_ne_child
    oracle statement decodeChallenge decodeQuery kchal kquery
    hchal hqueryBalance hkchal hkquery

end Lfzk.V1StrongV7TranscriptTerminal
