import Lfzk.V1StrongV7ContextFinal
import Lfzk.V1StrongV7TranscriptTerminal

/-! Terminal V1 extraction-failure bound for deployed prefix hash geometry. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Lfzk.V1StrongV7TranscriptContextFinal

open Finset LigeroFamily Lfzk.V1StrongV7Numeric
open Bcs.TotalOracle Merkle.RandomOracle
open scoped Classical

/-- The challenge and query hash points use the exact prefix-only V1
message geometry.  A final verifier query gives the `N+1` bound. -/
theorem v7_v1_transcript_context_final_le (i : Fin 4)
    {F : Type} {Equations : Type*} {Ctx Other Coin Out State : Type}
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
    (tree : Tree
      (Lfzk.V1StrongV7TranscriptTerminal.Point i Ctx Other F nl rounds)
      Coin Out N)
    (selected : Out →
      Lfzk.V1StrongV7TranscriptTerminal.Prefix i Ctx Other F nl rounds ×
      Lfzk.V1StrongV7Terminal.Payload i F)
    (state : (Lfzk.V1StrongV7TranscriptTerminal.Point
      i Ctx Other F nl rounds → Coin) → State)
    (hstateOff : ∀ p payload (H H' :
      Lfzk.V1StrongV7TranscriptTerminal.Point
        i Ctx Other F nl rounds → Coin),
      (∀ z, z ≠ Lfzk.LigeroPairGeometry.parent p →
        z ≠ Lfzk.LigeroPairGeometry.child p payload → H z = H' z) →
      state H = state H')
    (oracle : State → Lfzk.V1StrongV7TranscriptTerminal.Prefix
      i Ctx Other F nl rounds →
      Ligero.V1.Oracle F nw nq (row i).n 1)
    (statement : State → Lfzk.V1StrongV7TranscriptTerminal.Prefix
      i Ctx Other F nl rounds →
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
    let failure := fun H :
        Lfzk.V1StrongV7TranscriptTerminal.Point
          i Ctx Other F nl rounds → Coin =>
      let pr := selected (tree.run H).1
      Lfzk.V1StrongV7Terminal.accepts i D hkrow baseNodes responseNodes
        (oracle (state H) pr.1) (statement (state H) pr.1) (decodeChallenge (H (parent pr.1)))
        pr.2 (decodeQuery (H (child pr.1 pr.2)))
    ((univ.filter failure).card : ℚ) /
      (Fintype.card Coin : ℚ) ^
        Fintype.card (Lfzk.V1StrongV7TranscriptTerminal.Point
          i Ctx Other F nl rounds) ≤
      (N + 1 : ℕ) * density i := by
  exact Lfzk.V1StrongV7ContextFinal.v7_v1_context_final_density_le i
    hrows hfield D hkrow baseNodes responseNodes tree selected
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
    state hstateOff oracle statement decodeChallenge decodeQuery kchal kquery
    hchal hqueryBalance hkchal hkquery

/-- Checked v7 coefficient for every V1 signature/hash geometry.  Together
with `v7_v1_transcript_context_final_le`, the extraction-failure probability is
strictly below `6 * (N+1) / 2^128`. -/
theorem v7_v1_final_budget_lt_six (i : Fin 4) (N : ℕ) :
    (N + 1 : ℕ) * density i < (N + 1 : ℕ) * ((6 : ℚ) / 2 ^ 128) := by
  exact mul_lt_mul_of_pos_left (density_lt_six i) (by positivity)

end Lfzk.V1StrongV7TranscriptContextFinal
