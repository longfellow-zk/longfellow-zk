import Lfzk.V1StrongV7TwoSideOutput
import Bcs.TotalOracleCommit
import Bcs.Counting

/-! Average the two-side V1 charge over an independent Merkle tape. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Lfzk.V1StrongV7TwoSideSetup

open Finset LigeroFamily Lfzk.V1StrongV7Numeric
open Bcs.TotalOracle Merkle.RandomOracle
open scoped Classical

theorem v7_v1_two_side_fixed_merkle_tape_le (i : Fin 4)
    {F : Type} {Equations : Type*} {Enc D Coin X Other Msg₂ Out : Type}
    [Field F] [Fintype F] [DecidableEq F]
    [Fintype Equations] [DecidableEq Equations]
    [DecidableEq Enc]
    [Fintype D] [DecidableEq D] [Inhabited D]
    [Fintype Coin] [DecidableEq Coin] [Nonempty Coin]
    [Fintype X] [DecidableEq X]
    [Fintype Other] [DecidableEq Other] [Inhabited Other]
    [Fintype Msg₂] [DecidableEq Msg₂] [Inhabited Msg₂]
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
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → Coin) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Lfzk.LigeroTranscriptInputs.Message
      (Other := Other) (F := F)
      (block := (row i).k) (dblock := 2 * (row i).k - 1)
      (r := (row i).openings))
    (msgOf₂ : Out → ℕ → Msg₂)
    (responseOf : Out → Lfzk.V1StrongV7Terminal.Payload i F)
    (wellFormed : Out → Prop)
    (hresponse : ∀ out, wellFormed out →
      msgOf₁ out (Rounds.Role.layerBase rounds nl + 2) =
        Sum.inr (responseOf out))
    (oracle : (Fin TM → D) →
      (Lfzk.V1StrongV7TwoSideFinal.Outside i D Coin X Other F Msg₂
        nl nl₂ rounds rounds₂ → Coin) →
      Lfzk.V1StrongV7TwoSideFinal.Prefix i D Coin X Other F nl rounds →
      Ligero.V1.Oracle F nw nq (row i).n 1)
    (statement : (Fin TM → D) →
      (Lfzk.V1StrongV7TwoSideFinal.Outside i D Coin X Other F Msg₂
        nl nl₂ rounds rounds₂ → Coin) →
      Lfzk.V1StrongV7TwoSideFinal.Prefix i D Coin X Other F nl rounds →
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
      (QuerySet (row i).n (row i).openings) ≤ Fintype.card Coin)
    (mt : Fin TM → D) :
    let selected := Lfzk.LigeroPairGeometry.selectedFromOutput
      (nl := nl) (w := rounds)
      (Lfzk.NizkDeployedHashTwoField.ctxOf rootOf₁ rootOf₂ avOf pubOf)
      msgOf₁ responseOf
    let failure := fun H : Lfzk.V1StrongV7TwoSideFinal.Point i D Coin X
        Other F Msg₂ nl nl₂ rounds rounds₂ → Coin =>
      let out := S.proof mt H
      let pr := selected out
      wellFormed out ∧
      Lfzk.V1StrongV7Terminal.accepts i dom hkrow baseNodes responseNodes
        (oracle mt (Lfzk.LigeroPairGeometryTwoSide.outsideTerminal H) pr.1)
        (statement mt (Lfzk.LigeroPairGeometryTwoSide.outsideTerminal H) pr.1)
        (decodeChallenge (H (Lfzk.NizkDeployedHashTwoField.hash2
          (nl₁ := nl) (nl₂ := nl₂) (w₁ := rounds) (w₂ := rounds₂)
          rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out
          (1 + (Rounds.Role.layerBase rounds nl + 1)))))
        pr.2
        (decodeQuery (H (Lfzk.NizkDeployedHashTwoField.hash2
          (nl₁ := nl) (nl₂ := nl₂) (w₁ := rounds) (w₂ := rounds₂)
          rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out
          (1 + (Rounds.Role.layerBase rounds nl + 2)))))
    ((univ.filter failure).card : ℚ) /
      (Fintype.card Coin : ℚ) ^
        Fintype.card (Lfzk.V1StrongV7TwoSideFinal.Point i D Coin X
          Other F Msg₂ nl nl₂ rounds rounds₂) ≤
      (N + 1 : ℕ) * density i := by
  have h := Lfzk.V1StrongV7TwoSideOutput.v7_v1_two_side_output_failure_le i
    hrows hfield dom hkrow baseNodes responseNodes (S.search mt)
    rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ responseOf
    wellFormed hresponse (oracle mt) (statement mt)
    decodeChallenge decodeQuery kchal kquery
    hchal hqueryBalance hkchal hkquery
  simpa only [S.proof_eq] using h

end Lfzk.V1StrongV7TwoSideSetup
