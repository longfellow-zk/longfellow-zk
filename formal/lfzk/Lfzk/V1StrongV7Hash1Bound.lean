import Lfzk.V1StrongV7Hash1Local
import Lfzk.V1StrongV7TwoSideCutSetup

/-! The strong V1 hash1 bound at the concrete compiled statement and cut. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 0

namespace Lfzk.V1StrongV7Hash1Bound

open Finset LigeroFamily Lfzk.CertifiedV1 Lfzk.V1StrongV7Numeric
open Merkle.RandomOracle
open scoped Classical

theorem hash1_cut_failure_le
    {Coin F Other Enc D Salt X Msg₂ Out : Type}
    [Fintype Coin] [DecidableEq Coin] [Inhabited Coin]
    [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F]
    [Fintype D] [DecidableEq D] [Inhabited D]
    [Fintype X] [DecidableEq X]
    [Fintype Other] [DecidableEq Other] [Inhabited Other]
    [Fintype Msg₂] [DecidableEq Msg₂] [Inhabited Msg₂]
    [DecidableEq Enc] [Inhabited Salt]
    {M nt nlin nl₂ tA N TM : ℕ} {rounds₂ : ℕ → ℕ}
    {codec : Merkle.MH.Codec Salt
      (Lfzk.CompiledLongfellow.Col F v7Hash1.params.nw v7Hash1.params.nq)
      D Enc}
    {dec : Merkle.MH.RoleDecoders codec}
    {rootOfKey : D × D → D}
    (S : Lfzk.CompiledZk.CircuitSide v7Hash1 v7Hash1_valid
      v7Hash1_openings_pos 3 Coin F
      (Lfzk.LigeroTranscriptInputs.Message
        (Other := Other) (F := F)
        (block := (row (0 : Fin 4)).k)
        (dblock := 2 * (row (0 : Fin 4)).k - 1)
        (r := (row (0 : Fin 4)).openings))
      M nt nlin X dec rootOfKey)
    (baseNodes : Fin (row (0 : Fin 4)).k ↪
      Position (row (0 : Fin 4)).openings v7Hash1.params.q
        (row (0 : Fin 4)).n)
    (responseNodes : Fin (2 * (row (0 : Fin 4)).k - 1) ↪
      Position (row (0 : Fin 4)).openings v7Hash1.params.q
        (row (0 : Fin 4)).n)
    (body : TwoOracleTree Enc D
      (Lfzk.V1StrongV7TwoSideFinal.Point 0 D Coin X Other F Msg₂
        v7Hash1.params.nl nl₂ v7Hash1.params.rounds rounds₂)
      Coin Out tA N)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → Coin) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Lfzk.LigeroTranscriptInputs.Message
      (Other := Other) (F := F)
      (block := (row (0 : Fin 4)).k)
      (dblock := 2 * (row (0 : Fin 4)).k - 1)
      (r := (row (0 : Fin 4)).openings))
    (msgOf₂ : Out → ℕ → Msg₂)
    (responseOf : Out → Lfzk.V1StrongV7Terminal.Payload 0 F)
    (wellFormed : Out → Prop)
    (hresponse : ∀ out, wellFormed out →
      msgOf₁ out (Rounds.Role.layerBase v7Hash1.params.rounds
        v7Hash1.params.nl + 2) = Sum.inr (responseOf out))
    (mt : Fin TM → D) :
    let Ssetup := Lfzk.NizkDeployedHashTwoField.setup2 body
      rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
    let selected := Lfzk.LigeroPairGeometry.selectedFromOutput
      (nl := v7Hash1.params.nl) (w := v7Hash1.params.rounds)
      (Lfzk.NizkDeployedHashTwoField.ctxOf rootOf₁ rootOf₂ avOf pubOf)
      msgOf₁ responseOf
    let failure := fun H : Lfzk.V1StrongV7TwoSideFinal.Point 0 D Coin X
        Other F Msg₂ v7Hash1.params.nl nl₂
        v7Hash1.params.rounds rounds₂ → Coin =>
      let out := Ssetup.proof mt H
      let pr := selected out
      let st := Lfzk.V1StrongV7TwoSideCutContext.cutState Ssetup mt pr.1 H
      Lfzk.V1StrongV7Hash1Local.terminalFailureAt
        S baseNodes responseNodes st pr.1 (wellFormed out)
        (H (Lfzk.NizkDeployedHashTwoField.hash2
          rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out
          (1 + (Rounds.Role.layerBase v7Hash1.params.rounds
            v7Hash1.params.nl + 1))))
        pr.2
        (H (Lfzk.NizkDeployedHashTwoField.hash2
          rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out
          (1 + (Rounds.Role.layerBase v7Hash1.params.rounds
            v7Hash1.params.nl + 2))))
    ((univ.filter failure).card : ℚ) /
      (Fintype.card Coin : ℚ) ^
        Fintype.card (Lfzk.V1StrongV7TwoSideFinal.Point 0 D Coin X
          Other F Msg₂ v7Hash1.params.nl nl₂
          v7Hash1.params.rounds rounds₂) ≤
      (N + 1 : ℕ) * density 0 := by
  have hrows : CoreRowsNonempty v7Hash1.params.nw v7Hash1.params.nq := by
    change 0 < v7Hash1.params.nw ∨ 0 < v7Hash1.params.nq
    exact Or.inl (by decide)
  have hfield : Fintype.card F = (row (0 : Fin 4)).fieldSize := by
    have hsize : (row (0 : Fin 4)).fieldSize =
        v7Hash1.params.row.fieldSize := by decide
    rw [hsize]
    exact S.hF
  have hkrow : (row (0 : Fin 4)).openings + v7Hash1.params.q =
      (row (0 : Fin 4)).k := by decide
  have hkey : ∀ p response,
      (Lfzk.NizkDeployedHashTwoField.setup2 body rootOf₁ rootOf₂
        avOf pubOf msgOf₁ msgOf₂).key
          (Lfzk.LigeroPairGeometryTwoSide.parent p) =
      (Lfzk.NizkDeployedHashTwoField.setup2 body rootOf₁ rootOf₂
        avOf pubOf msgOf₁ msgOf₂).key
          (Lfzk.LigeroPairGeometryTwoSide.child p response) := by
    intro p response
    exact Lfzk.LigeroPairGeometryTwoSide.setup2_key_parent_eq_child
      body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ p response
  have h := Lfzk.V1StrongV7TwoSideCutSetup.v7_v1_two_side_cut_fixed_merkle_tape_le
    0 hrows hfield S.dom hkrow baseNodes responseNodes
    (Lfzk.NizkDeployedHashTwoField.setup2 body rootOf₁ rootOf₂
      avOf pubOf msgOf₁ msgOf₂)
    hkey rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ responseOf
    wellFormed hresponse
    (Lfzk.V1StrongV7Hash1Local.oracleAt S)
    (Lfzk.V1StrongV7Hash1Local.statementAt S)
    (fun st p c => (S.Vc p.1.2.1 p.1.2.2).decodeChal c)
    (fun st p c => (S.Vc p.1.2.1 p.1.2.2).decodeQuery c)
    S.kchal S.kq
    (fun st p challenge => S.hbalChal p.1.2.1 p.1.2.2 challenge)
    (fun st p query => S.hbalQuery p.1.2.1 p.1.2.2 query)
    S.hkchal S.hkq mt
  simpa only [Lfzk.V1StrongV7Hash1Local.terminalFailureAt] using h

end Lfzk.V1StrongV7Hash1Bound
