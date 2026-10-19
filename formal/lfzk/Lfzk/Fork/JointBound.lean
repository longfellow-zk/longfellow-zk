import Lfzk.V1StrongV7Hash1JointBound
import Lfzk.Fork.DeployedBridge

/-! Schedule-dependent bridge for the forked verifier. Generic local
counts, cut-context lemmas, and numerical certificates are reused. -/

namespace Lfzk.Fork.JointBound

open Lfzk.V1StrongV7Hash1JointBound

open Finset LigeroFamily Lfzk.CertifiedV1 Lfzk.V1StrongV7Numeric
  Lfzk.CompiledZk
open Merkle.MH Merkle.RandomOracle
open Lfzk.CompiledLongfellow (Col)
open scoped Classical

private abbrev HashPoint (D Coin X Other F Msg₂ : Type) :=
  Lfzk.V1StrongV7TwoSideFinal.Point 0 D Coin X Other F Msg₂
    v7Hash1.params.nl v7SigHahn.params.nl
    v7Hash1.params.rounds v7SigHahn.params.rounds

/-- The exact forked terminal event has the same bound over the joint
Merkle tape and challenge-oracle experiment as it has at every fixed tape. -/
theorem hash1_cut_failure_joint_le
    {Coin F Other Enc D Salt X Msg₂ Out : Type}
    [Fintype Coin] [DecidableEq Coin] [Inhabited Coin]
    [Field F] [Fintype F] [DecidableEq F] [SumcheckInterp F]
    [Fintype D] [DecidableEq D] [Inhabited D]
    [Fintype X] [DecidableEq X]
    [Fintype Other] [DecidableEq Other] [Inhabited Other]
    [Fintype Msg₂] [DecidableEq Msg₂] [Inhabited Msg₂]
    [DecidableEq Enc] [Inhabited Salt]
    {M nt nlin tA N TM : ℕ}
    {codec : Codec Salt (Col F v7Hash1.params.nw v7Hash1.params.nq) D Enc}
    {dec : RoleDecoders codec}
    (S : Lfzk.CompiledZk.CircuitSide v7Hash1 v7Hash1_valid
      v7Hash1_openings_pos 3 Coin F
      (Lfzk.LigeroTranscriptInputs.Message
        (Other := Other) (F := F)
        (block := (row (0 : Fin 4)).k)
        (dblock := 2 * (row (0 : Fin 4)).k - 1)
        (r := (row (0 : Fin 4)).openings))
      M nt nlin X dec Prod.fst)
    (baseNodes : Fin (row (0 : Fin 4)).k ↪
      Position (row (0 : Fin 4)).openings v7Hash1.params.q
        (row (0 : Fin 4)).n)
    (responseNodes : Fin (2 * (row (0 : Fin 4)).k - 1) ↪
      Position (row (0 : Fin 4)).openings v7Hash1.params.q
        (row (0 : Fin 4)).n)
    (body : TwoOracleTree Enc D
      (HashPoint D Coin X Other F Msg₂) Coin Out tA N)
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
        v7Hash1.params.nl + 2) = Sum.inr (responseOf out)) :
    let Ssetup := Lfzk.Fork.Transcript.setup2 body
      rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
    let selected := Lfzk.LigeroPairGeometry.selectedFromOutput
      (nl := v7Hash1.params.nl) (w := v7Hash1.params.rounds)
      (Lfzk.NizkDeployedHashTwoField.ctxOf rootOf₁ rootOf₂ avOf pubOf)
      msgOf₁ responseOf
    let failure := fun (mt : Fin TM → D)
        (H : HashPoint D Coin X Other F Msg₂ → Coin) =>
      let out := Ssetup.proof mt H
      let pr := selected out
      let st := Lfzk.V1StrongV7TwoSideCutContext.cutState Ssetup mt pr.1 H
      Lfzk.V1StrongV7Hash1Local.terminalFailureAt
        S baseNodes responseNodes st pr.1 (wellFormed out)
        (H (Lfzk.Fork.Transcript.hash2
          rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out
          (1 + (Rounds.Role.layerBase v7Hash1.params.rounds
            v7Hash1.params.nl + 1))))
        pr.2
        (H (Lfzk.Fork.Transcript.hash2
          rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out
          (1 + (Rounds.Role.layerBase v7Hash1.params.rounds
            v7Hash1.params.nl + 2))))
    ((univ.filter fun ω : (Fin TM → D) ×
        (HashPoint D Coin X Other F Msg₂ → Coin) =>
          failure ω.1 ω.2).card : ℚ) /
      ((Fintype.card D : ℚ) ^ TM *
        (Fintype.card Coin : ℚ) ^
          Fintype.card (HashPoint D Coin X Other F Msg₂)) ≤
      (N + 1 : ℕ) * density 0 := by
  classical
  let Ssetup := Lfzk.Fork.Transcript.setup2 body
    rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
  let selected := Lfzk.LigeroPairGeometry.selectedFromOutput
    (nl := v7Hash1.params.nl) (w := v7Hash1.params.rounds)
    (Lfzk.NizkDeployedHashTwoField.ctxOf rootOf₁ rootOf₂ avOf pubOf)
    msgOf₁ responseOf
  let failure := fun (mt : Fin TM → D)
      (H : HashPoint D Coin X Other F Msg₂ → Coin) =>
    let out := Ssetup.proof mt H
    let pr := selected out
    let st := Lfzk.V1StrongV7TwoSideCutContext.cutState Ssetup mt pr.1 H
    Lfzk.V1StrongV7Hash1Local.terminalFailureAt
      S baseNodes responseNodes st pr.1 (wellFormed out)
      (H (Lfzk.Fork.Transcript.hash2
        rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out
        (1 + (Rounds.Role.layerBase v7Hash1.params.rounds
          v7Hash1.params.nl + 1))))
      pr.2
      (H (Lfzk.Fork.Transcript.hash2
        rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out
        (1 + (Rounds.Role.layerBase v7Hash1.params.rounds
          v7Hash1.params.nl + 2))))
  have hfixed : ∀ mt : Fin TM → D,
      ((univ.filter (failure mt)).card : ℚ) /
        (Fintype.card Coin : ℚ) ^
          Fintype.card (HashPoint D Coin X Other F Msg₂) ≤
        (N + 1 : ℕ) * density 0 := by
    intro mt
    simpa only [failure, Ssetup, selected] using
      Lfzk.Fork.Bound.hash1_cut_failure_le
        S baseNodes responseNodes body rootOf₁ rootOf₂ avOf pubOf
        msgOf₁ msgOf₂ responseOf wellFormed hresponse mt
  have hfixed' : ∀ mt : Fin TM → D,
      ((univ.filter (failure mt)).card : ℚ) /
        Fintype.card (HashPoint D Coin X Other F Msg₂ → Coin) ≤
        (N + 1 : ℕ) * density 0 := by
    intro mt
    simpa only [Fintype.card_fun, Nat.cast_pow] using hfixed mt
  have h := joint_ratio_le_of_fixed failure ((N + 1 : ℕ) * density 0) hfixed'
  simpa only [failure, Ssetup, selected,
    Fintype.card_fun, Fintype.card_fin, Nat.cast_pow, Nat.cast_mul] using h


end Lfzk.Fork.JointBound
