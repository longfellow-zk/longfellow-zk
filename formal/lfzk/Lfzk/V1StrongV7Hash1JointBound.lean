import Lfzk.V1StrongV7Hash1Bound
import Lfzk.CertifiedHahn

/-! Lift the fixed Merkle-tape terminal estimate to the joint deployed
Merkle/random-oracle sample space. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.V1StrongV7Hash1JointBound

open Finset Bcs
open scoped Classical

/-- A conditional bound uniform in the Merkle tape has exactly the same
bound after averaging over that tape.  This is the counting step needed to
combine the direct V1 terminal estimate with a two-oracle FS compiler. -/
theorem joint_ratio_le_of_fixed
    {A B : Type} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (bad : A → B → Prop) (bound : ℚ)
    (hfixed : ∀ a,
      ((univ.filter (bad a)).card : ℚ) / Fintype.card B ≤ bound) :
    ((univ.filter fun p : A × B => bad p.1 p.2).card : ℚ) /
        (Fintype.card A * Fintype.card B : ℚ) ≤ bound := by
  have hB : (0 : ℚ) < Fintype.card B := by
    exact_mod_cast Fintype.card_pos
  have hA : (0 : ℚ) < Fintype.card A := by
    exact_mod_cast Fintype.card_pos
  have hsum :
      (∑ a : A, ((univ.filter (bad a)).card : ℚ)) ≤
        ∑ _a : A, bound * Fintype.card B := by
    apply Finset.sum_le_sum
    intro a _
    exact (div_le_iff₀ hB).mp (hfixed a)
  rw [div_le_iff₀ (mul_pos hA hB)]
  rw [card_filter_prod_fst]
  push_cast
  calc
    (∑ a : A, ((univ.filter (bad a)).card : ℚ)) ≤
        ∑ _a : A, bound * Fintype.card B := hsum
    _ = bound * (Fintype.card A * Fintype.card B : ℚ) := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

/-- A direct terminal estimate can be added to a potential estimate over
the same joint experiment, without changing the latter's query factor. -/
theorem ratio_le_of_cover
    {Ω : Type} [Fintype Ω]
    (failure charged terminal : Ω → Prop) (den chargedBound terminalBound : ℚ)
    (hden : 0 < den)
    (hcover : ∀ ω, failure ω → charged ω ∨ terminal ω)
    (hcharged : ((univ.filter charged).card : ℚ) / den ≤ chargedBound)
    (hterminal : ((univ.filter terminal).card : ℚ) / den ≤ terminalBound) :
    ((univ.filter failure).card : ℚ) / den ≤
      chargedBound + terminalBound := by
  have hsubset : (univ.filter failure : Finset Ω) ⊆
      univ.filter charged ∪ univ.filter terminal := by
    intro ω hω
    have hf : failure ω := (Finset.mem_filter.mp hω).2
    rcases hcover ω hf with hc | ht
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, hc⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, ht⟩)
  have hcard : (univ.filter failure).card ≤
      (univ.filter charged).card + (univ.filter terminal).card :=
    (Finset.card_le_card hsubset).trans (Finset.card_union_le _ _)
  have hq : ((univ.filter failure).card : ℚ) ≤
      ((univ.filter charged).card : ℚ) +
        ((univ.filter terminal).card : ℚ) := by
    exact_mod_cast hcard
  rw [div_le_iff₀ hden]
  have hc := (div_le_iff₀ hden).mp hcharged
  have ht := (div_le_iff₀ hden).mp hterminal
  nlinarith

end Lfzk.V1StrongV7Hash1JointBound

namespace Lfzk.V1StrongV7Hash1JointBound

open Finset LigeroFamily Lfzk.CertifiedV1 Lfzk.V1StrongV7Numeric
  Lfzk.CompiledZk
open Merkle.MH Merkle.RandomOracle
open Lfzk.CompiledLongfellow (Col)
open scoped Classical

private abbrev HashPoint (D Coin X Other F Msg₂ : Type) :=
  Lfzk.V1StrongV7TwoSideFinal.Point 0 D Coin X Other F Msg₂
    v7Hash1.params.nl v7SigHahn.params.nl
    v7Hash1.params.rounds v7SigHahn.params.rounds

/-- The exact deployed terminal event has the same bound over the joint
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
    let Ssetup := Lfzk.NizkDeployedHashTwoField.setup2 body
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
        (H (Lfzk.NizkDeployedHashTwoField.hash2
          rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out
          (1 + (Rounds.Role.layerBase v7Hash1.params.rounds
            v7Hash1.params.nl + 1))))
        pr.2
        (H (Lfzk.NizkDeployedHashTwoField.hash2
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
  let Ssetup := Lfzk.NizkDeployedHashTwoField.setup2 body
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
      (H (Lfzk.NizkDeployedHashTwoField.hash2
        rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out
        (1 + (Rounds.Role.layerBase v7Hash1.params.rounds
          v7Hash1.params.nl + 1))))
      pr.2
      (H (Lfzk.NizkDeployedHashTwoField.hash2
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
      Lfzk.V1StrongV7Hash1Bound.hash1_cut_failure_le
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

end Lfzk.V1StrongV7Hash1JointBound
