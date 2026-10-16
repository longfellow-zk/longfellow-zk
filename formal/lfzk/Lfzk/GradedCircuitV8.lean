import Lfzk.CompiledZkPotentialCircuit
import Lfzk.GradedCoreGrid

/-!
# Graded extraction for the deployed v8 circuit geometry

The hash row uses its checked six-step agreement potential.  The
signature side uses its checked single-step potential.  The event is the
actual two-circuit committed-pair extractor failing on an accepted FS
transcript.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.CompiledZkProfileRows

open Finset Bcs Merkle Merkle.MH Merkle.RandomOracle
  Merkle.RandomOracle.TwoOracleTree Lfzk.CompiledZk Lfzk.CertifiedV1
  Lfzk.NizkZk Lfzk.NizkZkTwoField Lfzk.NizkZkDeployedHash
  Lfzk.NizkDeployedHashTwoField Lfzk.CompiledZkDeployedHash
open Lfzk.CompiledLongfellow (Col)
open Lfzk.CompiledLongfellowAdaptive (slice1 slice2)
open Lfzk.NizkAdaptiveTwoField (check2)
open scoped Classical

section V8

variable {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]
variable {D : Type} [Fintype D] [DecidableEq D] [Inhabited D]
variable {Enc X Out : Type} [DecidableEq Enc] [Fintype X]
variable {Fmac : Type} [Field Fmac] [Fintype Fmac] [DecidableEq Fmac] {nblk : ℕ}
variable {F₁ Msg₁ : Type} [Field F₁] [Fintype F₁] [DecidableEq F₁] [SumcheckInterp F₁]
  [DecidableEq Msg₁] [Inhabited Msg₁] [Fintype Msg₁] {M₁ nt₁ nlin₁ : ℕ}
variable {F₂ Msg₂ : Type} [Field F₂] [Fintype F₂] [DecidableEq F₂] [SumcheckInterp F₂]
  [DecidableEq Msg₂] [Inhabited Msg₂] [Fintype Msg₂] {M₂ nt₂ nlin₂ : ℕ}
variable {Salt₁ Salt₂ : Type} [Inhabited Salt₁] [Inhabited Salt₂]

omit [DecidableEq Msg₁] [DecidableEq Msg₂] in
/-- The v8 circuit geometry satisfies the graded 115-bit extraction
bound for every Merkle-query budget. -/
theorem v8_circuit_potential_extraction_115
    {tA N TM : ℕ}
    (hD : Fintype.card D = 2 ^ 256)
    {codec₁ : Codec Salt₁ (Col F₁ v8Hash.params.nw
      v8Hash.params.nq) D Enc}
    {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ v8Sig.params.nw
      v8Sig.params.nq) D Enc}
    {dec₂ : RoleDecoders codec₂}
    (S₁ : CircuitSide v8Hash
      v8Hash_valid
      (by decide)
      5
      C F₁ Msg₁ M₁ nt₁ nlin₁ X dec₁ Prod.fst)
    (S₂ : CircuitSide v8Sig v8Sig_valid (by decide)
      3 C F₂ Msg₂ M₂ nt₂ nlin₂ X dec₂ Prod.snd)
    (body : TwoOracleTree Enc D
      (Pt2 D C X Msg₁ Msg₂
        v8Hash.params.nl v8Sig.params.nl
        v8Hash.params.rounds v8Sig.params.rounds)
      C Out tA N)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim
      v8Hash.params.row.n Salt₁
      (Col F₁ v8Hash.params.nw
        v8Hash.params.nq) D)
    (claimOf₂ : Out → OpeningClaim v8Sig.params.row.n Salt₂
      (Col F₂ v8Sig.params.nw v8Sig.params.nq) D)
    (aP : (D × D) × List (Enc × D) → Fmac) (decode : C → Fmac)
    (kmac : ℕ)
    (hbal : ∀ x : Fmac, (univ.filter fun c : C => decode c = x).card ≤ kmac)
    (hmac : kmac * 2 ^ 128 ≤ Fintype.card C)
    (tagOf : Out → Fin nblk → Fmac)
    (common₁ : (Fin S₁.c.ninp → F₁) → Fin nblk → Fmac)
    (common₂ : (Fin S₂.c.ninp → F₂) → Fin nblk → Fmac)
    (mac₁ : (Fin S₁.c.ninp → F₁) → Fmac → Fin nblk → Fmac)
    (mac₂ : (Fin S₂.c.ninp → F₂) → Fmac → Fin nblk → Fmac)
    (hcoll : ∀ a₁ a₂, common₁ a₁ ≠ common₂ a₂ →
      (univ.filter fun x => mac₁ a₁ x = mac₂ a₂ x).card ≤ 1)
    (hrow₁ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂
          v8Hash.params.nl v8Sig.params.nl
          v8Hash.params.rounds v8Sig.params.rounds → C)
        (a : Fin S₁.c.ninp → F₁),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      S₁.toSide.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂)
        rootOf₁ msgOf₁ claimOf₁ avOf pubOf
        (slice1 v8Hash v8Sig) mt ro →
      S₁.toSide.Good (sideCtx S avOf pubOf mt ro) a →
      mac₁ a (aP (S.context mt ro) + decode (avOf (S.proof mt ro))) =
        tagOf (S.proof mt ro))
    (hrow₂ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂
          v8Hash.params.nl v8Sig.params.nl
          v8Hash.params.rounds v8Sig.params.rounds → C)
        (a : Fin S₂.c.ninp → F₂),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      S₂.toSide.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂)
        rootOf₂ msgOf₂ claimOf₂ avOf pubOf
        (slice2 v8Hash v8Sig) mt ro →
      S₂.toSide.Good (sideCtx S avOf pubOf mt ro) a →
      mac₂ a (aP (S.context mt ro) + decode (avOf (S.proof mt ro))) =
        tagOf (S.proof mt ro))
    (htape : 2 * v8Sig.params.row.n +
      2 * v8Hash.params.row.n + tA ≤ TM)
    (hTM : 0 < TM) :
    circuitExtractionFailureRatio (TM := TM) S₁ S₂ body
      rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ claimOf₁ claimOf₂
      common₁ common₂ ≤ (1 + N + tA : ℚ) / 2 ^ 115 := by
  by_cases htA : tA ≤ 2 ^ 115
  · let H := v8Hash
    have hratio := twofield_circuit_potential_extraction
      v8Hash_valid v8Sig_valid
      (by decide) (by decide)
      S₁ S₂ Lfzk.GradedV8Hash.curve
      (Lfzk.GradedSignature.curve true) body
      rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ claimOf₁ claimOf₂
      aP decode kmac hbal tagOf common₁ common₂ mac₁ mac₂ hcoll
      ((1804 : ℚ) / 2 ^ 128)
      ((1134 : ℚ) / 2 ^ 128)
      (v8Sig.params.row.fail + v8Sig.params.row.arith)
      v8Sig.params.row.cover
      Lfzk.GradedV8Hash.challengeCost_le
      Lfzk.GradedV8Hash.queryCost_le
      (Lfzk.GradedSignature.challengeCost_le true)
      (Lfzk.GradedSignature.queryCost_le true)
      hrow₁ hrow₂ htape hTM
    have hcands : H.cardCand * v8Sig.cardCand = 4 := by
      decide
    have hnum := Lfzk.GradedCoreGrid.v8GradedBudgetRhs_le_115 (Fintype.card C) kmac N tA Fintype.card_pos hmac htA
    dsimp only at hnum
    rw [hD] at hratio
    apply le_trans hratio
    unfold Lfzk.GradedCoreGrid.v8GradedBudget at hnum
    dsimp only [H] at hcands
    convert hnum using 1
    · rfl
    · have hkey : (v8Hash.cardCand : ℚ) *
          (v8Sig.cardCand : ℚ) * (kmac : ℚ) = 4 * kmac := by
        have hnat : v8Hash.cardCand *
            v8Sig.cardCand * kmac = 4 * kmac := by rw [hcands]
        exact_mod_cast hnat
      have hfc : 2 * v8Sig.params.row.n +
          2 * v8Hash.params.row.n =
          2 * v8Hash.params.row.n +
            2 * v8Sig.params.row.n := by omega
      rw [hkey, hfc]
      norm_num
  · unfold circuitExtractionFailureRatio
    calc
      _ ≤ (1 : ℚ) := Lfzk.TSec.ratio_le_one _
      _ ≤ (1 + N + tA : ℚ) / 2 ^ 115 := by
        have hn : 2 ^ 115 ≤ tA := by omega
        have hq : (2 ^ 115 : ℚ) ≤ (tA : ℚ) := by exact_mod_cast hn
        apply (le_div_iff₀ (by positivity)).mpr
        nlinarith [show (0 : ℚ) ≤ N by positivity]

end V8

end Lfzk.CompiledZkProfileRows
