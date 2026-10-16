import Lfzk.CompiledZkPotentialCircuit
import Lfzk.GradedCoreGrid

/-!
# Graded extraction for the deployed v7 circuit geometries

The four hash rows use their checked six-step agreement potentials.  The
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

section V7

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
/-- All four v7 circuit geometries satisfy the graded 115-bit extraction
bound for every Merkle-query budget. -/
theorem v7_circuit_potential_extraction_115
    (i : Fin 4) {tA N TM : ℕ}
    (hD : Fintype.card D = 2 ^ 256)
    {codec₁ : Codec Salt₁ (Col F₁ (Lfzk.GradedV7Hash.row i).params.nw
      (Lfzk.GradedV7Hash.row i).params.nq) D Enc}
    {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ v7SigHahn.params.nw
      v7SigHahn.params.nq) D Enc}
    {dec₂ : RoleDecoders codec₂}
    (S₁ : CircuitSide (Lfzk.GradedV7Hash.row i)
      (Lfzk.GradedV7Hash.row_valid i)
      (Lfzk.GradedV7Hash.row_openings_pos i)
      (Lfzk.SoundnessAudit.v7HashLogv i)
      C F₁ Msg₁ M₁ nt₁ nlin₁ X dec₁ Prod.fst)
    (S₂ : CircuitSide v7SigHahn v7SigHahn_valid v7SigHahn_openings_pos
      8 C F₂ Msg₂ M₂ nt₂ nlin₂ X dec₂ Prod.snd)
    (body : TwoOracleTree Enc D
      (Pt2 D C X Msg₁ Msg₂
        (Lfzk.GradedV7Hash.row i).params.nl v7SigHahn.params.nl
        (Lfzk.GradedV7Hash.row i).params.rounds v7SigHahn.params.rounds)
      C Out tA N)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim
      (Lfzk.GradedV7Hash.row i).params.row.n Salt₁
      (Col F₁ (Lfzk.GradedV7Hash.row i).params.nw
        (Lfzk.GradedV7Hash.row i).params.nq) D)
    (claimOf₂ : Out → OpeningClaim v7SigHahn.params.row.n Salt₂
      (Col F₂ v7SigHahn.params.nw v7SigHahn.params.nq) D)
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
          (Lfzk.GradedV7Hash.row i).params.nl v7SigHahn.params.nl
          (Lfzk.GradedV7Hash.row i).params.rounds v7SigHahn.params.rounds → C)
        (a : Fin S₁.c.ninp → F₁),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      S₁.toSide.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂)
        rootOf₁ msgOf₁ claimOf₁ avOf pubOf
        (slice1 (Lfzk.GradedV7Hash.row i) v7SigHahn) mt ro →
      S₁.toSide.Good (sideCtx S avOf pubOf mt ro) a →
      mac₁ a (aP (S.context mt ro) + decode (avOf (S.proof mt ro))) =
        tagOf (S.proof mt ro))
    (hrow₂ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂
          (Lfzk.GradedV7Hash.row i).params.nl v7SigHahn.params.nl
          (Lfzk.GradedV7Hash.row i).params.rounds v7SigHahn.params.rounds → C)
        (a : Fin S₂.c.ninp → F₂),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      S₂.toSide.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂)
        rootOf₂ msgOf₂ claimOf₂ avOf pubOf
        (slice2 (Lfzk.GradedV7Hash.row i) v7SigHahn) mt ro →
      S₂.toSide.Good (sideCtx S avOf pubOf mt ro) a →
      mac₂ a (aP (S.context mt ro) + decode (avOf (S.proof mt ro))) =
        tagOf (S.proof mt ro))
    (htape : 2 * v7SigHahn.params.row.n +
      2 * (Lfzk.GradedV7Hash.row i).params.row.n + tA ≤ TM)
    (hTM : 0 < TM) :
    circuitExtractionFailureRatio (TM := TM) S₁ S₂ body
      rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ claimOf₁ claimOf₂
      common₁ common₂ ≤ (1 + N + tA : ℚ) / 2 ^ 115 := by
  by_cases htA : tA ≤ 2 ^ 115
  · let H := Lfzk.GradedV7Hash.row i
    have hratio := twofield_circuit_potential_extraction
      (Lfzk.GradedV7Hash.row_valid i) v7SigHahn_valid
      (Lfzk.GradedV7Hash.row_openings_pos i) v7SigHahn_openings_pos
      S₁ S₂ (Lfzk.GradedV7Hash.curve i)
      (Lfzk.GradedSignature.curve false) body
      rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ claimOf₁ claimOf₂
      aP decode kmac hbal tagOf common₁ common₂ mac₁ mac₂ hcoll
      ((Lfzk.GradedV7Hash.challengeNumerator i : ℚ) / 2 ^ 128)
      ((Lfzk.GradedV7Hash.queryNumerator i : ℚ) / 2 ^ 128)
      (v7SigHahn.params.row.fail + v7SigHahn.params.row.arith)
      v7SigHahn.params.row.cover
      (Lfzk.GradedV7Hash.challengeCost_le i)
      (Lfzk.GradedV7Hash.queryCost_le i)
      (Lfzk.GradedSignature.challengeCost_le false)
      (Lfzk.GradedSignature.queryCost_le false)
      hrow₁ hrow₂ htape hTM
    have hcands : H.cardCand * v7SigHahn.cardCand = 4 := by
      fin_cases i <;> decide
    have hnum := Lfzk.GradedCoreGrid.v7GradedBudgetRhs_le_115
      i (Fintype.card C) kmac N tA Fintype.card_pos hmac htA
    dsimp only at hnum
    rw [hD] at hratio
    apply le_trans hratio
    unfold Lfzk.GradedCoreGrid.v7GradedBudget at hnum
    dsimp only [H] at hcands
    convert hnum using 1
    · rfl
    · have hkey : ((Lfzk.GradedV7Hash.row i).cardCand : ℚ) *
          (v7SigHahn.cardCand : ℚ) * (kmac : ℚ) = 4 * kmac := by
        have hnat : (Lfzk.GradedV7Hash.row i).cardCand *
            v7SigHahn.cardCand * kmac = 4 * kmac := by rw [hcands]
        exact_mod_cast hnat
      have hfc : 2 * v7SigHahn.params.row.n +
          2 * (Lfzk.GradedV7Hash.row i).params.row.n =
          2 * (Lfzk.GradedV7Hash.row i).params.row.n +
            2 * v7SigHahn.params.row.n := by omega
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


omit [DecidableEq Msg₁] [DecidableEq Msg₂] in
/-- All four v7 circuit geometries satisfy the graded 116-bit extraction
bound when the adversary has a positive transcript-query budget. -/
theorem v7_circuit_potential_extraction_116_of_pos_queries
    (i : Fin 4) {tA N TM : ℕ}
    (hD : Fintype.card D = 2 ^ 256) (hN : 0 < N)
    {codec₁ : Codec Salt₁ (Col F₁ (Lfzk.GradedV7Hash.row i).params.nw
      (Lfzk.GradedV7Hash.row i).params.nq) D Enc}
    {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ v7SigHahn.params.nw
      v7SigHahn.params.nq) D Enc}
    {dec₂ : RoleDecoders codec₂}
    (S₁ : CircuitSide (Lfzk.GradedV7Hash.row i)
      (Lfzk.GradedV7Hash.row_valid i)
      (Lfzk.GradedV7Hash.row_openings_pos i)
      (Lfzk.SoundnessAudit.v7HashLogv i)
      C F₁ Msg₁ M₁ nt₁ nlin₁ X dec₁ Prod.fst)
    (S₂ : CircuitSide v7SigHahn v7SigHahn_valid v7SigHahn_openings_pos
      8 C F₂ Msg₂ M₂ nt₂ nlin₂ X dec₂ Prod.snd)
    (body : TwoOracleTree Enc D
      (Pt2 D C X Msg₁ Msg₂
        (Lfzk.GradedV7Hash.row i).params.nl v7SigHahn.params.nl
        (Lfzk.GradedV7Hash.row i).params.rounds v7SigHahn.params.rounds)
      C Out tA N)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim
      (Lfzk.GradedV7Hash.row i).params.row.n Salt₁
      (Col F₁ (Lfzk.GradedV7Hash.row i).params.nw
        (Lfzk.GradedV7Hash.row i).params.nq) D)
    (claimOf₂ : Out → OpeningClaim v7SigHahn.params.row.n Salt₂
      (Col F₂ v7SigHahn.params.nw v7SigHahn.params.nq) D)
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
          (Lfzk.GradedV7Hash.row i).params.nl v7SigHahn.params.nl
          (Lfzk.GradedV7Hash.row i).params.rounds v7SigHahn.params.rounds → C)
        (a : Fin S₁.c.ninp → F₁),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      S₁.toSide.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂)
        rootOf₁ msgOf₁ claimOf₁ avOf pubOf
        (slice1 (Lfzk.GradedV7Hash.row i) v7SigHahn) mt ro →
      S₁.toSide.Good (sideCtx S avOf pubOf mt ro) a →
      mac₁ a (aP (S.context mt ro) + decode (avOf (S.proof mt ro))) =
        tagOf (S.proof mt ro))
    (hrow₂ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂
          (Lfzk.GradedV7Hash.row i).params.nl v7SigHahn.params.nl
          (Lfzk.GradedV7Hash.row i).params.rounds v7SigHahn.params.rounds → C)
        (a : Fin S₂.c.ninp → F₂),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      S₂.toSide.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂)
        rootOf₂ msgOf₂ claimOf₂ avOf pubOf
        (slice2 (Lfzk.GradedV7Hash.row i) v7SigHahn) mt ro →
      S₂.toSide.Good (sideCtx S avOf pubOf mt ro) a →
      mac₂ a (aP (S.context mt ro) + decode (avOf (S.proof mt ro))) =
        tagOf (S.proof mt ro))
    (htape : 2 * v7SigHahn.params.row.n +
      2 * (Lfzk.GradedV7Hash.row i).params.row.n + tA ≤ TM)
    (hTM : 0 < TM) :
    circuitExtractionFailureRatio (TM := TM) S₁ S₂ body
      rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ claimOf₁ claimOf₂
      common₁ common₂ ≤ (1 + N + tA : ℚ) / 2 ^ 116 := by
  by_cases htA : tA ≤ 2 ^ 116
  · let H := Lfzk.GradedV7Hash.row i
    have hratio := twofield_circuit_potential_extraction
      (Lfzk.GradedV7Hash.row_valid i) v7SigHahn_valid
      (Lfzk.GradedV7Hash.row_openings_pos i) v7SigHahn_openings_pos
      S₁ S₂ (Lfzk.GradedV7Hash.curve i)
      (Lfzk.GradedSignature.curve false) body
      rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ claimOf₁ claimOf₂
      aP decode kmac hbal tagOf common₁ common₂ mac₁ mac₂ hcoll
      ((Lfzk.GradedV7Hash.challengeNumerator i : ℚ) / 2 ^ 128)
      ((Lfzk.GradedV7Hash.queryNumerator i : ℚ) / 2 ^ 128)
      (v7SigHahn.params.row.fail + v7SigHahn.params.row.arith)
      v7SigHahn.params.row.cover
      (Lfzk.GradedV7Hash.challengeCost_le i)
      (Lfzk.GradedV7Hash.queryCost_le i)
      (Lfzk.GradedSignature.challengeCost_le false)
      (Lfzk.GradedSignature.queryCost_le false)
      hrow₁ hrow₂ htape hTM
    have hcands : H.cardCand * v7SigHahn.cardCand = 4 := by
      fin_cases i <;> decide
    have hnum := Lfzk.GradedCoreGrid.v7GradedBudgetRhs_le_116_of_pos_queries
      i (Fintype.card C) kmac N tA Fintype.card_pos hmac hN htA
    dsimp only at hnum
    rw [hD] at hratio
    apply le_trans hratio
    unfold Lfzk.GradedCoreGrid.v7GradedBudget at hnum
    dsimp only [H] at hcands
    convert hnum using 1
    · rfl
    · have hkey : ((Lfzk.GradedV7Hash.row i).cardCand : ℚ) *
          (v7SigHahn.cardCand : ℚ) * (kmac : ℚ) = 4 * kmac := by
        have hnat : (Lfzk.GradedV7Hash.row i).cardCand *
            v7SigHahn.cardCand * kmac = 4 * kmac := by rw [hcands]
        exact_mod_cast hnat
      have hfc : 2 * v7SigHahn.params.row.n +
          2 * (Lfzk.GradedV7Hash.row i).params.row.n =
          2 * (Lfzk.GradedV7Hash.row i).params.row.n +
            2 * v7SigHahn.params.row.n := by omega
      rw [hkey, hfc]
      norm_num
  · unfold circuitExtractionFailureRatio
    calc
      _ ≤ (1 : ℚ) := Lfzk.TSec.ratio_le_one _
      _ ≤ (1 + N + tA : ℚ) / 2 ^ 116 := by
        have hn : 2 ^ 116 ≤ tA := by omega
        have hq : (2 ^ 116 : ℚ) ≤ (tA : ℚ) := by exact_mod_cast hn
        apply (le_div_iff₀ (by positivity)).mpr
        nlinarith [show (0 : ℚ) ≤ N by positivity]

end V7

end Lfzk.CompiledZkProfileRows
