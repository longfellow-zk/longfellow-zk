import Lfzk.CompiledZkPotentialFS
import Lfzk.CompiledZkProfileSepMac

/-!
# Circuit-level extraction for the graded two-field compiler

The committed candidate lists are the circuits' lift lists.  This wrapper
connects the extraction-first potential theorem to two accepted circuit
verifiers and discharges candidate membership and size from `CircuitSide`.
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
open Lfzk.NizkAdaptiveTwoField (check2 len2)
open scoped Classical

section Circuit

variable {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]
variable {D : Type} [Fintype D] [DecidableEq D] [Inhabited D]
variable {Enc X Out : Type} [DecidableEq Enc] [Fintype X] [DecidableEq X]
variable {Fmac : Type} [Field Fmac] [Fintype Fmac] [DecidableEq Fmac] {nblk : ℕ}
variable {F₁ Msg₁ : Type} [Field F₁] [Fintype F₁] [DecidableEq F₁] [SumcheckInterp F₁]
  [DecidableEq Msg₁] [Inhabited Msg₁] [Fintype Msg₁] {M₁ nt₁ nlin₁ : ℕ}
variable {F₂ Msg₂ : Type} [Field F₂] [Fintype F₂] [DecidableEq F₂] [SumcheckInterp F₂]
  [DecidableEq Msg₂] [Inhabited Msg₂] [Fintype Msg₂] {M₂ nt₂ nlin₂ : ℕ}
variable {Salt₁ Salt₂ : Type} [Inhabited Salt₁] [Inhabited Salt₂]

/-- Probability mass of accepted two-circuit transcripts on which the
committed-pair extractor returns no agreeing pair. -/
noncomputable def circuitExtractionFailureRatio
    {R₁ R₂ : Row} {h₁ : R₁.Valid} {h₂ : R₂.Valid}
    {hr₁ : 0 < R₁.params.row.openings} {hr₂ : 0 < R₂.params.row.openings}
    {logv₁ logv₂ tA N TM : ℕ}
    {codec₁ : Codec Salt₁ (Col F₁ R₁.params.nw R₁.params.nq) D Enc}
    {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ R₂.params.nw R₂.params.nq) D Enc}
    {dec₂ : RoleDecoders codec₂}
    (S₁ : CircuitSide R₁ h₁ hr₁ logv₁ C F₁ Msg₁ M₁ nt₁ nlin₁ X dec₁ Prod.fst)
    (S₂ : CircuitSide R₂ h₂ hr₂ logv₂ C F₂ Msg₂ M₂ nt₂ nlin₂ X dec₂ Prod.snd)
    (body : TwoOracleTree Enc D
      (Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds
        R₂.params.rounds) C Out tA N)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim R₁.params.row.n Salt₁
      (Col F₁ R₁.params.nw R₁.params.nq) D)
    (claimOf₂ : Out → OpeningClaim R₂.params.row.n Salt₂
      (Col F₂ R₂.params.nw R₂.params.nq) D)
    (common₁ : (Fin S₁.c.ninp → F₁) → Fin nblk → Fmac)
    (common₂ : (Fin S₂.c.ninp → F₂) → Fin nblk → Fmac) : ℚ :=
  ((univ.filter fun ω : (Fin TM → D) ×
        (Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl
          R₁.params.rounds R₂.params.rounds → C) =>
    (S₁.toSide.acceptsDH
        (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
        (check2 codec₁ claimOf₁ codec₂ claimOf₂)
        rootOf₁ msgOf₁ claimOf₁ avOf pubOf (slice1 R₁ R₂) ω.1 ω.2 ∧
    S₂.toSide.acceptsDH
        (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
        (check2 codec₁ claimOf₁ codec₂ claimOf₂)
        rootOf₂ msgOf₂ claimOf₂ avOf pubOf (slice2 R₁ R₂) ω.1 ω.2 ∧
    ω.2 (Sum.inl (rootOf₁
        ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2),
      rootOf₂
        ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2))) =
      avOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2)) ∧
    twoFieldExtract S₁.toSide.toZkSide S₂.toSide.toZkSide common₁ common₂
      (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
        avOf pubOf ω.1 ω.2) = none).card : ℚ) /
    ((Fintype.card D : ℚ) ^ TM * (Fintype.card C : ℚ) ^
      Fintype.card (Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl
        R₁.params.rounds R₂.params.rounds))

/-- Acceptance probability for the same two deployed circuit verifiers and
the explicit key-challenge equality, without an extraction condition. -/
noncomputable def circuitAcceptRatio
    {R₁ R₂ : Row} {h₁ : R₁.Valid} {h₂ : R₂.Valid}
    {hr₁ : 0 < R₁.params.row.openings} {hr₂ : 0 < R₂.params.row.openings}
    {logv₁ logv₂ tA N TM : ℕ}
    {codec₁ : Codec Salt₁ (Col F₁ R₁.params.nw R₁.params.nq) D Enc}
    {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ R₂.params.nw R₂.params.nq) D Enc}
    {dec₂ : RoleDecoders codec₂}
    (S₁ : CircuitSide R₁ h₁ hr₁ logv₁ C F₁ Msg₁ M₁ nt₁ nlin₁ X dec₁ Prod.fst)
    (S₂ : CircuitSide R₂ h₂ hr₂ logv₂ C F₂ Msg₂ M₂ nt₂ nlin₂ X dec₂ Prod.snd)
    (body : TwoOracleTree Enc D
      (Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds
        R₂.params.rounds) C Out tA N)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim R₁.params.row.n Salt₁
      (Col F₁ R₁.params.nw R₁.params.nq) D)
    (claimOf₂ : Out → OpeningClaim R₂.params.row.n Salt₂
      (Col F₂ R₂.params.nw R₂.params.nq) D) : ℚ :=
  ((univ.filter fun ω : (Fin TM → D) ×
        (Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl
          R₁.params.rounds R₂.params.rounds → C) =>
    S₁.toSide.acceptsDH
        (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
        (check2 codec₁ claimOf₁ codec₂ claimOf₂)
        rootOf₁ msgOf₁ claimOf₁ avOf pubOf (slice1 R₁ R₂) ω.1 ω.2 ∧
    S₂.toSide.acceptsDH
        (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
        (check2 codec₁ claimOf₁ codec₂ claimOf₂)
        rootOf₂ msgOf₂ claimOf₂ avOf pubOf (slice2 R₁ R₂) ω.1 ω.2 ∧
    ω.2 (Sum.inl (rootOf₁
        ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2),
      rootOf₂
        ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2))) =
      avOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2)).card : ℚ) /
    ((Fintype.card D : ℚ) ^ TM * (Fintype.card C : ℚ) ^
      Fintype.card (Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl
        R₁.params.rounds R₂.params.rounds))

/-- Acceptance probability restricted to outputs for which `Bad` holds.
This permits the statement to depend on the prover's random-oracle view. -/
noncomputable def circuitBadAcceptRatio
    {R₁ R₂ : Row} {h₁ : R₁.Valid} {h₂ : R₂.Valid}
    {hr₁ : 0 < R₁.params.row.openings} {hr₂ : 0 < R₂.params.row.openings}
    {logv₁ logv₂ tA N TM : ℕ}
    {codec₁ : Codec Salt₁ (Col F₁ R₁.params.nw R₁.params.nq) D Enc}
    {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ R₂.params.nw R₂.params.nq) D Enc}
    {dec₂ : RoleDecoders codec₂}
    (S₁ : CircuitSide R₁ h₁ hr₁ logv₁ C F₁ Msg₁ M₁ nt₁ nlin₁ X dec₁ Prod.fst)
    (S₂ : CircuitSide R₂ h₂ hr₂ logv₂ C F₂ Msg₂ M₂ nt₂ nlin₂ X dec₂ Prod.snd)
    (body : TwoOracleTree Enc D
      (Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds
        R₂.params.rounds) C Out tA N)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim R₁.params.row.n Salt₁
      (Col F₁ R₁.params.nw R₁.params.nq) D)
    (claimOf₂ : Out → OpeningClaim R₂.params.row.n Salt₂
      (Col F₂ R₂.params.nw R₂.params.nq) D)
    (Bad : Out → Prop) : ℚ :=
  ((univ.filter fun ω : (Fin TM → D) ×
        (Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl
          R₁.params.rounds R₂.params.rounds → C) =>
    Bad ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2) ∧
    S₁.toSide.acceptsDH
      (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
      (check2 codec₁ claimOf₁ codec₂ claimOf₂)
      rootOf₁ msgOf₁ claimOf₁ avOf pubOf (slice1 R₁ R₂) ω.1 ω.2 ∧
    S₂.toSide.acceptsDH
      (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
      (check2 codec₁ claimOf₁ codec₂ claimOf₂)
      rootOf₂ msgOf₂ claimOf₂ avOf pubOf (slice2 R₁ R₂) ω.1 ω.2 ∧
    ω.2 (Sum.inl (rootOf₁
        ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2),
      rootOf₂
        ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2))) =
      avOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof ω.1 ω.2)).card : ℚ) /
    ((Fintype.card D : ℚ) ^ TM * (Fintype.card C : ℚ) ^
      Fintype.card (Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl
        R₁.params.rounds R₂.params.rounds))

omit [DecidableEq X] [Field Fmac] [Fintype Fmac] [DecidableEq Fmac]
  [DecidableEq Msg₁] [DecidableEq Msg₂] in
/-- An adaptive false-statement acceptance event is contained in the
committed-pair extraction-failure event. -/
theorem circuitBadAcceptRatio_le_extractionFailureRatio_of_no_pair
    {R₁ R₂ : Row} {h₁ : R₁.Valid} {h₂ : R₂.Valid}
    {hr₁ : 0 < R₁.params.row.openings} {hr₂ : 0 < R₂.params.row.openings}
    {logv₁ logv₂ tA N TM : ℕ}
    {codec₁ : Codec Salt₁ (Col F₁ R₁.params.nw R₁.params.nq) D Enc}
    {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ R₂.params.nw R₂.params.nq) D Enc}
    {dec₂ : RoleDecoders codec₂}
    (S₁ : CircuitSide R₁ h₁ hr₁ logv₁ C F₁ Msg₁ M₁ nt₁ nlin₁ X dec₁ Prod.fst)
    (S₂ : CircuitSide R₂ h₂ hr₂ logv₂ C F₂ Msg₂ M₂ nt₂ nlin₂ X dec₂ Prod.snd)
    (body : TwoOracleTree Enc D
      (Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds
        R₂.params.rounds) C Out tA N)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim R₁.params.row.n Salt₁
      (Col F₁ R₁.params.nw R₁.params.nq) D)
    (claimOf₂ : Out → OpeningClaim R₂.params.row.n Salt₂
      (Col F₂ R₂.params.nw R₂.params.nq) D)
    (common₁ : (Fin S₁.c.ninp → F₁) → Fin nblk → Fmac)
    (common₂ : (Fin S₂.c.ninp → F₂) → Fin nblk → Fmac)
    (Bad : Out → Prop)
    (hno : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl
          R₁.params.rounds R₂.params.rounds → C),
      Bad ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof mt ro) →
      ¬ ∃ a₁ a₂,
        S₁.toSide.toZkSide.Good
          (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            avOf pubOf mt ro) a₁ ∧
        S₂.toSide.toZkSide.Good
          (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            avOf pubOf mt ro) a₂ ∧ common₁ a₁ = common₂ a₂) :
    circuitBadAcceptRatio (TM := TM) S₁ S₂ body rootOf₁ rootOf₂ avOf pubOf
      msgOf₁ msgOf₂ claimOf₁ claimOf₂ Bad ≤
    circuitExtractionFailureRatio (TM := TM) S₁ S₂ body rootOf₁ rootOf₂
      avOf pubOf msgOf₁ msgOf₂ claimOf₁ claimOf₂ common₁ common₂ := by
  unfold circuitBadAcceptRatio circuitExtractionFailureRatio
  apply div_le_div_of_nonneg_right (by
    exact_mod_cast (Finset.card_le_card (by
      intro ω hω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hω ⊢
      exact ⟨hω.2, (twoFieldExtract_none_iff
        S₁.toSide.toZkSide S₂.toSide.toZkSide common₁ common₂ _).2
          (hno ω.1 ω.2 hω.1)⟩)))
  positivity

omit [DecidableEq X] [Field Fmac] [Fintype Fmac] [DecidableEq Fmac]
  [DecidableEq Msg₁] [DecidableEq Msg₂] in
/-- Soundness is a direct corollary of extraction when no agreeing pair of
satisfying circuit witnesses exists at any transcript context. -/
theorem circuitAcceptRatio_eq_extractionFailureRatio_of_no_pair
    {R₁ R₂ : Row} {h₁ : R₁.Valid} {h₂ : R₂.Valid}
    {hr₁ : 0 < R₁.params.row.openings} {hr₂ : 0 < R₂.params.row.openings}
    {logv₁ logv₂ tA N TM : ℕ}
    {codec₁ : Codec Salt₁ (Col F₁ R₁.params.nw R₁.params.nq) D Enc}
    {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ R₂.params.nw R₂.params.nq) D Enc}
    {dec₂ : RoleDecoders codec₂}
    (S₁ : CircuitSide R₁ h₁ hr₁ logv₁ C F₁ Msg₁ M₁ nt₁ nlin₁ X dec₁ Prod.fst)
    (S₂ : CircuitSide R₂ h₂ hr₂ logv₂ C F₂ Msg₂ M₂ nt₂ nlin₂ X dec₂ Prod.snd)
    (body : TwoOracleTree Enc D
      (Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds
        R₂.params.rounds) C Out tA N)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim R₁.params.row.n Salt₁
      (Col F₁ R₁.params.nw R₁.params.nq) D)
    (claimOf₂ : Out → OpeningClaim R₂.params.row.n Salt₂
      (Col F₂ R₂.params.nw R₂.params.nq) D)
    (common₁ : (Fin S₁.c.ninp → F₁) → Fin nblk → Fmac)
    (common₂ : (Fin S₂.c.ninp → F₂) → Fin nblk → Fmac)
    (hno : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl
          R₁.params.rounds R₂.params.rounds → C),
      ¬ ∃ a₁ a₂,
        S₁.toSide.toZkSide.Good
          (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            avOf pubOf mt ro) a₁ ∧
        S₂.toSide.toZkSide.Good
          (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            avOf pubOf mt ro) a₂ ∧ common₁ a₁ = common₂ a₂) :
    circuitAcceptRatio (TM := TM) S₁ S₂ body rootOf₁ rootOf₂ avOf pubOf
      msgOf₁ msgOf₂ claimOf₁ claimOf₂ =
    circuitExtractionFailureRatio (TM := TM) S₁ S₂ body rootOf₁ rootOf₂
      avOf pubOf msgOf₁ msgOf₂ claimOf₁ claimOf₂ common₁ common₂ := by
  unfold circuitAcceptRatio circuitExtractionFailureRatio
  congr 1
  congr 1
  apply congrArg Finset.card
  apply Finset.filter_congr
  intro ω _
  constructor
  · intro ha
    exact ⟨ha, (twoFieldExtract_none_iff
      S₁.toSide.toZkSide S₂.toSide.toZkSide common₁ common₂ _).2
        (hno ω.1 ω.2)⟩
  · exact And.left

omit [DecidableEq X] [DecidableEq Msg₁] [DecidableEq Msg₂] in
/-- Extraction-first graded FS bound for two certified circuit sides. -/
theorem twofield_circuit_potential_extraction
    {R₁ R₂ : Row} (h₁ : R₁.Valid) (h₂ : R₂.Valid)
    (hr₁ : 0 < R₁.params.row.openings) (hr₂ : 0 < R₂.params.row.openings)
    {logv₁ logv₂ tA N TM : ℕ}
    {codec₁ : Codec Salt₁ (Col F₁ R₁.params.nw R₁.params.nq) D Enc}
    {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ R₂.params.nw R₂.params.nq) D Enc}
    {dec₂ : RoleDecoders codec₂}
    (S₁ : CircuitSide R₁ h₁ hr₁ logv₁ C F₁ Msg₁ M₁ nt₁ nlin₁ X dec₁ Prod.fst)
    (S₂ : CircuitSide R₂ h₂ hr₂ logv₂ C F₂ Msg₂ M₂ nt₂ nlin₂ X dec₂ Prod.snd)
    (ψ₁ : LigeroFamily.PotentialProfile.Curve R₁.params.row.n)
    (ψ₂ : LigeroFamily.PotentialProfile.Curve R₂.params.row.n)
    (body : TwoOracleTree Enc D
      (Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl R₁.params.rounds
        R₂.params.rounds) C Out tA N)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim R₁.params.row.n Salt₁
      (Col F₁ R₁.params.nw R₁.params.nq) D)
    (claimOf₂ : Out → OpeningClaim R₂.params.row.n Salt₂
      (Col F₂ R₂.params.nw R₂.params.nq) D)
    (aP : (D × D) × List (Enc × D) → Fmac) (decode : C → Fmac)
    (kmac : ℕ)
    (hbal : ∀ x : Fmac, (univ.filter fun c : C => decode c = x).card ≤ kmac)
    (tagOf : Out → Fin nblk → Fmac)
    (common₁ : (Fin S₁.c.ninp → F₁) → Fin nblk → Fmac)
    (common₂ : (Fin S₂.c.ninp → F₂) → Fin nblk → Fmac)
    (mac₁ : (Fin S₁.c.ninp → F₁) → Fmac → Fin nblk → Fmac)
    (mac₂ : (Fin S₂.c.ninp → F₂) → Fmac → Fin nblk → Fmac)
    (hcoll : ∀ a₁ a₂, common₁ a₁ ≠ common₂ a₂ →
      (univ.filter fun x => mac₁ a₁ x = mac₂ a₂ x).card ≤ 1)
    (b₁c b₁q b₂c b₂q : ℚ)
    (h₁c : Lfzk.GradedCost.challenge R₁ ψ₁ ≤ b₁c)
    (h₁q : Lfzk.GradedCost.query R₁ ψ₁ ≤ b₁q)
    (h₂c : Lfzk.GradedCost.challenge R₂ ψ₂ ≤ b₂c)
    (h₂q : Lfzk.GradedCost.query R₂ ψ₂ ≤ b₂q)
    (hrow₁ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl
          R₁.params.rounds R₂.params.rounds → C)
        (a : Fin S₁.c.ninp → F₁),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      S₁.toSide.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂)
        rootOf₁ msgOf₁ claimOf₁ avOf pubOf (slice1 R₁ R₂) mt ro →
      S₁.toSide.Good (sideCtx S avOf pubOf mt ro) a →
      mac₁ a (aP (S.context mt ro) + decode (avOf (S.proof mt ro))) =
        tagOf (S.proof mt ro))
    (hrow₂ : ∀ (mt : Fin TM → D)
        (ro : Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl
          R₁.params.rounds R₂.params.rounds → C)
        (a : Fin S₂.c.ninp → F₂),
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      S₂.toSide.acceptsDH S (check2 codec₁ claimOf₁ codec₂ claimOf₂)
        rootOf₂ msgOf₂ claimOf₂ avOf pubOf (slice2 R₁ R₂) mt ro →
      S₂.toSide.Good (sideCtx S avOf pubOf mt ro) a →
      mac₂ a (aP (S.context mt ro) + decode (avOf (S.proof mt ro))) =
        tagOf (S.proof mt ro))
    (htape : 2 * R₂.params.row.n + 2 * R₁.params.row.n + tA ≤ TM)
    (hTM : 0 < TM) :
    circuitExtractionFailureRatio (TM := TM) S₁ S₂ body rootOf₁ rootOf₂ avOf pubOf
      msgOf₁ msgOf₂ claimOf₁ claimOf₂ common₁ common₂ ≤
      gradedCombinedBudget R₁ R₂ logv₁ logv₂ (Fintype.card C) N
        (R₁.cardCand * R₂.cardCand * kmac : ℚ) b₁c b₁q b₂c b₂q +
      2 * (Bcs.AdaptiveCommit.adaptiveNumerator
        (2 * R₂.params.row.n + 2 * R₁.params.row.n) tA
        (len2 R₁ R₂ + N) : ℚ) / Fintype.card D := by
  let Acc : (Fin TM → D) →
      (Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl
        R₁.params.rounds R₂.params.rounds → C) → Prop := fun mt ro =>
    S₁.toSide.acceptsDH
        (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
        (check2 codec₁ claimOf₁ codec₂ claimOf₂)
        rootOf₁ msgOf₁ claimOf₁ avOf pubOf (slice1 R₁ R₂) mt ro ∧
    S₂.toSide.acceptsDH
        (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
        (check2 codec₁ claimOf₁ codec₂ claimOf₂)
        rootOf₂ msgOf₂ claimOf₂ avOf pubOf (slice2 R₁ R₂) mt ro ∧
    ro (Sum.inl (rootOf₁
        ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof mt ro),
      rootOf₂
        ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof mt ro))) =
      avOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof mt ro)
  have h := compiled_twoFieldPotential_fs_extraction_budgeted
    h₁ h₂ hr₁ hr₂ S₁.toSide S₂.toSide ψ₁ ψ₂ body
    rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ claimOf₁ claimOf₂
    S₁.cands S₂.cands S₁.cands_card_le S₂.cands_card_le
    S₁.good_mem_cands S₂.good_mem_cands
    common₁ common₂ mac₁ mac₂ hcoll aP decode tagOf hbal
    b₁c b₁q b₂c b₂q h₁c h₁q h₂c h₂q
    (Classical.choice ‹Nonempty C›) htape hTM Acc
    (fun _ _ ha => ha.1)
    (fun _ _ ha => ha.2.1)
    (fun _ _ ha => ha.2.2)
    (fun mt ro ha a hg => hrow₁ mt ro a ha.1 hg)
    (fun mt ro ha a hg => hrow₂ mt ro a ha.2.1 hg)
  simpa only [circuitExtractionFailureRatio, Acc, len2, Nat.cast_mul] using h

end Circuit

end Lfzk.CompiledZkProfileRows
