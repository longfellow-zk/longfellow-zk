import Lfzk.RbrZkPotentialFS
import Lfzk.CompiledZkPotential
import Lfzk.CompiledZkDeployedHash

/-!
# Compiled extraction-first Fiat--Shamir obligations

These lemmas connect the compiled side verifier to the graded two-field
potential.  The concrete acceptance predicate includes both side verifiers
and the MAC-key challenge read from the deployed hash input.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.CompiledZkDeployedHash

open Finset Bcs Merkle Merkle.MH Merkle.RandomOracle
  Merkle.RandomOracle.TwoOracleTree Lfzk.CompiledZk Lfzk.CertifiedV1
  Lfzk.NizkZk Lfzk.NizkZkTwoField Lfzk.NizkZkDeployedHash
  Lfzk.NizkDeployedHash Lfzk.NizkDeployedHashTwoField Lfzk.MacSep
open Lfzk.CompiledLongfellow (Col)
open Lfzk.CompiledLongfellowAdaptive (slice1 slice2)
open Lfzk.NizkAdaptiveTwoField (check2)
open scoped Classical

section Pair

variable {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]
variable {D : Type} [Fintype D] [DecidableEq D] [Inhabited D]
variable {Enc X Out : Type} [DecidableEq Enc] [Fintype X] [DecidableEq X]
variable {Fmac : Type} [Field Fmac] [Fintype Fmac] [DecidableEq Fmac] {nblk : ℕ}
variable {F₁ Msg₁ Witness₁ : Type} [Field F₁] [Fintype F₁] [DecidableEq F₁]
  [SumcheckInterp F₁] [DecidableEq Msg₁] [Inhabited Msg₁] [Fintype Msg₁]
  {M₁ ninp₁ nt₁ nlin₁ logw₁ logc₁ : ℕ}
variable {F₂ Msg₂ Witness₂ : Type} [Field F₂] [Fintype F₂] [DecidableEq F₂]
  [SumcheckInterp F₂] [DecidableEq Msg₂] [Inhabited Msg₂] [Fintype Msg₂]
  {M₂ ninp₂ nt₂ nlin₂ logw₂ logc₂ : ℕ}
variable {Salt₁ Salt₂ : Type} [Inhabited Salt₁] [Inhabited Salt₂]

omit [DecidableEq C] [Fintype D] [Fintype X] [DecidableEq X]
  [DecidableEq Msg₁] [Fintype Msg₁] [DecidableEq Msg₂] [Fintype Msg₂] in
/-- Failure of the committed-pair extractor, together with both accepted MAC
rows, pays at the deployed key hash input.  The candidates are functions of
the commitment context, so the event is local in the key answer. -/
theorem compiled_keyBad_of_extract_none
    {R₁ R₂ : Row} (h₁ : R₁.Valid) (h₂ : R₂.Valid)
    (hr₁ : 0 < R₁.params.row.openings) (hr₂ : 0 < R₂.params.row.openings)
    {logv₁ logv₂ tA N TM : ℕ}
    {codec₁ : Codec Salt₁ (Col F₁ R₁.params.nw R₁.params.nq) D Enc}
    {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ R₂.params.nw R₂.params.nq) D Enc}
    {dec₂ : RoleDecoders codec₂}
    (L₁ : CompiledZkSide R₁ h₁ hr₁ logv₁ C F₁ Msg₁ Witness₁
      M₁ ninp₁ nt₁ nlin₁ logw₁ logc₁ X dec₁ Prod.fst)
    (L₂ : CompiledZkSide R₂ h₂ hr₂ logv₂ C F₂ Msg₂ Witness₂
      M₂ ninp₂ nt₂ nlin₂ logw₂ logc₂ X dec₂ Prod.snd)
    (body : TwoOracleTree Enc D
      (Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl
        R₁.params.rounds R₂.params.rounds) C Out tA N)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (aP : (D × D) × List (Enc × D) → Fmac) (decode : C → Fmac)
    (tagOf : Out → Fin nblk → Fmac)
    (common₁ : Witness₁ → Fin nblk → Fmac)
    (common₂ : Witness₂ → Fin nblk → Fmac)
    (mac₁ : Witness₁ → Fmac → Fin nblk → Fmac)
    (mac₂ : Witness₂ → Fmac → Fin nblk → Fmac)
    (cands₁ : (D × D) × List (Enc × D) → Finset Witness₁)
    (cands₂ : (D × D) × List (Enc × D) → Finset Witness₂)
    (hcands₁ : ∀ σ a, L₁.Good σ a → a ∈ cands₁ σ.1)
    (hcands₂ : ∀ σ a, L₂.Good σ a → a ∈ cands₂ σ.1)
    (mt : Fin TM → D)
    (ro : Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl
      R₁.params.rounds R₂.params.rounds → C)
    (hrow₁ : ∀ a : Witness₁,
      L₁.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
        avOf pubOf mt ro) a →
      mac₁ a (aP ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).context mt ro) +
        decode (avOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof mt ro))) =
        tagOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof mt ro))
    (hrow₂ : ∀ a : Witness₂,
      L₂.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
        avOf pubOf mt ro) a →
      mac₂ a (aP ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).context mt ro) +
        decode (avOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof mt ro))) =
        tagOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof mt ro))
    (hav :
      ro (Sum.inl (rootOf₁
        ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof mt ro),
        rootOf₂ ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof mt ro))) =
      avOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof mt ro))
    (hfail :
      twoFieldExtract L₁.toZkSide L₂.toZkSide common₁ common₂
        (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
          avOf pubOf mt ro) = none)
    (hgood₁ : ¬ ZkFails L₁.toZkSide.Sat
      (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
        avOf pubOf mt ro))
    (hgood₂ : ¬ ZkFails L₂.toZkSide.Sat
      (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
        avOf pubOf mt ro)) :
    let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
    SepMacBad (cands₁ (S.context mt ro)) (cands₂ (S.context mt ro))
      common₁ common₂ mac₁ mac₂
      (aP (S.context mt ro) +
        decode (ro (Sum.inl (rootOf₁ (S.proof mt ro), rootOf₂ (S.proof mt ro))))) := by
  let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
  let σ := sideCtx S avOf pubOf mt ro
  have hc₁ : ∀ a, L₁.toZkSide.Good σ a → a ∈ cands₁ σ.1 := by
    intro a ha
    exact hcands₁ σ a ha
  have hc₂ : ∀ a, L₂.toZkSide.Good σ a → a ∈ cands₂ σ.1 := by
    intro a ha
    exact hcands₂ σ a ha
  have hb := twoFieldMacKey_of_extract_none L₁.toZkSide L₂.toZkSide
    cands₁ cands₂ common₁ common₂ mac₁ mac₂ aP decode
    (tagOf (S.proof mt ro)) σ (avOf (S.proof mt ro)) hc₁ hc₂
    hrow₁ hrow₂
    hfail hgood₁ hgood₂
  dsimp only
  rw [hav]
  exact hb

/-! The remaining constructor packages the compiled side's Merkle and
LayerStep implications for the generic potential compiler. -/

private abbrev PairPoint (D C X Msg₁ Msg₂ : Type)
    (R₁ R₂ : Row) :=
  Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl
    R₁.params.rounds R₂.params.rounds

omit [DecidableEq C] [Nonempty C] [Fintype D] [Fintype X]
  [DecidableEq X] [DecidableEq Msg₁] [Fintype Msg₁]
  [DecidableEq Msg₂] [Fintype Msg₂] in
/-- The checked row/curve densities, exact decoder balance, and fixed
candidate-pair MAC count discharge the generic merged local-charge premise. -/
theorem compiled_twoFieldPotential_local
    {R₁ R₂ : Row} (h₁ : R₁.Valid) (h₂ : R₂.Valid)
    (hr₁ : 0 < R₁.params.row.openings) (hr₂ : 0 < R₂.params.row.openings)
    {logv₁ logv₂ : ℕ}
    {codec₁ : Codec Salt₁ (Col F₁ R₁.params.nw R₁.params.nq) D Enc}
    {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ R₂.params.nw R₂.params.nq) D Enc}
    {dec₂ : RoleDecoders codec₂}
    (L₁ : CompiledZkSide R₁ h₁ hr₁ logv₁ C F₁ Msg₁ Witness₁
      M₁ ninp₁ nt₁ nlin₁ logw₁ logc₁ X dec₁ Prod.fst)
    (L₂ : CompiledZkSide R₂ h₂ hr₂ logv₂ C F₂ Msg₂ Witness₂
      M₂ ninp₂ nt₂ nlin₂ logw₂ logc₂ X dec₂ Prod.snd)
    (ψ₁ : LigeroFamily.PotentialProfile.Curve R₁.params.row.n)
    (ψ₂ : LigeroFamily.PotentialProfile.Curve R₂.params.row.n)
    {B₁ B₂ kmac : ℕ}
    (cands₁ : (D × D) × List (Enc × D) → Finset Witness₁)
    (cands₂ : (D × D) × List (Enc × D) → Finset Witness₂)
    (hcard₁ : ∀ κ, (cands₁ κ).card ≤ B₁)
    (hcard₂ : ∀ κ, (cands₂ κ).card ≤ B₂)
    (common₁ : Witness₁ → Fin nblk → Fmac)
    (common₂ : Witness₂ → Fin nblk → Fmac)
    (mac₁ : Witness₁ → Fmac → Fin nblk → Fmac)
    (mac₂ : Witness₂ → Fmac → Fin nblk → Fmac)
    (hcoll : ∀ a₁ a₂, common₁ a₁ ≠ common₂ a₂ →
      (univ.filter fun x => mac₁ a₁ x = mac₂ a₂ x).card ≤ 1)
    (aP : (D × D) × List (Enc × D) → Fmac) (decode : C → Fmac)
    (hbal : ∀ x : Fmac,
      (univ.filter fun c : C => decode c = x).card ≤ kmac)
    (b₁c b₁q b₂c b₂q : ℚ)
    (h₁c : Lfzk.GradedCost.challenge R₁ ψ₁ ≤ b₁c)
    (h₁q : Lfzk.GradedCost.query R₁ ψ₁ ≤ b₁q)
    (h₂c : Lfzk.GradedCost.challenge R₂ ψ₂ ≤ b₂c)
    (h₂q : Lfzk.GradedCost.query R₂ ψ₂ ≤ b₂q)
    (dflt : C)
    (κ : (D × D) × List (Enc × D))
    (p : PairPoint D C X Msg₁ Msg₂ R₁ R₂)
    (pref : Fin (pts2.slot p) → C) :
    (∑ c : C, twoFieldPotentialCharge L₁.toZkSide L₂.toZkSide
      (fun σ => L₁.terminalPotential σ ψ₁)
      (fun σ => L₂.terminalPotential σ ψ₂)
      (fun κ c => SepMacBad (cands₁ κ) (cands₂ κ)
        common₁ common₂ mac₁ mac₂ (aP κ + decode c))
      dflt κ p pref c) ≤
    twoFieldPotentialBudget (B₁ * B₂ * kmac : ℚ)
      (Lfzk.RbrZkFlat.sideUniformPotentialBudget (R := R₁)
        (logv := logv₁) (C := C)
        (max 0 ((Fintype.card C : ℚ) * b₁c))
        (max 0 ((Fintype.card C : ℚ) * b₁q)))
      (Lfzk.RbrZkFlat.sideUniformPotentialBudget (R := R₂)
        (logv := logv₂) (C := C)
        (max 0 ((Fintype.card C : ℚ) * b₂c))
        (max 0 ((Fintype.card C : ℚ) * b₂q))) p := by
  exact twoFieldPotentialCharge_local_of_sides L₁.toZkSide L₂.toZkSide
    L₁.hF L₂.hF
    (fun σ => L₁.terminalPotential σ ψ₁)
    (fun σ => L₂.terminalPotential σ ψ₂)
    (fun κ c => SepMacBad (cands₁ κ) (cands₂ κ)
      common₁ common₂ mac₁ mac₂ (aP κ + decode c)) dflt
    (B₁ * B₂ * kmac : ℚ)
    (fun κ => twoFieldMacKey_local
      cands₁ cands₂ hcard₁ hcard₂ common₁ common₂ mac₁ mac₂
      hcoll aP decode hbal κ)
    (max 0 ((Fintype.card C : ℚ) * b₁c))
    (max 0 ((Fintype.card C : ℚ) * b₁q))
    (max 0 ((Fintype.card C : ℚ) * b₂c))
    (max 0 ((Fintype.card C : ℚ) * b₂q))
    (le_max_left _ _) (le_max_left _ _)
    (le_max_left _ _) (le_max_left _ _)
    (fun σ => L₁.terminalPotential_challengeBudget_le_bound σ ψ₁ b₁c h₁c)
    (fun σ => L₁.terminalPotential_queryBudget_le_bound σ ψ₁ b₁q h₁q)
    (fun σ => L₂.terminalPotential_challengeBudget_le_bound σ ψ₂ b₂c h₂c)
    (fun σ => L₂.terminalPotential_queryBudget_le_bound σ ψ₂ b₂q h₂q)
    κ p pref

omit [DecidableEq C] [DecidableEq X]
  [DecidableEq Msg₁] [DecidableEq Msg₂] in
/-- Extraction-first FS bound at two compiled V1 side verifiers.  The
agreement curves and their local budgets are explicit parameters; accepted
compiled sides discharge the Merkle and layer-chain premises. -/
theorem compiled_twoFieldPotential_fs_extraction
    {R₁ R₂ : Row} (h₁ : R₁.Valid) (h₂ : R₂.Valid)
    (hr₁ : 0 < R₁.params.row.openings) (hr₂ : 0 < R₂.params.row.openings)
    {logv₁ logv₂ tA N TM : ℕ}
    {codec₁ : Codec Salt₁ (Col F₁ R₁.params.nw R₁.params.nq) D Enc}
    {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ R₂.params.nw R₂.params.nq) D Enc}
    {dec₂ : RoleDecoders codec₂}
    (L₁ : CompiledZkSide R₁ h₁ hr₁ logv₁ C F₁ Msg₁ Witness₁
      M₁ ninp₁ nt₁ nlin₁ logw₁ logc₁ X dec₁ Prod.fst)
    (L₂ : CompiledZkSide R₂ h₂ hr₂ logv₂ C F₂ Msg₂ Witness₂
      M₂ ninp₂ nt₂ nlin₂ logw₂ logc₂ X dec₂ Prod.snd)
    (body : TwoOracleTree Enc D (PairPoint D C X Msg₁ Msg₂ R₁ R₂) C Out tA N)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim R₁.params.row.n Salt₁
      (Col F₁ R₁.params.nw R₁.params.nq) D)
    (claimOf₂ : Out → OpeningClaim R₂.params.row.n Salt₂
      (Col F₂ R₂.params.nw R₂.params.nq) D)
    (P₁ : ∀ σ, Lfzk.RbrZkFlat.TerminalPotential (L₁.toZkSide.LD σ))
    (P₂ : ∀ σ, Lfzk.RbrZkFlat.TerminalPotential (L₂.toZkSide.LD σ))
    (keyBad : ((D × D) × List (Enc × D)) → C → Prop) (dflt : C)
    (budget : PairPoint D C X Msg₁ Msg₂ R₁ R₂ → ℚ)
    (hbudget : ∀ p, 0 ≤ budget p)
    (hlocal : ∀ κ p pref,
      (∑ c : C, twoFieldPotentialCharge L₁.toZkSide L₂.toZkSide
        P₁ P₂ keyBad dflt κ p pref c) ≤ budget p)
    (betaMax : ℚ) (hbetaMax : 0 ≤ betaMax)
    (hmax : ∀ p, budget p ≤ betaMax)
    (slotBeta : Fin (1 + Rounds.Role.length R₁.params.nl R₁.params.rounds +
      Rounds.Role.length R₂.params.nl R₂.params.rounds) → ℚ)
    (hslot : ∀ out i,
      budget (hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out i.val) ≤
        slotBeta i)
    (htape : 2 * R₂.params.row.n + 2 * R₁.params.row.n + tA ≤ TM)
    (hTM : 0 < TM)
    (Acc : (Fin TM → D) → (PairPoint D C X Msg₁ Msg₂ R₁ R₂ → C) → Prop)
    {Witness : Type}
    (extract : (Fin TM → D) → (PairPoint D C X Msg₁ Msg₂ R₁ R₂ → C) →
      Option Witness)
    (haccept₁ : ∀ mt ro, Acc mt ro →
      L₁.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
        (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁
        avOf pubOf (slice1 R₁ R₂) mt ro)
    (haccept₂ : ∀ mt ro, Acc mt ro →
      L₂.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
        (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂
        avOf pubOf (slice2 R₁ R₂) mt ro)
    (hkey : ∀ mt ro, Acc mt ro → extract mt ro = none →
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      let out := S.proof mt ro
      let σ := (S.context mt ro, avOf out, pubOf out)
      ¬ ZkFails L₁.toZkSide.Sat σ → ¬ ZkFails L₂.toZkSide.Sat σ →
        keyBad (S.context mt ro)
          (ro (Sum.inl (rootOf₁ out, rootOf₂ out)))) :
    ((univ.filter fun ω : (Fin TM → D) ×
          (PairPoint D C X Msg₁ Msg₂ R₁ R₂ → C) =>
      Acc ω.1 ω.2 ∧ extract ω.1 ω.2 = none).card : ℚ) /
      ((Fintype.card D : ℚ) ^ TM *
        (Fintype.card C : ℚ) ^
          Fintype.card (PairPoint D C X Msg₁ Msg₂ R₁ R₂)) ≤
      (N * betaMax + ∑ i, slotBeta i) / Fintype.card C +
        2 * (Bcs.AdaptiveCommit.adaptiveNumerator
          (2 * R₂.params.row.n + 2 * R₁.params.row.n) tA
          (1 + Rounds.Role.length R₁.params.nl R₁.params.rounds +
            Rounds.Role.length R₂.params.nl R₂.params.rounds + N) : ℚ) /
          Fintype.card D := by
  let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
  have hcheck₁ : ∀ (H : Enc → D) (out : Out),
      ∀ qa ∈ ((checkPass codec₁ R₁.params.row.n (claimOf₁ out).I
          (claimOf₁ out).a (claimOf₁ out).pf (2 * R₁.params.row.n)
          fun _ => default).run H).2,
        qa ∈ ((check2 codec₁ claimOf₁ codec₂ claimOf₂ out).run H).2 := by
    intro H out qa hqa
    rw [check2, Tree.run_bind]
    exact List.mem_append_left _
      (Lfzk.NizkAdaptive.lfCheck_trace codec₁ claimOf₁ H out qa hqa)
  have hcheck₂ : ∀ (H : Enc → D) (out : Out),
      ∀ qa ∈ ((checkPass codec₂ R₂.params.row.n (claimOf₂ out).I
          (claimOf₂ out).a (claimOf₂ out).pf (2 * R₂.params.row.n)
          fun _ => default).run H).2,
        qa ∈ ((check2 codec₁ claimOf₁ codec₂ claimOf₂ out).run H).2 := by
    intro H out qa hqa
    rw [check2, Tree.run_bind]
    exact List.mem_append_right _
      (Lfzk.NizkAdaptive.lfCheck_trace codec₂ claimOf₂ H out qa hqa)
  have hroot₁ : ∀ out, Prod.fst (S.keyOut out) = rootOf₁ out := fun _ => rfl
  have hroot₂ : ∀ out, Prod.snd (S.keyOut out) = rootOf₂ out := fun _ => rfl
  have hm₁ : ∀ mt ro, Acc mt ro →
      S.MerkleAccepts codec₁ (check2 codec₁ claimOf₁ codec₂ claimOf₂)
        Prod.fst claimOf₁ mt ro := by
    intro mt ro ha
    exact L₁.acceptsDH_merkle S _ rootOf₁ hroot₁ msgOf₁ claimOf₁
      avOf pubOf (slice1 R₁ R₂) mt ro (haccept₁ mt ro ha)
  have hm₂ : ∀ mt ro, Acc mt ro →
      S.MerkleAccepts codec₂ (check2 codec₁ claimOf₁ codec₂ claimOf₂)
        Prod.snd claimOf₂ mt ro := by
    intro mt ro ha
    exact L₂.acceptsDH_merkle S _ rootOf₂ hroot₂ msgOf₂ claimOf₂
      avOf pubOf (slice2 R₁ R₂) mt ro (haccept₂ mt ro ha)
  have hs₁ : ∀ mt ro, Acc mt ro → S.Explains dec₁ Prod.fst claimOf₁ mt ro →
      let out := S.proof mt ro
      let σ := (S.context mt ro, avOf out, pubOf out)
      Lfzk.RbrZkSplit.ZkLayerStepAccepts .accepted .start
        (Lfzk.RbrZkSplit.steps (nl := R₁.params.nl) (w := R₁.params.rounds)
          (L₁.toZkSide.V σ) (L₁.toZkSide.LD σ) (msgOf₁ out))
        (fun i => ro (Sum.inr (Sum.inl (msgPoint
          (ctxOf rootOf₁ rootOf₂ avOf pubOf out) msgOf₁ out i.val)))) := by
    intro mt ro ha hexp
    have hh := L₁.hrightDH_of_accepts S _ rootOf₁ hroot₁ msgOf₁
      claimOf₁ avOf pubOf (slice1 R₁ R₂) mt ro (haccept₁ mt ro ha) hexp
    dsimp only
    dsimp only [sideCtx] at hh
    convert hh using 1
    funext i
    symm
    change S.challenges mt ro
      ⟨1 + i.val, by omega⟩ = ro (Sum.inr (Sum.inl
        (msgPoint (ctxOf rootOf₁ rootOf₂ avOf pubOf (S.proof mt ro))
          msgOf₁ (S.proof mt ro) i.val)))
    change ro (hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      (S.proof mt ro) (1 + i.val)) = _
    rw [hash2_side1]
    all_goals omega
  have hs₂ : ∀ mt ro, Acc mt ro → S.Explains dec₂ Prod.snd claimOf₂ mt ro →
      let out := S.proof mt ro
      let σ := (S.context mt ro, avOf out, pubOf out)
      Lfzk.RbrZkSplit.ZkLayerStepAccepts .accepted .start
        (Lfzk.RbrZkSplit.steps (nl := R₂.params.nl) (w := R₂.params.rounds)
          (L₂.toZkSide.V σ) (L₂.toZkSide.LD σ) (msgOf₂ out))
        (fun i => ro (Sum.inr (Sum.inr (msgPoint
          (ctxOf rootOf₁ rootOf₂ avOf pubOf out,
            fun j : Fin (Rounds.Role.length R₁.params.nl R₁.params.rounds) =>
              msgOf₁ out j.val) msgOf₂ out i.val)))) := by
    intro mt ro ha hexp
    have hh := L₂.hrightDH_of_accepts S _ rootOf₂ hroot₂ msgOf₂
      claimOf₂ avOf pubOf (slice2 R₁ R₂) mt ro (haccept₂ mt ro ha) hexp
    dsimp only
    dsimp only [sideCtx] at hh
    convert hh using 1
    funext i
    symm
    change S.challenges mt ro
      ⟨1 + Rounds.Role.length R₁.params.nl R₁.params.rounds + i.val,
        by omega⟩ = ro (Sum.inr (Sum.inr
        (msgPoint
          (ctxOf rootOf₁ rootOf₂ avOf pubOf (S.proof mt ro),
            fun j : Fin (Rounds.Role.length R₁.params.nl R₁.params.rounds) =>
              msgOf₁ (S.proof mt ro) j.val)
          msgOf₂ (S.proof mt ro) i.val)))
    change ro (hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      (S.proof mt ro)
      (1 + Rounds.Role.length R₁.params.nl R₁.params.rounds + i.val)) = _
    rw [hash2_side2]
  exact twoFieldPotential_fs_extraction body rootOf₁ rootOf₂ avOf pubOf
    msgOf₁ msgOf₂ L₁.toZkSide L₂.toZkSide P₁ P₂ keyBad dflt
    codec₁ dec₁ codec₂ dec₂ (check2 codec₁ claimOf₁ codec₂ claimOf₂)
    claimOf₁ claimOf₂ hcheck₁ hcheck₂ budget hbudget hlocal
    betaMax hbetaMax hmax slotBeta hslot
    (by omega) (by omega) hTM Acc extract hm₁ hm₂ hkey hs₁ hs₂

omit [DecidableEq C] [DecidableEq X]
  [DecidableEq Msg₁] [DecidableEq Msg₂] in
/-- The graded extraction bound with the actual role-schedule sum, rather
than separately supplied bounds for every transcript hash input.  The four
terminal densities are measured per field challenge; the key count is the
number of colliding committed candidate pairs times decoder multiplicity. -/
theorem compiled_twoFieldPotential_fs_extraction_budgeted
    {R₁ R₂ : Row} (h₁ : R₁.Valid) (h₂ : R₂.Valid)
    (hr₁ : 0 < R₁.params.row.openings) (hr₂ : 0 < R₂.params.row.openings)
    {logv₁ logv₂ tA N TM : ℕ}
    {codec₁ : Codec Salt₁ (Col F₁ R₁.params.nw R₁.params.nq) D Enc}
    {dec₁ : RoleDecoders codec₁}
    {codec₂ : Codec Salt₂ (Col F₂ R₂.params.nw R₂.params.nq) D Enc}
    {dec₂ : RoleDecoders codec₂}
    (L₁ : CompiledZkSide R₁ h₁ hr₁ logv₁ C F₁ Msg₁ Witness₁
      M₁ ninp₁ nt₁ nlin₁ logw₁ logc₁ X dec₁ Prod.fst)
    (L₂ : CompiledZkSide R₂ h₂ hr₂ logv₂ C F₂ Msg₂ Witness₂
      M₂ ninp₂ nt₂ nlin₂ logw₂ logc₂ X dec₂ Prod.snd)
    (ψ₁ : LigeroFamily.PotentialProfile.Curve R₁.params.row.n)
    (ψ₂ : LigeroFamily.PotentialProfile.Curve R₂.params.row.n)
    (body : TwoOracleTree Enc D (PairPoint D C X Msg₁ Msg₂ R₁ R₂) C Out tA N)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (claimOf₁ : Out → OpeningClaim R₁.params.row.n Salt₁
      (Col F₁ R₁.params.nw R₁.params.nq) D)
    (claimOf₂ : Out → OpeningClaim R₂.params.row.n Salt₂
      (Col F₂ R₂.params.nw R₂.params.nq) D)
    {B₁ B₂ kmac : ℕ}
    (cands₁ : (D × D) × List (Enc × D) → Finset Witness₁)
    (cands₂ : (D × D) × List (Enc × D) → Finset Witness₂)
    (hcard₁ : ∀ κ, (cands₁ κ).card ≤ B₁)
    (hcard₂ : ∀ κ, (cands₂ κ).card ≤ B₂)
    (hcands₁ : ∀ σ a, L₁.Good σ a → a ∈ cands₁ σ.1)
    (hcands₂ : ∀ σ a, L₂.Good σ a → a ∈ cands₂ σ.1)
    (common₁ : Witness₁ → Fin nblk → Fmac)
    (common₂ : Witness₂ → Fin nblk → Fmac)
    (mac₁ : Witness₁ → Fmac → Fin nblk → Fmac)
    (mac₂ : Witness₂ → Fmac → Fin nblk → Fmac)
    (hcoll : ∀ a₁ a₂, common₁ a₁ ≠ common₂ a₂ →
      (univ.filter fun x => mac₁ a₁ x = mac₂ a₂ x).card ≤ 1)
    (aP : (D × D) × List (Enc × D) → Fmac) (decode : C → Fmac)
    (tagOf : Out → Fin nblk → Fmac)
    (hbal : ∀ x : Fmac,
      (univ.filter fun c : C => decode c = x).card ≤ kmac)
    (b₁c b₁q b₂c b₂q : ℚ)
    (h₁c : Lfzk.GradedCost.challenge R₁ ψ₁ ≤ b₁c)
    (h₁q : Lfzk.GradedCost.query R₁ ψ₁ ≤ b₁q)
    (h₂c : Lfzk.GradedCost.challenge R₂ ψ₂ ≤ b₂c)
    (h₂q : Lfzk.GradedCost.query R₂ ψ₂ ≤ b₂q)
    (dflt : C)
    (htape : 2 * R₂.params.row.n + 2 * R₁.params.row.n + tA ≤ TM)
    (hTM : 0 < TM)
    (Acc : (Fin TM → D) → (PairPoint D C X Msg₁ Msg₂ R₁ R₂ → C) → Prop)
    (haccept₁ : ∀ mt ro, Acc mt ro →
      L₁.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
        (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₁ msgOf₁ claimOf₁
        avOf pubOf (slice1 R₁ R₂) mt ro)
    (haccept₂ : ∀ mt ro, Acc mt ro →
      L₂.acceptsDH (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
        (check2 codec₁ claimOf₁ codec₂ claimOf₂) rootOf₂ msgOf₂ claimOf₂
        avOf pubOf (slice2 R₁ R₂) mt ro)
    (hav : ∀ mt ro, Acc mt ro →
      ro (Sum.inl (rootOf₁
        ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof mt ro),
        rootOf₂
        ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof mt ro))) =
      avOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof mt ro))
    (hrow₁ : ∀ mt ro, Acc mt ro → ∀ a : Witness₁,
      L₁.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
        avOf pubOf mt ro) a →
      mac₁ a (aP ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).context mt ro) +
        decode (avOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof mt ro))) =
        tagOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof mt ro))
    (hrow₂ : ∀ mt ro, Acc mt ro → ∀ a : Witness₂,
      L₂.Good (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
        avOf pubOf mt ro) a →
      mac₂ a (aP ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).context mt ro) +
        decode (avOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof mt ro))) =
        tagOf ((setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof mt ro)) :
    let keyBudget : ℚ := B₁ * B₂ * kmac
    ((univ.filter fun ω : (Fin TM → D) ×
          (PairPoint D C X Msg₁ Msg₂ R₁ R₂ → C) =>
      Acc ω.1 ω.2 ∧
        twoFieldExtract L₁.toZkSide L₂.toZkSide common₁ common₂
          (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
            avOf pubOf ω.1 ω.2) = none).card : ℚ) /
      ((Fintype.card D : ℚ) ^ TM *
        (Fintype.card C : ℚ) ^
          Fintype.card (PairPoint D C X Msg₁ Msg₂ R₁ R₂)) ≤
      gradedCombinedBudget R₁ R₂ logv₁ logv₂
        (Fintype.card C) N keyBudget b₁c b₁q b₂c b₂q +
      2 * (Bcs.AdaptiveCommit.adaptiveNumerator
        (2 * R₂.params.row.n + 2 * R₁.params.row.n) tA
        (1 + Rounds.Role.length R₁.params.nl R₁.params.rounds +
          Rounds.Role.length R₂.params.nl R₂.params.rounds + N) : ℚ) /
        Fintype.card D := by
  dsimp only
  let keyBudget : ℚ := B₁ * B₂ * kmac
  let β₁c : ℚ := max 0 ((Fintype.card C : ℚ) * b₁c)
  let β₁q : ℚ := max 0 ((Fintype.card C : ℚ) * b₁q)
  let β₂c : ℚ := max 0 ((Fintype.card C : ℚ) * b₂c)
  let β₂q : ℚ := max 0 ((Fintype.card C : ℚ) * b₂q)
  let budget : PairPoint D C X Msg₁ Msg₂ R₁ R₂ → ℚ :=
    twoFieldPotentialBudget (R₁ := R₁) (R₂ := R₂)
    keyBudget
    (Lfzk.RbrZkFlat.sideUniformPotentialBudget (R := R₁)
      (logv := logv₁) (C := C) β₁c β₁q)
    (Lfzk.RbrZkFlat.sideUniformPotentialBudget (R := R₂)
      (logv := logv₂) (C := C) β₂c β₂q)
  let betaMax := twoFieldPotentialMaxBudget R₁ R₂ logv₁ logv₂
    (Fintype.card C) keyBudget β₁c β₁q β₂c β₂q
  let slotBeta : Fin (1 + Rounds.Role.length R₁.params.nl R₁.params.rounds +
      Rounds.Role.length R₂.params.nl R₂.params.rounds) → ℚ :=
    fun i => twoFieldPotentialSlotBudgetAt (R₁ := R₁) (R₂ := R₂)
      (logv₁ := logv₁) (logv₂ := logv₂) (C := C)
      keyBudget β₁c β₁q β₂c β₂q i.val
  let extract : (Fin TM → D) → (PairPoint D C X Msg₁ Msg₂ R₁ R₂ → C) →
      Option (Witness₁ × Witness₂) := fun mt ro =>
    twoFieldExtract L₁.toZkSide L₂.toZkSide common₁ common₂
      (sideCtx (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂)
        avOf pubOf mt ro)
  have hb : ∀ p, 0 ≤ budget p := by
    intro p
    rcases p with p | p | p
    · dsimp [budget, twoFieldPotentialBudget, keyBudget]
      positivity
    · exact Lfzk.RbrZkFlat.sideUniformPotentialBudget_nonneg
        (R := R₁) (logv := logv₁) (C := C) β₁c β₁q
        (le_max_left _ _) (le_max_left _ _) p
    · exact Lfzk.RbrZkFlat.sideUniformPotentialBudget_nonneg
        (R := R₂) (logv := logv₂) (C := C) β₂c β₂q
        (le_max_left _ _) (le_max_left _ _) p
  have hm : 0 ≤ betaMax := by
    dsimp [betaMax, twoFieldPotentialMaxBudget]
    exact le_trans (by positivity : (0 : ℚ) ≤ keyBudget) (le_max_left _ _)
  have hloc : ∀ κ p pref,
      (∑ c : C, twoFieldPotentialCharge L₁.toZkSide L₂.toZkSide
        (fun σ => L₁.terminalPotential σ ψ₁)
        (fun σ => L₂.terminalPotential σ ψ₂)
        (fun κ c => SepMacBad (cands₁ κ) (cands₂ κ)
          common₁ common₂ mac₁ mac₂ (aP κ + decode c))
        dflt κ p pref c) ≤ budget p := by
    intro κ p pref
    exact compiled_twoFieldPotential_local h₁ h₂ hr₁ hr₂ L₁ L₂
      ψ₁ ψ₂ cands₁ cands₂ hcard₁ hcard₂ common₁ common₂
      mac₁ mac₂ hcoll aP decode hbal b₁c b₁q b₂c b₂q
      h₁c h₁q h₂c h₂q dflt κ p pref
  have hmax : ∀ p, budget p ≤ betaMax := by
    intro p
    exact twoFieldPotentialBudget_le_max (R₁ := R₁) (R₂ := R₂)
      (logv₁ := logv₁) (logv₂ := logv₂) (C := C)
      keyBudget β₁c β₁q β₂c β₂q p
  have hslot : ∀ out i,
      budget (hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out i.val) ≤
        slotBeta i := by
    intro out i
    exact le_of_eq (twoFieldPotentialSlotBudgetAt_hash2
      (R₁ := R₁) (R₂ := R₂) (logv₁ := logv₁) (logv₂ := logv₂)
      (C := C) rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      keyBudget β₁c β₁q β₂c β₂q out i)
  have hkey : ∀ mt ro, Acc mt ro → extract mt ro = none →
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      let out := S.proof mt ro
      let σ := (S.context mt ro, avOf out, pubOf out)
      ¬ ZkFails L₁.toZkSide.Sat σ → ¬ ZkFails L₂.toZkSide.Sat σ →
        SepMacBad (cands₁ (S.context mt ro)) (cands₂ (S.context mt ro))
          common₁ common₂ mac₁ mac₂
          (aP (S.context mt ro) +
            decode (ro (Sum.inl (rootOf₁ out, rootOf₂ out)))) := by
    intro mt ro ha hfail
    dsimp only
    intro hg₁ hg₂
    exact compiled_keyBad_of_extract_none h₁ h₂ hr₁ hr₂ L₁ L₂
      body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ aP decode tagOf
      common₁ common₂ mac₁ mac₂ cands₁ cands₂ hcands₁ hcands₂
      mt ro (hrow₁ mt ro ha) (hrow₂ mt ro ha) (hav mt ro ha)
      hfail hg₁ hg₂
  have h := compiled_twoFieldPotential_fs_extraction h₁ h₂ hr₁ hr₂
    L₁ L₂ body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
    claimOf₁ claimOf₂
    (fun σ => L₁.terminalPotential σ ψ₁)
    (fun σ => L₂.terminalPotential σ ψ₂)
    (fun κ c => SepMacBad (cands₁ κ) (cands₂ κ)
      common₁ common₂ mac₁ mac₂ (aP κ + decode c)) dflt
    budget hb hloc betaMax hm hmax slotBeta hslot htape hTM
    Acc extract haccept₁ haccept₂ hkey
  convert h using 1
  congr 1
  rw [twoFieldPotentialSlotBudgetAt_sum]
  rfl

end Pair

end Lfzk.CompiledZkDeployedHash
