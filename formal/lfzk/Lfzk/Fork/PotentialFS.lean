import Lfzk.RbrZkPotentialHybridFS
import Lfzk.Fork.HybridCharge

/-! Schedule-dependent bridge for the forked verifier. Generic local
counts, cut-context lemmas, and numerical certificates are reused. -/

/-! The hybrid two-field charge enters the unchanged two-opening FS compiler.
The direct hash-side terminal event is left out of this call and bounded on
the full experiment separately. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 300000

namespace Lfzk.Fork.PotentialFS

open Lfzk.NizkZkDeployedHash

open Finset Bcs Bcs.TotalOracleCommit Merkle Merkle.MH Merkle.RandomOracle
  Merkle.RandomOracle.TwoOracleTree Lfzk.NizkDeployedHash
  Lfzk.NizkDeployedHashTwoField Lfzk.NizkZkTwoField Lfzk.NizkZk
open scoped Classical

variable {R₁ R₂ : Lfzk.CertifiedV1.Row} {logv₁ logv₂ : ℕ}
variable {C : Type} [Fintype C] [DecidableEq C] [Nonempty C]
variable {D : Type} [Fintype D] [DecidableEq D] [Inhabited D]
variable {Enc X Out : Type} [DecidableEq Enc] [Fintype X] [DecidableEq X]
variable {F₁ X₁ Q₁ Msg₁ Witness₁ : Type} [Field F₁] [Fintype F₁]
  [DecidableEq F₁] [SumcheckInterp F₁] [Fintype X₁] [DecidableEq X₁]
  [Fintype Q₁] [DecidableEq Q₁] [Inhabited Msg₁] [DecidableEq Msg₁]
  [Fintype Msg₁] {M₁ ninp₁ logw₁ logc₁ : ℕ}
variable {F₂ X₂ Q₂ Msg₂ Witness₂ : Type} [Field F₂] [Fintype F₂]
  [DecidableEq F₂] [SumcheckInterp F₂] [Fintype X₂] [DecidableEq X₂]
  [Fintype Q₂] [DecidableEq Q₂] [Inhabited Msg₂] [DecidableEq Msg₂]
  [Fintype Msg₂] {M₂ ninp₂ logw₂ logc₂ : ℕ}
variable {Salt₁ Mc₁ Salt₂ Mc₂ : Type} [Inhabited Salt₁] [Inhabited Mc₁]
  [Inhabited Salt₂] [Inhabited Mc₂] {n₁ n₂ : ℕ}

private abbrev HybridKey (D Enc : Type) := (D × D) × List (Enc × D)
private abbrev HybridSig (D C X Enc : Type) := HybridKey D Enc × C × X
private abbrev HybridPoint (D C X Msg₁ Msg₂ : Type)
    (R₁ R₂ : Lfzk.CertifiedV1.Row) :=
  Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl
    R₁.params.rounds R₂.params.rounds

omit [DecidableEq C] [DecidableEq X] [DecidableEq Msg₁]
  [DecidableEq Msg₂] in
/-- Graded FS extraction outside the directly charged hash-side terminal
event.  The `N` adaptive challenge-oracle calls retain the compiler's
existing `N * betaMax` coefficient, and both Merkle openings retain factor
two.  A client proves the actual forked path payment with
`Lfzk.Fork.HybridCharge.twoFieldHybridCharge_accepted_path_of_field`. -/
theorem twoFieldHybrid_fs_extraction_outside
    {tA N TM fc : ℕ}
    (body : TwoOracleTree Enc D (HybridPoint D C X Msg₁ Msg₂ R₁ R₂)
      C Out tA N)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (S₁ : ZkSide R₁ logv₁ (HybridSig D C X Enc) C F₁ X₁ Q₁
      Msg₁ Witness₁ M₁ ninp₁ logw₁ logc₁)
    (S₂ : ZkSide R₂ logv₂ (HybridSig D C X Enc) C F₂ X₂ Q₂
      Msg₂ Witness₂ M₂ ninp₂ logw₂ logc₂)
    (P₁ : ∀ σ, Lfzk.RbrZkFlat.TerminalPotential (S₁.LD σ))
    (P₂ : ∀ σ, Lfzk.RbrZkFlat.TerminalPotential (S₂.LD σ))
    (keyBad : HybridKey D Enc → C → Prop) (dflt : C)
    (codec₁ : Codec Salt₁ Mc₁ D Enc) (dec₁ : RoleDecoders codec₁)
    (codec₂ : Codec Salt₂ Mc₂ D Enc) (dec₂ : RoleDecoders codec₂)
    (check : Out → Tree Enc D Unit fc)
    (claimOf₁ : Out → OpeningClaim n₁ Salt₁ Mc₁ D)
    (claimOf₂ : Out → OpeningClaim n₂ Salt₂ Mc₂ D)
    (hcheck₁ : ∀ (H : Enc → D) (out : Out),
      ∀ qa ∈ ((checkPass codec₁ n₁ (claimOf₁ out).I (claimOf₁ out).a
          (claimOf₁ out).pf (2 * n₁) fun _ => default).run H).2,
        qa ∈ ((check out).run H).2)
    (hcheck₂ : ∀ (H : Enc → D) (out : Out),
      ∀ qa ∈ ((checkPass codec₂ n₂ (claimOf₂ out).I (claimOf₂ out).a
          (claimOf₂ out).pf (2 * n₂) fun _ => default).run H).2,
        qa ∈ ((check out).run H).2)
    (budget : HybridPoint D C X Msg₁ Msg₂ R₁ R₂ → ℚ)
    (hbudget : ∀ p, 0 ≤ budget p)
    (hlocal : ∀ κ p pref,
      (∑ c : C, twoFieldHybridCharge S₁ S₂ P₁ P₂
        keyBad dflt κ p pref c) ≤ budget p)
    (betaMax : ℚ) (hbetaMax : 0 ≤ betaMax)
    (hmax : ∀ p, budget p ≤ betaMax)
    (slotBeta : Fin (1 + Rounds.Role.length R₁.params.nl R₁.params.rounds +
      Rounds.Role.length R₂.params.nl R₂.params.rounds) → ℚ)
    (hslot : ∀ out i,
      budget (Lfzk.Fork.Transcript.hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out i.val) ≤
        slotBeta i)
    (ht : tA ≤ TM) (hF : fc + tA ≤ TM) (hTM : 1 ≤ TM)
    (Acc terminal : (Fin TM → D) →
      (HybridPoint D C X Msg₁ Msg₂ R₁ R₂ → C) → Prop)
    {Witness : Type}
    (extract : (Fin TM → D) →
      (HybridPoint D C X Msg₁ Msg₂ R₁ R₂ → C) → Option Witness)
    (hacc₁ : ∀ mt ro, Acc mt ro →
      (Lfzk.Fork.Transcript.setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).MerkleAccepts
        codec₁ check Prod.fst claimOf₁ mt ro)
    (hacc₂ : ∀ mt ro, Acc mt ro →
      (Lfzk.Fork.Transcript.setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).MerkleAccepts
        codec₂ check Prod.snd claimOf₂ mt ro)
    (hpath : ∀ mt ro, Acc mt ro → ¬ terminal mt ro →
      (Lfzk.Fork.Transcript.setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).Explains
        dec₁ Prod.fst claimOf₁ mt ro →
      (Lfzk.Fork.Transcript.setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).Explains
        dec₂ Prod.snd claimOf₂ mt ro →
      extract mt ro = none →
      let S := Lfzk.Fork.Transcript.setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      let out := S.proof mt ro
      1 ≤ ∑ i : Fin (1 + Rounds.Role.length R₁.params.nl
          R₁.params.rounds +
          Rounds.Role.length R₂.params.nl R₂.params.rounds),
        twoFieldHybridCharge S₁ S₂ P₁ P₂ keyBad dflt
          (S.context mt ro) (S.hashInput out i.val)
          (pts2.chal ro (S.hashInput out i.val))
          (ro (S.hashInput out i.val))) :
    ((univ.filter fun ω : (Fin TM → D) ×
          (HybridPoint D C X Msg₁ Msg₂ R₁ R₂ → C) =>
      Acc ω.1 ω.2 ∧ ¬ terminal ω.1 ω.2 ∧
        extract ω.1 ω.2 = none).card : ℚ) /
      ((Fintype.card D : ℚ) ^ TM *
        (Fintype.card C : ℚ) ^
          Fintype.card (HybridPoint D C X Msg₁ Msg₂ R₁ R₂)) ≤
      (N * betaMax + ∑ i, slotBeta i) / Fintype.card C +
        2 * (Bcs.AdaptiveCommit.adaptiveNumerator fc tA
          (1 + Rounds.Role.length R₁.params.nl R₁.params.rounds +
            Rounds.Role.length R₂.params.nl R₂.params.rounds + N) : ℚ) /
          Fintype.card D := by
  let S := Lfzk.Fork.Transcript.setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
  let charge := twoFieldHybridCharge S₁ S₂ P₁ P₂ keyBad dflt
  let Acc' := fun mt ro => Acc mt ro ∧ ¬ terminal mt ro
  have hpath' : ∀ mt ro, Acc' mt ro →
      S.Explains dec₁ Prod.fst claimOf₁ mt ro →
      S.Explains dec₂ Prod.snd claimOf₂ mt ro →
      extract mt ro = none →
      let G := S.potentialCarrier mt pts2
      1 ≤ ∑ i : Fin (1 + Rounds.Role.length R₁.params.nl
          R₁.params.rounds +
          Rounds.Role.length R₂.params.nl R₂.params.rounds),
        charge (G.ctxAt ro (G.key (G.point ro i.val)))
          (G.point ro i.val) (pts2.chal ro (G.point ro i.val))
          (ro (G.point ro i.val)) := by
    intro mt ro ha he₁ he₂ hx
    have hp := hpath mt ro ha.1 ha.2 he₁ he₂ hx
    dsimp only at hp ⊢
    calc
      1 ≤ ∑ i : Fin (1 + Rounds.Role.length R₁.params.nl
          R₁.params.rounds +
          Rounds.Role.length R₂.params.nl R₂.params.rounds),
        charge (S.context mt ro) (S.hashInput (S.proof mt ro) i.val)
          (pts2.chal ro (S.hashInput (S.proof mt ro) i.val))
          (ro (S.hashInput (S.proof mt ro) i.val)) := hp
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i _
        dsimp only [Bcs.TotalOracleCommit.Setup.potentialCarrier]
        rw [S.grinding_ctx_point mt pts2 (fun _ _ _ _ => False)
          (fun _ => 0) (by simp) ro i.val,
          S.grinding_point mt pts2 (fun _ _ _ _ => False)
            (fun _ => 0) (by simp) ro i.val]
  have h := S.extraction_failure_ratio_le_two_verifier_potential
    codec₁ dec₁ check Prod.fst claimOf₁ hcheck₁
    codec₂ dec₂ Prod.snd claimOf₂ hcheck₂
    pts2 (Lfzk.Fork.Transcript.setup2_hashInput_injective body rootOf₁ rootOf₂ avOf pubOf
      msgOf₁ msgOf₂)
    charge (twoFieldHybridCharge_nonneg S₁ S₂ P₁ P₂ keyBad dflt)
    budget hbudget hlocal betaMax hbetaMax hmax slotBeta hslot
    (by omega) ht hF hTM Acc' extract
    (fun mt ro ha => hacc₁ mt ro ha.1)
    (fun mt ro ha => hacc₂ mt ro ha.1) hpath'
  simpa only [Acc', and_assoc] using h

end Lfzk.Fork.PotentialFS
