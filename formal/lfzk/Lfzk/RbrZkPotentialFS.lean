import Lfzk.RbrZkPotentialTwoField
import Bcs.PotentialCommit

/-!
# Deployed two-field extraction through the graded FS compiler

The protocol argument supplies one unit of charge along the actual
verifier path.  The deployed hash inputs record their slots injectively,
so the adaptive oracle compiler counts that entire path without choosing
a challenge/query threshold or an escape slot.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.NizkZkDeployedHash

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

private abbrev PKey (D Enc : Type) := (D × D) × List (Enc × D)
private abbrev PSig (D C X Enc : Type) := PKey D Enc × C × X
private abbrev PPoint (D C X Msg₁ Msg₂ : Type)
    (R₁ R₂ : Lfzk.CertifiedV1.Row) :=
  Pt2 D C X Msg₁ Msg₂ R₁.params.nl R₂.params.nl
    R₁.params.rounds R₂.params.rounds

omit [DecidableEq C] [Fintype D] [Fintype X] [DecidableEq X]
  [DecidableEq Msg₁] [Fintype Msg₁] [DecidableEq Msg₂] [Fintype Msg₂] in
/-- The accepted LayerSteps and key collision pay along the deployed
verifier's exact hash inputs, at the cut context extracted from its proof. -/
theorem twoFieldPotential_fs_path_of_accepted
    {tA N TM : ℕ}
    (body : TwoOracleTree Enc D (PPoint D C X Msg₁ Msg₂ R₁ R₂) C Out tA N)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (S₁ : ZkSide R₁ logv₁ (PSig D C X Enc) C F₁ X₁ Q₁ Msg₁ Witness₁
      M₁ ninp₁ logw₁ logc₁)
    (S₂ : ZkSide R₂ logv₂ (PSig D C X Enc) C F₂ X₂ Q₂ Msg₂ Witness₂
      M₂ ninp₂ logw₂ logc₂)
    (P₁ : ∀ σ, Lfzk.RbrZkFlat.TerminalPotential (S₁.LD σ))
    (P₂ : ∀ σ, Lfzk.RbrZkFlat.TerminalPotential (S₂.LD σ))
    (keyBad : PKey D Enc → C → Prop) (dflt : C)
    (mt : Fin TM → D) (ro : PPoint D C X Msg₁ Msg₂ R₁ R₂ → C)
    (out : Out) (cut : List (Enc × D))
    (hout : out =
      (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).proof mt ro)
    (hctx :
      (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).context mt ro =
        ((rootOf₁ out, rootOf₂ out), cut))
    (hkey : ¬ ZkFails S₁.Sat
        (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out) →
      ¬ ZkFails S₂.Sat
        (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out) →
      keyBad ((rootOf₁ out, rootOf₂ out), cut)
        (ro (Sum.inl (rootOf₁ out, rootOf₂ out))))
    (hacc₁ : Lfzk.RbrZkSplit.ZkLayerStepAccepts .accepted .start
      (Lfzk.RbrZkSplit.steps (nl := R₁.params.nl) (w := R₁.params.rounds)
        (S₁.V (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out))
        (S₁.LD (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out))
        (msgOf₁ out))
      (fun i => ro (Sum.inr (Sum.inl (msgPoint
        (ctxOf rootOf₁ rootOf₂ avOf pubOf out) msgOf₁ out i.val)))))
    (hacc₂ : Lfzk.RbrZkSplit.ZkLayerStepAccepts .accepted .start
      (Lfzk.RbrZkSplit.steps (nl := R₂.params.nl) (w := R₂.params.rounds)
        (S₂.V (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out))
        (S₂.LD (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out))
        (msgOf₂ out))
      (fun i => ro (Sum.inr (Sum.inr (msgPoint
        (ctxOf rootOf₁ rootOf₂ avOf pubOf out,
          fun j : Fin (Rounds.Role.length R₁.params.nl R₁.params.rounds) =>
            msgOf₁ out j.val) msgOf₂ out i.val))))) :
    let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
    1 ≤ ∑ i : Fin (1 + Rounds.Role.length R₁.params.nl R₁.params.rounds +
        Rounds.Role.length R₂.params.nl R₂.params.rounds),
      twoFieldPotentialCharge S₁ S₂ P₁ P₂ keyBad dflt
        (S.context mt ro) (S.hashInput (S.proof mt ro) i.val)
        (pts2.chal ro (S.hashInput (S.proof mt ro) i.val))
        (ro (S.hashInput (S.proof mt ro) i.val)) := by
  have hp := twoFieldPotentialCharge_accepted_path S₁ S₂ P₁ P₂ keyBad dflt
    rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out cut ro hkey hacc₁ hacc₂
  dsimp only
  rw [hctx, ← hout]
  exact hp

omit [DecidableEq C] [DecidableEq X] [DecidableEq Msg₁] [DecidableEq Msg₂] in
/-- Extraction-first FS theorem for the actual two-field deployed hash
schedule.  The local graded budgets and the path payment are separate
proof obligations; `twoFieldPotentialCharge_accepted_path` discharges the
latter from two accepted LayerSteps and the key-point MAC event. -/
theorem twoFieldPotential_fs_extraction
    {tA N TM fc : ℕ}
    (body : TwoOracleTree Enc D (PPoint D C X Msg₁ Msg₂ R₁ R₂) C Out tA N)
    (rootOf₁ rootOf₂ : Out → D) (avOf : Out → C) (pubOf : Out → X)
    (msgOf₁ : Out → ℕ → Msg₁) (msgOf₂ : Out → ℕ → Msg₂)
    (S₁ : ZkSide R₁ logv₁ (PSig D C X Enc) C F₁ X₁ Q₁ Msg₁ Witness₁
      M₁ ninp₁ logw₁ logc₁)
    (S₂ : ZkSide R₂ logv₂ (PSig D C X Enc) C F₂ X₂ Q₂ Msg₂ Witness₂
      M₂ ninp₂ logw₂ logc₂)
    (P₁ : ∀ σ, Lfzk.RbrZkFlat.TerminalPotential (S₁.LD σ))
    (P₂ : ∀ σ, Lfzk.RbrZkFlat.TerminalPotential (S₂.LD σ))
    (keyBad : PKey D Enc → C → Prop) (dflt : C)
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
    (budget : PPoint D C X Msg₁ Msg₂ R₁ R₂ → ℚ)
    (hbudget : ∀ p, 0 ≤ budget p)
    (hlocal : ∀ κ p pref,
      (∑ c : C, twoFieldPotentialCharge S₁ S₂ P₁ P₂
        keyBad dflt κ p pref c) ≤ budget p)
    (betaMax : ℚ) (hbetaMax : 0 ≤ betaMax)
    (hmax : ∀ p, budget p ≤ betaMax)
    (slotBeta : Fin (1 + Rounds.Role.length R₁.params.nl R₁.params.rounds +
      Rounds.Role.length R₂.params.nl R₂.params.rounds) → ℚ)
    (hslot : ∀ out i,
      budget (hash2 rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂ out i.val) ≤
        slotBeta i)
    (ht : tA ≤ TM) (hF : fc + tA ≤ TM) (hTM : 1 ≤ TM)
    (Acc : (Fin TM → D) → (PPoint D C X Msg₁ Msg₂ R₁ R₂ → C) → Prop)
    {Witness : Type}
    (extract : (Fin TM → D) → (PPoint D C X Msg₁ Msg₂ R₁ R₂ → C) →
      Option Witness)
    (hacc₁ : ∀ mt ro, Acc mt ro →
      (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).MerkleAccepts
        codec₁ check Prod.fst claimOf₁ mt ro)
    (hacc₂ : ∀ mt ro, Acc mt ro →
      (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).MerkleAccepts
        codec₂ check Prod.snd claimOf₂ mt ro)
    (hkey : ∀ mt ro, Acc mt ro → extract mt ro = none →
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      let out := S.proof mt ro
      let σ := (S.context mt ro, avOf out, pubOf out)
      ¬ ZkFails S₁.Sat σ → ¬ ZkFails S₂.Sat σ →
        keyBad (S.context mt ro)
          (ro (Sum.inl (rootOf₁ out, rootOf₂ out))))
    (hside₁ : ∀ mt ro, Acc mt ro →
      (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).Explains
        dec₁ Prod.fst claimOf₁ mt ro →
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      let out := S.proof mt ro
      let σ := (S.context mt ro, avOf out, pubOf out)
      Lfzk.RbrZkSplit.ZkLayerStepAccepts .accepted .start
        (Lfzk.RbrZkSplit.steps (nl := R₁.params.nl) (w := R₁.params.rounds)
          (S₁.V σ) (S₁.LD σ) (msgOf₁ out))
        (fun i => ro (Sum.inr (Sum.inl (msgPoint
          (ctxOf rootOf₁ rootOf₂ avOf pubOf out) msgOf₁ out i.val)))))
    (hside₂ : ∀ mt ro, Acc mt ro →
      (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).Explains
        dec₂ Prod.snd claimOf₂ mt ro →
      let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
      let out := S.proof mt ro
      let σ := (S.context mt ro, avOf out, pubOf out)
      Lfzk.RbrZkSplit.ZkLayerStepAccepts .accepted .start
        (Lfzk.RbrZkSplit.steps (nl := R₂.params.nl) (w := R₂.params.rounds)
          (S₂.V σ) (S₂.LD σ) (msgOf₂ out))
        (fun i => ro (Sum.inr (Sum.inr (msgPoint
          (ctxOf rootOf₁ rootOf₂ avOf pubOf out,
            fun j : Fin (Rounds.Role.length R₁.params.nl R₁.params.rounds) =>
              msgOf₁ out j.val) msgOf₂ out i.val))))) :
    ((univ.filter fun ω : (Fin TM → D) ×
          (PPoint D C X Msg₁ Msg₂ R₁ R₂ → C) =>
      Acc ω.1 ω.2 ∧ extract ω.1 ω.2 = none).card : ℚ) /
      ((Fintype.card D : ℚ) ^ TM *
        (Fintype.card C : ℚ) ^
          Fintype.card (PPoint D C X Msg₁ Msg₂ R₁ R₂)) ≤
      (N * betaMax + ∑ i, slotBeta i) / Fintype.card C +
        2 * (AdaptiveCommit.adaptiveNumerator fc tA
          (1 + Rounds.Role.length R₁.params.nl R₁.params.rounds +
            Rounds.Role.length R₂.params.nl R₂.params.rounds + N) : ℚ) /
          Fintype.card D := by
  let S := setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂
  let charge := twoFieldPotentialCharge S₁ S₂ P₁ P₂ keyBad dflt
  have hpath' : ∀ mt ro, Acc mt ro →
      S.Explains dec₁ Prod.fst claimOf₁ mt ro →
      S.Explains dec₂ Prod.snd claimOf₂ mt ro →
      extract mt ro = none →
      let G := S.potentialCarrier mt pts2
      1 ≤ ∑ i : Fin (1 + Rounds.Role.length R₁.params.nl R₁.params.rounds +
          Rounds.Role.length R₂.params.nl R₂.params.rounds),
        charge (G.ctxAt ro (G.key (G.point ro i.val)))
          (G.point ro i.val) (pts2.chal ro (G.point ro i.val))
          (ro (G.point ro i.val)) := by
    intro mt ro ha he₁ he₂ hx
    let out := S.proof mt ro
    let cut := (S.context mt ro).2
    have hctx : S.context mt ro = ((rootOf₁ out, rootOf₂ out), cut) := by
      apply Prod.ext
      · rfl
      · rfl
    have hctx' :
        (setup2 body rootOf₁ rootOf₂ avOf pubOf msgOf₁ msgOf₂).context mt ro =
          ((rootOf₁ out, rootOf₂ out), cut) := hctx
    have hkey' : ¬ ZkFails S₁.Sat
        (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out) →
        ¬ ZkFails S₂.Sat
          (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out) →
        keyBad ((rootOf₁ out, rootOf₂ out), cut)
          (ro (Sum.inl (rootOf₁ out, rootOf₂ out))) := by
      simpa only [hctx'] using hkey mt ro ha hx
    have hacc₁' : Lfzk.RbrZkSplit.ZkLayerStepAccepts .accepted .start
        (Lfzk.RbrZkSplit.steps (nl := R₁.params.nl) (w := R₁.params.rounds)
          (S₁.V (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out))
          (S₁.LD (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out))
          (msgOf₁ out))
        (fun i => ro (Sum.inr (Sum.inl (msgPoint
          (ctxOf rootOf₁ rootOf₂ avOf pubOf out) msgOf₁ out i.val)))) := by
      have hh := hside₁ mt ro ha he₁
      dsimp only at hh
      rw [hctx'] at hh
      exact hh
    have hacc₂' : Lfzk.RbrZkSplit.ZkLayerStepAccepts .accepted .start
        (Lfzk.RbrZkSplit.steps (nl := R₂.params.nl) (w := R₂.params.rounds)
          (S₂.V (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out))
          (S₂.LD (((rootOf₁ out, rootOf₂ out), cut), avOf out, pubOf out))
          (msgOf₂ out))
        (fun i => ro (Sum.inr (Sum.inr (msgPoint
          (ctxOf rootOf₁ rootOf₂ avOf pubOf out,
            fun j : Fin (Rounds.Role.length R₁.params.nl R₁.params.rounds) =>
              msgOf₁ out j.val) msgOf₂ out i.val)))) := by
      have hh := hside₂ mt ro ha he₂
      dsimp only at hh
      rw [hctx'] at hh
      exact hh
    have hp := twoFieldPotential_fs_path_of_accepted body rootOf₁ rootOf₂
      avOf pubOf msgOf₁ msgOf₂ S₁ S₂ P₁ P₂ keyBad dflt mt ro out cut
      rfl hctx hkey' hacc₁' hacc₂'
    change 1 ≤ ∑ i : Fin (1 + Rounds.Role.length R₁.params.nl R₁.params.rounds +
        Rounds.Role.length R₂.params.nl R₂.params.rounds),
      charge (S.context mt ro) (S.hashInput (S.proof mt ro) i.val)
        (pts2.chal ro (S.hashInput (S.proof mt ro) i.val))
        (ro (S.hashInput (S.proof mt ro) i.val)) at hp
    calc
      1 ≤ ∑ i : Fin (1 + Rounds.Role.length R₁.params.nl R₁.params.rounds +
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
  exact S.extraction_failure_ratio_le_two_verifier_potential
    codec₁ dec₁ check Prod.fst claimOf₁ hcheck₁
    codec₂ dec₂ Prod.snd claimOf₂ hcheck₂
    pts2 (setup2_hashInput_injective body rootOf₁ rootOf₂ avOf pubOf
      msgOf₁ msgOf₂)
    charge (twoFieldPotentialCharge_nonneg S₁ S₂ P₁ P₂ keyBad dflt)
    budget hbudget hlocal betaMax hbetaMax hmax slotBeta hslot
    (by omega) ht hF hTM Acc extract hacc₁ hacc₂ hpath'

end Lfzk.NizkZkDeployedHash
