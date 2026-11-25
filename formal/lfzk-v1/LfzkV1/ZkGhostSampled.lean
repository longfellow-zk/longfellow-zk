import LfzkV1.ZkGhostLegacyBridge
import LfzkV1.CompiledLongfellowZkV7Mac

/-! Exact challenge programming and eager evaluation for any finite honest tape sampler. -/

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedSectionVars false

namespace LfzkV1.ZkGhostSampled

open LfzkV1.CompiledLongfellowZk LfzkV1.CompiledLongfellowZkTwoField
  LfzkV1.CompiledLongfellowZkV7Mac LfzkV1.Mac LfzkV1.MacSep
  LfzkV1.ZkGhostTwoField LfzkV1.ZkGhostProgramming LfzkV1.ZkGhostLegacyBridge

private abbrev SharedCoins (n₁ n₂ T₁ T₂ : ℕ) (Salt D Fmac RO₁ RO₂ : Type) :=
  (D × D → Fmac) × (RO₁ × RO₂) × (Index n₁ n₂ → Salt) × ((Fin T₁ → D) × (Fin T₂ → D))

abbrev RealOuterCoins (n₁ n₂ T₁ T₂ : ℕ) (Salt D Fmac RO₁ LQ₁ Coin₁ RO₂ LQ₂ Coin₂ : Type) :=
  SharedCoins n₁ n₂ T₁ T₂ Salt D Fmac RO₁ RO₂ × ((LQ₁ → Coin₁) × (LQ₂ → Coin₂))

private abbrev ProgrammedOuterCoins (n₁ n₂ T₁ T₂ : ℕ)
    (Salt D Fmac RO₁ LQ₁ Coin₁ RO₂ LQ₂ Coin₂ : Type) :=
  SharedCoins n₁ n₂ T₁ T₂ Salt D Fmac RO₁ RO₂ ×
    (((LQ₁ → Coin₁) × Coin₁ × Coin₁) × ((LQ₂ → Coin₂) × Coin₂ × Coin₂))

private def groupProgrammed
    (X K R₁ R₂ G₁ G₂ S H : Type) :
    (X × (K × (R₁ × G₁) × (R₂ × G₂)) × S) × H ≃
      X × (K × (R₁ × R₂) × S × H) × (G₁ × G₂) where
  toFun p :=
    let (x, (k, (r₁, g₁), r₂, g₂), s) := p.1
    (x, (k, (r₁, r₂), s, p.2), g₁, g₂)
  invFun p :=
    let (x, (k, (r₁, r₂), s, h), g₁, g₂) := p
    ((x, (k, (r₁, g₁), r₂, g₂), s), h)
  left_inv _ := rfl
  right_inv _ := rfl

variable {F₁ E₁ F₂ E₂ : Type} [Field F₁] [Fintype F₁] [DecidableEq F₁] [Fintype E₁]
  [Field F₂] [Fintype F₂] [DecidableEq F₂] [Fintype E₂]
variable {r₁ w₁ n₁ nw₁ nq₁ reps₁ r₂ w₂ n₂ nw₂ nq₂ reps₂ : ℕ}
variable {Salt D Enc₁ Enc₂ Coin₁ Coin₂ LQ₁ LQ₂ Ctx₁ Ctx₂ Wit₁ Wit₂ B₁ B₂ Tr₁ Tr₂ RO₁ RO₂ : Type}
variable [Inhabited D] [DecidableEq Enc₁] [DecidableEq Enc₂] [DecidableEq LQ₁] [DecidableEq LQ₂]
variable {Fmac : Type} [Field Fmac] {nblk Q T₁ T₂ : ℕ} {V X : Type}

variable (P₁ : Side F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ E₁ Salt D Enc₁ Coin₁ LQ₁ Ctx₁ Wit₁ B₁ Tr₁ RO₁)
variable (P₂ : Side F₂ r₂ w₂ n₂ nw₂ nq₂ reps₂ E₂ Salt D Enc₂ Coin₂ LQ₂ Ctx₂ Wit₂ B₂ Tr₂ RO₂)
variable (ctx₁ : D → D → Fmac → Tag Fmac nblk → Ctx₁)
variable (ctx₂ : D → D → Fmac → Tag Fmac nblk → LProof F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ Salt D Tr₁ Coin₁ →
  Ctx₂)
variable (dist : TwoDistinguisher F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ F₂ r₂ w₂ n₂ nw₂ nq₂ reps₂
  Salt D Enc₁ Enc₂ Tr₁ Tr₂ Coin₁ Coin₂ LQ₁ LQ₂ RO₁ RO₂ Fmac nblk V Q)
variable (wit₁ : Tag Fmac nblk → Wit₁) (wit₂ : Tag Fmac nblk → Wit₂) (msg : Fin nblk → Fmac)

local notation "Honest" => HonestTape P₁ P₂ (Fmac := Fmac) (nblk := nblk)
local notation "RealOuter" => RealOuterCoins n₁ n₂ T₁ T₂ Salt D Fmac RO₁ LQ₁ Coin₁ RO₂ LQ₂ Coin₂
local notation "ProgrammedOuter" => ProgrammedOuterCoins n₁ n₂ T₁ T₂ Salt D Fmac RO₁ LQ₁ Coin₁ RO₂ LQ₂ Coin₂
local notation "Outer" => OuterCoins n₁ n₂ Salt D Enc₁ Enc₂ Fmac RO₁ LQ₁ Coin₁ RO₂ LQ₂ Coin₂

private def sideCoins (x : Honest) (o : RealOuter) :
    RealCoins P₁.C nw₁ nq₁ reps₁ B₁ T₁ Salt D RO₁ LQ₁ Coin₁ ×
    RealCoins P₂.C nw₂ nq₂ reps₂ B₂ T₂ Salt D RO₂ LQ₂ Coin₂ :=
  let ((_, (r₁, r₂), s, t₁, t₂), g₁, g₂) := o
  ((x.2.1.2, x.2.1.1, (s ∘ Sum.inl, t₁), r₁, g₁),
   (x.2.2.2, x.2.2.1, (s ∘ Sum.inr, t₂), r₂, g₂))

/-- The two original lazy oracles with all honest arithmetic coins supplied by `draw`. -/
noncomputable def realSampled (draw : X → Honest) (ω : X × RealOuter) : V :=
  let x : Honest := draw ω.1
  realExp2 P₁ P₂ ctx₁ ctx₂ wit₁ wit₂ msg dist (x.1, ω.2.1.1, sideCoins P₁ P₂ x ω.2)

private noncomputable def programmedSampled (draw : X → Honest) (ω : X × ProgrammedOuter) : V :=
  let (k, (r₁, r₂), s, t₁, t₂) := ω.2.1
  let (g₁, c₁, i₁) := ω.2.2.1
  let (g₂, c₂, i₂) := ω.2.2.2
  let x : Honest := draw ω.1
  programmedCore2 P₁ P₂ ctx₁ ctx₂ wit₁ wit₂ msg dist x.1 k
    x.2.1.2 x.2.1.1 (s ∘ Sum.inl, t₁) r₁ g₁ c₁ i₁
    x.2.2.2 x.2.2.1 (s ∘ Sum.inr, t₂) r₂ g₂ c₂ i₂

variable [Fintype X] [Fintype D] [DecidableEq D] [Fintype Fmac] [Fintype Salt]
  [Fintype LQ₁] [Fintype LQ₂] [Fintype Coin₁] [Fintype Coin₂] [Nonempty Coin₁] [Nonempty Coin₂]
  [Fintype RO₁] [Fintype RO₂]

private theorem realSampled_statClose_programmed (draw : X → Honest) :
    StatClose 0 (realSampled P₁ P₂ ctx₁ ctx₂ dist wit₁ wit₂ msg (T₁ := T₁) (T₂ := T₂) draw)
      (programmedSampled P₁ P₂ ctx₁ ctx₂ dist wit₁ wit₂ msg (T₁ := T₁) (T₂ := T₂) draw) := by
  refine statClose_mix_equiv le_rfl _ _ (Equiv.prodAssoc _ _ _) (Equiv.prodAssoc _ _ _) ?_
  rintro ⟨a, k, ⟨r₁, r₂⟩, s, t₁, t₂⟩
  let x : Honest := draw a
  exact programmedCore2_statClose P₁ P₂ ctx₁ ctx₂ wit₁ wit₂ msg dist x.1 k
    x.2.1.2 x.2.1.1 (s ∘ Sum.inl, t₁) r₁ x.2.2.2 x.2.2.1 (s ∘ Sum.inr, t₂) r₂

variable [Fintype Enc₁] [Fintype Enc₂]

private theorem programmedSampled_statClose_eager (draw : X → Honest)
    (hT₁ : Q + (2 * n₂ - 1) + (2 * n₁ - 1) ≤ T₁)
    (hT₂ : Q + (2 * n₂ - 1) + (2 * n₁ - 1) ≤ T₂) :
    StatClose 0 (programmedSampled P₁ P₂ ctx₁ ctx₂ dist wit₁ wit₂ msg (T₁ := T₁) (T₂ := T₂) draw)
      (fun ω : X × Outer => eagerProgrammedExp P₁ P₂ ctx₁ ctx₂ dist wit₁ wit₂ msg (draw ω.1, ω.2)) := by
  refine statClose_mix_equiv le_rfl _ _ (groupProgrammed _ _ _ _ _ _ _ _)
    ((Equiv.prodAssoc _ _ _).trans ((Equiv.refl _).prodCongr (Equiv.prodAssoc _ _ _))) ?_
  rintro ⟨a, g, s⟩
  have hs := programmedCore2_statClose_eager P₁ P₂ ctx₁ ctx₂ dist wit₁ wit₂ msg g (draw a) s hT₁ hT₂
  intro test
  change |probOf _ test -
    probOf (fun p : (Enc₁ ⊕ Enc₂ → D) × (Index n₁ n₂ → D) =>
      eagerProgrammedCore P₁ P₂ ctx₁ ctx₂ dist wit₁ wit₂ msg g (draw a) s p.1) test| ≤ 0
  rw [CompiledLigeroZk.probOf_fst]
  exact hs test

/-- Both exact simulation steps preserve the chosen distribution of the honest tape. -/
theorem realSampled_statClose_eager (draw : X → Honest)
    (hT₁ : Q + (2 * n₂ - 1) + (2 * n₁ - 1) ≤ T₁)
    (hT₂ : Q + (2 * n₂ - 1) + (2 * n₁ - 1) ≤ T₂) :
    StatClose 0 (realSampled P₁ P₂ ctx₁ ctx₂ dist wit₁ wit₂ msg (T₁ := T₁) (T₂ := T₂) draw)
      (fun ω : X × Outer => eagerProgrammedExp P₁ P₂ ctx₁ ctx₂ dist wit₁ wit₂ msg (draw ω.1, ω.2)) := by
  simpa only [zero_add] using
    (realSampled_statClose_programmed P₁ P₂ ctx₁ ctx₂ dist wit₁ wit₂ msg
      (T₁ := T₁) (T₂ := T₂) draw).trans
      (programmedSampled_statClose_eager P₁ P₂ ctx₁ ctx₂ dist wit₁ wit₂ msg draw hT₁ hT₂)

variable [DecidableEq Fmac] [DecidableEq E₁] [DecidableEq E₂]

/-- Change the share coordinate for the masked-tag representation, keeping both prover tapes. -/
def v7ToMasked (x : Honest) : Honest :=
  (shareEquiv msg x.1, x.2)

/-- The genuine v7 MAC formula on a caller-supplied honest tape. -/
noncomputable def realSampledV7 (draw : X → Honest) (ω : X × RealOuter) : V :=
  let x : Honest := draw ω.1
  realExp2V7 P₁ P₂ ctx₁ ctx₂ wit₁ wit₂ msg dist (x.1, ω.2.1.1, sideCoins P₁ P₂ x ω.2)

private theorem realSampledV7_eq_masked (draw : X → Honest) :
    realSampledV7 P₁ P₂ ctx₁ ctx₂ dist wit₁ wit₂ msg (T₁ := T₁) (T₂ := T₂) draw =
      realSampled P₁ P₂ (maskCtx₁ ctx₁ (zeroPat msg)) (maskCtx₂ ctx₂ (zeroPat msg))
        (maskDist dist (zeroPat msg)) (wit₁ ∘ (shareEquiv msg).symm) (wit₂ ∘ (shareEquiv msg).symm) msg
        (fun a => v7ToMasked P₁ P₂ msg (draw a)) := by
  funext ω
  let x : Honest := draw ω.1
  exact realExp2V7_eq P₁ P₂ ctx₁ ctx₂ wit₁ wit₂ msg dist
    (x.1, ω.2.1.1, sideCoins P₁ P₂ x ω.2)

/-- Transfer the v7 observer law to the eager experiment at the masked tags. -/
theorem realSampledV7_statClose_eager (draw : X → Honest)
    (hT₁ : Q + (2 * n₂ - 1) + (2 * n₁ - 1) ≤ T₁)
    (hT₂ : Q + (2 * n₂ - 1) + (2 * n₁ - 1) ≤ T₂) :
    StatClose 0 (realSampledV7 P₁ P₂ ctx₁ ctx₂ dist wit₁ wit₂ msg (T₁ := T₁) (T₂ := T₂) draw)
      (fun ω : X × Outer =>
        eagerProgrammedExp P₁ P₂ (maskCtx₁ ctx₁ (zeroPat msg)) (maskCtx₂ ctx₂ (zeroPat msg))
          (maskDist dist (zeroPat msg)) (wit₁ ∘ (shareEquiv msg).symm) (wit₂ ∘ (shareEquiv msg).symm)
          msg (v7ToMasked P₁ P₂ msg (draw ω.1), ω.2)) := by
  rw [realSampledV7_eq_masked]
  exact realSampled_statClose_eager P₁ P₂ (maskCtx₁ ctx₁ (zeroPat msg)) (maskCtx₂ ctx₂ (zeroPat msg))
    (maskDist dist (zeroPat msg)) (wit₁ ∘ (shareEquiv msg).symm) (wit₂ ∘ (shareEquiv msg).symm) msg
    (fun a => v7ToMasked P₁ P₂ msg (draw a)) hT₁ hT₂

end LfzkV1.ZkGhostSampled
