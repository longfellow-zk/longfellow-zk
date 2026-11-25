import LfzkV1.ZkGhostSampled
import LfzkV1.ZkGhostSubfield

/-!
# Query-bounded v7 zero knowledge with joint Merkle hiding

The observer receives both proofs and all five challenge functions before
making any Merkle query. Its one interleaved tree bounds the total number of
queries to both independent typed Merkle oracles, including repeated queries.
Honest commitment calls and the simulator's oracle programming do not consume
that observer budget. As in the original theorem, the simulator receives the
zero pattern of the common blocks, and the public statement is fixed first.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LfzkV1.CompiledLongfellowZkV7Joint

open LigeroFamily Merkle.MH
open LfzkV1.Mac LfzkV1.MacSep LfzkV1.CompiledLongfellowZk
  LfzkV1.CompiledLongfellowZkTwoField LfzkV1.CompiledLongfellowZkV7Mac
  LfzkV1.ZkGhostTwoField

variable {F₁ E₁ F₂ E₂ : Type} [Field F₁] [Fintype F₁] [DecidableEq F₁] [Fintype E₁]
  [DecidableEq E₁] [Field F₂] [Fintype F₂] [DecidableEq F₂] [Fintype E₂] [DecidableEq E₂]
variable {r₁ w₁ n₁ nw₁ nq₁ reps₁ r₂ w₂ n₂ nw₂ nq₂ reps₂ : ℕ}
variable {Salt D Enc₁ Enc₂ Coin₁ Coin₂ LQ₁ LQ₂ Ctx₁ Ctx₂ Wit₁ Wit₂ B₁ B₂ Tr₁ Tr₂ RO₁ RO₂ : Type}
variable [Inhabited D] [DecidableEq LQ₁] [DecidableEq LQ₂]
variable {Fmac : Type} [Field Fmac] {nblk Q : ℕ} {V : Type}

variable (P₁ : Side F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ E₁ Salt D Enc₁ Coin₁ LQ₁ Ctx₁ Wit₁ B₁ Tr₁ RO₁)
variable (P₂ : Side F₂ r₂ w₂ n₂ nw₂ nq₂ reps₂ E₂ Salt D Enc₂ Coin₂ LQ₂ Ctx₂ Wit₂ B₂ Tr₂ RO₂)
variable (ctx₁ : D → D → Fmac → Tag Fmac nblk → Ctx₁)
variable (ctx₂ : D → D → Fmac → Tag Fmac nblk → LProof F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ Salt D Tr₁ Coin₁ →
  Ctx₂)
variable (dist : TwoDistinguisher F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ F₂ r₂ w₂ n₂ nw₂ nq₂ reps₂
  Salt D Enc₁ Enc₂ Tr₁ Tr₂ Coin₁ Coin₂ LQ₁ LQ₂ RO₁ RO₂ Fmac nblk V Q)
variable (wit₁ : Tag Fmac nblk → Wit₁) (wit₂ : Tag Fmac nblk → Wit₂) (msg : Fin nblk → Fmac)

variable [DecidableEq Fmac]

/-- The v7 witness-free arithmetic with the allowed MAC leakage, against
the two Merkle tables programmed only at disclosed leaves. -/
noncomputable def ghostSimExpLeak (z : Fin nblk → Bool) :=
  ghostSimExp P₁ P₂ (maskCtx₁ ctx₁ z) (maskCtx₂ ctx₂ z) (maskDist dist z)

theorem ghostSimExpLeak_of_ne_zero (hmsg : ∀ j, msg j ≠ 0) :
    ghostSimExpLeak P₁ P₂ ctx₁ ctx₂ dist (zeroPat msg) = ghostSimExp P₁ P₂ ctx₁ ctx₂ dist := by
  have h := maskTag_zeroPat_of_ne_zero hmsg
  have e₁ : maskCtx₁ ctx₁ (zeroPat msg) = ctx₁ := by
    funext r₁ r₂ av t
    simp only [maskCtx₁, h, id]
  have e₂ : maskCtx₂ ctx₂ (zeroPat msg) = ctx₂ := by
    funext r₁ r₂ av t pf₁
    simp only [maskCtx₂, h, id]
  have e₃ : maskDist dist (zeroPat msg) = dist := by
    funext p G
    rcases p with ⟨t, p₁, p₂⟩
    simp only [maskDist, h, id]
  simp only [ghostSimExpLeak, e₁, e₂, e₃]

section Supported

open LfzkV1.ZkGhostSubfield LfzkV1.ZkGhostSampled LfzkV1.ZkGhostSimulator

variable [Fintype Salt] [Nonempty Salt] [Fintype D] [DecidableEq D]
  [DecidableEq Enc₁] [DecidableEq Enc₂] [Fintype Enc₁] [Fintype Enc₂]
  [Fintype LQ₁] [Fintype LQ₂] [Fintype Coin₁] [Fintype Coin₂]
  [Nonempty Coin₁] [Nonempty Coin₂] [Fintype RO₁] [Fintype RO₂]
  [Fintype Fmac] [Fintype B₁] [Fintype B₂] [Fintype Tr₁] [Fintype Tr₂]

variable (p : Tape P₁.C nw₁ nq₁ reps₁ → Prop) (q : Tape P₂.C nw₂ nq₂ reps₂ → Prop)
  [Fintype (Subtype p)] [Fintype (Subtype q)]

local notation "Real" => Tag Fmac nblk × (B₁ × Subtype p) × (B₂ × Subtype q)
local notation "Sim" => Tag Fmac nblk × (Tr₁ × Subtype p) × (Tr₂ × Subtype q)
local notation "Outer" => OuterCoins n₁ n₂ Salt D Enc₁ Enc₂ Fmac RO₁ LQ₁ Coin₁ RO₂ LQ₂ Coin₂

/-- The strengthened v7 bound on tapes restricted to their sampler's support,
which can enforce the hash side's subfield padding. The same support is used
when sampling the simulator's zero-tableau tapes. -/
theorem v7_zk_joint_restricted {T₁ T₂ : ℕ}
    (hT₁ : Q + (2 * n₂ - 1) + (2 * n₁ - 1) ≤ T₁)
    (hT₂ : Q + (2 * n₂ - 1) + (2 * n₁ - 1) ≤ T₂)
    (leaf₁ : Function.Injective P₁.Cod.leafEnc) (leaf₂ : Function.Injective P₂.Cod.leafEnc)
    (node₁ : ∀ children sm, P₁.Cod.nodeEnc children ≠ P₁.Cod.leafEnc sm)
    (node₂ : ∀ children sm, P₂.Cod.nodeEnc children ≠ P₂.Cod.leafEnc sm)
    (hp : ∀ side, Stable P₁ side wit₁ p) (hq : ∀ side, Stable P₂ side wit₂ q)
    (hvalid₁ : ∀ ap rt₁ rt₂ av, P₁.FE.Valid (wit₁ ap) (ctx₁ rt₁ rt₂ av (shiftTag av ap msg)))
    (hvalid₂ : ∀ ap rt₁ rt₂ av p₁, P₂.FE.Valid (wit₂ ap) (ctx₂ rt₁ rt₂ av (shiftTag av ap msg) p₁)) :
    StatClose ((Q : ℚ) / Fintype.card Salt +
        probOf (forgetSupport : Real → HonestTape P₁ P₂) (fun x => ¬ separateColumns P₁ P₂ wit₁ wit₂ x))
      (realSampledV7 P₁ P₂ ctx₁ ctx₂ dist wit₁ wit₂ msg (T₁ := T₁) (T₂ := T₂)
        (forgetSupport : Real → HonestTape P₁ P₂))
      (fun ω : Sim × Outer =>
        ghostSimExpLeak P₁ P₂ ctx₁ ctx₂ dist (zeroPat msg) (forgetSupport ω.1, ω.2)) := by
  let z := zeroPat msg
  let pull := (shareEquiv msg).symm
  let draw : Real → HonestTape P₁ P₂ := v7ToMasked P₁ P₂ msg ∘ forgetSupport
  let reindex : Real ≃ Real := (shareEquiv msg).prodCongr (Equiv.refl _)
  have h₁ := realSampledV7_statClose_eager P₁ P₂ ctx₁ ctx₂ dist wit₁ wit₂ msg
    (forgetSupport : Real → HonestTape P₁ P₂) hT₁ hT₂
  have h₂ := joint_hiding_sampled P₁ P₂ (maskCtx₁ ctx₁ z) (maskCtx₂ ctx₂ z) (maskDist dist z)
    (wit₁ ∘ pull) (wit₂ ∘ pull) msg draw leaf₁ leaf₂ node₁ node₂
  have hprob :
      probOf draw (fun x => ¬ separateColumns P₁ P₂ (wit₁ ∘ pull) (wit₂ ∘ pull) x) =
        probOf (forgetSupport : Real → HonestTape P₁ P₂) (fun x => ¬ separateColumns P₁ P₂ wit₁ wit₂ x) := by
    unfold probOf
    congr 2
    apply congrArg Finset.card
    ext x
    rcases x with ⟨ap, x₁, x₂⟩
    simp [draw, v7ToMasked, forgetSupport, separateColumns, payloads, pull]
  rw [hprob] at h₂
  have law := ghost_simulation_restricted P₁ P₂ (maskCtx₁ ctx₁ z) (maskCtx₂ ctx₂ z)
    (wit₁ ∘ pull) (wit₂ ∘ pull) msg p q
      (fun ap rt₁ rt₂ av => by
        have hv := hvalid₁ (pull ap) rt₁ rt₂ av
        rwa [← maskTag_macTag_shareEquiv, Equiv.apply_symm_apply] at hv)
      (fun ap rt₁ rt₂ av p₁ => by
        have hv := hvalid₂ (pull ap) rt₁ rt₂ av p₁
        rwa [← maskTag_macTag_shareEquiv, Equiv.apply_symm_apply] at hv)
      (maskDist dist z) (fun side ap => hp side (pull ap)) (fun side ap => hq side (pull ap))
  have h₃ := (LfzkV1.CompiledLigeroZk.statClose_comp_equiv_left _ _
    (reindex.prodCongr (Equiv.refl Outer))).mpr law
  simpa only [zero_add, add_zero, ghostSimExpLeak, z] using h₁.trans (h₂.trans h₃)

end Supported

end LfzkV1.CompiledLongfellowZkV7Joint
