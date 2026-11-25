import LfzkV1.CompiledLongfellowZkTwoField
import LfzkV1.MacSep

/-! The real v7 two-field experiment and its MAC reparameterization.

On a nonzero message block, multiplying the private share by the message
permutes the share space. The zero blocks always have zero tags. The resulting
mask is the zero-pattern input to the simulator in `V7ZkProfile`.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace LfzkV1.CompiledLongfellowZkV7Mac

open Merkle Merkle.MH LigeroFamily LigeroFamily.ZeroKnowledge
open LfzkV1.ZkAdaptiveV1 LfzkV1.CompiledLongfellowZk LfzkV1.ZkTwoTape LfzkV1.Mac LfzkV1.MacSep
open LfzkV1.CompiledLongfellowZkTwoField

/-! ## 1. The v7 experiment, and the masked public data -/

section Defs

variable {F₁ E₁ F₂ E₂ : Type} [Field F₁] [Fintype F₁] [DecidableEq F₁] [Fintype E₁]
  [DecidableEq E₁] [Field F₂] [Fintype F₂] [DecidableEq F₂] [Fintype E₂] [DecidableEq E₂]
variable {r₁ w₁ n₁ nw₁ nq₁ reps₁ r₂ w₂ n₂ nw₂ nq₂ reps₂ : ℕ}
variable {Salt D Enc₁ Enc₂ Coin₁ Coin₂ LQ₁ LQ₂ Ctx₁ Ctx₂ Wit₁ Wit₂ B₁ B₂ Tr₁ Tr₂ RO₁ RO₂ V : Type}
variable [DecidableEq Enc₁] [DecidableEq Enc₂] [Inhabited D] [DecidableEq LQ₁] [DecidableEq LQ₂]
variable {Fmac : Type} [Field Fmac] [DecidableEq Fmac] {nblk : ℕ}

variable (P₁ : Side F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ E₁ Salt D Enc₁ Coin₁ LQ₁ Ctx₁ Wit₁ B₁ Tr₁ RO₁)
variable (P₂ : Side F₂ r₂ w₂ n₂ nw₂ nq₂ reps₂ E₂ Salt D Enc₂ Coin₂ LQ₂ Ctx₂ Wit₂ B₂ Tr₂ RO₂)
variable (ctx₁ : D → D → Fmac → Tag Fmac nblk → Ctx₁)
variable (ctx₂ : D → D → Fmac → Tag Fmac nblk → LProof F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ Salt D Tr₁ Coin₁ →
  Ctx₂)
variable (wit₁ : Tag Fmac nblk → Wit₁) (wit₂ : Tag Fmac nblk → Wit₂) (msg : Fin nblk → Fmac)

/-- Side 1's context as a function of its root, at the v7 tags of the shares `s`. -/
def ctxOf₁V7 (s : Tag Fmac nblk) (Gav : D × D → Fmac) (root₂ : D) : D → Ctx₁ :=
  fun root₁ => ctx₁ root₁ root₂ (Gav (root₁, root₂)) (shiftTag (Gav (root₁, root₂)) s msg)

/-- Side 2's context as a function of its root, after side 1's proof `pf₁`, at the v7 tags. -/
def ctxOf₂V7 (s : Tag Fmac nblk) (Gav : D × D → Fmac)
    (pf₁ : LProof F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ Salt D Tr₁ Coin₁) : D → Ctx₂ :=
  fun root₂ => ctx₂ pf₁.root root₂ (Gav (pf₁.root, root₂))
    (shiftTag (Gav (pf₁.root, root₂)) s msg) pf₁

variable {T₁ T₂ f : ℕ}
variable (dist : TwoDistinguisher F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ F₂ r₂ w₂ n₂ nw₂ nq₂ reps₂
  Salt D Enc₁ Enc₂ Tr₁ Tr₂ Coin₁ Coin₂ LQ₁ LQ₂ RO₁ RO₂ Fmac nblk V f)

/-- **The real two-field run with the v7 MAC, at fixed coins.**  `realCore2` with the v7 tags
`shiftTag av s msg` at the prover's shares `s` (`push_legacy_macs`): both commitments, `av` at the
two roots, side 1 at context `(root₁, root₂, av, tags)`, side 2 after it, the distinguisher on the
tags, both proofs and every challenge oracle. -/
noncomputable def realCore2V7 (s : Tag Fmac nblk) (Gav : D × D → Fmac)
    (ρ₁ : Tape P₁.C nw₁ nq₁ reps₁) (b₁ : B₁) (hs₁ : HidingSample n₁ T₁ Salt D) (Gr₁ : RO₁)
    (Gl₁ : LQ₁ → Coin₁)
    (ρ₂ : Tape P₂.C nw₂ nq₂ reps₂) (b₂ : B₂) (hs₂ : HidingSample n₂ T₂ Salt D) (Gr₂ : RO₂)
    (Gl₂ : LQ₂ → Coin₂) : V :=
  let O₁ := commitOut P₁.Cod hs₁.1 (colsOf (v1Oracle (P₁.FE.msgs (wit₁ s) b₁) ρ₁)) hs₁.2
  let O₂ := commitOut P₂.Cod hs₂.1 (colsOf (v1Oracle (P₂.FE.msgs (wit₂ s) b₂) ρ₂)) hs₂.2
  let pf₁ := realProof P₁.dec₁ P₁.dec₂ P₁.FE (ctxOf₁V7 ctx₁ msg s Gav (O₂.1 1) (O₁.1 1)) P₁.pts
    (wit₁ s) ρ₁ b₁ hs₁.1 Gr₁ Gl₁ O₁.1
  let pf₂ := realProof P₂.dec₁ P₂.dec₂ P₂.FE (ctxOf₂V7 ctx₂ msg s Gav pf₁ (O₂.1 1)) P₂.pts
    (wit₂ s) ρ₂ b₂ hs₂.1 Gr₂ Gl₂ O₂.1
  lazyRun2 hs₁.2 hs₂.2 default
    (dist (shiftTag (Gav (pf₁.root, O₂.1 1)) s msg, pf₁, pf₂) (Gav, Gr₁, Gl₁, Gr₂, Gl₂)) O₁.2 O₂.2

/-- **The real two-field experiment with the v7 MAC.**  Coins: the shares `mac_ap`, `av`'s oracle
and each side's real coins — `realExp2`'s coin space. -/
noncomputable def realExp2V7 :
    Tag Fmac nblk × (D × D → Fmac) × RealCoins P₁.C nw₁ nq₁ reps₁ B₁ T₁ Salt D RO₁ LQ₁ Coin₁ ×
      RealCoins P₂.C nw₂ nq₂ reps₂ B₂ T₂ Salt D RO₂ LQ₂ Coin₂ → V :=
  fun ω => realCore2V7 P₁ P₂ ctx₁ ctx₂ wit₁ wit₂ msg dist ω.1 ω.2.1
    ω.2.2.1.1 ω.2.2.1.2.1 ω.2.2.1.2.2.1 ω.2.2.1.2.2.2.1 ω.2.2.1.2.2.2.2
    ω.2.2.2.1 ω.2.2.2.2.1 ω.2.2.2.2.2.1 ω.2.2.2.2.2.2.1 ω.2.2.2.2.2.2.2

/-- Side 1's public input, reading the tags through `maskTag z`. -/
def maskCtx₁ (z : Fin nblk → Bool) : D → D → Fmac → Tag Fmac nblk → Ctx₁ :=
  fun r₁ r₂ av t => ctx₁ r₁ r₂ av (maskTag z t)

/-- Side 2's public input, reading the tags through `maskTag z`. -/
def maskCtx₂ (z : Fin nblk → Bool) :
    D → D → Fmac → Tag Fmac nblk → LProof F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ Salt D Tr₁ Coin₁ → Ctx₂ :=
  fun r₁ r₂ av t pf₁ => ctx₂ r₁ r₂ av (maskTag z t) pf₁

/-- The distinguisher, reading the tags through `maskTag z`. -/
def maskDist (z : Fin nblk → Bool) :
    TwoDistinguisher F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ F₂ r₂ w₂ n₂ nw₂ nq₂ reps₂
      Salt D Enc₁ Enc₂ Tr₁ Tr₂ Coin₁ Coin₂ LQ₁ LQ₂ RO₁ RO₂ Fmac nblk V f :=
  fun p G => dist (maskTag z p.1, p.2.1, p.2.2) G

/--
**The v7 experiment is a v8 experiment.**  At the v8 blinds `shareEquiv msg s`, with the
witnesses read through `(shareEquiv msg).symm` and the public data and the distinguisher reading the
tags through `maskTag (zeroPat msg)`, `realExp2` is the v7 experiment at the shares `s`.
-/
theorem realExp2V7_eq (ω : Tag Fmac nblk × (D × D → Fmac) ×
      RealCoins P₁.C nw₁ nq₁ reps₁ B₁ T₁ Salt D RO₁ LQ₁ Coin₁ ×
      RealCoins P₂.C nw₂ nq₂ reps₂ B₂ T₂ Salt D RO₂ LQ₂ Coin₂) :
    realExp2V7 P₁ P₂ ctx₁ ctx₂ wit₁ wit₂ msg dist ω
      = realExp2 P₁ P₂ (maskCtx₁ ctx₁ (zeroPat msg)) (maskCtx₂ ctx₂ (zeroPat msg))
          (fun b => wit₁ ((shareEquiv msg).symm b)) (fun b => wit₂ ((shareEquiv msg).symm b)) msg
          (maskDist dist (zeroPat msg)) (shareEquiv msg ω.1, ω.2) := by
  simp only [realExp2V7, realCore2V7, realExp2, realCore2, ctxOf₁V7, ctxOf₂V7, ctxOf₁, ctxOf₂,
    maskCtx₁, maskCtx₂, maskDist, Equiv.symm_apply_apply, maskTag_macTag_shareEquiv]

end Defs

end LfzkV1.CompiledLongfellowZkV7Mac
