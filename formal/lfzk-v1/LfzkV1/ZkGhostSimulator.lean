import LfzkV1.ZkGhostProgramming

/-!
# Exact simulation after replacing the two Merkle leaf tables

The commitments' node labels are fixed independently of the Ligero tape, the
sumcheck blinders, and the MAC shares. The two raw Ligero challenges on each
side have already been sampled. At these fixed coins we construct bijections
that preserve the entire proof and all five challenge functions, including the
opened columns that determine the Merkle oracle's opened-leaf programming.
-/

set_option autoImplicit false

namespace LfzkV1.ZkGhostSimulator

open LigeroFamily LigeroFamily.ZeroKnowledge
open LfzkV1.ZkAdaptiveV1 LfzkV1.CompiledLongfellowZk
  LfzkV1.CompiledLongfellowZkTwoField LfzkV1.Mac

section Side

variable {F E : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype E] [DecidableEq E]
variable {r w n nw nq reps : ℕ}
variable {Salt D Enc Coin LQ Ctx Wit Blind Tr RO : Type}
variable (P : Side F r w n nw nq reps E Salt D Enc Coin LQ Ctx Wit Blind Tr RO)

/-- The honest proof at supplied node labels and pre-sampled challenges. -/
noncomputable def honestProof (κ : Ctx) (wit : Wit) (ρ : Tape P.C nw nq reps) (b : Blind)
    (nonce : Fin n → Salt) (Gr : RO) (c i : Coin) (vals : ℕ → D) :
    LProof F r w n nw nq reps Salt D Tr Coin :=
  ZkGhostProgramming.honestProofAt P.dec₁ P.dec₂ P.FE κ wit ρ b nonce Gr c i vals

/-- Reindex the conditional tableau tape, then reindex the blinders as the
transmission. Neither reindexing changes the uniform joint law. -/
noncomputable def sideCoinsEquiv (κ : Ctx) (wit : Wit) (Gr : RO) (c i : Coin)
    (hvalid : P.FE.Valid wit κ) : Blind × Tape P.C nw nq reps ≃ Tr × Tape P.C nw nq reps :=
  let t := Equiv.ofBijective (P.FE.transmit wit Gr κ) (P.FE.transmit_bijective wit Gr κ)
  let e : Blind → Tape P.C nw nq reps ≃ Tape P.C nw nq reps := fun b =>
    adaptiveEquiv (P.FE.msgs wit b) (P.dec₂ i) (P.dec₁ c)
      (fun _ => P.FE.stmt Gr κ (t b)) (fun _ => P.FE.honest_sat wit Gr κ b hvalid)
  (Equiv.prodCongrRight e).trans (t.prodCongr (Equiv.refl _))

/-- The two sides of the tape bijection give identical proof data. Equality
includes the response, both challenges, the opened columns/salts and frontier. -/
theorem simProof_sideCoinsEquiv (κ : Ctx) (wit : Wit) (Gr : RO) (c i : Coin)
    (hvalid : P.FE.Valid wit κ) (nonce : Fin n → Salt) (vals : ℕ → D)
    (x : Blind × Tape P.C nw nq reps) :
    let y := sideCoinsEquiv P κ wit Gr c i hvalid x
    simProof P.dec₁ P.dec₂ P.FE.stmt κ y.2 y.1 c i Gr nonce vals =
      honestProof P κ wit x.2 x.1 nonce Gr c i vals := by
  rcases x with ⟨b, ρ⟩
  have h := adaptive_translate (C := P.C) (P.FE.msgs wit b) (P.dec₂ i) (P.dec₁ c)
    (fun _ => P.FE.stmt Gr κ (P.FE.transmit wit Gr κ b))
    (fun _ => P.FE.honest_sat wit Gr κ b hvalid) ρ
  dsimp [adaptiveSimResp] at h
  dsimp [sideCoinsEquiv, simProof, honestProof, ZkGhostProgramming.honestProofAt,
    Equiv.prodCongr, Equiv.refl, Prod.map]
  rw [h.1, h.2]
  rfl

end Side

/-- The commitment labels and the remaining fixed coins for one side.
The Merkle game supplies labels independently of the secret tape. -/
structure FixedSide (n : ℕ) (Salt D Coin LQ RO : Type) where
  vals : ℕ → D
  nonce : Fin n → Salt
  round : RO
  base : LQ → Coin
  challenge : Coin
  query : Coin

section Joint

variable {F₁ E₁ F₂ E₂ : Type} [Field F₁] [Fintype F₁] [DecidableEq F₁] [Fintype E₁]
  [DecidableEq E₁] [Field F₂] [Fintype F₂] [DecidableEq F₂] [Fintype E₂] [DecidableEq E₂]
variable {r₁ w₁ n₁ nw₁ nq₁ reps₁ r₂ w₂ n₂ nw₂ nq₂ reps₂ : ℕ}
variable {Salt D Enc₁ Enc₂ Coin₁ Coin₂ LQ₁ LQ₂ Ctx₁ Ctx₂ Wit₁ Wit₂ B₁ B₂ Tr₁ Tr₂ RO₁ RO₂ : Type}
variable [DecidableEq LQ₁] [DecidableEq LQ₂]
variable {Fmac : Type} [Field Fmac] {nblk : ℕ}
variable (P₁ : Side F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ E₁ Salt D Enc₁ Coin₁ LQ₁ Ctx₁ Wit₁ B₁ Tr₁ RO₁)
variable (P₂ : Side F₂ r₂ w₂ n₂ nw₂ nq₂ reps₂ E₂ Salt D Enc₂ Coin₂ LQ₂ Ctx₂ Wit₂ B₂ Tr₂ RO₂)
variable (ctx₁ : D → D → Fmac → Tag Fmac nblk → Ctx₁)
variable (ctx₂ : D → D → Fmac → Tag Fmac nblk → LProof F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ Salt D Tr₁ Coin₁ →
  Ctx₂)
variable (Gav : D × D → Fmac)
variable (s₁ : FixedSide n₁ Salt D Coin₁ LQ₁ RO₁) (s₂ : FixedSide n₂ Salt D Coin₂ LQ₂ RO₂)

abbrev JointView
    (_ : Side F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ E₁ Salt D Enc₁ Coin₁ LQ₁ Ctx₁ Wit₁ B₁ Tr₁ RO₁)
    (_ : Side F₂ r₂ w₂ n₂ nw₂ nq₂ reps₂ E₂ Salt D Enc₂ Coin₂ LQ₂ Ctx₂ Wit₂ B₂ Tr₂ RO₂) :=
  TwoProof F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ F₂ r₂ w₂ n₂ nw₂ nq₂ reps₂ Salt D Tr₁ Tr₂ Coin₁ Coin₂ Fmac nblk ×
    TwoOracles D Fmac RO₁ LQ₁ Coin₁ RO₂ LQ₂ Coin₂

section Honest

variable (wit₁ : Tag Fmac nblk → Wit₁) (wit₂ : Tag Fmac nblk → Wit₂) (msg : Fin nblk → Fmac)

/-- The honest arithmetic at the two fixed commitments, showing the whole
proof and all challenge oracles. The observer can then use the proof's openings
to install the Merkle answers. -/
noncomputable def honestJoint
    (x : Tag Fmac nblk × (B₁ × Tape P₁.C nw₁ nq₁ reps₁) × (B₂ × Tape P₂.C nw₂ nq₂ reps₂)) :
    JointView P₁ P₂ (Fmac := Fmac) (nblk := nblk) :=
  let av := Gav (s₁.vals 1, s₂.vals 1)
  let tag := macTag av x.1 msg
  let k₁ := ctx₁ (s₁.vals 1) (s₂.vals 1) av tag
  let p₁ := honestProof P₁ k₁ (wit₁ x.1) x.2.1.2 x.2.1.1 s₁.nonce s₁.round
    s₁.challenge s₁.query s₁.vals
  let k₂ := ctx₂ (s₁.vals 1) (s₂.vals 1) av tag p₁
  let p₂ := honestProof P₂ k₂ (wit₂ x.1) x.2.2.2 x.2.2.1 s₂.nonce s₂.round
    s₂.challenge s₂.query s₂.vals
  ((tag, p₁, p₂), (Gav, s₁.round, simOracle k₁ P₁.pts s₁.base p₁,
    s₂.round, simOracle k₂ P₂.pts s₂.base p₂))

end Honest

/-- The witness-free arithmetic at the same commitments. The first coin is
the uniform tag, and the next two factors give uniform transmissions and
zero-tableau tapes. -/
noncomputable def simJoint
    (x : Tag Fmac nblk × (Tr₁ × Tape P₁.C nw₁ nq₁ reps₁) × (Tr₂ × Tape P₂.C nw₂ nq₂ reps₂)) :
    JointView P₁ P₂ (Fmac := Fmac) (nblk := nblk) :=
  let av := Gav (s₁.vals 1, s₂.vals 1)
  let k₁ := ctx₁ (s₁.vals 1) (s₂.vals 1) av x.1
  let p₁ := simProof P₁.dec₁ P₁.dec₂ P₁.FE.stmt k₁ x.2.1.2 x.2.1.1 s₁.challenge
    s₁.query s₁.round s₁.nonce s₁.vals
  let k₂ := ctx₂ (s₁.vals 1) (s₂.vals 1) av x.1 p₁
  let p₂ := simProof P₂.dec₁ P₂.dec₂ P₂.FE.stmt k₂ x.2.2.2 x.2.2.1 s₂.challenge
    s₂.query s₂.round s₂.nonce s₂.vals
  ((x.1, p₁, p₂), (Gav, s₁.round, simOracle k₁ P₁.pts s₁.base p₁,
    s₂.round, simOracle k₂ P₂.pts s₂.base p₂))

private def fiberEquiv {A B C E : Type} (e : A ≃ B) (f : B → C ≃ E) : A × C ≃ B × E :=
  (e.prodCongr (Equiv.refl _)).trans (Equiv.prodCongrRight f)

section Reindex

variable (wit₁ : Tag Fmac nblk → Wit₁) (wit₂ : Tag Fmac nblk → Wit₂) (msg : Fin nblk → Fmac)
variable
  (hvalid₁ : ∀ ap root₁ root₂ av, P₁.FE.Valid (wit₁ ap) (ctx₁ root₁ root₂ av (macTag av ap msg)))
  (hvalid₂ : ∀ ap root₁ root₂ av p₁,
    P₂.FE.Valid (wit₂ ap) (ctx₂ root₁ root₂ av (macTag av ap msg) p₁))

/-- The tag translation and the two dependent tape translations are one
bijection. The second context uses the first simulated proof, which agrees
pointwise with the honest first proof along the first tape translation. -/
noncomputable def jointCoinsEquiv :
    (Tag Fmac nblk × (B₁ × Tape P₁.C nw₁ nq₁ reps₁) × (B₂ × Tape P₂.C nw₂ nq₂ reps₂)) ≃
      (Tag Fmac nblk × (Tr₁ × Tape P₁.C nw₁ nq₁ reps₁) × (Tr₂ × Tape P₂.C nw₂ nq₂ reps₂)) :=
  let av := Gav (s₁.vals 1, s₂.vals 1)
  let tagMap := tagEquiv av msg
  fiberEquiv tagMap fun tag =>
    let ap := tagMap.symm tag
    let eqTag : macTag av ap msg = tag := tagMap.apply_symm_apply tag
    let k₁ := ctx₁ (s₁.vals 1) (s₂.vals 1) av tag
    fiberEquiv (sideCoinsEquiv P₁ k₁ (wit₁ ap) s₁.round s₁.challenge s₁.query
      (by dsimp [k₁]; rw [← eqTag]; exact hvalid₁ ap _ _ _)) fun y₁ =>
      let p₁ := simProof P₁.dec₁ P₁.dec₂ P₁.FE.stmt k₁ y₁.2 y₁.1 s₁.challenge
        s₁.query s₁.round s₁.nonce s₁.vals
      let k₂ := ctx₂ (s₁.vals 1) (s₂.vals 1) av tag p₁
      sideCoinsEquiv P₂ k₂ (wit₂ ap) s₂.round s₂.challenge s₂.query
        (by dsimp [k₂]; rw [← eqTag]; exact hvalid₂ ap _ _ _ p₁)

include hvalid₁ hvalid₂ in
theorem simJoint_jointCoinsEquiv
    (x : Tag Fmac nblk × (B₁ × Tape P₁.C nw₁ nq₁ reps₁) × (B₂ × Tape P₂.C nw₂ nq₂ reps₂)) :
    simJoint P₁ P₂ ctx₁ ctx₂ Gav s₁ s₂
        (jointCoinsEquiv P₁ P₂ ctx₁ ctx₂ Gav s₁ s₂ wit₁ wit₂ msg hvalid₁ hvalid₂ x) =
      honestJoint P₁ P₂ ctx₁ ctx₂ Gav s₁ s₂ wit₁ wit₂ msg x := by
  simp only [simJoint, honestJoint, jointCoinsEquiv, fiberEquiv, Equiv.trans_apply,
    Equiv.prodCongrRight_apply, Equiv.prodCongr_apply, Prod.map, Equiv.refl_apply, Equiv.symm_apply_apply]
  simp only [simProof_sideCoinsEquiv, tagEquiv_apply]

end Reindex

end Joint

end LfzkV1.ZkGhostSimulator
