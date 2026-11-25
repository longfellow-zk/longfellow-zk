import LfzkV1.ZkGhostProgramming
import LfzkV1.ZkGhostTwoField
import LfzkV1.ZkLazyOracleLaw

/-! The joint eager Merkle game presents the same bounded observer interface
and samples the same honest experiment as the existing two lazy tapes. -/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace LfzkV1.ZkGhostLegacyBridge

open Merkle Merkle.MH Merkle.RandomOracle
open LfzkV1.CompiledLongfellowZk LfzkV1.CompiledLongfellowZkTwoField
  LfzkV1.ZkGhostTwoField LfzkV1.ZkGhostProgramming LfzkV1.ZkGhostSimulator LfzkV1.ZkTwoTape

private theorem commitPass_zero {Salt M D Enc : Type} [DecidableEq Enc] [Inhabited D]
    (C : Codec Salt M D Enc) {n : ℕ} (s : Fin n → Salt) (m : Fin n → M) (H : Enc → D)
    (k : ℕ) (vals : ℕ → D) :
    ((commitPass C n s m k vals).run H).1 0 = vals 0 := by
  induction k generalizing vals with
  | zero => rfl
  | succ k ih =>
    rw [commitPass]
    split
    · simp [ih]
    · split <;> simp [ih]

private theorem commitPass_labels {Salt M D Enc : Type} [DecidableEq Enc] [Inhabited D]
    (C : Codec Salt M D Enc) {n : ℕ} (s : Fin n → Salt) (m : Fin n → M) (H : Enc → D) :
    ((commitPass C n s m (2*n-1) (fun _ => default)).run H).1 =
       commitLabels (C.withOracle H) n s m := by
  funext v
  cases v with
  | zero =>
    rw [commitPass_zero, commitLabels]
    by_cases hn : n = 0 <;> simp [hn]
  | succ v =>
    refine commitPass_run C n s m H _ _ (fun w hw => ?_) _ (Nat.succ_pos _)
    rw [commitLabels_of_ge]
    omega

section Fixed

variable {F₁ E₁ F₂ E₂ : Type} [Field F₁] [Fintype F₁] [DecidableEq F₁] [Fintype E₁]
  [Field F₂] [Fintype F₂] [DecidableEq F₂] [Fintype E₂]
variable {r₁ w₁ n₁ nw₁ nq₁ reps₁ r₂ w₂ n₂ nw₂ nq₂ reps₂ : ℕ}
variable {Salt D Enc₁ Enc₂ Coin₁ Coin₂ LQ₁ LQ₂ Ctx₁ Ctx₂ Wit₁ Wit₂ B₁ B₂ Tr₁ Tr₂ RO₁ RO₂ : Type}
variable [Inhabited D] [DecidableEq Enc₁] [DecidableEq Enc₂] [DecidableEq LQ₁] [DecidableEq LQ₂]
variable {Fmac : Type} [Field Fmac] {nblk Q : ℕ} {V : Type}

variable (P₁ : Side F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ E₁ Salt D Enc₁ Coin₁ LQ₁ Ctx₁ Wit₁ B₁ Tr₁ RO₁)
variable (P₂ : Side F₂ r₂ w₂ n₂ nw₂ nq₂ reps₂ E₂ Salt D Enc₂ Coin₂ LQ₂ Ctx₂ Wit₂ B₂ Tr₂ RO₂)
variable (ctx₁ : D → D → Fmac → Tag Fmac nblk → Ctx₁)
variable (ctx₂ : D → D → Fmac → Tag Fmac nblk → LProof F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ Salt D Tr₁ Coin₁ →
  Ctx₂)
variable (dist : TwoDistinguisher F₁ r₁ w₁ n₁ nw₁ nq₁ reps₁ F₂ r₂ w₂ n₂ nw₂ nq₂ reps₂
  Salt D Enc₁ Enc₂ Tr₁ Tr₂ Coin₁ Coin₂ LQ₁ LQ₂ RO₁ RO₂ Fmac nblk V Q)
variable (wit₁ : Tag Fmac nblk → Wit₁) (wit₂ : Tag Fmac nblk → Wit₂) (msg : Fin nblk → Fmac)
variable (g : ChallengeCoins D Fmac RO₁ LQ₁ Coin₁ RO₂ LQ₂ Coin₂)
variable (x : HonestTape P₁ P₂ (Fmac := Fmac) (nblk := nblk)) (s : Index n₁ n₂ → Salt)

private theorem programmedCore2_observerAtLabels {T₁ T₂ : ℕ} (τ₁ : Fin T₁ → D) (τ₂ : Fin T₂ → D) :
    let cols := payloads P₁ P₂ wit₁ wit₂ x
    let o₁ := commitOut P₁.Cod (s ∘ Sum.inl) cols.1 τ₁
    let o₂ := commitOut P₂.Cod (s ∘ Sum.inr) cols.2 τ₂
    programmedCore2 P₁ P₂ ctx₁ ctx₂ wit₁ wit₂ msg dist x.1 g.1
      x.2.1.2 x.2.1.1 (s ∘ Sum.inl, τ₁) g.2.1.1 g.2.1.2.1 g.2.1.2.2.1 g.2.1.2.2.2
      x.2.2.2 x.2.2.1 (s ∘ Sum.inr, τ₂) g.2.2.1 g.2.2.2.1 g.2.2.2.2.1 g.2.2.2.2.2 =
    lazyRun2 τ₁ τ₂ default (observerAtLabels P₁ P₂ ctx₁ ctx₂ dist wit₁ wit₂ msg g x s o₁.1 o₂.1)
      o₁.2 o₂.2 := rfl

open LfzkV1.ZkLazyOracleLaw

private noncomputable def fullProgram :
    Merkle.RandomOracle.Tree (Enc₁ ⊕ Enc₂) D V (Q + (2 * n₂ - 1) + (2 * n₁ - 1)) :=
  let cols := payloads P₁ P₂ wit₁ wit₂ x
  let t₁ := commitPass P₁.Cod n₁ (s ∘ Sum.inl) cols.1 (2 * n₁ - 1) (fun _ => default)
  let t₂ := commitPass P₂.Cod n₂ (s ∘ Sum.inr) cols.2 (2 * n₂ - 1) (fun _ => default)
  (tagLeft t₁).bind fun v₁ => (tagRight t₂).bind fun v₂ =>
    observerAtLabels P₁ P₂ ctx₁ ctx₂ dist wit₁ wit₂ msg g x s v₁ v₂

private theorem programmedCore2_lazy {T₁ T₂ : ℕ} (τ₁ : Fin T₁ → D) (τ₂ : Fin T₂ → D) :
    programmedCore2 P₁ P₂ ctx₁ ctx₂ wit₁ wit₂ msg dist x.1 g.1
      x.2.1.2 x.2.1.1 (s ∘ Sum.inl, τ₁) g.2.1.1 g.2.1.2.1 g.2.1.2.2.1 g.2.1.2.2.2
      x.2.2.2 x.2.2.1 (s ∘ Sum.inr, τ₂) g.2.2.1 g.2.2.2.1 g.2.2.2.2.1 g.2.2.2.2.2 =
    lazyRun2 τ₁ τ₂ default (fullProgram P₁ P₂ ctx₁ ctx₂ dist wit₁ wit₂ msg g x s) [] [] := by
  rw [programmedCore2_observerAtLabels, fullProgram, lazyRun2_tagLeft_bind, lazyRun2_tagRight_bind]
  rfl

private theorem programmedCore2_eager (H₁ : Enc₁ → D) (H₂ : Enc₂ → D) :
    ((fullProgram P₁ P₂ ctx₁ ctx₂ dist wit₁ wit₂ msg g x s).run (Sum.elim H₁ H₂)).1 =
      eagerProgrammedCore P₁ P₂ ctx₁ ctx₂ dist wit₁ wit₂ msg g x s (Sum.elim H₁ H₂) := by
  dsimp only [fullProgram]
  simp only [Tree.run_bind, run_tagLeft, run_tagRight, eagerProgrammedCore, commitPass_labels]
  rfl

variable [Fintype D] [DecidableEq D] [Fintype Enc₁] [Fintype Enc₂]

theorem programmedCore2_statClose_eager {T₁ T₂ : ℕ}
    (hT₁ : Q + (2 * n₂ - 1) + (2 * n₁ - 1) ≤ T₁)
    (hT₂ : Q + (2 * n₂ - 1) + (2 * n₁ - 1) ≤ T₂) :
    StatClose 0
      (fun τ : (Fin T₁ → D) × (Fin T₂ → D) =>
        programmedCore2 P₁ P₂ ctx₁ ctx₂ wit₁ wit₂ msg dist x.1 g.1
          x.2.1.2 x.2.1.1 (s ∘ Sum.inl, τ.1) g.2.1.1 g.2.1.2.1 g.2.1.2.2.1 g.2.1.2.2.2
          x.2.2.2 x.2.2.1 (s ∘ Sum.inr, τ.2) g.2.2.1 g.2.2.2.1 g.2.2.2.2.1 g.2.2.2.2.2)
      (fun H : Enc₁ ⊕ Enc₂ → D =>
        eagerProgrammedCore P₁ P₂ ctx₁ ctx₂ dist wit₁ wit₂ msg g x s H) := by
  have h := lazyRun2_statClose default (fullProgram P₁ P₂ ctx₁ ctx₂ dist wit₁ wit₂ msg g x s) hT₁ hT₂
  refine statClose_reindex (Equiv.refl _) (Equiv.sumArrowEquivProdArrow _ _ _) ?_ ?_ h
  · intro τ
    exact programmedCore2_lazy P₁ P₂ ctx₁ ctx₂ dist wit₁ wit₂ msg g x s τ.1 τ.2
  · intro H
    have he : Sum.elim (H ∘ Sum.inl) (H ∘ Sum.inr) = H := by funext p; cases p <;> rfl
    exact he ▸ (programmedCore2_eager P₁ P₂ ctx₁ ctx₂ dist wit₁ wit₂ msg g x s
      (H ∘ Sum.inl) (H ∘ Sum.inr)).symm

end Fixed

end LfzkV1.ZkGhostLegacyBridge
