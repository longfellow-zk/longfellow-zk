import LigeroFamily.Protocol.DirectProduct
import LigeroFamily.Soundness.PolicySelectedMCA

/-! # Common extractor instance for direct-product arithmetic -/

namespace LigeroFamily

open MultiplicativeCode

variable {F Equations : Type*} [Field F] [Fintype F]
variable [Fintype Equations]
variable {q r w n nw nq : ℕ}

/-- V3's selected-MCA tail contains only the linear challenge. -/
def directChallengeProductEquiv :
    DirectChallenge F Equations nw nq 1 ≃
      (Equations → F) × SchemeSelectedMCA.Weights F LinearConstraintMask nw nq :=
  (Equiv.funUnique (Fin 1)
    (DirectRoundChallenge F Equations nw nq 1)).trans
    ((directRoundChallengeEquiv F Equations nw nq 1).trans
      (Equiv.prodComm _ _))

noncomputable def directExtractorPolicy
    (C : MultiplicativeCode F r w n) (M : C.MaskingBasis)
    (layout : ConstraintLayout F q w) :
    SchemeExtractorPolicy
      (DirectVerifier.policy (Equations := Equations) (nw := nw) (nq := nq)
        (repetitions := 1) C M layout)
      (Equations → F) where
  challengeProductEquiv := directChallengeProductEquiv
  weights_eq := by intro challenge; rfl

namespace DirectChallengeCounting

noncomputable def liftLinear [DecidableEq F] [DecidableEq Equations]
    (special : Finset (Equations → F)) :
    Finset (DirectChallenge F Equations nw nq 1) := by
  classical
  exact Finset.univ.filter fun challenge => (challenge 0).linear ∈ special

omit [Field F] in
theorem card_liftLinear [DecidableEq F] [DecidableEq Equations]
    (special : Finset (Equations → F)) :
    (liftLinear (nw := nw) (nq := nq) special).card =
      special.card *
        Fintype.card (SchemeSelectedMCA.Weights F LinearConstraintMask nw nq) := by
  classical
  let target := special ×ˢ
    (Finset.univ : Finset
      (SchemeSelectedMCA.Weights F LinearConstraintMask nw nq))
  calc
    (liftLinear (nw := nw) (nq := nq) special).card = target.card := by
      apply Finset.card_bij (fun challenge _ => directChallengeProductEquiv challenge)
      · intro challenge hchallenge
        apply Finset.mem_product.mpr
        refine ⟨?_, Finset.mem_univ _⟩
        change (challenge 0).linear ∈ special
        exact (Finset.mem_filter.mp hchallenge).2
      · intro first _ second _ hequal
        exact directChallengeProductEquiv.injective hequal
      · intro value hvalue
        refine ⟨directChallengeProductEquiv.symm value, ?_,
          directChallengeProductEquiv.apply_symm_apply value⟩
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        change (directChallengeProductEquiv
          (directChallengeProductEquiv.symm value)).1 ∈ special
        rw [directChallengeProductEquiv.apply_symm_apply]
        exact (Finset.mem_product.mp hvalue).1
    _ = _ := by simp [target]

omit [Field F] in
theorem liftLinear_density [DecidableEq F] [DecidableEq Equations]
    (denominator bound : ℕ) (special : Finset (Equations → F))
    (hspecial : denominator * special.card ≤
      bound * Fintype.card (Equations → F)) :
    denominator * (liftLinear (nw := nw) (nq := nq) special).card ≤
      bound * Fintype.card (DirectChallenge F Equations nw nq 1) := by
  rw [card_liftLinear]
  have hcard : Fintype.card (DirectChallenge F Equations nw nq 1) =
      Fintype.card (Equations → F) *
        Fintype.card
          (SchemeSelectedMCA.Weights F LinearConstraintMask nw nq) :=
    (Fintype.card_congr directChallengeProductEquiv).trans
      (Fintype.card_prod (Equations → F)
        (SchemeSelectedMCA.Weights F LinearConstraintMask nw nq))
  rw [hcard]
  calc
    denominator * (special.card *
        Fintype.card (SchemeSelectedMCA.Weights F LinearConstraintMask nw nq)) =
      (denominator * special.card) *
        Fintype.card (SchemeSelectedMCA.Weights F LinearConstraintMask nw nq) := by
      ring
    _ ≤ (bound * Fintype.card (Equations → F)) *
        Fintype.card (SchemeSelectedMCA.Weights F LinearConstraintMask nw nq) := by
      gcongr
    _ = bound * (Fintype.card (Equations → F) *
        Fintype.card (SchemeSelectedMCA.Weights F LinearConstraintMask nw nq)) := by
      ring

end DirectChallengeCounting

end LigeroFamily
