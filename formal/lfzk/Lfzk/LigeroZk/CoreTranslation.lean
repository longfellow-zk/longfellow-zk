import LigeroFamily.Protocol.HonestCore
import Lfzk.LigeroZk.Conditional

-- Ported verbatim from `proofs/ligero/LigeroFamily/ZeroKnowledge/CoreTranslation.lean` (only the import paths are rewritten);
-- `formal/ligero/` must not change, so the module lives under `Lfzk.LigeroZk`.
set_option autoImplicit false
set_option relaxedAutoImplicit false

/-! # Mask-independent Longfellow core-row witness translation -/

namespace LigeroFamily

open MultiplicativeCode

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {r w n : ℕ}

noncomputable def interpolationQuery
    (C : MultiplicativeCode F r w n) : QuerySet n C.k :=
  Classical.choice (QuerySet.nonempty C.k_le_n)

omit [Fintype F] [DecidableEq F] in
@[simp] theorem interpolationQuery_card
    (C : MultiplicativeCode F r w n) :
    (interpolationQuery C).coordinates.card = C.k :=
  QuerySet.card_coordinates _

noncomputable def openedRowEquiv
    (C : MultiplicativeCode F r w n) (query : QuerySet n r)
    (witness : Fin w → F) : (Fin r → F) ≃ (↥query.coordinates → F) :=
  Equiv.ofBijective (openedRow C query.coordinates witness)
    (longfellow_openings_bijective C query.coordinates
      (QuerySet.card_coordinates query) witness)

noncomputable def translateCorePaddingEquiv
    (C : MultiplicativeCode F r w n) (query : QuerySet n r)
    (fromWitness toWitness : Fin w → F) : (Fin r → F) ≃ (Fin r → F) :=
  (openedRowEquiv C query fromWitness).trans
    (openedRowEquiv C query toWitness).symm

noncomputable def translateCorePadding
    (C : MultiplicativeCode F r w n) (query : QuerySet n r)
    (fromWitness toWitness : Fin w → F) (padding : Fin r → F) : Fin r → F :=
  translateCorePaddingEquiv C query fromWitness toWitness padding

omit [Fintype F] [DecidableEq F] in
theorem translateCorePadding_opening
    (C : MultiplicativeCode F r w n) (query : QuerySet n r)
    (fromWitness toWitness : Fin w → F) (padding : Fin r → F) :
    openedRow C query.coordinates toWitness
        (translateCorePadding C query fromWitness toWitness padding) =
      openedRow C query.coordinates fromWitness padding :=
  (openedRowEquiv C query toWitness).apply_symm_apply _

def witnessSumLinearMap : (Fin w → F) →ₗ[F] F where
  toFun values := ∑ i, values i
  map_add' left right := Finset.sum_add_distrib
  map_smul' scalar values := by simp [Finset.mul_sum]

end LigeroFamily
