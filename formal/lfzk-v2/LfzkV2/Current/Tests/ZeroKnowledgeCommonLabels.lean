import LfzkV2.Current.ZeroKnowledge.CommonLabels

/-! The common-label change of coins may depend on the root-label tape.
This is precisely the dependence that prevents a conditional-independence
argument at the actual commitment root. -/
namespace LfzkV2.Current.Tests.ZeroKnowledgeCommonLabels

open ZeroKnowledge.CommonLabels

def shift (tape : Fin 1 → Bool) : Bool ≃ Bool :=
  if tape 0 then Equiv.swap false true else Equiv.refl Bool

example (backend : Bool) (nonce : Fin 2 → Bool) (tape : Fin 1 → Bool) :
    (fiberEquiv shift) (backend,nonce,tape) = (shift tape backend,nonce,tape) := rfl

example (coin : Bool × ((Fin 2 → Bool) × (Fin 1 → Bool))) :
    (fiberEquiv shift).symm ((fiberEquiv shift) coin) = coin :=
  (fiberEquiv shift).symm_apply_apply coin

#print axioms fiberEquiv
#print axioms compiled_hiding

end LfzkV2.Current.Tests.ZeroKnowledgeCommonLabels
