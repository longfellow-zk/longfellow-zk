import polygero.Algebra.PolynomialChallenges.Shift.Growth

namespace RecursivePolygero.Local.Shift
open Submodule
variable {F M N : Type*} [Field F] [AddCommGroup M] [Module F M]
  [AddCommGroup N] [Module F N] [FiniteDimensional F M]

/-- Rank--nullity for restriction of a linear map to a subspace, with its
kernel expressed in the original ambient space. -/
theorem restriction_rank_nullity (f : M →ₗ[F] N) (U : Submodule F M) :
    Module.finrank F (U.map f) + Module.finrank F (U ⊓ LinearMap.ker f : Submodule F M) =
      Module.finrank F U := by
  have hd := LinearMap.finrank_range_add_finrank_ker (f.domRestrict U)
  have hr : LinearMap.range (f.domRestrict U) = U.map f := by
    ext v
    exact ⟨fun ⟨a,ha⟩ => ⟨a,a.2,ha⟩,fun ⟨a,ha,he⟩ => ⟨⟨a,ha⟩,he⟩⟩
  have hk : (LinearMap.ker (f.domRestrict U)).map U.subtype = U ⊓ LinearMap.ker f := by
    ext v
    exact ⟨fun ⟨a,ha,he⟩ => he ▸ ⟨a.2,ha⟩,fun ⟨hv,hf⟩ => ⟨⟨v,hv⟩,hf,rfl⟩⟩
  rw [hr,← Submodule.finrank_map_subtype_eq, hk] at hd
  exact hd

end RecursivePolygero.Local.Shift
