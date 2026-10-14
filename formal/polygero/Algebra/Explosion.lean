import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The explosion lemma

An invariant subspace that absorbs the only new direction of a space containing
a cyclic vector completes it to the whole ambient space (paper, Lemma 3.1).
-/

namespace RecursivePolygero
open Submodule

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
  [FiniteDimensional F V]

/-- If `U` contains a cyclic vector and grows by at most one dimension under `L`,
then any invariant `J` for which `U ⊓ J` is not invariant satisfies `U ⊔ J = ⊤`. -/
theorem explosion (L : Module.End F V) (U J : Submodule F V) (c : V)
    (hc : c ∈ U) (hcyclic : span F (Set.range fun a : ℕ => (L ^ a) c) = ⊤)
    (hg : Module.finrank F ↥(U ⊔ U.map L) ≤ Module.finrank F U + 1)
    (hJ : J.map L ≤ J) (hescape : ¬ (U ⊓ J).map L ≤ U ⊓ J) :
    U ⊔ J = ⊤ := by
  classical
  obtain ⟨_, ⟨v, hv, rfl⟩, hout⟩ := SetLike.not_le_iff_exists.mp hescape
  have hvJ : L v ∈ J := hJ ⟨v, hv.2, rfl⟩
  have hvU : L v ∉ U := fun h => hout ⟨h, hvJ⟩
  have heq : U ⊔ span F {L v} = U ⊔ U.map L := by
    apply Submodule.eq_of_le_of_finrank_le
    · exact sup_le le_sup_left (span_le.mpr (by
        rintro _ (rfl : _ = L v)
        exact mem_sup_right ⟨v, hv.1, rfl⟩))
    · rw [finrank_sup_span_singleton hvU]
      exact hg
  have hgJ : U ⊔ U.map L ≤ U ⊔ J := by
    rw [← heq]
    exact sup_le le_sup_left (span_le.mpr (by
      rintro _ (rfl : _ = L v)
      exact mem_sup_right hvJ))
  have hstable : (U ⊔ J).map L ≤ U ⊔ J := by
    rw [Submodule.map_sup]
    exact sup_le (le_trans le_sup_right hgJ) (le_trans hJ le_sup_right)
  apply top_unique
  rw [← hcyclic]
  apply span_le.mpr
  rintro _ ⟨a, rfl⟩
  change (L ^ a) c ∈ U ⊔ J
  induction a with
  | zero => simpa using (mem_sup_left hc : c ∈ U ⊔ J)
  | succ a ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact hstable ⟨_, ih, rfl⟩

end RecursivePolygero
