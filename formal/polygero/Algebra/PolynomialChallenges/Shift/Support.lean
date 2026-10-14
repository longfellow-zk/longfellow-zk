import polygero.Algebra.PolynomialChallenges.Shift.Restriction
import polygero.Algebra.PolynomialChallenges.Shift.ResidualGrowth

namespace RecursivePolygero.Local.Shift
open Finset Submodule Polynomial
variable {F : Type*} [Field F] {n : ℕ}

open scoped Classical in
/-- Coordinate directions already contained in the fixed word space. -/
noncomputable def coordinateDirections (U : Submodule F (Fin n → F)) : Finset (Fin n) :=
  univ.filter fun j => Pi.single j (1 : F) ∈ U

noncomputable def column (J : Finset (Fin n)) (j : Fin J.card) : Fin n :=
  ((equivFin J).symm j).val

theorem column_injective (J : Finset (Fin n)) : Function.Injective (column J) :=
  fun _ _ h => (equivFin J).symm.injective (Subtype.ext h)

theorem column_mem (J : Finset (Fin n)) (j : Fin J.card) : column J j ∈ J :=
  ((equivFin J).symm j).property

noncomputable def restrict (J : Finset (Fin n)) : (Fin n → F) →ₗ[F] (Fin J.card → F) where
  toFun w j := w (column J j)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem restrict_surjective (J : Finset (Fin n)) : Function.Surjective (restrict (F := F) J) := by
  classical
  intro w
  refine ⟨fun j => if h : j ∈ J then w (equivFin J ⟨j,h⟩) else 0,?_⟩
  ext j
  simp [restrict,column]

theorem restrict_ker (J : Finset (Fin n)) (w : Fin n → F) :
    w ∈ LinearMap.ker (restrict J) ↔ ∀ j ∈ J, w j = 0 := by
  constructor
  · intro h j hj
    have he := congrFun (LinearMap.mem_ker.mp h) (equivFin J ⟨j,hj⟩)
    simpa [restrict,column] using he
  · intro h
    ext j
    exact h _ (column_mem J j)

/-- Membership of each shift permits interpolation to isolate every nonzero coordinate. -/
theorem single_mem_of_shifts (x : Fin n → F) (hx : Function.Injective x)
    (U : Submodule F (Fin n → F)) (w : Fin n → F)
    (hshifts : ∀ a : ℕ, ((shift x)^a) w ∈ U)
    (j : Fin n) (hj : w j ≠ 0) : Pi.single j 1 ∈ U := by
  classical
  let p := Lagrange.interpolate univ x (fun a => if a=j then (w j)⁻¹ else 0)
  have hp : p ∈ degreeLT F n := mem_degreeLT.mpr (by
    simpa only [card_univ,Fintype.card_fin] using Lagrange.degree_interpolate_lt (v := x) (r := fun a => if a=j then (w j)⁻¹ else 0)
      (s := univ) hx.injOn)
  have hm := multiplyWord_mem x U w p (degreeLT_mono (Nat.le_succ n) hp)
    (fun a _ => hshifts a)
  have he : multiplyWord x p w = Pi.single j 1 := by
    ext a
    have hi := Lagrange.eval_interpolate_at_node (s := univ) (v := x)
      (r := fun a => if a=j then (w j)⁻¹ else 0) hx.injOn (mem_univ a)
    change p.eval (x a)*w a = _
    rw [hi]
    by_cases ha : a=j
    · subst a; simp [hj]
    · simp [ha]
  exact he ▸ hm

/-- The constant word is cyclic for the shift at distinct evaluation points. -/
theorem span_shifts_one (x : Fin n → F) (hx : Function.Injective x) :
    span F (Set.range fun a : ℕ => ((shift x)^a) (evaluate x 1)) = ⊤ := by
  apply top_unique
  rw [← evalSpace_top x hx]
  apply (evalSpace_le_iff x n _).mpr
  intro j _
  have h : ((shift x)^j) (evaluate x 1) ∈
      span F (Set.range fun a : ℕ => ((shift x)^a) (evaluate x 1)) :=
    subset_span (Set.mem_range_self j)
  simpa [shift_pow_evaluate] using h

/-- All coordinate vectors in `I` span every word supported on `I`. -/
theorem kernel_le_of_singles (I : Finset (Fin n)) (U : Submodule F (Fin n → F))
    (hI : ∀ j ∈ I, Pi.single j 1 ∈ U) : LinearMap.ker (restrict (univ \ I)) ≤ U := by
  classical
  intro w hw
  have he : w = ∑ j ∈ I, w j • Pi.single j (1 : F) := by
    ext a
    by_cases ha : a ∈ I
    · simp [Pi.single_apply,apply_ite,ha]
    · have hz := (restrict_ker _ w).mp hw a (mem_sdiff.mpr ⟨mem_univ _,ha⟩)
      simp [Pi.single_apply,apply_ite,ha,hz]
  rw [he]
  exact U.sum_mem (fun j hj => U.smul_mem _ (hI j hj))

/-- A proper word space containing the evaluation code has few coordinate directions.
The fixed set is bounded before any residual is supplied. -/
theorem coordinate_directions_card_le (x : Fin n → F) (hx : Function.Injective x)
    (U : Submodule F (Fin n → F)) (R : ℕ)
    (hcode : evalSpace x R ≤ U) (hn : Module.finrank F U < n) :
    (coordinateDirections U).card ≤ Module.finrank F U-R := by
  classical
  let I := coordinateDirections U
  let J := univ \ I
  let f := restrict (F := F) J
  have hk := kernel_le_of_singles I U (fun _ hj => (mem_filter.mp hj).2)
  have hdim := restriction_rank_nullity f U
  rw [inf_eq_right.mpr hk] at hdim
  have hfull := LinearMap.finrank_range_add_finrank_ker f
  rw [LinearMap.range_eq_top.mpr (restrict_surjective J),finrank_top,Module.finrank_fin_fun,
    Module.finrank_fin_fun] at hfull
  have hc : J.card+I.card=n := by
    simpa [J] using card_sdiff_add_card_eq_card (subset_univ I)
  have hkerdim : Module.finrank F (LinearMap.ker f) = I.card := by omega
  rw [hkerdim] at hdim
  have hsmall : evalSpace (x ∘ column J) (min R J.card) ≤ U.map f := by
    rintro v ⟨p,hp,rfl⟩
    exact ⟨evaluate x p,hcode ⟨p,degreeLT_mono (Nat.min_le_left ..) hp,rfl⟩,rfl⟩
  have hle := Submodule.finrank_mono hsmall
  rw [finrank_evalSpace _ (hx.comp (column_injective J)) (Nat.min_le_right ..)] at hle
  change I.card ≤ _
  omega
end RecursivePolygero.Local.Shift
