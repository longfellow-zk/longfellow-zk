import polygero.Algebra.PolynomialChallenges.CanonicalCore

/-!
Closure of a joint affine system of coordinate equations. The unknown retains
both the polynomial challenge and the response; projecting away the response
would lose the information needed to distinguish fully consistent systems.
-/
namespace RecursivePolygero.Local.ConsistencyClosure
open Finset Submodule
open Shift
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable {n : ℕ}

/-- Joint solutions, with no projection onto a subset of the unknowns. -/
def solutions (A : V →ₗ[F] (Fin n → F)) (offset : Fin n → F)
    (S : Finset (Fin n)) : Set V :=
  {v | ∀ j ∈ S, A v j = offset j}

open scoped Classical in
/-- All coordinate equations implied by the fixed joint system. -/
noncomputable def closure (A : V →ₗ[F] (Fin n → F)) (offset : Fin n → F)
    (S : Finset (Fin n)) : Finset (Fin n) :=
  univ.filter fun j => ∀ v ∈ solutions A offset S, A v j = offset j

@[simp] theorem mem_closure (A : V →ₗ[F] (Fin n → F)) (offset : Fin n → F)
    (S : Finset (Fin n)) (j : Fin n) : j ∈ closure A offset S ↔
      ∀ v ∈ solutions A offset S, A v j = offset j := by
  classical
  simp only [closure, mem_filter, mem_univ, true_and]

theorem subset_closure (A : V →ₗ[F] (Fin n → F)) (offset : Fin n → F)
    (S : Finset (Fin n)) : S ⊆ closure A offset S := by
  classical
  exact fun j hj => mem_filter.mpr ⟨mem_univ _, fun v hv => hv j hj⟩

theorem solutions_antitone (A : V →ₗ[F] (Fin n → F)) (offset : Fin n → F)
    {S T : Finset (Fin n)} (hST : S ⊆ T) : solutions A offset T ⊆ solutions A offset S :=
  fun _ hv j hj => hv j (hST hj)

theorem solutions_closure (A : V →ₗ[F] (Fin n → F)) (offset : Fin n → F)
    (S : Finset (Fin n)) : solutions A offset (closure A offset S) = solutions A offset S := by
  classical
  apply Set.Subset.antisymm (solutions_antitone A offset (subset_closure A offset S))
  exact fun v hv j hj => (mem_filter.mp hj).2 v hv

theorem closure_idempotent (A : V →ₗ[F] (Fin n → F)) (offset : Fin n → F)
    (S : Finset (Fin n)) : closure A offset (closure A offset S) = closure A offset S := by
  classical
  ext j
  rw [mem_closure, mem_closure, solutions_closure]

theorem closure_mono (A : V →ₗ[F] (Fin n → F)) (offset : Fin n → F)
    {S T : Finset (Fin n)} (hST : S ⊆ T) : closure A offset S ⊆ closure A offset T := by
  classical
  intro j hj
  exact mem_filter.mpr ⟨mem_univ _, fun v hv =>
    (mem_filter.mp hj).2 v (solutions_antitone A offset hST hv)⟩

/-- Deduplicating closures is exactly deduplicating joint solution systems. -/
theorem closure_eq_iff_solutions_eq (A : V →ₗ[F] (Fin n → F)) (offset : Fin n → F)
    (S T : Finset (Fin n)) : closure A offset S = closure A offset T ↔
      solutions A offset S = solutions A offset T := by
  constructor
  · intro h
    rw [← solutions_closure A offset S, h, solutions_closure]
  · intro h
    classical
    ext j
    rw [mem_closure, mem_closure, h]

/-- Homogeneous directions of a consistent affine system, expressed using any
one solution as an anchor. -/
theorem mem_solutions_iff_sub_mem_ker (A : V →ₗ[F] (Fin n → F)) (offset : Fin n → F)
    (S : Finset (Fin n)) (anchor : V) (ha : anchor ∈ solutions A offset S) (v : V) :
    v ∈ solutions A offset S ↔ v-anchor ∈ LinearMap.ker ((Shift.restrict S).comp A) := by
  change (∀ j ∈ S, A v j = offset j) ↔ Shift.restrict S (A (v-anchor)) = 0
  rw [← LinearMap.mem_ker, restrict_ker]
  simp only [map_sub, Pi.sub_apply, sub_eq_zero]
  exact ⟨fun hv j hj => (hv j hj).trans (ha j hj).symm,
    fun hv j hj => (hv j hj).trans (ha j hj)⟩

theorem closure_kernel (A : V →ₗ[F] (Fin n → F)) (offset : Fin n → F)
    (S : Finset (Fin n)) (hne : (solutions A offset S).Nonempty) :
    LinearMap.ker ((Shift.restrict (closure A offset S)).comp A) =
      LinearMap.ker ((Shift.restrict S).comp A) := by
  obtain ⟨a, ha⟩ := hne
  have hac : a ∈ solutions A offset (closure A offset S) := by rwa [solutions_closure]
  ext v
  rw [← show (v+a)-a = v by abel]
  rw [← mem_solutions_iff_sub_mem_ker A offset _ a hac,
    ← mem_solutions_iff_sub_mem_ker A offset _ a ha, solutions_closure]

/-- Each deleted coordinate has a direction that vanishes on the core and
is one at that coordinate. This witness is independent of affine offsets. -/
theorem deleted_coordinate_witness (A : V →ₗ[F] (Fin n → F))
    (T : Finset (Fin n)) {j : Fin n}
    (hj : j ∈ T \ canonicalSubset (LinearMap.range A) T) :
    ∃ v : V, v ∈ LinearMap.ker ((Shift.restrict (canonicalSubset (LinearMap.range A) T)).comp A) ∧
      A v j = 1 := by
  classical
  obtain ⟨hjT,hjS⟩ := mem_sdiff.mp hj
  let i : Fin T.card := equivFin T ⟨j,hjT⟩
  have hi : column T i = j := by simp [column,i]
  have hiE : i ∈ coordinateDirections ((LinearMap.range A).map (Shift.restrict T)) := by
    simpa only [hi,not_not] using
      (not_congr (column_mem_canonicalSubset_iff (LinearMap.range A) T i)).mp (hi ▸ hjS)
  obtain ⟨w,⟨v,rfl⟩,hv⟩ := (mem_filter.mp hiE).2
  refine ⟨v,?_,?_⟩
  · change A v ∈ LinearMap.ker (Shift.restrict (canonicalSubset (LinearMap.range A) T))
    apply (restrict_ker _ _).mpr
    intro a ha
    obtain ⟨b,hb,rfl⟩ := mem_image.mp ha
    have hbi : b ≠ i := by
      intro h
      exact (mem_sdiff.mp hb).2 (h ▸ hiE)
    simpa only [Shift.restrict,LinearMap.coe_mk,AddHom.coe_mk,Pi.single_eq_of_ne hbi] using congrFun hv b
  · simpa only [Shift.restrict,LinearMap.coe_mk,AddHom.coe_mk,hi,Pi.single_eq_same] using congrFun hv i

/-- Deleted coordinates cannot meet any set determined by the core kernel. -/
theorem disjoint_deleted_of_kernel_le (A : V →ₗ[F] (Fin n → F))
    (T H : Finset (Fin n))
    (hk : LinearMap.ker ((Shift.restrict (canonicalSubset (LinearMap.range A) T)).comp A) ≤
      LinearMap.ker ((Shift.restrict H).comp A)) :
    Disjoint (T \ canonicalSubset (LinearMap.range A) T) H := by
  classical
  apply disjoint_left.mpr
  intro j hj hjH
  obtain ⟨v,hv,hvj⟩ := deleted_coordinate_witness A T hj
  exact one_ne_zero (hvj.symm.trans ((restrict_ker H _).mp (hk hv) j hjH))

/-- Closure adds no discarded coordinate back to the original system. -/
theorem inter_closure_canonicalSubset (A : V →ₗ[F] (Fin n → F))
    (offset : Fin n → F) (T : Finset (Fin n))
    (hne : (solutions A offset T).Nonempty) :
    T ∩ closure A offset (canonicalSubset (LinearMap.range A) T) =
      canonicalSubset (LinearMap.range A) T := by
  classical
  let S := canonicalSubset (LinearMap.range A) T
  have hST : S ⊆ T := canonicalSubset_subset _ _
  have hd := disjoint_deleted_of_kernel_le A T (closure A offset S)
    (le_of_eq (closure_kernel A offset S (hne.mono (solutions_antitone A offset hST))).symm)
  apply subset_antisymm ?_ (subset_inter hST (subset_closure A offset S))
  intro j hj
  obtain ⟨hjT,hjD⟩ := mem_inter.mp hj
  contrapose! hjD
  exact disjoint_left.mp hd (mem_sdiff.mpr ⟨hjT,hjD⟩)

noncomputable def rank (A : V →ₗ[F] (Fin n → F)) (S : Finset (Fin n)) : ℕ :=
  Module.finrank F (LinearMap.range ((Shift.restrict S).comp A))

theorem rank_eq_restriction (A : V →ₗ[F] (Fin n → F)) (S : Finset (Fin n)) :
    rank A S = Module.finrank F ((LinearMap.range A).map (Shift.restrict S)) := by
  rw [rank, LinearMap.range_comp]

theorem rank_mono (A : V →ₗ[F] (Fin n → F)) {S T : Finset (Fin n)} (hST : S ⊆ T) :
    rank A S ≤ rank A T := by
  rw [rank_eq_restriction, rank_eq_restriction]
  exact restriction_rank_mono _ hST

theorem closure_rank [FiniteDimensional F V]
    (A : V →ₗ[F] (Fin n → F)) (offset : Fin n → F)
    (S : Finset (Fin n)) (hne : (solutions A offset S).Nonempty) :
    rank A (closure A offset S) = rank A S := by
  have hc := LinearMap.finrank_range_add_finrank_ker ((Shift.restrict (closure A offset S)).comp A)
  have hs := LinearMap.finrank_range_add_finrank_ker ((Shift.restrict S).comp A)
  rw [closure_kernel A offset S hne] at hc
  unfold rank
  omega

theorem kernel_eq_of_rank_eq [FiniteDimensional F V] (A : V →ₗ[F] (Fin n → F))
    {S T : Finset (Fin n)} (hST : S ⊆ T) (hr : rank A S = rank A T) :
    LinearMap.ker ((Shift.restrict S).comp A) =
      LinearMap.ker ((Shift.restrict T).comp A) := by
  have hk : LinearMap.ker ((Shift.restrict T).comp A) ≤
      LinearMap.ker ((Shift.restrict S).comp A) := by
    intro v hv
    exact (restrict_ker S _).mpr (fun j hj => (restrict_ker T _).mp hv j (hST hj))
  have hs := LinearMap.finrank_range_add_finrank_ker ((Shift.restrict S).comp A)
  have ht := LinearMap.finrank_range_add_finrank_ker ((Shift.restrict T).comp A)
  exact (Submodule.eq_of_le_of_finrank_le hk (by dsimp [rank] at hr; omega)).symm

/-- Nested consistent systems of equal rank have the same affine solutions. -/
theorem solutions_eq_of_rank_eq [FiniteDimensional F V]
    (A : V →ₗ[F] (Fin n → F)) (offset : Fin n → F)
    {S T : Finset (Fin n)} (hST : S ⊆ T)
    (hne : (solutions A offset T).Nonempty) (hr : rank A S = rank A T) :
    solutions A offset S = solutions A offset T := by
  obtain ⟨a,ha⟩ := hne
  have haS := solutions_antitone A offset hST ha
  ext v
  rw [mem_solutions_iff_sub_mem_ker A offset S a haS,
    mem_solutions_iff_sub_mem_ker A offset T a ha,kernel_eq_of_rank_eq A hST hr]

/-- Equal ranks of nested consistent systems mean that every added equation
is already implied. Consistency cannot be omitted from this statement. -/
theorem subset_closure_of_rank_eq [FiniteDimensional F V]
    (A : V →ₗ[F] (Fin n → F)) (offset : Fin n → F)
    {S T : Finset (Fin n)} (hST : S ⊆ T)
    (hne : (solutions A offset T).Nonempty) (hr : rank A S = rank A T) :
    T ⊆ closure A offset S := by
  have he := solutions_eq_of_rank_eq A offset hST hne hr
  intro j hj
  apply (mem_closure A offset S j).mpr
  intro v hv
  exact (he ▸ hv) j hj

/-- Restricting the index set preserves the rank of its equations. -/
theorem rank_restrict (A : V →ₗ[F] (Fin n → F))
    {S T : Finset (Fin n)} (hST : S ⊆ T) :
    rank ((Shift.restrict T).comp A) (localColumns T S) = rank A S := by
  rw [rank_eq_restriction, LinearMap.range_comp]
  exact (restriction_rank_through (LinearMap.range A) hST).trans (rank_eq_restriction A S).symm

/-- Coordinate equation rank is submodular. -/
theorem rank_submodular [FiniteDimensional F V] (A : V →ₗ[F] (Fin n → F)) (D E : Finset (Fin n)) :
    rank A (D ∪ E) + rank A (D ∩ E) ≤ rank A D + rank A E := by
  classical
  let kd := LinearMap.ker ((Shift.restrict D).comp A)
  let ke := LinearMap.ker ((Shift.restrict E).comp A)
  have hu : LinearMap.ker ((Shift.restrict (D ∪ E)).comp A) = kd ⊓ ke := by
    ext v
    simp only [LinearMap.mem_ker, LinearMap.comp_apply]
    rw [← LinearMap.mem_ker, restrict_ker]
    simp only [Submodule.mem_inf, kd, ke, LinearMap.mem_ker, LinearMap.comp_apply]
    rw [← LinearMap.mem_ker, ← LinearMap.mem_ker, restrict_ker, restrict_ker]
    simp only [mem_union]
    aesop
  have hi : kd ⊔ ke ≤ LinearMap.ker ((Shift.restrict (D ∩ E)).comp A) := by
    apply sup_le
    · intro v hv
      apply LinearMap.mem_ker.mpr
      apply (restrict_ker _ _).mpr
      intro j hj
      exact (restrict_ker _ _).mp (LinearMap.mem_ker.mp hv) j (mem_inter.mp hj).1
    · intro v hv
      apply LinearMap.mem_ker.mpr
      apply (restrict_ker _ _).mpr
      intro j hj
      exact (restrict_ker _ _).mp (LinearMap.mem_ker.mp hv) j (mem_inter.mp hj).2
  have hsup := Submodule.finrank_mono hi
  have hsum := kd.finrank_sup_add_finrank_inf_eq ke
  have hd := LinearMap.finrank_range_add_finrank_ker ((Shift.restrict D).comp A)
  have he := LinearMap.finrank_range_add_finrank_ker ((Shift.restrict E).comp A)
  have hh := LinearMap.finrank_range_add_finrank_ker ((Shift.restrict (D ∩ E)).comp A)
  have ht := LinearMap.finrank_range_add_finrank_ker ((Shift.restrict (D ∪ E)).comp A)
  rw [hu] at ht
  dsimp [rank, kd, ke] at *
  omega

/-- Equal-rank nested equation sets still have equal rank after adjoining
the same equations. This follows directly from rank submodularity. -/
theorem rank_union_eq_of_rank_eq [FiniteDimensional F V]
    (A : V →ₗ[F] (Fin n → F)) {S T : Finset (Fin n)}
    (hST : S ⊆ T) (hr : rank A S = rank A T) (E : Finset (Fin n)) :
    rank A (S ∪ E) = rank A (T ∪ E) := by
  classical
  apply Nat.le_antisymm (rank_mono A (union_subset_union hST Subset.rfl))
  have hs := rank_submodular A T (S ∪ E)
  rw [← union_assoc, union_eq_left.mpr hST] at hs
  have hi := rank_mono A (subset_inter hST (subset_union_left : S ⊆ S ∪ E))
  omega

/-- Adjoining a set of equations increases rank by at most its cardinality. -/
theorem rank_union_le_rank_add_card [FiniteDimensional F V]
    (A : V →ₗ[F] (Fin n → F)) (S E : Finset (Fin n)) :
    rank A (S ∪ E) ≤ rank A S + E.card := by
  have hs := rank_submodular A S E
  have he : rank A E ≤ E.card := by
    simpa [rank] using Submodule.finrank_le (LinearMap.range ((Shift.restrict E).comp A))
  omega

/-- If adjoining E increases rank by its full cardinality, E is disjoint
from every equation set with the same coefficient-row span as S. -/
theorem disjoint_of_rank_add_card [FiniteDimensional F V]
    (A : V →ₗ[F] (Fin n → F)) (S S' E : Finset (Fin n))
    (hr : rank A S = rank A (S ∪ S'))
    (hr' : rank A S' = rank A (S ∪ S'))
    (hadd : rank A (S ∪ E) = rank A S + E.card) : Disjoint E S' := by
  classical
  have hsame := (rank_union_eq_of_rank_eq A subset_union_left hr E).trans
    (rank_union_eq_of_rank_eq A subset_union_right hr' E).symm
  have hbound := rank_union_le_rank_add_card A S' (E \ S')
  rw [union_sdiff_self_eq_union] at hbound
  have hcards := card_sdiff_add_card_inter E S'
  have hrr := hr.trans hr'.symm
  have hzero : (E ∩ S').card = 0 := by omega
  exact disjoint_iff_inter_eq_empty.mpr (card_eq_zero.mp hzero)


end RecursivePolygero.Local.ConsistencyClosure
