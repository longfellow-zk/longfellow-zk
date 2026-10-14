import polygero.Algebra.ProximityGap

/-!
Canonical coordinate reduction and elementary rank identities, followed by
MDS restriction ranks for slowly growing word spaces. These are structural
statements, independent of challenges or soundness bounds.
-/
namespace RecursivePolygero.Local.Shift
open Finset Submodule Polynomial
variable {F : Type*} [Field F] {n : ℕ}

noncomputable def canonicalCore (U : Submodule F (Fin n → F)) : Finset (Fin n) :=
  univ \ coordinateDirections U

noncomputable def coreSpace (U : Submodule F (Fin n → F)) :
    Submodule F (Fin (canonicalCore U).card → F) :=
  U.map (restrict (canonicalCore U))

theorem core_rank_add_directions (U : Submodule F (Fin n → F)) :
    Module.finrank F (coreSpace U) + (coordinateDirections U).card =
      Module.finrank F U := by
  classical
  have hk := kernel_le_of_singles (coordinateDirections U) U
    (fun _ hj => (mem_filter.mp hj).2)
  have hd := restriction_rank_nullity (restrict (F := F) (canonicalCore U)) U
  change LinearMap.ker (restrict (canonicalCore U)) ≤ U at hk
  rw [inf_eq_right.mpr hk] at hd
  have hf := LinearMap.finrank_range_add_finrank_ker (restrict (F := F) (canonicalCore U))
  rw [LinearMap.range_eq_top.mpr (restrict_surjective _), finrank_top,
    Module.finrank_fin_fun, Module.finrank_fin_fun] at hf
  have hc := card_sdiff_add_card_eq_card (subset_univ (coordinateDirections U))
  simp only [card_univ, Fintype.card_fin] at hc
  change Module.finrank F (coreSpace U) + _ = _ at hd
  change (canonicalCore U).card + _ = n at hc
  omega

/-- Deleting all coordinate directions cannot create a new coordinate direction. -/
theorem coreSpace_unitfree (U : Submodule F (Fin n → F)) :
    coordinateDirections (coreSpace U) = ∅ := by
  classical
  apply eq_empty_iff_forall_notMem.mpr
  intro i hi
  obtain ⟨u, hu, he⟩ := (mem_filter.mp hi).2
  let j := column (canonicalCore U) i
  have hj : j ∉ coordinateDirections U := (mem_sdiff.mp (column_mem _ i)).2
  have hs : restrict (canonicalCore U) (Pi.single j (1 : F)) = Pi.single i 1 := by
    ext a
    change (Pi.single j (1 : F) : Fin n → F) (column (canonicalCore U) a) =
      (Pi.single i (1 : F) : Fin (canonicalCore U).card → F) a
    simp only [Pi.single_apply]
    simp only [show column (canonicalCore U) a = j ↔ a = i from
      (column_injective _).eq_iff]
  have hk := kernel_le_of_singles (coordinateDirections U) U
    (fun _ hj => (mem_filter.mp hj).2)
  have hz : u-Pi.single j (1 : F) ∈ LinearMap.ker (restrict (canonicalCore U)) := by
    change restrict (canonicalCore U) (u-Pi.single j (1 : F)) = 0
    rw [map_sub, he, hs, sub_self]
  have hv : Pi.single j (1 : F) ∈ U := by
    have h := U.sub_mem hu (hk hz)
    simpa only [sub_sub_cancel] using h
  exact hj (mem_filter.mpr ⟨mem_univ _, hv⟩)

/-- Restriction rank is monotone in the set of retained coordinates. -/
theorem restriction_rank_mono (U : Submodule F (Fin n → F))
    {H T : Finset (Fin n)} (hHT : H ⊆ T) :
    Module.finrank F (U.map (restrict H)) ≤ Module.finrank F (U.map (restrict T)) := by
  have hk : U ⊓ LinearMap.ker (restrict T) ≤ U ⊓ LinearMap.ker (restrict H) := by
    intro u hu
    exact ⟨hu.1, (restrict_ker H u).mpr (fun j hj => (restrict_ker T u).mp hu.2 j (hHT hj))⟩
  have h := Submodule.finrank_mono hk
  have hH := restriction_rank_nullity (restrict H) U
  have hT := restriction_rank_nullity (restrict T) U
  omega

open scoped Classical in
/-- The indices of `H` in the coordinate system obtained by restricting to `T`. -/
noncomputable def localColumns (T H : Finset (Fin n)) : Finset (Fin T.card) :=
  univ.filter fun j => column T j ∈ H

theorem localColumns_image (T : Finset (Fin n)) (H : Finset (Fin T.card)) :
    localColumns T (H.image (column T)) = H := by
  classical
  ext j
  simp [localColumns, mem_image, (column_injective T).eq_iff]

theorem image_localColumns (T H : Finset (Fin n)) :
    (localColumns T H).image (column T) = T ∩ H := by
  classical
  ext j
  constructor
  · intro hj
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hj
    exact mem_inter.mpr ⟨column_mem _ _, (mem_filter.mp hi).2⟩
  · intro hj
    obtain ⟨hjT, hjH⟩ := mem_inter.mp hj
    refine mem_image.mpr ⟨equivFin T ⟨j, hjT⟩, ?_, ?_⟩ <;>
      simp [localColumns, column, hjH]

theorem localColumns_card {T H : Finset (Fin n)} (hHT : H ⊆ T) :
    (localColumns T H).card = H.card := by
  classical
  rw [← card_image_of_injective _ (column_injective T), image_localColumns,
    inter_eq_right.mpr hHT]

/-- The absence of coordinate directions is independent of the indexing of a
restricted word space. -/
theorem restriction_unitfree_through (U : Submodule F (Fin n → F))
    {T S : Finset (Fin n)} (hST : S ⊆ T)
    (hfree : coordinateDirections (U.map (restrict S)) = ∅) :
    coordinateDirections ((U.map (restrict T)).map (restrict (localColumns T S))) = ∅ := by
  classical
  apply eq_empty_iff_forall_notMem.mpr
  intro j hj
  obtain ⟨v, ⟨u, hu, rfl⟩, he⟩ := (mem_filter.mp hj).2
  let a := column (localColumns T S) j
  have ha : column T a ∈ S := (mem_filter.mp (column_mem (localColumns T S) j)).2
  let b := equivFin S ⟨column T a, ha⟩
  have hv : restrict S u = Pi.single b (1 : F) := by
    ext i
    let z := column S i
    have hz : z ∈ T := hST (column_mem S i)
    let ti := equivFin T ⟨z, hz⟩
    have hti : ti ∈ localColumns T S := by
      simp [ti, localColumns, column, z]
    let si := equivFin (localColumns T S) ⟨ti, hti⟩
    have hi : si = j ↔ i = b := by
      constructor
      · intro hij
        have hv := congrArg (fun l => column T (column (localColumns T S) l)) hij
        have hval : column S i = column S b := by simpa [si, ti, column, b, a, z] using hv
        exact column_injective S hval
      · intro hib
        subst i
        apply column_injective (localColumns T S)
        apply column_injective T
        simp [si, ti, column, b, a, z]
    have hv := congrFun he si
    simp only [Pi.single_apply, hi] at hv
    simpa [restrict, column, si, ti, z, Pi.single_apply] using hv
  have hb : b ∈ coordinateDirections (U.map (restrict S)) :=
    mem_filter.mpr ⟨mem_univ _, ⟨u, hu, hv⟩⟩
  simp [hfree] at hb

/-- The converse reindexing direction for coordinate-unit freeness. -/
theorem restriction_unitfree_of_through (U : Submodule F (Fin n → F))
    {T S : Finset (Fin n)} (hST : S ⊆ T)
    (hfree : coordinateDirections ((U.map (restrict T)).map
      (restrict (localColumns T S))) = ∅) :
    coordinateDirections (U.map (restrict S)) = ∅ := by
  classical
  apply eq_empty_iff_forall_notMem.mpr
  intro j hj
  obtain ⟨u, hu, he⟩ := (mem_filter.mp hj).2
  let a := equivFin T ⟨column S j, hST (column_mem _ _)⟩
  have ha : a ∈ localColumns T S := by simp [a, localColumns, column]
  let b := equivFin (localColumns T S) ⟨a, ha⟩
  have hv : restrict (localColumns T S) (restrict T u) = Pi.single b (1 : F) := by
    ext i
    let c := column (localColumns T S) i
    have hc : column T c ∈ S := (mem_filter.mp (column_mem _ i)).2
    let d := equivFin S ⟨column T c, hc⟩
    have hd : d = j ↔ i = b := by
      constructor
      · intro h
        apply column_injective (localColumns T S)
        apply column_injective T
        simpa [b,a,d,c,column] using congrArg (column S) h
      · intro h
        subst i
        apply column_injective S
        simp [d,c,b,a,column]
    have h := congrFun he d
    change u (column T c) = (Pi.single b (1 : F) : Fin (localColumns T S).card → F) i
    have hcol : column S d = column T c := by simp [d, column]
    change u (column S d) = (Pi.single j (1 : F) : Fin S.card → F) d at h
    rw [hcol] at h
    simpa only [Pi.single_apply, hd] using h
  have hb : b ∈ coordinateDirections ((U.map (restrict T)).map
      (restrict (localColumns T S))) :=
    mem_filter.mpr ⟨mem_univ _, ⟨restrict T u, ⟨u,hu,rfl⟩, hv⟩⟩
  simp [hfree] at hb

/-- Restricting twice changes the indexing but not the rank. -/
theorem restriction_rank_through (U : Submodule F (Fin n → F))
    {T H : Finset (Fin n)} (hHT : H ⊆ T) :
    Module.finrank F ((U.map (restrict T)).map (restrict (localColumns T H))) =
      Module.finrank F (U.map (restrict H)) := by
  classical
  let f := (restrict (F := F) (localColumns T H)).comp (restrict T)
  have hk : LinearMap.ker f = LinearMap.ker (restrict H) := by
    ext u
    change restrict (localColumns T H) (restrict T u) = 0 ↔ restrict H u = 0
    rw [← LinearMap.mem_ker, ← LinearMap.mem_ker, restrict_ker, restrict_ker]
    constructor
    · intro h j hj
      have hi : equivFin T ⟨j, hHT hj⟩ ∈ localColumns T H := by
        simp [localColumns, column, hj]
      simpa [restrict, column] using h _ hi
    · intro h j hj
      exact h _ (mem_filter.mp hj).2
  have h1 := restriction_rank_nullity f U
  have h2 := restriction_rank_nullity (restrict H) U
  rw [hk] at h1
  rw [← Submodule.map_comp]
  change Module.finrank F (U.map f) = _
  omega

/-- For the restriction kernel `J`, invariance of `U ⊓ J` leaves only coordinate
 directions. Otherwise explosion makes restriction surjective. The two cases
 give the minimum-rank formula directly. -/
theorem rank_on_core_subset (x : Fin n → F) (hx : Function.Injective x)
    (U : Submodule F (Fin n → F)) (h1 : evaluate x 1 ∈ U)
    (hg : Module.finrank F (grow (shift x) U) ≤ Module.finrank F U + 1)
    (_hn : Module.finrank F U < n) (H : Finset (Fin n))
    (hH : H ⊆ canonicalCore U) :
    Module.finrank F (U.map (restrict H)) =
      min H.card (Module.finrank F (coreSpace U)) := by
  classical
  let J := LinearMap.ker (restrict (F := F) H)
  have hJ : J.map (shift x) ≤ J := by
    rintro _ ⟨u, hu, rfl⟩
    apply (restrict_ker H _).mpr
    intro j hj
    change x j * u j = 0
    rw [(restrict_ker H u).mp hu j hj, mul_zero]
  by_cases hstable : (U ⊓ J).map (shift x) ≤ U ⊓ J
  · have hker : U ⊓ J = U ⊓ LinearMap.ker (restrict (canonicalCore U)) := by
      apply le_antisymm
      · intro u hu
        refine ⟨hu.1, (restrict_ker _ u).mpr ?_⟩
        intro j hj
        by_cases hz : u j = 0
        · exact hz
        have hshifts (a : ℕ) : ((shift x)^a) u ∈ U ⊓ J := by
          induction a with
          | zero => simpa using hu
          | succ a ih =>
            rw [pow_succ', Module.End.mul_apply]
            exact hstable ⟨_, ih, rfl⟩
        have he := single_mem_of_shifts x hx (U ⊓ J) u hshifts j hz
        exact False.elim ((mem_sdiff.mp hj).2 (mem_filter.mpr ⟨mem_univ j, he.1⟩))
      · intro u hu
        exact ⟨hu.1, (restrict_ker H u).mpr (fun j hj =>
          (restrict_ker _ u).mp hu.2 j (hH hj))⟩
    have hdH := restriction_rank_nullity (restrict H) U
    have hdS := restriction_rank_nullity (restrict (canonicalCore U)) U
    change Module.finrank F (U.map (restrict H)) + Module.finrank F ↥(U ⊓ J) = _ at hdH
    rw [hker] at hdH
    have heq : Module.finrank F (U.map (restrict H)) = Module.finrank F (coreSpace U) := by
      change _ = Module.finrank F (U.map (restrict (canonicalCore U)))
      omega
    have hle : Module.finrank F (U.map (restrict H)) ≤ H.card := by
      simpa using Submodule.finrank_le (U.map (restrict H))
    rw [heq, min_eq_right (heq ▸ hle)]
  · have hex := RecursivePolygero.explosion (shift x) U J (evaluate x 1) h1
      (span_shifts_one x hx) hg hJ hstable
    have htop : U.map (restrict H) = ⊤ :=
      (LinearMap.map_eq_top_iff (LinearMap.range_eq_top.mpr (restrict_surjective H))).mpr hex
    have hle := restriction_rank_mono U hH
    change _ ≤ Module.finrank F (coreSpace U) at hle
    rw [htop, finrank_top, Module.finrank_fin_fun] at hle ⊢
    exact (min_eq_left hle).symm

/-- In the absence of coordinate directions the core is the whole word space. -/
theorem restriction_rank_eq_min (x : Fin n → F) (hx : Function.Injective x)
    (U : Submodule F (Fin n → F)) (h1 : evaluate x 1 ∈ U)
    (hg : Module.finrank F (grow (shift x) U) ≤ Module.finrank F U + 1)
    (hn : Module.finrank F U < n) (hfree : coordinateDirections U = ∅)
    (H : Finset (Fin n)) :
    Module.finrank F (U.map (restrict H)) = min H.card (Module.finrank F U) := by
  have hr := core_rank_add_directions U
  simp only [hfree, card_empty, add_zero] at hr
  rw [← hr]
  exact rank_on_core_subset x hx U h1 hg hn H (by simp [canonicalCore, hfree])

/-- A coordinate direction survives every restriction containing its index. -/
theorem subset_core_of_restriction_unitfree (U : Submodule F (Fin n → F))
    (S : Finset (Fin n)) (hfree : coordinateDirections (U.map (restrict S)) = ∅) :
    S ⊆ canonicalCore U := by
  classical
  intro j hj
  refine mem_sdiff.mpr ⟨mem_univ _, ?_⟩
  intro he
  let i : Fin S.card := equivFin S ⟨j, hj⟩
  have hi : Pi.single i (1 : F) ∈ U.map (restrict S) := by
    refine ⟨Pi.single j 1, (mem_filter.mp he).2, ?_⟩
    have hcol : column S i = j := by simp [column, i]
    ext a
    change (Pi.single j (1 : F) : Fin n → F) (column S a) =
      (Pi.single i (1 : F) : Fin S.card → F) a
    have heq : column S a = j ↔ a = i := by rw [← hcol]; exact (column_injective S).eq_iff
    simp only [Pi.single_apply, heq]
  have hmem : i ∈ coordinateDirections (U.map (restrict S)) :=
    mem_filter.mpr ⟨mem_univ _, hi⟩
  simp [hfree] at hmem

/-- A unit-free restriction of equal rank makes the original space unit-free. -/
theorem unitfree_of_restriction_rank_eq (U : Submodule F (Fin n → F))
    (S : Finset (Fin n)) (hfree : coordinateDirections (U.map (restrict S)) = ∅)
    (hr : Module.finrank F (U.map (restrict S)) = Module.finrank F U) :
    coordinateDirections U = ∅ := by
  classical
  have hd := restriction_rank_nullity (restrict S) U
  have hz : U ⊓ LinearMap.ker (restrict S) = ⊥ :=
    Submodule.finrank_eq_zero.mp (by omega)
  have hsub := subset_core_of_restriction_unitfree U S hfree
  apply eq_empty_iff_forall_notMem.mpr
  intro j hj
  have hjS : j ∉ S := fun h => (mem_sdiff.mp (hsub h)).2 hj
  have hk : Pi.single j (1 : F) ∈ LinearMap.ker (restrict S) := by
    apply (restrict_ker _ _).mpr
    intro a ha
    have hne : a ≠ j := by intro he; subst a; exact hjS ha
    simp only [Pi.single_apply, if_neg hne]
  have hm : Pi.single j (1 : F) ∈ U ⊓ LinearMap.ker (restrict S) :=
    ⟨(mem_filter.mp hj).2,hk⟩
  rw [hz] at hm
  have he : (Pi.single j (1 : F) : Fin n → F) = 0 := by
    simp only [Submodule.mem_bot] at hm
    exact hm
  have hh := congrFun he j
  simp at hh

theorem rank_lt_of_restriction_rank_lt (U : Submodule F (Fin n → F))
    (S : Finset (Fin n)) (hS : Module.finrank F (U.map (restrict S)) < S.card) :
    Module.finrank F U < n := by
  have hd := restriction_rank_nullity (restrict S) U
  have hk := Submodule.finrank_mono (inf_le_right :
    U ⊓ LinearMap.ker (restrict S) ≤ LinearMap.ker (restrict S))
  have hf := LinearMap.finrank_range_add_finrank_ker (restrict (F := F) S)
  rw [LinearMap.range_eq_top.mpr (restrict_surjective S), finrank_top,
    Module.finrank_fin_fun, Module.finrank_fin_fun] at hf
  omega

/-- Canonical coordinates of a restricted word space, expressed in the original
ambient index set. -/
noncomputable def canonicalSubset (U : Submodule F (Fin n → F)) (T : Finset (Fin n)) :
    Finset (Fin n) :=
  (canonicalCore (U.map (restrict T))).image (column T)

theorem canonicalSubset_subset (U : Submodule F (Fin n → F)) (T : Finset (Fin n)) :
    canonicalSubset U T ⊆ T := by
  classical
  intro j hj
  obtain ⟨i, _, rfl⟩ := mem_image.mp hj
  exact column_mem T i

/-- Membership of an original coordinate in the canonical subset. -/
theorem column_mem_canonicalSubset_iff (U : Submodule F (Fin n → F))
    (T : Finset (Fin n)) (i : Fin T.card) :
    column T i ∈ canonicalSubset U T ↔ i ∉ coordinateDirections (U.map (restrict T)) := by
  classical
  simp [canonicalSubset,canonicalCore,mem_image,(column_injective T).eq_iff]

theorem canonicalSubset_card (U : Submodule F (Fin n → F)) (T : Finset (Fin n)) :
    (canonicalSubset U T).card + (coordinateDirections (U.map (restrict T))).card = T.card := by
  classical
  rw [canonicalSubset, card_image_of_injective _ (column_injective T)]
  simpa [canonicalCore] using
    card_sdiff_add_card_eq_card (subset_univ (coordinateDirections (U.map (restrict T))))

theorem canonicalSubset_rank (U : Submodule F (Fin n → F)) (T : Finset (Fin n)) :
    Module.finrank F (U.map (restrict (canonicalSubset U T))) =
      Module.finrank F (coreSpace (U.map (restrict T))) := by
  have h := restriction_rank_through U (canonicalSubset_subset U T)
  rw [show localColumns T (canonicalSubset U T) = canonicalCore (U.map (restrict T)) from
    localColumns_image T _] at h
  exact h.symm

theorem canonicalSubset_unitfree (U : Submodule F (Fin n → F)) (T : Finset (Fin n)) :
    coordinateDirections (U.map (restrict (canonicalSubset U T))) = ∅ := by
  apply restriction_unitfree_of_through U (canonicalSubset_subset U T)
  rw [show localColumns T (canonicalSubset U T) = canonicalCore (U.map (restrict T)) from
    localColumns_image T _]
  exact coreSpace_unitfree _

/-- A coordinate direction on a union would survive on a constituent. -/
theorem unitfree_union (U : Submodule F (Fin n → F)) (D E : Finset (Fin n))
    (hd : coordinateDirections (U.map (Shift.restrict D)) = ∅)
    (he : coordinateDirections (U.map (Shift.restrict E)) = ∅) :
    coordinateDirections (U.map (Shift.restrict (D ∪ E))) = ∅ := by
  classical
  let T := D ∪ E
  let Z := U.map (Shift.restrict T)
  have hD := subset_core_of_restriction_unitfree Z (localColumns T D)
    (restriction_unitfree_through U subset_union_left hd)
  have hE := subset_core_of_restriction_unitfree Z (localColumns T E)
    (restriction_unitfree_through U subset_union_right he)
  apply eq_empty_iff_forall_notMem.mpr
  intro j hj
  have hm : column T j ∈ D ∪ E := column_mem T j
  have hc : j ∈ canonicalCore Z := by
    rcases mem_union.mp hm with h | h
    · exact hD (mem_filter.mpr ⟨mem_univ _, h⟩)
    · exact hE (mem_filter.mpr ⟨mem_univ _, h⟩)
  exact (mem_sdiff.mp hc).2 hj


end RecursivePolygero.Local.Shift

namespace RecursivePolygero.ProximityGap
open Finset Submodule Polynomial Local.Shift
variable {F : Type*} [Field F] {n m : ℕ}

/-- Polynomial word spaces commute with puncturing. -/
theorem polynomialSpace_restrict (x : Fin n → F) (W : Fin m → (Fin n → F))
    (k s : ℕ) (T : Finset (Fin n)) :
    (polynomialSpace x W k s).map (restrict T) =
      polynomialSpace (x ∘ column T) (fun i => restrict T (W i)) k s := by
  rw [polynomialSpace, polynomialSpace, Submodule.map_sup]
  congr 1
  · unfold evalSpace
    rw [← Submodule.map_comp]
    rfl
  · rw [← LinearMap.range_comp]
    rfl

end RecursivePolygero.ProximityGap
