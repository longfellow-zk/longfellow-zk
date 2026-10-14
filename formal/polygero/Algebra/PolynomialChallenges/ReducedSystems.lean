import polygero.Algebra.PolynomialChallenges.PolynomialClosure

/-! Fixed reduced systems with rank defect bounded by the challenge degree. -/
namespace RecursivePolygero.Local.ReducedSystems
open Finset Codes Shift PolynomialClosure
variable {F : Type*} [Field F] {n m k s : ℕ}

open scoped Classical in
/-- Construct every admissible core, enlarge it to its closure, and keep the
distinct closures. `Finset.image` removes duplicates; no representative core
is selected for a system. All subsequent data are attached to the closure. -/
noncomputable def family (C : RSCode F n (k+s)) (W : Fin m → Word F n)
    (mask : Word F n) : Finset (Finset (Fin n)) :=
  (univ.filter fun T : Finset (Fin n) => k+s+s+1 ≤ T.card ∧
    fixedConsistencyCodimension C W T s ≤ s ∧
    (ConsistencyClosure.solutions (jointMap C W) mask T).Nonempty).image
      fun T => closure C W mask (canonicalCoreSet C W T)

structure Geometry (C : RSCode F n (k+s)) (W : Fin m → Word F n)
    (mask : Word F n) (D : Finset (Fin n)) : Prop where
  core : IsCore C W D
  closed : closure C W mask D = D
  nonempty : (ConsistencyClosure.solutions (jointMap C W) mask D).Nonempty

theorem canonical_mem_family (C : RSCode F n (k+s)) (W : Fin m → Word F n)
    (mask : Word F n) (T : Finset (Fin n))
    (hsize : k+s+s+1 ≤ T.card) (hlow : fixedConsistencyCodimension C W T s ≤ s)
    (hne : (ConsistencyClosure.solutions (jointMap C W) mask T).Nonempty) :
    closure C W mask (canonicalCoreSet C W T) ∈ family C W mask := by
  classical
  exact mem_image.mpr ⟨T, mem_filter.mpr ⟨mem_univ _,hsize,hlow,hne⟩,rfl⟩

/-- Every closure retains its core's rank defect and unit-freeness. -/
theorem geometry (C : RSCode F n (k+s)) (W : Fin m → Word F n)
    (mask : Word F n)
    (D : Finset (Fin n)) (hD : D ∈ family C W mask) : Geometry C W mask D := by
  classical
  obtain ⟨T,hT,rfl⟩ := mem_image.mp hD
  obtain ⟨_,hsize,hlow,hne⟩ := mem_filter.mp hT
  obtain ⟨hcore,hsub,_⟩ := canonical_core C W T hlow (by omega)
  have hneS := hne.mono (ConsistencyClosure.solutions_antitone _ _ hsub)
  obtain ⟨hg,_⟩ := closure_geometry C W mask _ hcore hneS
  refine ⟨hg,ConsistencyClosure.closure_idempotent _ _ _,?_⟩
  rwa [ConsistencyClosure.solutions_closure]

open scoped Classical in
/-- Actual consistent analysis sets assigned to the indicated affine closure. -/
noncomputable def associatedSets (C : RSCode F n (k+s)) (W : Fin m → Word F n)
    (mask : Word F n) (D : Finset (Fin n)) : Finset (Finset (Fin n)) :=
  univ.filter fun T => k+s+s+1 ≤ T.card ∧ fixedConsistencyCodimension C W T s ≤ s ∧
    (ConsistencyClosure.solutions (jointMap C W) mask T).Nonempty ∧
    closure C W mask (canonicalCoreSet C W T) = D

/-- The largest actual compatible set assigned to a system. No set is enlarged. -/
noncomputable def capacity (C : RSCode F n (k+s)) (W : Fin m → Word F n)
    (mask : Word F n) (D : Finset (Fin n)) : ℕ :=
  (associatedSets C W mask D).sup Finset.card

/-- A large consistent good set is assigned to one fixed reduced system. The
defect drop equals the number of columns discarded when passing to that system. -/
theorem assign (C : RSCode F n (k+s)) (W : Fin m → Word F n)
    (mask : Word F n)
    (G : Finset (Fin n)) (hsize : k+s+s+1 ≤ G.card)
    (hlow : fixedConsistencyCodimension C W G s ≤ s)
    (v : Challenge F m s × DegreeLT F (k+s))
    (hv : v ∈ ConsistencyClosure.solutions (jointMap C W) mask G) :
    ∃ D ∈ family C W mask,
      v ∈ ConsistencyClosure.solutions (jointMap C W) mask D ∧
      fixedConsistencyCodimension C W D s+(G \ D).card = fixedConsistencyCodimension C W G s ∧
      G.card ≤ capacity C W mask D := by
  let S := canonicalCoreSet C W G
  let D := closure C W mask S
  have hne : (ConsistencyClosure.solutions (jointMap C W) mask G).Nonempty := ⟨v,hv⟩
  obtain ⟨hcore,hsub,hdrop⟩ := canonical_core C W G hlow (by omega)
  have hneS := hne.mono (ConsistencyClosure.solutions_antitone _ _ hsub)
  have hdefect := (closure_geometry C W mask S hcore hneS).2
  have hinter : G ∩ D = S := ConsistencyClosure.inter_closure_canonicalSubset _ _ _ hne
  have houtside : G \ D = G \ S := by
    rw [← hinter]
    exact (sdiff_inter_self_left G D).symm
  have hbudget : fixedConsistencyCodimension C W D s+(G \ D).card =
      fixedConsistencyCodimension C W G s := by
    rw [hdefect,houtside]
    exact hdrop
  have hd : D ∈ family C W mask := canonical_mem_family C W mask G hsize hlow hne
  refine ⟨D,hd,?_,?_,?_⟩
  · rw [ConsistencyClosure.solutions_closure]
    exact ConsistencyClosure.solutions_antitone _ _ hsub hv
  · exact hbudget
  · classical
    exact Finset.le_sup (f := Finset.card)
      (show G ∈ associatedSets C W mask D from
        mem_filter.mpr ⟨mem_univ _,hsize,hlow,hne,rfl⟩)

end RecursivePolygero.Local.ReducedSystems
