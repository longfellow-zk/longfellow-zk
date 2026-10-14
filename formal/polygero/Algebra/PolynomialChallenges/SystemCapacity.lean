import polygero.Algebra.PolynomialChallenges.CoreOverlap

/-! Fixed capacities of actual compatible analysis sets, with no padding or
independent-coordinate extension. -/
namespace RecursivePolygero.Local.ReducedSystems
open Finset Codes PolynomialClosure ConsistencyClosure
variable {F : Type*} [Field F] {n m k s : ℕ}

/-- A system's cap is attained by an existing analysis set in its defining family. -/
theorem capacity_witness (C : RSCode F n (k+s)) (W : Fin m → Word F n)
    (mask : Word F n) (D : Finset (Fin n)) (hD : D ∈ family C W mask) :
    ∃ T ∈ associatedSets C W mask D, T.card = capacity C W mask D := by
  classical
  obtain ⟨S,hS,he⟩ := mem_image.mp hD
  obtain ⟨_,hsize,hlow,hne⟩ := mem_filter.mp hS
  have hmem : S ∈ associatedSets C W mask D :=
    mem_filter.mpr ⟨mem_univ _,hsize,hlow,hne,he⟩
  obtain ⟨T,hT,hmax⟩ := exists_max_image (associatedSets C W mask D) Finset.card ⟨S,hmem⟩
  exact ⟨T,hT,le_antisymm (Finset.le_sup hT) (Finset.sup_le hmax)⟩

theorem capacity_le_n (C : RSCode F n (k+s)) (W : Fin m → Word F n)
    (mask : Word F n) (D : Finset (Fin n)) : capacity C W mask D ≤ n := by
  apply Finset.sup_le
  intro T _
  simpa using card_le_univ T

/-- Any actual analysis sets assigned to different systems have small overlap. -/
theorem associated_intersection (C : RSCode F n (k+s)) (W : Fin m → Word F n)
    (mask : Word F n) (hk : 1 ≤ k) (D E T T' : Finset (Fin n))
    (hT : T ∈ associatedSets C W mask D) (hT' : T' ∈ associatedSets C W mask E)
    (hne : D ≠ E) : (T ∩ T').card ≤ k+2*s-1 := by
  classical
  obtain ⟨_,hsize,hlow,hneT,hlabel⟩ := mem_filter.mp hT
  obtain ⟨_,hsize',hlow',hneT',hlabel'⟩ := mem_filter.mp hT'
  contrapose! hne
  have hsame := canonical_closures_eq C W mask hk T T' hlow hlow'
    (by omega) (by omega) hneT hneT' (by omega)
  exact hlabel.symm.trans (hsame.trans hlabel')

end RecursivePolygero.Local.ReducedSystems
