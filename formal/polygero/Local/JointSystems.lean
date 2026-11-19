import polygero.Algebra.Counting.JointFamilies
import polygero.Algebra.PolynomialChallenges.SystemCapacity

/-! The joint counting family instantiated with the two fields' actual
reduced systems. A common good-column set keeps both canonical assignments. -/
noncomputable section
namespace RecursivePolygero.Local.ReducedSystems.Joint
open Finset Codes PolynomialClosure Shift
open scoped Classical

variable {F G : Type} [Field F] [Field G] {n k s m₁ m₂ : ℕ}
variable (C₁ : RSCode F n (k+s)) (W₁ : Fin m₁ → Word F n) (mask₁ : Word F n)
variable (C₂ : RSCode G n (k+s)) (W₂ : Fin m₂ → Word G n) (mask₂ : Word G n)

def sets {H : Type} [Field H] {m : ℕ} (C : RSCode H n (k+s))
    (W : Fin m → Word H n) (mask : Word H n) (d : ↥(family C W mask)) :=
  associatedSets C W mask d.1

abbrev Label := JointFamilies.Label (sets C₁ W₁ mask₁) (sets C₂ W₂ mask₂)

/-- Preserve the common set in the assignment result. The separate-field
`assign` theorem exposes its capacity only; joint counting needs the actual
set so that both participants describe the same opened columns. -/
theorem associated_data {H : Type} [Field H] {m : ℕ}
    (C : RSCode H n (k+s)) (W : Fin m → Word H n) (mask : Word H n)
    (D T : Finset (Fin n)) (hT : T ∈ associatedSets C W mask D)
    (v : Challenge H m s × DegreeLT H (k+s))
    (hv : v ∈ ConsistencyClosure.solutions (jointMap C W) mask T) :
    v ∈ ConsistencyClosure.solutions (jointMap C W) mask D ∧
      fixedConsistencyCodimension C W D s + (T \ D).card =
        fixedConsistencyCodimension C W T s := by
  obtain ⟨_,hsize,hlow,hne,hlabel⟩ := mem_filter.mp hT
  obtain ⟨hcore,hsub,hdrop⟩ := canonical_core C W T hlow (by omega)
  have hneS := hne.mono (ConsistencyClosure.solutions_antitone _ _ hsub)
  have hdefect := (closure_geometry C W mask _ hcore hneS).2
  have hinter : T ∩ D = canonicalCoreSet C W T := by
    rw [← hlabel]
    exact ConsistencyClosure.inter_closure_canonicalSubset (jointMap C W) mask T hne
  have houtside : T \ D = T \ canonicalCoreSet C W T := by
    rw [← hinter]
    exact (sdiff_inter_self_left T D).symm
  constructor
  · rw [← hlabel, ConsistencyClosure.solutions_closure]
    exact ConsistencyClosure.solutions_antitone _ _ hsub hv
  · rw [← hlabel, hdefect]
    rw [hlabel, houtside]
    exact hdrop

/-- Enlarging a common good set cannot change its canonical system when the
larger set is still consistent and has low defect. Otherwise the two assigned
sets would overlap in more columns than the one-field overlap theorem allows. -/
theorem associated_superset {H : Type} [Field H] {m : ℕ}
    (C : RSCode H n (k+s)) (W : Fin m → Word H n) (mask : Word H n)
    (hk : 1 ≤ k) (D T S : Finset (Fin n))
    (hT : T ∈ associatedSets C W mask D) (hTS : T ⊆ S)
    (hlow : fixedConsistencyCodimension C W S s ≤ s)
    (hne : (ConsistencyClosure.solutions (jointMap C W) mask S).Nonempty) :
    S ∈ associatedSets C W mask D := by
  have hsizeT := (mem_filter.mp hT).2.1
  have hsizeS : k+s+s+1 ≤ S.card := hsizeT.trans (card_le_card hTS)
  let E := closure C W mask (canonicalCoreSet C W S)
  have hS : S ∈ associatedSets C W mask E :=
    mem_filter.mpr ⟨mem_univ _,hsizeS,hlow,hne,rfl⟩
  have he : D = E := by
    by_contra hdiff
    have hoverlap := ReducedSystems.associated_intersection C W mask hk D E T S hT hS hdiff
    rw [inter_eq_left.mpr hTS] at hoverlap
    omega
  rwa [he]

theorem overlap (hk : 1 ≤ k) (d e : Label C₁ W₁ mask₁ C₂ W₂ mask₂)
    (T T' : Finset (Fin n))
    (hT : T ∈ JointFamilies.associated (sets C₁ W₁ mask₁) (sets C₂ W₂ mask₂) d)
    (hT' : T' ∈ JointFamilies.associated (sets C₁ W₁ mask₁) (sets C₂ W₂ mask₂) e)
    (hne : d ≠ e) : (T ∩ T').card ≤ k+2*s-1 := by
  apply JointFamilies.associated_intersection _ _ ?_ ?_ d e T T' hT hT' hne
  · intro l l' U U' hU hU' hll
    exact ReducedSystems.associated_intersection C₁ W₁ mask₁ hk l.1 l'.1 U U' hU hU'
      (fun h => hll (Subtype.ext h))
  · intro r r' U U' hU hU' hrr
    exact ReducedSystems.associated_intersection C₂ W₂ mask₂ hk r.1 r'.1 U U' hU hU'
      (fun h => hrr (Subtype.ext h))

end RecursivePolygero.Local.ReducedSystems.Joint
