import polygero.Algebra.Counting.BinomialExcess

/-! Joint reduced systems are indexed by a pair of labels. Their analysis
sets are the actual column sets associated with both labels. Maximizing over
this intersection, rather than combining the two separate capacities, retains
the one-field overlap bound without any independence assumption. -/
noncomputable section
namespace RecursivePolygero.JointFamilies
open Finset
open scoped Classical

variable {L R : Type} [Fintype L] [Fintype R] {n : ℕ}

def pairs (left : L → Finset (Finset (Fin n))) (right : R → Finset (Finset (Fin n))) :
    Finset (L × R) := univ.filter fun d => (left d.1 ∩ right d.2).Nonempty

abbrev Label (left : L → Finset (Finset (Fin n))) (right : R → Finset (Finset (Fin n))) :=
  ↥(pairs left right)

variable (left : L → Finset (Finset (Fin n))) (right : R → Finset (Finset (Fin n)))

def associated (d : Label left right) : Finset (Finset (Fin n)) :=
  left d.1.1 ∩ right d.1.2

def capacity (d : Label left right) : ℕ := (associated left right d).sup Finset.card

theorem capacity_witness (d : Label left right) :
    ∃ T ∈ associated left right d, T.card = capacity left right d := by
  have hne : (associated left right d).Nonempty := (mem_filter.mp d.2).2
  obtain ⟨T,hT,hmax⟩ := exists_max_image (associated left right d) Finset.card hne
  exact ⟨T,hT,le_antisymm (Finset.le_sup hT) (Finset.sup_le hmax)⟩

def capacitySet (d : Label left right) : Finset (Fin n) :=
  Classical.choose (capacity_witness left right d)

theorem capacitySet_spec (d : Label left right) :
    capacitySet left right d ∈ associated left right d ∧
      (capacitySet left right d).card = capacity left right d :=
  Classical.choose_spec (capacity_witness left right d)

/-- A set accepted by both participants has one joint label, and its size
is bounded by that label's capacity. The label family is fixed by the two
committed oracles, before either participant's challenges. -/
theorem common_set (l : L) (r : R) (T : Finset (Fin n))
    (hl : T ∈ left l) (hr : T ∈ right r) :
    ∃ d : Label left right, d.1 = (l,r) ∧ T ∈ associated left right d ∧
      T.card ≤ capacity left right d := by
  have hd : (l,r) ∈ pairs left right := mem_filter.mpr
    ⟨mem_univ _, ⟨T, mem_inter.mpr ⟨hl,hr⟩⟩⟩
  refine ⟨⟨(l,r),hd⟩, rfl, mem_inter.mpr ⟨hl,hr⟩, ?_⟩
  exact le_sup (mem_inter.mpr ⟨hl,hr⟩)

/-- Different pairs differ in at least one field. Apply that field's overlap
bound to the same two common column sets; no extra list factor appears. -/
theorem associated_intersection {overlap : ℕ}
    (hl : ∀ l l' T T', T ∈ left l → T' ∈ left l' → l ≠ l' →
      (T ∩ T').card ≤ overlap)
    (hr : ∀ r r' T T', T ∈ right r → T' ∈ right r' → r ≠ r' →
      (T ∩ T').card ≤ overlap)
    (d e : Label left right) (T T' : Finset (Fin n))
    (hT : T ∈ associated left right d) (hT' : T' ∈ associated left right e)
    (hne : d ≠ e) : (T ∩ T').card ≤ overlap := by
  obtain ⟨hTl,hTr⟩ := mem_inter.mp hT
  obtain ⟨hT'l,hT'r⟩ := mem_inter.mp hT'
  by_cases hleft : d.1.1 = e.1.1
  · apply hr _ _ _ _ hTr hT'r
    intro hright
    exact hne (Subtype.ext (Prod.ext hleft hright))
  · exact hl _ _ _ _ hTl hT'l hleft

/-- The same Hahn excess certificate applies to the joint family. Each
capacity witness is an existing common analysis set, not a padded set. -/
theorem capacity_excess {t overlap q cutoff bound : ℕ} {theta : ℚ}
    (hN : 0 < n.choose t) (htheta : theta ≤ 1) (hoverlap : overlap < cutoff)
    (hfloor : (((cutoff-1).choose t : ℚ) / n.choose t) ≤ theta)
    (hl : ∀ l l' T T', T ∈ left l → T' ∈ left l' → l ≠ l' →
      (T ∩ T').card ≤ overlap)
    (hr : ∀ r r' T T', T ∈ right r → T' ∈ right r' → r ≠ r' →
      (T ∩ T').card ≤ overlap)
    (hbound : DirectBinomial.ActiveFamilyBound n cutoff overlap q bound)
    (hcondition : DirectBinomial.HahnExcessCondition n t overlap q cutoff bound theta)
    (T : Finset (Label left right)) (hTq : T.card ≤ q) :
    ∑ d ∈ T, max 0 (((capacity left right d).choose t : ℚ) / n.choose t - theta) ≤
      1 - theta := by
  have h := DirectBinomial.normalized_excess_le_of_activeFamilyBound T
    (capacitySet left right) t overlap q cutoff bound theta hN htheta hoverlap hfloor
    (fun d _ e _ hne => associated_intersection left right hl hr d e _ _
      (capacitySet_spec left right d).1 (capacitySet_spec left right e).1 hne)
    hbound hcondition hTq
  simpa only [(capacitySet_spec left right _).2] using h

end RecursivePolygero.JointFamilies
