import polygero.Algebra.PolynomialChallenges.ReducedSystems

/-! Large overlap identifies affine systems. The maximal intermediate space is
 the sole consumer of the slow-growth MDS theorem in this analysis. -/
namespace RecursivePolygero.Local.ConsistencyClosure
open Finset Submodule Shift
variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable [FiniteDimensional F V] {n : ℕ}

/-- One MDS intermediate space suffices to identify the ranks of both cores
and their union. The intermediate set is selected before invoking MDS;
its maximality then identifies it with the union. -/
theorem unitfree_overlap_ranks (A : V →ₗ[F] (Fin n → F))
    (S S' : Finset (Fin n)) (K : ℕ)
    (hsmall : rank A S < S.card) (hsmall' : rank A S' < S'.card)
    (hbound : rank A S ≤ K) (hbound' : rank A S' ≤ K)
    (hfree : coordinateDirections ((LinearMap.range A).map (Shift.restrict S)) = ∅)
    (hfree' : coordinateDirections ((LinearMap.range A).map (Shift.restrict S')) = ∅)
    (hoverlap : rank A S + rank A S' ≤ (S ∩ S').card + K)
    (hmds : ∀ M, S ⊆ M → M ⊆ S ∪ S' → rank A M ≤ K →
      coordinateDirections ((LinearMap.range A).map (Shift.restrict M)) = ∅ →
      rank A M < M.card → ∀ H ⊆ M, rank A H = min H.card (rank A M)) :
    rank A S = rank A (S ∪ S') ∧ rank A S' = rank A (S ∪ S') ∧
      ∀ H ⊆ S ∪ S', rank A H = min H.card (rank A (S ∪ S')) := by
  classical
  let candidates := univ.filter fun M : Finset (Fin n) => S ⊆ M ∧ M ⊆ S ∪ S' ∧
    rank A M ≤ K ∧ coordinateDirections ((LinearMap.range A).map (Shift.restrict M)) = ∅
  have hS : S ∈ candidates := mem_filter.mpr ⟨mem_univ _,Subset.rfl,subset_union_left,hbound,hfree⟩
  obtain ⟨M,hM,hmax⟩ := exists_max_image candidates Finset.card ⟨S,hS⟩
  obtain ⟨_,hSM,hMU,hK,hF⟩ := mem_filter.mp hM
  have hproper : rank A M < M.card := by
    rw [rank_eq_restriction]
    apply rank_lt_of_restriction_rank_lt _ (localColumns M S)
    rw [restriction_rank_through _ hSM,localColumns_card hSM,← rank_eq_restriction]
    exact hsmall
  -- This is the only invocation; all later ranks reuse this one conclusion.
  have hm := hmds M hSM hMU hK hF hproper
  have hrankM : rank A M = rank A S := by
    have h := hm S hSM
    omega
  have hrI : rank A (S ∩ S') = min (S ∩ S').card (rank A S) := by
    simpa only [hrankM] using hm (S ∩ S') (inter_subset_left.trans hSM)
  have hsub := rank_submodular A S S'
  have hU : rank A (S ∪ S') ≤ K := by
    rw [hrI] at hsub
    omega
  have hmem : S ∪ S' ∈ candidates := mem_filter.mpr
    ⟨mem_univ _,subset_union_left,Subset.rfl,hU,unitfree_union _ S S' hfree hfree'⟩
  have he : M = S ∪ S' := eq_of_subset_of_card_le hMU (hmax _ hmem)
  subst M
  refine ⟨hrankM.symm,?_,hm⟩
  have h := hm S' subset_union_right
  omega

end RecursivePolygero.Local.ConsistencyClosure

namespace RecursivePolygero.Local.PolynomialClosure
open Finset Submodule Codes Shift ConsistencyClosure
variable {F : Type*} [Field F] {n m k s : ℕ}

/-- Auxiliary rank lemma: two unit-free low-defect cores with sufficient
intersection have an MDS union of the same rank. This is the sole polynomial
MDS application; affine closure identification below reuses its conclusion. -/
theorem core_union_mds (C : RSCode F n (k+s)) (W : Fin m → Word F n)
    (hk : 1 ≤ k) (S S' : Finset (Fin n))
    (hc : IsCore C W S) (hc' : IsCore C W S')
    (hoverlap : rank (jointMap C W) S + rank (jointMap C W) S' ≤
      (S ∩ S').card + (k+2*s)) :
    rank (jointMap C W) S = rank (jointMap C W) (S ∪ S') ∧
      rank (jointMap C W) S' = rank (jointMap C W) (S ∪ S') ∧
      ∀ H ⊆ S ∪ S', rank (jointMap C W) H =
        min H.card (rank (jointMap C W) (S ∪ S')) := by
  have hSsize : k+s ≤ S.card := by have := hc.large; omega
  have hrS := joint_rank C W S hSsize
  have hrS' := joint_rank C W S' (by have := hc'.large; omega)
  refine unitfree_overlap_ranks (jointMap C W) S S' (k+2*s)
    (by rw [hrS]; exact hc.large) (by rw [hrS']; exact hc'.large)
    (by rw [hrS]; have := hc.low; omega)
    (by rw [hrS']; have := hc'.low; omega)
    hc.unitfree hc'.unitfree hoverlap ?_
  intro M hSM _ hK hfree hproper
  have hMsize := hSsize.trans (card_le_card hSM)
  have hrM := joint_rank C W M hMsize
  have hg := restricted_slow_growth C W hk M hMsize (by rw [hrM] at hK; omega) hproper
  have hm := restriction_rank_eq_min (C.node ∘ column M)
    (C.node_injective.comp (column_injective M))
    (LinearMap.range ((Shift.restrict M).comp (jointMap C W)))
    (restricted_one C W hk M) hg hproper
    (by rwa [LinearMap.range_comp])
  intro H hHM
  have hmH := hm (localColumns M H)
  rw [LinearMap.range_comp,restriction_rank_through _ hHM,localColumns_card hHM,
    ← rank_eq_restriction] at hmH
  rw [← rank_eq_restriction] at hmH
  exact hmH

/-- Large overlap of consistent low-defect systems identifies their canonical
affine closures, without constructing any homogeneous closure. -/
theorem canonical_closures_eq (C : RSCode F n (k+s)) (W : Fin m → Word F n)
    (mask : Word F n) (hk : 1 ≤ k) (T T' : Finset (Fin n))
    (hlow : fixedConsistencyCodimension C W T s ≤ s)
    (hlow' : fixedConsistencyCodimension C W T' s ≤ s)
    (hlarge : k+s+fixedConsistencyCodimension C W T s < T.card)
    (hlarge' : k+s+fixedConsistencyCodimension C W T' s < T'.card)
    (hne : (solutions (jointMap C W) mask T).Nonempty)
    (hne' : (solutions (jointMap C W) mask T').Nonempty)
    (hoverlap : k+2*s ≤ (T ∩ T').card) :
    closure C W mask (canonicalCoreSet C W T) =
      closure C W mask (canonicalCoreSet C W T') := by
  classical
  let A := jointMap C W
  let S := canonicalCoreSet C W T
  let S' := canonicalCoreSet C W T'
  let E := T \ S
  let E' := T' \ S'
  obtain ⟨hc,hST,hdrop⟩ := canonical_core C W T hlow hlarge
  obtain ⟨hc',hST',hdrop'⟩ := canonical_core C W T' hlow' hlarge'
  change IsCore C W S at hc
  change IsCore C W S' at hc'
  change S ⊆ T at hST
  change S' ⊆ T' at hST'
  change fixedConsistencyCodimension C W S s + E.card = fixedConsistencyCodimension C W T s at hdrop
  change fixedConsistencyCodimension C W S' s + E'.card = fixedConsistencyCodimension C W T' s at hdrop'
  have hSsize : k+s ≤ S.card := by have := hc.large; omega
  have hSsize' : k+s ≤ S'.card := by have := hc'.large; omega
  have hrS := joint_rank C W S hSsize
  have hrS' := joint_rank C W S' hSsize'
  change rank A S = _ at hrS
  change rank A S' = _ at hrS'
  have hbudget : rank A S + E.card ≤ k+2*s := by rw [hrS]; omega
  have hbudget' : rank A S' + E'.card ≤ k+2*s := by rw [hrS']; omega
  have hcover : T ∩ T' ⊆ (S ∩ S') ∪ (E ∪ E') := by
    intro j hj
    simp only [mem_inter,mem_union,mem_sdiff,E,E'] at hj ⊢
    tauto
  have hcount := (card_le_card hcover).trans (card_union_le _ _)
  have herrors := card_union_le E E'
  have hranks := core_union_mds C W hk S S' hc hc' (by
    change rank A S + rank A S' ≤ (S ∩ S').card + (k+2*s)
    omega)
  obtain ⟨hrU,hrU',hmds⟩ := hranks
  -- Compare ranks after adjoining the entire deleted set; no coordinate
  -- witness is needed to rule out the two mixed intersections.
  have hd := disjoint_of_rank_add_card A S S' E hrU hrU' (by
    dsimp only [E]
    rw [union_sdiff_of_subset hST]
    have hrT := joint_rank C W T (hSsize.trans (card_le_card hST))
    change rank A T = _ at hrT
    change rank A T = rank A S + E.card
    rw [hrT, hrS]
    omega)
  have hd' := disjoint_of_rank_add_card A S' S E'
    (by rw [union_comm]; exact hrU') (by rw [union_comm]; exact hrU) (by
      dsimp only [E']
      rw [union_sdiff_of_subset hST']
      have hrT' := joint_rank C W T' (hSsize'.trans (card_le_card hST'))
      change rank A T' = _ at hrT'
      change rank A T' = rank A S' + E'.card
      rw [hrT', hrS']
      omega)
  have hcover' : T ∩ T' ⊆ (S ∩ S') ∪ (E ∩ E') := by
    intro j hj
    have hmix : ¬(j ∈ E ∧ j ∈ S') := fun h => disjoint_left.mp hd h.1 h.2
    have hmix' : ¬(j ∈ E' ∧ j ∈ S) := fun h => disjoint_left.mp hd' h.1 h.2
    simp only [mem_inter,mem_union,mem_sdiff,E,E'] at hmix hmix' hj ⊢
    tauto
  have hcount' := (card_le_card hcover').trans (card_union_le _ _)
  have herrors' := card_le_card (inter_subset_left : E ∩ E' ⊆ E)
  have hI : rank A S ≤ (S ∩ S').card := by omega
  have hIr : rank A (S ∩ S') = rank A S := by
    rw [hmds _ (inter_subset_left.trans subset_union_left),← hrU,min_eq_right hI]
  apply (closure_eq_iff_solutions_eq A mask S S').mpr
  exact (solutions_eq_of_rank_eq A mask inter_subset_left
    (hne.mono (solutions_antitone A mask hST)) hIr).symm.trans
    (solutions_eq_of_rank_eq A mask inter_subset_right
      (hne'.mono (solutions_antitone A mask hST')) (hIr.trans (hrU.trans hrU'.symm)))

end RecursivePolygero.Local.PolynomialClosure
