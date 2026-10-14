import polygero.Algebra.PolynomialChallenges.RankSelection
import polygero.Algebra.PolynomialChallenges.ReducedSystems

/-! The response-independent event excluding large rank. Its exponent is
one more than the polynomial-challenge degree. -/
namespace RecursivePolygero.Local.ReducedSystems
open Finset Codes PolynomialClosure
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] {n m k s : ℕ}

open scoped Classical in
noncomputable def badChallenges (C : RSCode F n (k+s)) (W : Fin m → Word F n)
    (mask : Word F n) : Finset (Challenge F m s) :=
  ((univ.powersetCard (k+s+s+1)).filter fun T =>
    s < fixedConsistencyCodimension C W T s).biUnion (Affine.consistent C W mask)

theorem badChallenges_card (C : RSCode F n (k+s)) (W : Fin m → Word F n)
    (mask : Word F n) :
    (badChallenges C W mask).card * Nat.card F^(s+1) ≤
      n.choose (k+s+s+1)*Nat.card (Challenge F m s) := by
  classical
  let sets := (univ.powersetCard (k+s+s+1)).filter fun T =>
    s < fixedConsistencyCodimension C W T s
  have hc (T : Finset (Fin n)) (hT : T ∈ sets) :
      (Affine.consistent C W mask T).card*Nat.card F^(s+1) ≤ Nat.card (Challenge F m s) := by
    have hδ := (mem_filter.mp hT).2
    have hd := fixedConsistencyDimension_add_codimension C W T (s := s)
    exact Affine.consistent_card_mul_field_pow_le C W mask T s (by omega)
  calc
    _ ≤ (∑ T ∈ sets, (Affine.consistent C W mask T).card)*Nat.card F^(s+1) :=
      Nat.mul_le_mul_right _ (card_biUnion_le)
    _ = ∑ T ∈ sets, (Affine.consistent C W mask T).card*Nat.card F^(s+1) := sum_mul _ _ _
    _ ≤ ∑ _T ∈ sets, Nat.card (Challenge F m s) := sum_le_sum hc
    _ = sets.card*Nat.card (Challenge F m s) := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ (by
      have h := card_le_card (filter_subset (s := univ.powersetCard (k+s+s+1))
        (p := fun T => s < fixedConsistencyCodimension C W T s))
      simpa only [card_powersetCard,card_univ,Fintype.card_fin] using h)

/-- Outside the fixed event, every sufficiently large consistent response set
has defect at most `s`, regardless of how the response was selected. -/
theorem low_defect_of_not_bad (C : RSCode F n (k+s)) (W : Fin m → Word F n)
    (mask : Word F n) (B : Challenge F m s)
    (hout : B ∉ badChallenges C W mask) (G : Finset (Fin n))
    (hsize : k+s+s+1 ≤ G.card) (p : DegreeLT F (k+s))
    (hp : (B,p) ∈ ConsistencyClosure.solutions (jointMap C W) mask G) :
    fixedConsistencyCodimension C W G s ≤ s := by
  classical
  apply le_of_not_gt
  intro hδ
  have hr := joint_rank C W G (by omega)
  obtain ⟨T,hTG,hcard,hrank⟩ := ConsistencyClosure.exists_subset_rank_eq_card
    (jointMap C W) mask G ⟨(B,p),hp⟩ (k+s+s+1) (by omega)
  have hrT := joint_rank C W T (by omega)
  apply hout
  apply mem_biUnion.mpr
  refine ⟨T,mem_filter.mpr ⟨mem_powersetCard.mpr ⟨subset_univ _,hcard⟩,by omega⟩,?_⟩
  apply mem_filter.mpr
  exact ⟨mem_univ _,(exists_joint_iff C W mask T B).mp
    ⟨p,ConsistencyClosure.solutions_antitone _ _ hTG hp⟩⟩

end RecursivePolygero.Local.ReducedSystems
