import polygero.Algebra.PolynomialChallenges.ConsistencyClosure
import polygero.Algebra.PolynomialChallenges.SelectedColumns
import polygero.Algebra.PolynomialChallenges.AffineInstance

/-!
Joint consistency closures for the polynomial challenges used by the verifier.
The structural rank is connected to the existing consistency codimension.
Aggregate exceptional counting and concrete verifier soundness are proved in
the later closure-analysis modules.
-/
namespace RecursivePolygero.Local.PolynomialClosure
open Polynomial Finset Submodule Codes Shift
variable {F : Type*} [Field F] {n m k s : ℕ}

/-- The primary equations keep the challenge and response as joint unknowns. -/
noncomputable def jointMap (C : RSCode F n (k+s)) (W : Fin m → Word F n) :
    (Challenge F m s × DegreeLT F (k+s)) →ₗ[F] Word F n where
  toFun v := evaluate C.node v.2 - aggregate C W v.1
  map_add' := by intros; simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, map_add]; abel
  map_smul' := by intros; simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul,
    map_smul, smul_sub]; rfl

theorem jointMap_range (C : RSCode F n (k+s)) (W : Fin m → Word F n) :
    LinearMap.range (jointMap C W) = ProximityGap.polynomialSpace C.node W k s := by
  change LinearMap.range (jointMap C W) = aggregateSpace C W s
  classical
  apply le_antisymm
  · rintro _ ⟨⟨B,p⟩, rfl⟩
    exact (aggregateSpace C W s).sub_mem (mem_sup_left ⟨p,p.2,rfl⟩)
      (mem_sup_right (LinearMap.mem_range_self _ B))
  · apply sup_le
    · rintro _ ⟨p,hp,rfl⟩
      refine ⟨(0,⟨p,hp⟩), ?_⟩
      simp [jointMap]
    · rintro _ ⟨B,rfl⟩
      refine ⟨(-B,0), ?_⟩
      simp [jointMap]

/-- Rank of the joint equations equals response dimension plus the production
consistency codimension, provided there are enough columns for evaluation. -/
theorem joint_rank (C : RSCode F n (k+s)) (W : Fin m → Word F n)
    (S : Finset (Fin n)) (hS : k+s ≤ S.card) :
    ConsistencyClosure.rank (jointMap C W) S = k+s+fixedConsistencyCodimension C W S s := by
  rw [ConsistencyClosure.rank_eq_restriction, jointMap_range,
    ProximityGap.polynomialSpace_restrict]
  let CP := C.puncture S hS
  let WP := fun i => C.restrictWord S (W i)
  change Module.finrank F (aggregateSpace CP WP s) = _
  rw [finrank_aggregateSpace, quotientDimension_eq_codimension]
  unfold fixedConsistencyCodimension
  rw [fixedConsistencyDimension_puncture C W S hS]

/-- The new joint system projects to the existing affine-consistency predicate. -/
theorem exists_joint_iff (C : RSCode F n (k+s)) (W : Fin m → Word F n)
    (mask : Word F n) (S : Finset (Fin n)) (B : Challenge F m s) :
    (∃ p, (B,p) ∈ ConsistencyClosure.solutions (jointMap C W) mask S) ↔
      ∃ p : DegreeLT F (k+s), ∀ j ∈ S,
        (p : F[X]).eval (C.node j) = response C W B j + mask j := by
  constructor <;> rintro ⟨p,hp⟩ <;> refine ⟨p, ?_⟩ <;> intro j hj
  · have h := hp j hj
    change (p : F[X]).eval (C.node j) - response C W B j = mask j at h
    exact sub_eq_iff_eq_add.mp h |>.trans (add_comm _ _)
  · change (p : F[X]).eval (C.node j) - response C W B j = mask j
    rw [hp j hj]
    abel

noncomputable abbrev closure (C : RSCode F n (k+s)) (W : Fin m → Word F n)
    (mask : Word F n) (S : Finset (Fin n)) :=
  ConsistencyClosure.closure (jointMap C W) mask S

/-- Structural hypotheses of a canonical core, without assuming any result
about the number of closures or exceptional challenges. -/
structure IsCore (C : RSCode F n (k+s)) (W : Fin m → Word F n) (S : Finset (Fin n)) : Prop where
  large : k+s+fixedConsistencyCodimension C W S s < S.card
  low : fixedConsistencyCodimension C W S s ≤ s
  unitfree : coordinateDirections ((LinearMap.range (jointMap C W)).map (Shift.restrict S)) = ∅

theorem restricted_one (C : RSCode F n (k+s)) (W : Fin m → Word F n)
    (hk : 1 ≤ k) (T : Finset (Fin n)) :
    evaluate (C.node ∘ column T) 1 ∈ LinearMap.range ((Shift.restrict T).comp (jointMap C W)) := by
  rw [LinearMap.range_comp, jointMap_range]
  refine ⟨evaluate C.node 1, mem_sup_left ⟨1, ?_, rfl⟩, rfl⟩
  apply mem_degreeLT.mpr
  rw [degree_one]
  exact_mod_cast (show 0 < k+s by omega)

theorem restricted_slow_growth (C : RSCode F n (k+s)) (W : Fin m → Word F n)
    (hk : 1 ≤ k) (T : Finset (Fin n)) (hT : k+s ≤ T.card)
    (hlow : fixedConsistencyCodimension C W T s ≤ s)
    (hlarge : ConsistencyClosure.rank (jointMap C W) T < T.card) :
    Module.finrank F (grow (shift (C.node ∘ column T))
      (LinearMap.range ((Shift.restrict T).comp (jointMap C W)))) ≤
      ConsistencyClosure.rank (jointMap C W) T + 1 := by
  have he : LinearMap.range ((Shift.restrict T).comp (jointMap C W)) =
      ProximityGap.polynomialSpace (C.node ∘ column T) (fun i => Shift.restrict T (W i)) k s := by
    rw [LinearMap.range_comp, jointMap_range, ProximityGap.polynomialSpace_restrict]
  have hd : Module.finrank F (ProximityGap.polynomialSpace (C.node ∘ column T)
      (fun i => Shift.restrict T (W i)) k s) = k+s+fixedConsistencyCodimension C W T s := by
    rw [← he]
    exact joint_rank C W T hT
  have hn : k+s+fixedConsistencyCodimension C W T s < T.card := by
    rwa [joint_rank C W T hT] at hlarge
  have h := ProximityGap.polynomialSpace_slow_growth _ (C.node_injective.comp (column_injective T))
    _ k s _ hk hlow hn hd
  rw [← he] at h
  exact h

noncomputable abbrev canonicalCoreSet (C : RSCode F n (k+s)) (W : Fin m → Word F n)
    (T : Finset (Fin n)) := canonicalSubset (LinearMap.range (jointMap C W)) T

/-- Every dense analysis set has a fixed canonical core. The defect drops
exactly by the number of deleted coordinates. -/
theorem canonical_core (C : RSCode F n (k+s)) (W : Fin m → Word F n)
    (T : Finset (Fin n))
    (hlow : fixedConsistencyCodimension C W T s ≤ s)
    (hlarge : k+s+fixedConsistencyCodimension C W T s < T.card) :
    let S := canonicalCoreSet C W T
    IsCore C W S ∧ S ⊆ T ∧
      fixedConsistencyCodimension C W S s + (T \ S).card = fixedConsistencyCodimension C W T s := by
  classical
  let U := LinearMap.range (jointMap C W)
  let S := canonicalCoreSet C W T
  change IsCore C W S ∧ S ⊆ T ∧
    fixedConsistencyCodimension C W S s + (T \ S).card = fixedConsistencyCodimension C W T s
  have hST : S ⊆ T := canonicalSubset_subset U T
  have hT : k+s ≤ T.card := by omega
  have hrT : Module.finrank F (U.map (Shift.restrict T)) = k+s+fixedConsistencyCodimension C W T s :=
    (ConsistencyClosure.rank_eq_restriction _ _).symm.trans (joint_rank C W T hT)
  have hE : (coordinateDirections (U.map (Shift.restrict T))).card ≤ fixedConsistencyCodimension C W T s := by
    have heval : evalSpace (C.node ∘ column T) (k+s) ≤ U.map (Shift.restrict T) := by
      dsimp only [U]
      rw [jointMap_range, ProximityGap.polynomialSpace_restrict]
      exact le_sup_left
    have h := coordinate_directions_card_le (C.node ∘ column T)
      (C.node_injective.comp (column_injective T)) _ (k+s) heval (by omega)
    omega
  have hc : S.card + (coordinateDirections (U.map (Shift.restrict T))).card = T.card :=
    canonicalSubset_card U T
  have hr : Module.finrank F (U.map (Shift.restrict S)) +
      (coordinateDirections (U.map (Shift.restrict T))).card = Module.finrank F (U.map (Shift.restrict T)) := by
    rw [canonicalSubset_rank U T]
    exact core_rank_add_directions _
  have hS : k+s ≤ S.card := by omega
  have hrS : Module.finrank F (U.map (Shift.restrict S)) = k+s+fixedConsistencyCodimension C W S s :=
    (ConsistencyClosure.rank_eq_restriction _ _).symm.trans (joint_rank C W S hS)
  have hdifference := card_sdiff_add_card_eq_card hST
  refine ⟨⟨by omega, by omega, canonicalSubset_unitfree U T⟩, hST, ?_⟩
  omega

/-- Closing a consistent core preserves rank, properness and unit-freeness.
No slow-growth or MDS result is needed here. -/
theorem closure_geometry (C : RSCode F n (k+s)) (W : Fin m → Word F n)
    (mask : Word F n) (S : Finset (Fin n)) (hcore : IsCore C W S)
    (hne : (ConsistencyClosure.solutions (jointMap C W) mask S).Nonempty) :
    let D := closure C W mask S
    IsCore C W D ∧ fixedConsistencyCodimension C W D s = fixedConsistencyCodimension C W S s := by
  classical
  let A := jointMap C W
  let D := closure C W mask S
  have hSD : S ⊆ D := ConsistencyClosure.subset_closure A mask S
  have hS : k+s ≤ S.card := by have := hcore.large; omega
  have hD : k+s ≤ D.card := hS.trans (card_le_card hSD)
  have hr : ConsistencyClosure.rank A D = ConsistencyClosure.rank A S :=
    ConsistencyClosure.closure_rank A mask S hne
  have hdefect : fixedConsistencyCodimension C W D s = fixedConsistencyCodimension C W S s := by
    rw [joint_rank C W D hD, joint_rank C W S hS] at hr
    omega
  have hfreeLocal : coordinateDirections (((LinearMap.range A).map (Shift.restrict D)).map
      (Shift.restrict (localColumns D S))) = ∅ :=
    restriction_unitfree_through _ hSD hcore.unitfree
  have hfree := unitfree_of_restriction_rank_eq ((LinearMap.range A).map (Shift.restrict D))
    (localColumns D S) hfreeLocal (by
      rw [restriction_rank_through _ hSD]
      simpa only [ConsistencyClosure.rank_eq_restriction] using hr.symm)
  refine ⟨⟨?_, hdefect ▸ hcore.low, hfree⟩, hdefect⟩
  rw [← joint_rank C W D hD, hr, joint_rank C W S hS]
  exact hcore.large.trans_le (card_le_card hSD)

end RecursivePolygero.Local.PolynomialClosure
