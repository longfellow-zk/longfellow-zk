import polygero.Algebra.PolynomialChallenges.Shift.Words

namespace RecursivePolygero.Local.Shift
open Polynomial Finset Submodule RecursivePolygero.Local Codes
variable {F : Type*} [Field F] {n R m s : ℕ}

noncomputable def aggregate (C : RSCode F n R) (W : Fin m → Word F n) :
    Challenge F m s →ₗ[F] Word F n where
  toFun := response C W
  map_add' := by intros; ext; simp [response,add_mul,Finset.sum_add_distrib]
  map_smul' := by intros; ext; simp [response,mul_assoc,← Finset.mul_sum]

noncomputable def aggregateSpace (C : RSCode F n R) (W : Fin m → Word F n) (s : ℕ) :
    Submodule F (Word F n) :=
  evalSpace C.node R ⊔ LinearMap.range (aggregate (s := s) C W)

/-- The allowed response subspace, viewed inside the received-word space. -/
noncomputable def responsePart (C : RSCode F n R) (W : Fin m → Word F n) (s : ℕ) :
    Submodule F (aggregateSpace C W s) :=
  (evalSpace C.node R).comap (aggregateSpace C W s).subtype

/-- The primary defect parameter is the dimension of the received-word quotient. -/
noncomputable def quotientDimension (C : RSCode F n R) (W : Fin m → Word F n) (s : ℕ) : ℕ :=
  Module.finrank F (aggregateSpace C W s ⧸ responsePart C W s)

/-- Aggregation with codomain restricted to the received-word space. -/
noncomputable def aggregateInto (C : RSCode F n R) (W : Fin m → Word F n) (s : ℕ) :
    Challenge F m s →ₗ[F] aggregateSpace C W s :=
  (aggregate C W).codRestrict _ (fun B => (show LinearMap.range (aggregate C W) ≤ aggregateSpace C W s
    from le_sup_right) (LinearMap.mem_range_self _ B))

/-- Aggregation modulo allowed responses. -/
noncomputable def quotientConsistencyMap (C : RSCode F n R) (W : Fin m → Word F n) (s : ℕ) :=
  (responsePart C W s).mkQ.comp (aggregateInto C W s)

/-- The zero aggregate class means exactly that an allowed response exists. -/
theorem quotient_map_eq_zero_iff_agrees (C : RSCode F n R) (W : Fin m → Word F n)
    (B : Challenge F m s) :
    quotientConsistencyMap C W s B = 0 ↔ AgreesOn C W univ B := by
  change (responsePart C W s).mkQ (aggregateInto C W s B) = 0 ↔ _
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  change response C W B ∈ evalSpace C.node R ↔ _
  constructor
  · rintro ⟨p,hp,he⟩
    exact ⟨⟨p,hp⟩, fun j _ => (congrFun he j).symm⟩
  · rintro ⟨p,hp⟩
    exact ⟨p.1,p.2,funext (fun j => (hp j (mem_univ j)).symm)⟩

theorem quotientConsistencyMap_surjective (C : RSCode F n R) (W : Fin m → Word F n) :
    Function.Surjective (quotientConsistencyMap C W s) := by
  intro y
  induction y using Submodule.Quotient.induction_on with
  | H u =>
    obtain ⟨e,he,z,⟨B,rfl⟩,hu⟩ := Submodule.mem_sup.mp u.2
    refine ⟨B, ?_⟩
    apply (Submodule.Quotient.eq _).mpr
    change aggregate C W B - u.1 ∈ evalSpace C.node R
    rw [← hu]
    simpa using (evalSpace C.node R).neg_mem he

/-- Add the response-space dimension to the quotient dimension. -/
theorem finrank_aggregateSpace (C : RSCode F n R) (W : Fin m → Word F n) :
    Module.finrank F (aggregateSpace C W s) = R + quotientDimension C W s := by
  have h := (responsePart C W s).finrank_quotient_add_finrank
  have hE : Module.finrank F (responsePart C W s) = R :=
    (Submodule.comapSubtypeEquivOfLe (show evalSpace C.node R ≤ aggregateSpace C W s
      from le_sup_left)).finrank_eq.trans
        (finrank_evalSpace C.node C.node_injective C.dimension_le_length)
  rw [hE] at h
  exact h.symm.trans (Nat.add_comm _ _)

/-- The entire challenged orbit of every received row lies in the aggregate space. -/
theorem row_shift_mem (C : RSCode F n R) (W : Fin m → Word F n)
    (i : Fin m) (j : ℕ) (hj : j ≤ s) :
    ((shift C.node)^j) (W i) ∈ aggregateSpace C W s := by
  classical
  apply (show LinearMap.range (aggregate (s := s) C W) ≤ aggregateSpace C W s from le_sup_right)
  let b : DegreeLT F (s+1) := ⟨X^j,mem_degreeLT.mpr (by rw [degree_X_pow]; exact_mod_cast (show j<s+1 by omega))⟩
  refine ⟨fun l => if l=i then b else 0, ?_⟩
  ext z
  simp [aggregate, response, b, shift_pow_apply, apply_ite]

/-- Bridge to the production kernel-based interface. -/
theorem ker_quotientConsistencyMap (C : RSCode F n R) (W : Fin m → Word F n) :
    LinearMap.ker (quotientConsistencyMap C W s) = consistentChallenges C W univ := by
  ext B
  exact quotient_map_eq_zero_iff_agrees C W B

/-- The first isomorphism theorem identifies the two consistency quotients. -/
noncomputable def aggregationEquiv (C : RSCode F n R) (W : Fin m → Word F n) :
    (Challenge F m s ⧸ LinearMap.ker (quotientConsistencyMap C W s)) ≃ₗ[F]
      (aggregateSpace C W s ⧸ responsePart C W s) :=
  (quotientConsistencyMap C W s).quotKerEquivOfSurjective
    (quotientConsistencyMap_surjective C W)

/-- The quotient dimension equals the production consistency codimension.
This equality is only needed when reusing the existing soundness consumers. -/
theorem quotientDimension_eq_codimension (C : RSCode F n R) (W : Fin m → Word F n) :
    quotientDimension C W s = fixedConsistencyCodimension C W univ s := by
  have he := (aggregationEquiv (s := s) C W).finrank_eq
  rw [ker_quotientConsistencyMap] at he
  change _ = quotientDimension C W s at he
  have hd := (consistentChallenges (s := s) C W univ).finrank_quotient_add_finrank
  rw [he, finrank_challenge] at hd
  have hc := fixedConsistencyDimension_add_codimension (s := s) C W univ
  dsimp only [fixedConsistencyDimension] at hc
  omega

end RecursivePolygero.Local.Shift
