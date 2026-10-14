import polygero.Algebra.PolynomialChallenges.SelectedColumns

/-!
# Low-degree consistency fibers for an additive mask

A fixed additive word translates each nonempty consistency fiber without
changing its size. These counts are used in small-core incidence counting.
-/
namespace RecursivePolygero.Local.Affine
open Polynomial Finset Function Codes
variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {n m k s : ℕ} (C : RSCode F n (k+s))
variable (W : Fin m → Word F n) (g : Word F n)

noncomputable def consistent (S : Finset (Fin n)) : Finset (Challenge F m s) := by
  classical
  exact univ.filter fun B => ∃ p : DegreeLT F (k+s),
    ∀ j ∈ S, (p : F[X]).eval (C.node j) = response C W B j + g j

/-- An agreeing anchor translates affine consistency exactly into linear consistency. -/
theorem mem_consistent_iff_sub_mem (S : Finset (Fin n))
    (B₀ : Challenge F m s) (hB₀ : B₀ ∈ consistent C W g S) (B : Challenge F m s) :
    B ∈ consistent C W g S ↔ B-B₀ ∈ consistentChallenges C W S := by
  classical
  obtain ⟨p₀,hp₀⟩ := (mem_filter.mp hB₀).2
  constructor
  · intro hB
    obtain ⟨p,hp⟩ := (mem_filter.mp hB).2
    refine ⟨p-p₀, ?_⟩
    intro j hj
    have hd : response C W (B-B₀) j = response C W B j - response C W B₀ j := by
      simp [response, sub_mul, sum_sub_distrib]
    change response C W (B-B₀) j = (p-p₀ : F[X]).eval (C.node j)
    rw [hd, eval_sub, hp j hj, hp₀ j hj]
    ring
  · rintro ⟨p,hp⟩
    refine mem_filter.mpr ⟨mem_univ _,p+p₀,?_⟩
    intro j hj
    have he := hp j hj
    change response C W (B-B₀) j = (p : F[X]).eval (C.node j) at he
    change (p+p₀ : F[X]).eval (C.node j) = _
    rw [eval_add,← he,hp₀ j hj]
    simp only [response,Pi.sub_apply,Submodule.coe_sub,eval_sub,sub_mul,sum_sub_distrib]
    ring

/-- A nonempty affine consistency fiber has exactly the cardinality of its
linear direction space. -/
theorem consistent_card_eq_of_nonempty (S : Finset (Fin n))
    (hne : (consistent C W g S).Nonempty) :
    (consistent C W g S).card = Nat.card F ^ fixedConsistencyDimension C W S s := by
  classical
  obtain ⟨B₀,hB₀⟩ := hne
  let e : ↥(consistent C W g S) ≃ consistentChallenges (s := s) C W S :=
    { toFun := fun B => ⟨B.1-B₀,(mem_consistent_iff_sub_mem C W g S B₀ hB₀ B.1).mp B.2⟩
      invFun := fun B => ⟨B.1+B₀,(mem_consistent_iff_sub_mem C W g S B₀ hB₀ _).mpr
        (by simpa only [add_sub_cancel_right] using B.2)⟩
      left_inv := fun B => Subtype.ext (sub_add_cancel B.1 B₀)
      right_inv := fun B => Subtype.ext (add_sub_cancel_right B.1 B₀) }
  have hc : (consistent C W g S).card = Nat.card (consistentChallenges (s := s) C W S) := by
    simpa only [Nat.card_eq_fintype_card,Fintype.card_coe] using Nat.card_congr e
  exact hc.trans (Module.natCard_eq_pow_finrank (K := F)
    (V := consistentChallenges (s := s) C W S))

/-- Empty and nonempty affine consistency fibers obey the same cardinality bound. -/
theorem consistent_card_le (S : Finset (Fin n)) :
    (consistent C W g S).card ≤ Nat.card (consistentChallenges (s := s) C W S) := by
  classical
  by_cases hne : (consistent C W g S).Nonempty
  · rw [consistent_card_eq_of_nonempty C W g S hne,
      Module.natCard_eq_pow_finrank (K := F) (V := consistentChallenges (s := s) C W S)]
    rfl
  · rw [not_nonempty_iff_eq_empty.mp hne]
    simp

/-- On any fixed set of columns, proper affine consistency admits at most
one field fraction of polynomial challenges. No size or density premise is needed. -/
theorem consistent_card_mul_field_le_of_proper (S : Finset (Fin n))
    (hproper : consistent C W g S ≠ univ) :
    (consistent C W g S).card * Nat.card F ≤ Nat.card (Challenge F m s) := by
  classical
  by_cases hne : (consistent C W g S).Nonempty
  · obtain ⟨B₀,hB₀⟩ := hne
    have hlinear : consistentChallenges (s := s) C W S ≠ ⊤ := by
      intro htop
      apply hproper
      apply eq_univ_of_forall
      intro B
      apply (mem_consistent_iff_sub_mem C W g S B₀ hB₀ B).mpr
      rw [htop]
      trivial
    exact (Nat.mul_le_mul_right _ (consistent_card_le C W g S)).trans
      (card_submodule_mul_field_le (consistentChallenges (s := s) C W S) hlinear)
  · rw [not_nonempty_iff_eq_empty.mp hne]
    simp

/-- The affine fiber obeys the same exact codimension penalty as its
homogeneous direction space, including every cutoff `T`. -/
theorem consistent_card_mul_field_pow_le (S : Finset (Fin n)) (T : ℕ)
    (hsmall : fixedConsistencyDimension C W S s + T + 1 ≤ m * (s + 1)) :
    (consistent C W g S).card * Nat.card F ^ (T + 1) ≤
      Nat.card (Challenge F m s) := by
  exact (Nat.mul_le_mul_right _ (consistent_card_le C W g S)).trans
    (fixedConsistent_card_mul_field_pow_le C W S T hsmall)

end RecursivePolygero.Local.Affine
