import polygero.Algebra.Explosion
import polygero.Algebra.PolynomialChallenges.Shift.Support

/-!
# Proximity gaps from polynomial challenges

The public interface uses only distinct field points, received words, bounded
polynomials and the dimension of their generated space. The proof specializes
the abstract explosion lemma of Section 3.1. The extraction and soundness
proofs use the direct MDS argument in `CanonicalCore.lean`, which shares the
slow-growth and coordinate-direction results developed here.
-/
namespace RecursivePolygero.ProximityGap
open Polynomial Finset Submodule
open RecursivePolygero.Local RecursivePolygero.Local.Shift
variable {F : Type*} [Field F] {n m s R k : ℕ}

open scoped Classical in
noncomputable def errorSet (u : Fin n → F) : Finset (Fin n) :=
  univ.filter fun j => u j ≠ 0

/-- Either all errors are exceptional, or adjoining the support space fills
all coordinates. This specializes the explosion lemma to coordinate support spaces. -/
theorem support_extension_alternative (x : Fin n → F) (hx : Function.Injective x)
    (U : Submodule F (Fin n → F)) (h1 : evaluate x 1 ∈ U)
    (hg : Module.finrank F (grow (shift x) U) ≤ Module.finrank F U + 1)
    (u : Fin n → F) (hu : u ∈ U) :
    errorSet u ⊆ coordinateDirections U ∨
      U ⊔ Pi.spanSubset F (errorSet u : Set (Fin n)) = ⊤ := by
  classical
  by_cases hsub : errorSet u ⊆ coordinateDirections U
  · exact Or.inl hsub
  apply Or.inr
  obtain ⟨j, hjS, hout⟩ := Finset.not_subset.mp hsub
  have hj : u j ≠ 0 := (mem_filter.mp hjS).2
  let P := Pi.spanSubset F (errorSet u : Set (Fin n))
  have huP : u ∈ P := by
    apply Pi.mem_spanSubset_iff.mpr
    intro i hi
    simpa [errorSet] using hi
  apply RecursivePolygero.explosion (shift x) U P (evaluate x 1) h1
    (span_shifts_one x hx) hg
  · rintro _ ⟨v, hv, rfl⟩
    apply Pi.mem_spanSubset_iff.mpr
    intro i hi
    change x i * v i = 0
    rw [Pi.mem_spanSubset_iff.mp hv i hi, mul_zero]
  · intro hstable
    have hshifts (a : ℕ) : ((shift x)^a) u ∈ U ⊓ P := by
      induction a with
      | zero => simpa using (show u ∈ U ⊓ P from ⟨hu, huP⟩)
      | succ a ih =>
        rw [pow_succ', Module.End.mul_apply]
        exact hstable ⟨_, ih, rfl⟩
    have hsingle := single_mem_of_shifts x hx (U ⊓ P) u hshifts j hj
    exact hout (mem_filter.mpr ⟨mem_univ j, hsingle.1⟩)

/-- An error outside the exceptional coordinates rules out the first branch
of the support-extension dichotomy. -/
theorem support_extension_eq_top (x : Fin n → F) (hx : Function.Injective x)
    (U : Submodule F (Fin n → F)) (h1 : evaluate x 1 ∈ U)
    (hg : Module.finrank F (grow (shift x) U) ≤ Module.finrank F U + 1)
    (u : Fin n → F) (hu : u ∈ U) (j : Fin n)
    (hj : u j ≠ 0) (hout : j ∉ coordinateDirections U) :
    U ⊔ Pi.spanSubset F (errorSet u : Set (Fin n)) = ⊤ := by
  classical
  exact (support_extension_alternative x hx U h1 hg u hu).resolve_left
    (fun hsub => hout (hsub (mem_filter.mpr ⟨mem_univ j, hj⟩)))

/-- The support supplies at most `|support|-1` dimensions beyond `U`, since
its nonzero residual already lies in `U`. This is the error threshold. -/
theorem error_lower_bound (x : Fin n → F) (hx : Function.Injective x)
    (U : Submodule F (Fin n → F)) (h1 : evaluate x 1 ∈ U)
    (hg : Module.finrank F (grow (shift x) U) ≤ Module.finrank F U + 1)
    (hD : Module.finrank F U < n)
    (u : Fin n → F) (hu : u ∈ U) (j : Fin n)
    (hj : u j ≠ 0) (hout : j ∉ coordinateDirections U) :
    n - Module.finrank F U + 1 ≤ (errorSet u).card := by
  classical
  let P := Pi.spanSubset F (errorSet u : Set (Fin n))
  have huP : u ∈ P := by
    apply Pi.mem_spanSubset_iff.mpr
    intro i hi
    simpa [errorSet] using hi
  have hi : 0 < Module.finrank F (U ⊓ P : Submodule F (Fin n → F)) :=
    Module.finrank_pos_iff_exists_ne_zero.mpr
      ⟨⟨u, hu, huP⟩, fun he => hj (congrFun (congrArg Subtype.val he) j)⟩
  have hd := U.finrank_sup_add_finrank_inf_eq P
  have ht := support_extension_eq_top x hx U h1 hg u hu j hj hout
  change U ⊔ P = ⊤ at ht
  rw [ht, finrank_top, Module.finrank_fin_fun] at hd
  have hp : Module.finrank F P = (errorSet u).card := by
    simp only [P, Pi.dim_spanSubset, Set.ncard_coe_finset]
  omega

/-- Polynomial batching, with no protocol structure in its inputs. -/
noncomputable def batch (x : Fin n → F) (W : Fin m → (Fin n → F)) :
    (Fin m → degreeLT F (s+1)) →ₗ[F] (Fin n → F) where
  toFun B j := ∑ i, (B i).1.eval (x j) * W i j
  map_add' := by intros; ext; simp [add_mul, sum_add_distrib]
  map_smul' := by intros; ext; simp [mul_assoc, ← mul_sum]

/-- Equivalently, span of degree-`<k+s` evaluations and all row shifts
with exponents from zero through `s`. -/
noncomputable def polynomialSpace (x : Fin n → F) (W : Fin m → (Fin n → F))
    (k s : ℕ) : Submodule F (Fin n → F) :=
  evalSpace x (k+s) ⊔ LinearMap.range (batch (s := s) x W)

/-- The batching image is exactly the span of all allowed row shifts. -/
theorem batch_range_eq_span_shifts (x : Fin n → F) (W : Fin m → (Fin n → F)) :
    LinearMap.range (batch (s := s) x W) =
      span F (Set.range (fun ia : Fin m × Fin (s+1) => ((shift x)^ia.2.val) (W ia.1))) := by
  classical
  let V := span F (Set.range (fun ia : Fin m × Fin (s+1) =>
    ((shift x)^ia.2.val) (W ia.1)))
  apply le_antisymm
  · rintro _ ⟨B, rfl⟩
    have he : batch x W B = ∑ i, multiplyWord x (B i).1 (W i) := by
      ext j
      simp [batch, multiplyWord]
    rw [he]
    apply V.sum_mem
    intro i _
    apply multiplyWord_mem x V (W i) (B i).1 (B i).2
    intro a ha
    exact subset_span ⟨(i, ⟨a, by omega⟩), rfl⟩
  · apply span_le.mpr
    rintro _ ⟨⟨i, a⟩, rfl⟩
    let b : degreeLT F (s+1) := ⟨X^a.val, mem_degreeLT.mpr (by
      rw [degree_X_pow]
      exact_mod_cast a.isLt)⟩
    refine ⟨fun l => if l=i then b else 0, ?_⟩
    ext j
    simp [batch, b, shift_pow_apply, apply_ite]

/-- Exact correspondence with the word space in the proximity gap theorem. -/
theorem polynomialSpace_eq_span_shifts (x : Fin n → F)
    (W : Fin m → (Fin n → F)) (k s : ℕ) :
    polynomialSpace x W k s = evalSpace x (k+s) ⊔
      span F (Set.range (fun ia : Fin m × Fin (s+1) => ((shift x)^ia.2.val) (W ia.1))) := by
  rw [polynomialSpace, batch_range_eq_span_shifts]

/-- The dimension budget forces the final shift increment to be at most one. -/
theorem polynomialSpace_slow_growth (x : Fin n → F) (hx : Function.Injective x)
    (W : Fin m → (Fin n → F)) (k s δ : ℕ) (hk : 1 ≤ k) (hδ : δ ≤ s)
    (hN : k+s+δ < n) (hd : Module.finrank F (polynomialSpace x W k s) = k+s+δ) :
    Module.finrank F (grow (shift x) (polynomialSpace x W k s)) ≤
      Module.finrank F (polynomialSpace x W k s) + 1 := by
  let C : Codes.RSCode F n (k+s) := ⟨x, hx, by omega⟩
  have he : polynomialSpace x W k s = receivedSpace x W k s :=
    aggregateSpace_eq_receivedSpace C W hk
  rw [he] at hd ⊢
  exact slow_growth x hx W k s hk (by omega) (by omega)

/-- Contrapositive theorem: any error outside one fixed exceptional set
requires at least `n-D+1` errors. No challenge or response has been chosen. -/
theorem polynomial_error_threshold (x : Fin n → F) (hx : Function.Injective x)
    (W : Fin m → (Fin n → F)) (k s δ : ℕ) (hk : 1 ≤ k) (hδ : δ ≤ s)
    (hN : k+s+δ < n) (hd : Module.finrank F (polynomialSpace x W k s) = k+s+δ) :
    ∃ E : Finset (Fin n), E.card ≤ δ ∧
      ∀ u ∈ polynomialSpace x W k s, ∀ j, j ∉ E → u j ≠ 0 →
        n-(k+s+δ)+1 ≤ (errorSet u).card := by
  classical
  let U := polynomialSpace x W k s
  have hcode : evalSpace x (k+s) ≤ U := le_sup_left
  have h1 : evaluate x 1 ∈ U := by
    have h := (evalSpace_le_iff x (k+s) U).mp hcode 0 (by omega)
    simpa using h
  have hg := polynomialSpace_slow_growth x hx W k s δ hk hδ hN hd
  refine ⟨coordinateDirections U, ?_, ?_⟩
  · have h := coordinate_directions_card_le x hx U (k+s) hcode (by dsimp [U]; omega)
    simpa only [U, hd, Nat.add_sub_cancel_left] using h
  intro u hu j hj hne
  have h := error_lower_bound x hx U h1 hg (by dsimp [U]; omega) u hu j hne hj
  simpa only [U, hd] using h

open scoped Classical in
/-- Fixed exceptional set, chosen before all challenges and responses.
The result gives both the error lower bound and fixed-core agreement. -/
theorem dimension_proximity_gap (x : Fin n → F) (hx : Function.Injective x)
    (W : Fin m → (Fin n → F)) (k s δ : ℕ) (hk : 1 ≤ k) (hδ : δ ≤ s)
    (hN : k+s+δ < n) (hd : Module.finrank F (polynomialSpace x W k s) = k+s+δ) :
    ∃ E : Finset (Fin n), E.card ≤ δ ∧
      ∀ w₀ ∈ polynomialSpace x W k s, ∀ B : Fin m → degreeLT F (s+1),
      ∀ p : degreeLT F (k+s),
        (∀ j, j ∉ E → (w₀ + batch x W B - evaluate x p) j ≠ 0 →
          n-(k+s+δ)+1 ≤ (errorSet (w₀ + batch x W B - evaluate x p)).card) ∧
        (k+s+δ ≤ (univ.filter fun j => (w₀ + batch x W B) j = p.1.eval (x j)).card →
          ∀ j, j ∉ E → (w₀ + batch x W B) j = p.1.eval (x j)) := by
  classical
  let U := polynomialSpace x W k s
  have hcode : evalSpace x (k+s) ≤ U := le_sup_left
  obtain ⟨E, hE, herr⟩ := polynomial_error_threshold x hx W k s δ hk hδ hN hd
  refine ⟨E, hE, ?_⟩
  intro w₀ hw₀ B p
  let u := w₀ + batch x W B - evaluate x p
  have hu : u ∈ U := U.sub_mem
    (U.add_mem hw₀ (mem_sup_right (LinearMap.mem_range_self _ B)))
    (hcode ⟨p, p.2, rfl⟩)
  have hbound (j : Fin n) (hj : j ∉ E) (hne : u j ≠ 0) :
      n-(k+s+δ)+1 ≤ (errorSet u).card := herr u hu j hj hne
  refine ⟨hbound, ?_⟩
  intro hag j hj
  have hcount : (errorSet u).card +
      (univ.filter fun j => (w₀ + batch x W B) j = p.1.eval (x j)).card = n := by
    have h := card_filter_add_card_filter_not (s := (univ : Finset (Fin n)))
      (p := fun j => u j ≠ 0)
    simpa [errorSet, u, evaluate, sub_eq_zero] using h
  by_cases he : (w₀ + batch x W B) j = p.1.eval (x j)
  · exact he
  · have hne : u j ≠ 0 := by simpa [u, evaluate, sub_eq_zero] using he
    have := hbound j hj hne
    omega

open scoped Classical in
/-- Agreement counts lie on one side of the threshold or in the fixed-core
range. A nonempty interval is excluded when `n > k+s+2*δ`. -/
theorem agreement_count_alternative (x : Fin n → F) (hx : Function.Injective x)
    (W : Fin m → (Fin n → F)) (k s δ : ℕ) (hk : 1 ≤ k) (hδ : δ ≤ s)
    (hN : k+s+δ < n) (hd : Module.finrank F (polynomialSpace x W k s) = k+s+δ)
    (w₀ : Fin n → F) (hw₀ : w₀ ∈ polynomialSpace x W k s)
    (B : Fin m → degreeLT F (s+1)) (p : degreeLT F (k+s)) :
    (univ.filter fun j => (w₀ + batch x W B) j = p.1.eval (x j)).card < k+s+δ ∨
      n-δ ≤ (univ.filter fun j => (w₀ + batch x W B) j = p.1.eval (x j)).card := by
  classical
  obtain ⟨E, hE, h⟩ := dimension_proximity_gap x hx W k s δ hk hδ hN hd
  by_cases hlow :
      (univ.filter fun j => (w₀ + batch x W B) j = p.1.eval (x j)).card < k+s+δ
  · exact Or.inl hlow
  · right
    have hag := (h w₀ hw₀ B p).2 (by omega)
    have hsub : univ \ E ⊆
        univ.filter fun j => (w₀ + batch x W B) j = p.1.eval (x j) := by
      intro j hj
      exact mem_filter.mpr ⟨mem_univ _, hag j (mem_sdiff.mp hj).2⟩
    have hc := card_le_card hsub
    have he := card_sdiff_add_card_eq_card (subset_univ E)
    simp only [card_univ, Fintype.card_fin] at he
    omega

end RecursivePolygero.ProximityGap
