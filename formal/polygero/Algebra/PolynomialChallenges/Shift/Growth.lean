import polygero.Algebra.PolynomialChallenges.Shift.Words

namespace RecursivePolygero.Local.Shift
open Polynomial Submodule
variable {F M : Type*} [Field F] [AddCommGroup M] [Module F M]
  [FiniteDimensional F M]

/-- Shift one subspace forward. -/
noncomputable def grow (T : M →ₗ[F] M) (U : Submodule F M) := U ⊔ U.map T

/-- Successive quotient dimensions decrease. The map sends `[w]` to `[Tw]`
from `B/A` onto `(B+TB)/B`; it is not an endomorphism of either quotient. -/
theorem quotient_growth_bound (T : M →ₗ[F] M) (A B : Submodule F M)
    (hAB : A ≤ B) (hTA : A.map T ≤ B) :
    Module.finrank F (grow T B) + Module.finrank F A ≤ 2 * Module.finrank F B := by
  let G := grow T B
  let A' := A.comap B.subtype
  let B' := B.comap G.subtype
  let t : B →ₗ[F] G := (T.comp B.subtype).codRestrict G (fun w =>
    (show B.map T ≤ G from le_sup_right) ⟨w.1,w.2,rfl⟩)
  let f : (B ⧸ A') →ₗ[F] (G ⧸ B') := A'.mapQ B' t (by
    intro w hw
    exact hTA ⟨w.1,hw,rfl⟩)
  have hf : Function.Surjective f := by
    intro z
    induction z using Submodule.Quotient.induction_on with
    | H w =>
      obtain ⟨b,hb,v,⟨a,ha,rfl⟩,he⟩ := Submodule.mem_sup.mp w.2
      refine ⟨A'.mkQ ⟨a,ha⟩, ?_⟩
      apply (Submodule.Quotient.eq _).mpr
      change T a - w.1 ∈ B
      rw [← he]
      simpa using B.neg_mem hb
  have hd := LinearMap.finrank_le_finrank_of_surjective hf
  have hA := (Submodule.comapSubtypeEquivOfLe hAB).finrank_eq
  have hB := (Submodule.comapSubtypeEquivOfLe
    (show B ≤ G from le_sup_left)).finrank_eq
  have hqA := A'.finrank_quotient_add_finrank
  have hqB := B'.finrank_quotient_add_finrank
  change Module.finrank F A' = Module.finrank F A at hA
  change Module.finrank F B' = Module.finrank F B at hB
  rw [hA] at hqA
  rw [hB] at hqB
  change Module.finrank F G + _ ≤ _
  omega

noncomputable def growthChain (T : M →ₗ[F] M) (U : Submodule F M) : ℕ → Submodule F M
  | 0 => U
  | j+1 => grow T (growthChain T U j)

omit [FiniteDimensional F M] in
theorem growthChain_mono (T : M →ₗ[F] M) (U : Submodule F M) :
    Monotone (growthChain T U) :=
  monotone_nat_of_le_succ (fun _ => le_sup_left)

omit [FiniteDimensional F M] in
theorem shift_mem_growthChain (T : M →ₗ[F] M) (U : Submodule F M)
    (w : M) (hw : w ∈ U) (j : ℕ) : (T^j) w ∈ growthChain T U j := by
  induction j with
  | zero => simpa [growthChain] using hw
  | succ j ih =>
    rw [pow_succ', Module.End.mul_apply]
    exact (show (growthChain T U j).map T ≤ growthChain T U (j+1) from le_sup_right)
      ⟨_,ih,rfl⟩

omit [FiniteDimensional F M] in
theorem growthChain_le (T : M →ₗ[F] M) (U V : Submodule F M) (j : ℕ)
    (h : ∀ w ∈ U, ∀ a ≤ j, (T^a) w ∈ V) : growthChain T U j ≤ V := by
  induction j generalizing V with
  | zero => intro w hw; simpa using h w hw 0 le_rfl
  | succ j ih =>
    apply sup_le (ih V (fun w hw a ha => h w hw a (by omega)))
    rw [Submodule.map_le_iff_le_comap]
    apply ih
    intro w hw a ha
    change T ((T^a) w) ∈ V
    rw [← Module.End.mul_apply, ← pow_succ']
    exact h w hw (a+1) (by omega)

variable {n : ℕ}

/-- A shift-stable word space containing constants contains all words. -/
theorem stable_eq_top (x : Fin n → F) (hx : Function.Injective x)
    (U : Submodule F (Fin n → F)) (h1 : evaluate x 1 ∈ U)
    (hT : U.map (shift x) ≤ U) : U = ⊤ := by
  apply top_unique
  rw [← evalSpace_top x hx]
  apply (evalSpace_le_iff x n U).mpr
  suffices h : ∀ j, evaluate x (X^j) ∈ U from fun j _ => h j
  intro j
  induction j with
  | zero => simpa using h1
  | succ j ih =>
    have h := hT ⟨_,ih,rfl⟩
    simpa only [shift_evaluate, ← pow_succ'] using h

theorem grow_strict (x : Fin n → F) (hx : Function.Injective x)
    (U : Submodule F (Fin n → F)) (h1 : evaluate x 1 ∈ U)
    (hn : Module.finrank F U < n) : Module.finrank F U < Module.finrank F (grow (shift x) U) := by
  apply Submodule.finrank_lt_finrank_of_lt
  apply lt_of_le_of_ne le_sup_left
  intro he
  have ht := stable_eq_top x hx U h1 (by intro w hw; rw [he]; exact (show U.map (shift x) ≤ grow (shift x) U from le_sup_right) hw)
  rw [ht, finrank_top, Module.finrank_fin_fun] at hn
  omega

end RecursivePolygero.Local.Shift
