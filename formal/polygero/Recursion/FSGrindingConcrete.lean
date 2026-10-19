import polygero.Recursion.FSGrindingPrepare
import polygero.Local.GrindingGeometry
import polygero.Recursion.FSGrindingLowerBound

/-! The actual 8192-column / 512-dimensional three-region root family,
with all preparation and query-mass premises discharged. -/
namespace RecursivePolygero.FiatShamir.TwoLevel
open Finset Codes Polynomial ProfileAnalysis Local Local.Polygero LigeroFamily
open GrindingAlgebra
open Merkle.RandomOracle
open scoped Classical
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

section Geometry
variable {q r w : ℕ} (D : ReedSolomon.Domain F r w 8192)
  (layout : ConstraintLayout F q w) (slot : Fin q) (hcode : r+w = 512)

include hcode in
omit [Fintype F] [DecidableEq F] in
private theorem commonPolynomial_exists : ∃ g : DegreeLT F (r+w),
    (g : F[X]).eval (D.point (logicalWitnessPosition layout slot)) = 1 ∧
    ∀ col ∈ GrindingGeometry.common, (g : F[X]).eval (D.point (codePosition col)) = 0 := by
  apply exists_domain_common_roots
  rw [GrindingGeometry.common_card, hcode]
  decide

noncomputable def commonPolynomial : DegreeLT F (r+w) :=
  Classical.choose (commonPolynomial_exists D layout slot hcode)

omit [Fintype F] [DecidableEq F] in
theorem commonPolynomial_spec :
    ((commonPolynomial D layout slot hcode : DegreeLT F (r+w)) : F[X]).eval
        (D.point (logicalWitnessPosition layout slot)) = 1 ∧
    ∀ col ∈ GrindingGeometry.common,
      ((commonPolynomial D layout slot hcode : DegreeLT F (r+w)) : F[X]).eval
        (D.point (codePosition col)) = 0 :=
  Classical.choose_spec (commonPolynomial_exists D layout slot hcode)

omit [Fintype F] [DecidableEq F] in
theorem geometry_region_agrees (values : Fin 3 → F) (i : Fin 3) (col : Fin 8192)
    (hc : col ∈ GrindingGeometry.region i) :
    GrindingGeometry.label values col = values i ∨
      ((commonPolynomial D layout slot hcode : DegreeLT F (r+w)) : F[X]).eval
        (D.point (codePosition col)) = 0 := by
  rcases GrindingGeometry.label_agrees values i col hc with ha | ha
  · exact Or.inr ((commonPolynomial_spec D layout slot hcode).2 col ha)
  · exact Or.inl ha

end Geometry

section Prepare
variable {q r w : ℕ} (D : ReedSolomon.Domain F r w 8192)
  (layout : ConstraintLayout F q w) (d s t : ℕ) (hprimary : r+w+s ≤ 8192)
  (hquery : t ≤ 8192) (j : Slots d q) (hcode : r+w = 512) (values : Fin 3 → F)
local notation "I₀" => linearInstance D layout d s t hprimary hquery
local notation "g₀" => commonPolynomial D layout (Prod.snd j) hcode

noncomputable def geometryRoots : F → (I₀).layer.Oracle :=
  mixtureRoots D layout d s t hprimary hquery j g₀ (GrindingGeometry.label values) GrindingGeometry.spare

theorem geometryRoots_injective :
    Function.Injective (geometryRoots D layout d s t hprimary hquery j hcode values) :=
  mixtureRoots_injective D layout d s t hprimary hquery j g₀
    (GrindingGeometry.label values) GrindingGeometry.spare

noncomputable def geometryPrepare : ∀ (W : (I₀).layer.Oracle) (coin : (I₀).layer.Coin),
    Option (GrindingReady (I := I₀) (contradictoryStatement j) W coin) :=
  mixturePrepare D layout d s t hprimary hquery (by omega) j g₀
    (commonPolynomial_spec D layout j.2 hcode).1
    (GrindingGeometry.label values) values GrindingGeometry.region GrindingGeometry.spare
    (geometry_region_agrees D layout j.2 hcode values) GrindingGeometry.region_avoids_spare

local notation "prepare₀" => geometryPrepare D layout d s t hprimary hquery j hcode values
local notation "roots₀" => geometryRoots D layout d s t hprimary hquery j hcode values

theorem geometryPrepare_root_isSome (c : F) (coin : (I₀).layer.Coin) :
    (prepare₀ (roots₀ c) coin).isSome = true ↔
      ∃ i, (coin.1 false, coin.1 true) ∈ exceptionLine (values i) := by
  unfold geometryPrepare geometryRoots
  apply mixturePrepare_root_isSome

theorem geometryPrepare_good_mean (W : (I₀).layer.Oracle) (coin : (I₀).layer.Coin)
    (ready : GrindingReady (I := I₀) (contradictoryStatement j) W coin)
    (hready : prepare₀ W coin = some ready) :
    mean (fun Q => indicator (ready.goodQueries Q)) =
      (Nat.choose 3071 t : ℚ) / Nat.choose 8192 t := by
  unfold geometryPrepare at hready
  apply mixturePrepare_good_mean _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ W coin ready hready
  intro i
  exact GrindingGeometry.region_query_mean i t

theorem geometryPrepare_root_mean (hv : Function.Injective values) (c : F) :
    mean (fun coin : (I₀).layer.Coin => indicator ((prepare₀ (roots₀ c) coin).isSome = true)) =
      3 / (Fintype.card F : ℚ) - 2 / (Fintype.card F : ℚ)^2 := by
  convert three_regions_eligible_mean d s values hv using 1
  apply mean_congr
  intro coin
  congr 1
  exact propext (geometryPrepare_root_isSome D layout d s t hprimary hquery j hcode values c coin)

theorem geometryPrepare_root_mean_ne_none (hv : Function.Injective values) (c : F) :
    mean (fun coin : (I₀).layer.Coin => indicator (prepare₀ (roots₀ c) coin ≠ none)) =
      3 / (Fintype.card F : ℚ) - 2 / (Fintype.card F : ℚ)^2 := by
  convert geometryPrepare_root_mean D layout d s t hprimary hquery j hcode values hv c using 1
  apply mean_congr
  intro coin
  cases he : prepare₀ (roots₀ c) coin <;> simp

private theorem event_mean_bounds {A : Type} [Fintype A] [Nonempty A] (P : A → Prop) :
    0 ≤ mean (fun a => indicator (P a)) ∧ mean (fun a => indicator (P a)) ≤ 1 := by
  constructor
  · have h := mean_mono (fun a : A => indicator_nonneg (P a))
    simpa only [mean_const] using h
  · have h := mean_mono (fun a : A => show indicator (P a) ≤ 1 by
      unfold indicator
      split_ifs <;> norm_num)
    simpa only [mean_const] using h

include hcode in
/-- An ordinary proof-valued bounded oracle tree realizes the concrete
three-region attack. Both commitment lists have pairwise distinct actual
inputs; every root/region probability is discharged by Polygero algebra.
The child remains arbitrary, subject to its actual linear-child interface. -/
theorem geometry_exists_failure_tree (hv : Function.Injective values)
    (child : Child (I₀)) (p : HahnSystemCertificate (I₀))
    (cp : HahnSystemCertificate child.instance)
    (hchildk : 1 ≤ child.instance.r + child.instance.w)
    (row : child.instance.WireRow false) (col : Fin child.instance.n)
    (R M depth : ℕ) (hR : R ≤ Fintype.card F) (hM : M ≤ Fintype.card F)
    (hdepth : depth ≤ M) :
    let rootMass : ℚ := 3 / (Fintype.card F : ℚ) - 2 / (Fintype.card F : ℚ)^2
    let queryMass : ℚ := (Nat.choose 3071 t : ℚ) / Nat.choose 8192 t
    ∃ tree : Tree (HashInput child) (Answer child) (Proof child) ((2+M)+R),
      (R * rootMass - (R.choose 2 : ℚ) * rootMass^2) *
        (1 - 1 / (∑ k ∈ range (depth+1), (M.choose k : ℚ) * queryMass^k)) *
        grindingAvoidance child ≤
      Bcs.FiniteProbability.density (fun H => failure child p cp (contradictoryStatement j)
        (fun _ => False) H (tree.run H).1) := by
  let er : Fin R ↪ F := Classical.choice (Function.Embedding.nonempty_of_card_le (by simpa using hR))
  let em : Fin M ↪ F := Classical.choice (Function.Embedding.nonempty_of_card_le (by simpa using hM))
  let rootList : List (I₀).layer.Oracle := List.ofFn (fun i => roots₀ (er i))
  let childList : List F := List.ofFn em
  have hrnodup : rootList.Nodup := List.nodup_ofFn.mpr
    ((geometryRoots_injective D layout d s t hprimary hquery j hcode values).comp er.injective)
  have hmnodup : childList.Nodup := List.nodup_ofFn.mpr em.injective
  let mu : ℚ := 3 / (Fintype.card F : ℚ) - 2 / (Fintype.card F : ℚ)^2
  let rho : ℚ := (Nat.choose 3071 t : ℚ) / Nat.choose 8192 t
  have hmu : 0 ≤ mu ∧ mu ≤ 1 := by
    unfold mu
    rw [← geometryPrepare_root_mean D layout d s t hprimary hquery j hcode values hv (0 : F)]
    exact event_mean_bounds _
  letI : Nonempty (QuerySet 8192 t) := QuerySet.nonempty hquery
  have hrho : 0 ≤ rho ∧ rho ≤ 1 := by
    unfold rho
    rw [← GrindingGeometry.region_query_mean 0 t]
    exact event_mean_bounds _
  have hready : ∀ W ∈ rootList,
      mean (fun coin => indicator (prepare₀ W coin ≠ none)) = mu := by
    intro W hW
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hW
    rw [← hi]
    exact geometryPrepare_root_mean_ne_none D layout d s t hprimary hquery j hcode values hv (er i)
  have hgood : ∀ W ∈ rootList, ∀ coin ready, prepare₀ W coin = some ready →
      mean (fun Q => indicator (ready.goodQueries Q)) = rho := by
    intro W _ coin ready hh
    exact geometryPrepare_good_mean D layout d s t hprimary hquery j hcode values W coin ready hh
  have hfalse : ∀ witness, ¬ (I₀).layer.satisfies (contradictoryStatement j) witness :=
    fun witness hs => contradictoryStatement_false j ⟨witness, hs⟩
  let fallback : Proof child := Classical.choice inferInstance
  have h := grindingAdversary_failure_lower child p cp hchildk (contradictoryStatement j) hfalse
    prepare₀ row col childList hmnodup rootList hrnodup fallback mu rho hmu.1 hmu.2 hrho.1 hrho.2
    hready hgood depth (by simpa only [childList, List.length_ofFn] using hdepth)
  have he : ∃ tree : Tree (HashInput child) (Answer child) (Proof child)
      ((2+childList.length)+rootList.length),
      (rootList.length * mu - (rootList.length.choose 2 : ℚ) * mu^2) *
        (1 - 1 / (∑ k ∈ range (depth+1), (childList.length.choose k : ℚ) * rho^k)) *
        grindingAvoidance child ≤
      Bcs.FiniteProbability.density (fun H => failure child p cp (contradictoryStatement j)
        (fun _ => False) H (tree.run H).1) :=
    ⟨grindingAdversary child hchildk (contradictoryStatement j) prepare₀ row col childList rootList fallback, h⟩
  rw [show childList.length = M by simp only [childList, List.length_ofFn],
    show rootList.length = R by simp only [rootList, List.length_ofFn]] at he
  simpa only [mu, rho] using he

end Prepare

end RecursivePolygero.FiatShamir.TwoLevel
