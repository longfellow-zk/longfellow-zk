import JBAgreement.Recenter

/-!
# Guruswami–Sudan: interpolation with multiplicities, and the root property

This file removes the last assumption of the development: it *proves* the
Guruswami–Sudan input consumed by `correlatedAgreement_of_GS_sharp`.

## Multiplicity via the Taylor shift

`vanishesTo m x₀ y₀ Q` says every coefficient of the shifted polynomial
`Q(X + x₀, Y + y₀)` in bidegree `(i, j)` with `i + j < m` vanishes.  Two facts make
this the right definition here:

* it is preserved by *any* coefficient homomorphism (`vanishesTo_map`), so the
  vanishing conditions imposed over `F[Z]` at the moving point `(dom x, u₀x + Z·u₁x)`
  specialise for free to every `z`; and

* it yields the divisibility that drives the root count: if `p(x₀) = y₀`, then
  `(X - x₀)^m ∣ Q(X, p(X))` (`pow_dvd_eval_of_vanishesTo`) — each monomial of the
  shifted polynomial contributes `(X-x₀)^i · (p - y₀)^j` with `i + j ≥ m`.

## Interpolation without linear algebra

Over the *finite* field `F` the existence of a nonzero interpolant needs no rank
argument: the map sending a coefficient vector to its tuple of constraint values is
additive, so as soon as the constraint space is smaller than the coefficient space it
is not injective, and the difference of two colliding vectors assembles into a nonzero
`Q` with all constraints zero (`exists_interpolant`).

The support is the Guruswami–Sudan triangle `{(a,b) : b ≤ dY, a + w·b ≤ D}` — the
weighted-degree shape is what reaches the Johnson radius (a rectangular support loses
a factor `√2`) — and the coefficients are polynomials in `Z` of degree `≤ dZ`.  The
counting hypothesis is the standard one, `#constraints < #coefficients`, in closed
form.

## The root property

`eval_map_eq_zero_of_agreements` : if `p` has degree at most the interpolation
weight `w` and agrees with the specialised
word on more than `D/m` points, then `Q_z(X, p(X)) = 0` — i.e. `(Y - p) ∣ Q_z`.  The
divisibilities `(X - x₀)^m` at the (distinct) agreement points multiply up by pairwise
coprimality and overwhelm the weighted degree `D` of `Q_z(X, p(X))`.
-/

namespace JBAgreement

open Polynomial Finset

/-! ### The Taylor shift and vanishing to order `m` -/

section Shift

variable {A B : Type*} [CommRing A] [CommRing B]

/-- The `X`-shift `X ↦ X + x₀` on `A[X]`. -/
noncomputable def xShift (x₀ : A) : A[X] →+* A[X] :=
  eval₂RingHom (C : A →+* A[X]) (X + C x₀)

@[simp] lemma xShift_apply (x₀ : A) (p : A[X]) : xShift x₀ p = p.comp (X + C x₀) := rfl

lemma xShift_xShift (x₀ x₁ : A) (p : A[X]) :
    xShift x₀ (xShift x₁ p) = xShift (x₀ + x₁) p := by
  have h : (xShift x₀).comp (xShift x₁) = xShift (x₀ + x₁) := by
    refine ringHom_ext ?_ ?_
    · intro a
      simp [xShift]
    · simp [xShift, add_assoc]
  exact RingHom.congr_fun h p

@[simp] lemma xShift_zero (p : A[X]) : xShift (0 : A) p = p := by
  have h : xShift (0 : A) = RingHom.id A[X] := by
    refine ringHom_ext ?_ ?_ <;> simp [xShift]
  rw [h]
  rfl

/-- The bivariate Taylor shift `Q(X, Y) ↦ Q(X + x₀, Y + y₀)` on `A[X][Y]`. -/
noncomputable def shift2 (x₀ y₀ : A) (Q : (A[X])[X]) : (A[X])[X] :=
  ((Q.map (xShift x₀)).comp (X + C (C y₀)))

/-- Vanishing to order `m` at `(x₀, y₀)`: all Taylor coefficients of total degree
`< m` vanish. -/
def vanishesTo (m : ℕ) (x₀ y₀ : A) (Q : (A[X])[X]) : Prop :=
  ∀ i j, i + j < m → ((shift2 x₀ y₀ Q).coeff j).coeff i = 0

/-- The Taylor shift is additive. -/
lemma shift2_sub (x₀ y₀ : A) (Q Q' : (A[X])[X]) :
    shift2 x₀ y₀ (Q - Q') = shift2 x₀ y₀ Q - shift2 x₀ y₀ Q' := by
  unfold shift2
  rw [Polynomial.map_sub, sub_comp]

/-- The Taylor shift commutes with coefficient homomorphisms. -/
lemma shift2_map (φ : A →+* B) (x₀ y₀ : A) (Q : (A[X])[X]) :
    shift2 (φ x₀) (φ y₀) (Q.map (mapRingHom φ))
      = (shift2 x₀ y₀ Q).map (mapRingHom φ) := by
  unfold shift2
  rw [map_comp]
  congr 1
  · rw [Polynomial.map_map, Polynomial.map_map]
    congr 1
    refine ringHom_ext ?_ ?_
    · intro a
      simp [xShift]
    · simp [xShift]
  · simp

/-- Vanishing specialises along any coefficient homomorphism. -/
lemma vanishesTo_map (φ : A →+* B) {m : ℕ} {x₀ y₀ : A} {Q : (A[X])[X]}
    (h : vanishesTo m x₀ y₀ Q) :
    vanishesTo m (φ x₀) (φ y₀) (Q.map (mapRingHom φ)) := by
  intro i j hij
  rw [shift2_map, coeff_map, coe_mapRingHom, coeff_map, h i j hij, map_zero]

/-- Un-shifting: mapping the Taylor shift by `X ↦ X - x₀` recovers the `Y`-shift
alone. -/
lemma map_xShift_neg_shift2 (x₀ y₀ : A) (Q : (A[X])[X]) :
    (shift2 x₀ y₀ Q).map (xShift (-x₀)) = Q.comp (X + C (C y₀)) := by
  unfold shift2
  rw [map_comp, Polynomial.map_map]
  have hid : (xShift (-x₀)).comp (xShift x₀) = RingHom.id A[X] := by
    refine ringHom_ext ?_ ?_
    · intro a
      simp [xShift]
    · simp [xShift]
  rw [hid, Polynomial.map_id]
  congr 1
  rw [Polynomial.map_add, map_C, Polynomial.map_X]
  congr 1
  simp [xShift]

/-- **The multiplicity divisibility.**  If `Q` vanishes to order `m` at `(x₀, y₀)` and
`p(x₀) = y₀`, then `(X - x₀)^m` divides `Q(X, p(X))`. -/
theorem pow_dvd_eval_of_vanishesTo {m : ℕ} {x₀ y₀ : A} {Q : (A[X])[X]}
    (hV : vanishesTo m x₀ y₀ Q) {p : A[X]} (hp : p.eval x₀ = y₀) :
    ((X : A[X]) - C x₀) ^ m ∣ Q.eval p := by
  set Qh := shift2 x₀ y₀ Q with hQh
  -- Un-shift: `Q.eval p` in terms of the shifted polynomial.
  have hunshift : Q.eval p = ((Qh.map (xShift (-x₀))).eval (p - C y₀)) := by
    rw [hQh, map_xShift_neg_shift2, eval_comp]
    congr 1
    rw [eval_add, eval_C, eval_X, sub_add_cancel]
  rw [hunshift]
  -- Expand as a sum over `Y`-coefficients and divide each term.
  rw [eval_eq_sum_range]
  refine Finset.dvd_sum fun j _ => ?_
  rw [coeff_map]
  have hpy : ((X : A[X]) - C x₀) ∣ (p - C y₀) := by
    rw [dvd_iff_isRoot]
    simp [IsRoot, hp]
  have hshiftpow : ∀ r : ℕ, xShift (-x₀) ((X : A[X]) ^ r)
      = ((X : A[X]) - C x₀) ^ r := by
    intro r
    rw [map_pow, xShift_apply, X_comp, map_neg, ← sub_eq_add_neg]
  rcases lt_or_ge j m with hj | hj
  · -- Low `Y`-degree: the `X`-order of the coefficient makes up the difference.
    have hcoeff : (X : A[X]) ^ (m - j) ∣ Qh.coeff j := by
      rw [X_pow_dvd_iff]
      intro i hi
      exact hV i j (by omega)
    have h1 : ((X : A[X]) - C x₀) ^ (m - j) ∣ xShift (-x₀) (Qh.coeff j) := by
      have h2 := map_dvd (xShift (-x₀)) hcoeff
      rwa [hshiftpow] at h2
    have h2 : ((X : A[X]) - C x₀) ^ j ∣ (p - C y₀) ^ j := pow_dvd_pow_of_dvd hpy j
    have h3 := mul_dvd_mul h1 h2
    rwa [← pow_add, Nat.sub_add_cancel (le_of_lt hj)] at h3
  · -- High `Y`-degree: the substituted factor alone suffices.
    have h2 : ((X : A[X]) - C x₀) ^ m ∣ (p - C y₀) ^ j := by
      calc ((X : A[X]) - C x₀) ^ m ∣ (p - C y₀) ^ m := pow_dvd_pow_of_dvd hpy m
        _ ∣ (p - C y₀) ^ j := pow_dvd_pow _ hj
    exact Dvd.dvd.mul_left h2 _

end Shift



/-! ### Heights of the shifted polynomial -/

section Heights

variable {F : Type*} [Field F]

/-- The two-layer height system on `F[Z][X][Y]`: every `(Y,X)`-coefficient has
`Z`-degree at most the size. -/
noncomputable def heightSizeSystem₂ (F : Type*) [CommRing F] :
    SizeSystem ((F[X][X])[X]) where
  P W d := ∀ j, IsHeightLE (W.coeff j) d
  mono := fun h hle j => (h j).mono hle
  zero := fun d j => by simp
  one := fun j => by
    rcases eq_or_ne j 0 with rfl | h
    · intro i
      rw [coeff_one]
      split_ifs with h'
      · rcases eq_or_ne i 0 with rfl | hi
        · simp [coeff_one]
        · simp [coeff_one, hi]
      · simp
    · intro i
      simp [coeff_one, h]
  neg := fun h j => by
    rw [coeff_neg]
    exact (h j).neg
  add := fun h₁ h₂ j => by
    rw [coeff_add]
    exact (h₁ j).add (h₂ j)
  mul := fun {g h m m'} h₁ h₂ j => by
    rw [coeff_mul]
    exact IsHeightLE.sum _ _ fun p _ => (h₁ p.1).mul (h₂ p.2)

/-- The `X`-shift by a scalar preserves two-layer heights. -/
theorem heightLE₂_map_xShift {W : (F[X][X])[X]} {d : ℕ} (v : F)
    (hW : ∀ j, IsHeightLE (W.coeff j) d) :
    ∀ j, IsHeightLE ((W.map (xShift (C v))).coeff j) d := by
  intro j
  rw [coeff_map]
  have hx : xShift (C v) = shiftZ v := rfl
  rw [hx]
  exact isHeightLE_shiftZ v (hW j)

/-- Composition with `Y + y₀` (`y₀` of `Z`-degree ≤ 1) raises two-layer heights by the
`Y`-degree. -/
theorem heightLE₂_comp {W : (F[X][X])[X]} {d dY : ℕ} {y₀ : F[X]}
    (hW : ∀ j, IsHeightLE (W.coeff j) d) (hWdeg : W.natDegree ≤ dY)
    (hy : y₀.natDegree ≤ 1) :
    ∀ j, IsHeightLE ((W.comp (X + C (C y₀))).coeff j) (d + dY) := by
  have hbase : (heightSizeSystem₂ F).P ((X : (F[X][X])[X]) + C (C y₀)) 1 := by
    intro j
    rw [coeff_add, coeff_X, coeff_C]
    split_ifs with h1 h2 h2
    · exfalso; omega
    · intro i
      rw [add_zero, coeff_one]
      split_ifs <;> simp
    · intro i
      rw [zero_add, coeff_C]
      split_ifs with h3
      · exact le_trans hy (by norm_num)
      · simp
    · intro i
      simp
  have hsum : (heightSizeSystem₂ F).P (W.comp (X + C (C y₀))) (d + dY) := by
    rw [comp, eval₂_eq_sum_range]
    refine (heightSizeSystem₂ F).sum _ _ fun j hj => ?_
    have hj' : j ≤ dY := by
      have := Finset.mem_range.mp hj
      omega
    have hC : (heightSizeSystem₂ F).P (C (W.coeff j)) d := by
      intro j'
      rw [coeff_C]
      split_ifs with h
      · exact hW j
      · simp
    have hpow : (heightSizeSystem₂ F).P (((X : (F[X][X])[X]) + C (C y₀)) ^ j) (j * 1) :=
      (heightSizeSystem₂ F).pow hbase j
    refine (heightSizeSystem₂ F).mono ((heightSizeSystem₂ F).mul hC hpow) ?_
    omega
  exact hsum

/-- **Heights of the Taylor shift.**  At a scalar `X`-point and a `Z`-degree-1
`Y`-point, the shifted polynomial's coefficients have `Z`-degree at most `dZ + dY`. -/
theorem heightLE₂_shift2 {Q : (F[X][X])[X]} {dY dZ : ℕ} (v : F) {y₀ : F[X]}
    (hQY : Q.natDegree ≤ dY) (hQZ : ∀ j, IsHeightLE (Q.coeff j) dZ)
    (hy : y₀.natDegree ≤ 1) :
    ∀ j, IsHeightLE ((shift2 (C v) y₀ Q).coeff j) (dZ + dY) := by
  unfold shift2
  refine heightLE₂_comp (heightLE₂_map_xShift v hQZ) ?_ hy
  exact le_trans (natDegree_map_le) hQY

end Heights

/-! ### Interpolation -/

section Interpolation

variable {F : Type*} [Field F]
variable {ι : Type*}

/-- The coefficient index for weighted interpolation: the Guruswami–Sudan
triangle `{(b,a) : a + w·b ≤ D}`
thickened by the `Z`-box. -/
abbrev gsIdx (w D dY dZ : ℕ) : Type :=
  (b : Fin (dY + 1)) × (Fin (D + 1 - w * b) × Fin (dZ + 1))

/-- The constraint index: a point, a Taylor bidegree `(i,j)` with `i + j < m`, and a
`Z`-coefficient slot. -/
abbrev gsCon (ι : Type*) (m dY dZ : ℕ) : Type _ :=
  ι × ((j : Fin m) × Fin (m - j)) × Fin (dZ + dY + 1)

/-- Assembling a coefficient vector into a polynomial. -/
noncomputable def gsAssemble (w D dY dZ : ℕ) (q : gsIdx w D dY dZ → F) :
    (F[X][X])[X] :=
  ∑ v : gsIdx w D dY dZ,
    monomial (v.1 : ℕ) (monomial (v.2.1 : ℕ) (monomial (v.2.2 : ℕ) (q v)))

/-- Coefficient extraction: the assembly is coefficientwise. -/
theorem gsAssemble_coeff (w D dY dZ : ℕ) (q : gsIdx w D dY dZ → F)
    (v : gsIdx w D dY dZ) :
    (((gsAssemble w D dY dZ q).coeff v.1).coeff v.2.1).coeff v.2.2 = q v := by
  unfold gsAssemble
  rw [finsetSum_coeff]
  simp_rw [finsetSum_coeff]
  rw [Finset.sum_eq_single v]
  · simp
  · intro v' _ hne
    by_cases h1 : (v'.1 : ℕ) = (v.1 : ℕ)
    · have hb : v'.1 = v.1 := Fin.ext h1
      obtain ⟨b, a', c'⟩ := v'
      obtain ⟨b₂, a, c⟩ := v
      cases hb
      by_cases h2 : (a' : ℕ) = (a : ℕ)
      · have ha : a' = a := Fin.ext h2
        cases ha
        by_cases h3 : (c' : ℕ) = (c : ℕ)
        · have hc : c' = c := Fin.ext h3
          cases hc
          exact (hne rfl).elim
        · simp [coeff_monomial, h3]
      · simp [coeff_monomial, h2]
    · simp [coeff_monomial, h1]
  · intro h
    exact absurd (Finset.mem_univ v) h

/-- The assembly is subtractive. -/
theorem gsAssemble_sub (w D dY dZ : ℕ) (q q' : gsIdx w D dY dZ → F) :
    gsAssemble w D dY dZ (q - q')
      = gsAssemble w D dY dZ q - gsAssemble w D dY dZ q' := by
  simp [gsAssemble, Pi.sub_apply, map_sub, Finset.sum_sub_distrib]

/-- `Y`-degree of the assembly. -/
theorem gsAssemble_natDegree (w D dY dZ : ℕ) (q : gsIdx w D dY dZ → F) :
    (gsAssemble w D dY dZ q).natDegree ≤ dY := by
  refine natDegree_sum_le_of_forall_le _ _ fun v _ => ?_
  refine le_trans (natDegree_monomial_le _) ?_
  have := v.1.isLt
  omega

/-- Weighted `X`-degree of the assembly. -/
theorem gsAssemble_coeff_natDegree (w D dY dZ : ℕ) (q : gsIdx w D dY dZ → F) (b : ℕ) :
    ((gsAssemble w D dY dZ q).coeff b).natDegree ≤ D - w * b := by
  unfold gsAssemble
  rw [finsetSum_coeff]
  refine natDegree_sum_le_of_forall_le _ _ fun v _ => ?_
  rw [coeff_monomial]
  split_ifs with h
  · refine le_trans (natDegree_monomial_le _) ?_
    have h2 := v.2.1.isLt
    rw [← h]
    omega
  · simp

/-- `Z`-heights of the assembly. -/
theorem gsAssemble_isHeightLE (w D dY dZ : ℕ) (q : gsIdx w D dY dZ → F) (b : ℕ) :
    IsHeightLE ((gsAssemble w D dY dZ q).coeff b) dZ := by
  unfold gsAssemble
  rw [finsetSum_coeff]
  intro a
  rw [finsetSum_coeff]
  refine natDegree_sum_le_of_forall_le _ _ fun v _ => ?_
  rw [coeff_monomial]
  split_ifs with h
  · rw [coeff_monomial]
    split_ifs with h'
    · refine le_trans (natDegree_monomial_le _) ?_
      have := v.2.2.isLt
      omega
    · simp
  · simp

/-- The moving word point over `F[Z]`. -/
noncomputable def wordZ (u₀ u₁ : ι → F) (x : ι) : F[X] :=
  C (u₀ x) + X * C (u₁ x)

lemma wordZ_natDegree_le (u₀ u₁ : ι → F) (x : ι) : (wordZ u₀ u₁ x).natDegree ≤ 1 := by
  unfold wordZ
  refine le_trans (natDegree_add_le _ _) (max_le (by simp) ?_)
  refine le_trans (natDegree_mul_le) ?_
  simp

lemma wordZ_eval (u₀ u₁ : ι → F) (x : ι) (z : F) :
    (wordZ u₀ u₁ x).eval z = u₀ x + z * u₁ x := by
  unfold wordZ
  simp
  ring

section Finite

variable [Fintype F] [Fintype ι] [DecidableEq ι]

/-- **Existence of the Guruswami–Sudan interpolant.**

Over the finite field `F`, as soon as the constraint count is smaller than the
coefficient count (hypothesis `hcnt`, stated in doubled closed form), there is a
*nonzero* `Q ∈ F[Z][X][Y]` with `Y`-degree ≤ `dY`, weighted `X`-degrees
(`deg_X Q_b ≤ D - k·b`), `Z`-height ≤ `dZ`, vanishing to order `m` at every point
`(dom x, u₀ x + Z·u₁ x)`.

No rank computation: the constraint map is subtractive, and a counting collision
provides the interpolant. -/
theorem exists_interpolant (dom : ι → F) (u₀ u₁ : ι → F) (w m D dY dZ : ℕ)
    (hwdY : w * dY ≤ D)
    (hcnt : Fintype.card ι * (m * (m + 1)) * (dZ + dY + 1)
        < ((dY + 1) * (2 * (D + 1)) - w * (dY * (dY + 1))) * (dZ + 1)) :
    ∃ Q : (F[X][X])[X], Q ≠ 0 ∧ Q.natDegree ≤ dY ∧
      (∀ b, (Q.coeff b).natDegree ≤ D - w * b) ∧
      (∀ b, IsHeightLE (Q.coeff b) dZ) ∧
      ∀ x : ι, vanishesTo m (C (dom x)) (wordZ u₀ u₁ x) Q := by
  set φ : (gsIdx w D dY dZ → F) → (gsCon ι m dY dZ → F) := fun q con =>
    (((shift2 (C (dom con.1)) (wordZ u₀ u₁ con.1) (gsAssemble w D dY dZ q)).coeff
        con.2.1.1).coeff con.2.1.2).coeff con.2.2 with hφ
  have hφsub : ∀ q q', φ (q - q') = φ q - φ q' := by
    intro q q'
    funext con
    simp only [hφ, Pi.sub_apply]
    rw [gsAssemble_sub, shift2_sub, coeff_sub, coeff_sub, coeff_sub]
  -- The two cardinalities, in doubled closed form.
  have hIdx2 : 2 * Fintype.card (gsIdx w D dY dZ)
      = ((dY + 1) * (2 * (D + 1)) - w * (dY * (dY + 1))) * (dZ + 1) := by
    have h1 : Fintype.card (gsIdx w D dY dZ)
        = ∑ b : Fin (dY + 1), (D + 1 - w * b) * (dZ + 1) := by
      rw [Fintype.card_sigma]
      exact Finset.sum_congr rfl fun b _ => by
        rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    rw [h1, Fin.sum_univ_eq_sum_range (fun b => (D + 1 - w * b) * (dZ + 1))]
    rw [← Finset.sum_mul]
    have h2 : (∑ b ∈ Finset.range (dY + 1), (D + 1 - w * b))
        + w * (∑ b ∈ Finset.range (dY + 1), b)
        = (dY + 1) * (D + 1) := by
      rw [Finset.mul_sum, ← Finset.sum_add_distrib]
      have h3 : ∀ b ∈ Finset.range (dY + 1),
          D + 1 - w * b + w * b = D + 1 := by
        intro b hb
        have hb' : b ≤ dY := by
          have := Finset.mem_range.mp hb
          omega
        have : w * b ≤ w * dY := Nat.mul_le_mul_left _ hb'
        omega
      rw [Finset.sum_congr rfl h3, Finset.sum_const, Finset.card_range, smul_eq_mul]
    have h4 : (∑ b ∈ Finset.range (dY + 1), b) * 2 = (dY + 1) * dY :=
      Finset.sum_range_id_mul_two (dY + 1)
    -- Combine.
    have h5 : 2 * (∑ b ∈ Finset.range (dY + 1), (D + 1 - w * b))
        = (dY + 1) * (2 * (D + 1)) - w * (dY * (dY + 1)) := by
      have e1 : 2 * ((∑ b ∈ Finset.range (dY + 1), (D + 1 - w * b))
          + w * (∑ b ∈ Finset.range (dY + 1), b)) =
            2 * ((dY + 1) * (D + 1)) := by
        rw [h2]
      have e2 : 2 * (w * (∑ b ∈ Finset.range (dY + 1), b)) =
          w * (dY * (dY + 1)) := by
        calc 2 * (w * (∑ b ∈ Finset.range (dY + 1), b))
            = w * ((∑ b ∈ Finset.range (dY + 1), b) * 2) := by ring
          _ = w * ((dY + 1) * dY) := by rw [h4]
          _ = w * (dY * (dY + 1)) := by ring
      have e3 : (dY + 1) * (2 * (D + 1)) = 2 * ((dY + 1) * (D + 1)) := by ring
      omega
    calc 2 * ((∑ b ∈ Finset.range (dY + 1), (D + 1 - w * b)) * (dZ + 1))
        = (2 * (∑ b ∈ Finset.range (dY + 1), (D + 1 - w * b))) *
            (dZ + 1) := by ring
      _ = ((dY + 1) * (2 * (D + 1)) - w * (dY * (dY + 1))) *
            (dZ + 1) := by rw [h5]
  have hCon2 : 2 * Fintype.card (gsCon ι m dY dZ)
      = Fintype.card ι * (m * (m + 1)) * (dZ + dY + 1) := by
    have h1 : Fintype.card ((j : Fin m) × Fin (m - j)) = ∑ j ∈ Finset.range m, (m - j) := by
      rw [Fintype.card_sigma]
      have h0 : ∀ j : Fin m, Fintype.card (Fin (m - j)) = m - (j : ℕ) := fun j =>
        Fintype.card_fin _
      rw [Finset.sum_congr rfl (fun j _ => h0 j)]
      exact Fin.sum_univ_eq_sum_range (fun j => m - j) m
    have h2 : (∑ j ∈ Finset.range m, (m - j)) * 2 = m * (m + 1) := by
      have h3 : (∑ j ∈ Finset.range m, (m - j)) = (∑ j ∈ Finset.range m, j) + m := by
        rcases Nat.eq_zero_or_pos m with rfl | hm
        · simp
        · rw [← Finset.sum_range_reflect]
          have h4 : ∀ j ∈ Finset.range m, m - (m - 1 - j) = j + 1 := by
            intro j hj
            have := Finset.mem_range.mp hj
            omega
          rw [Finset.sum_congr rfl h4, Finset.sum_add_distrib, Finset.sum_const,
            Finset.card_range, smul_eq_mul, mul_one]
      have h5 := Finset.sum_range_id_mul_two m
      calc (∑ j ∈ Finset.range m, (m - j)) * 2
          = (∑ j ∈ Finset.range m, j) * 2 + m * 2 := by rw [h3]; ring
        _ = m * (m - 1) + m * 2 := by rw [h5]
        _ = m * (m + 1) := by
            rcases Nat.eq_zero_or_pos m with rfl | hm
            · simp
            · have : m - 1 + 2 = m + 1 := by omega
              calc m * (m - 1) + m * 2 = m * ((m - 1) + 2) := by ring
                _ = m * (m + 1) := by rw [this]
    rw [Fintype.card_prod, Fintype.card_prod, h1, Fintype.card_fin]
    calc 2 * (Fintype.card ι * ((∑ j ∈ Finset.range m, (m - j)) * (dZ + dY + 1)))
        = Fintype.card ι * ((∑ j ∈ Finset.range m, (m - j)) * 2) * (dZ + dY + 1) := by
          ring
      _ = Fintype.card ι * (m * (m + 1)) * (dZ + dY + 1) := by rw [h2]
  have hcards : Fintype.card (gsCon ι m dY dZ) < Fintype.card (gsIdx w D dY dZ) := by
    omega
  -- Non-injectivity over the finite field.
  have hnoninj : ¬ Function.Injective φ := by
    intro hinj
    have h1 := Fintype.card_le_of_injective φ hinj
    rw [Fintype.card_fun, Fintype.card_fun] at h1
    have hF : 1 < Fintype.card F := Fintype.one_lt_card
    have h2 := Nat.pow_lt_pow_right hF hcards
    omega
  obtain ⟨q₁, q₂, hEq, hne⟩ := Function.not_injective_iff.mp hnoninj
  set q : gsIdx w D dY dZ → F := q₁ - q₂ with hqdef
  have hq0 : q ≠ 0 := sub_ne_zero.mpr hne
  have hφq : φ q = 0 := by
    rw [hqdef, hφsub, hEq, sub_self]
  refine ⟨gsAssemble w D dY dZ q, ?_, gsAssemble_natDegree w D dY dZ q,
    gsAssemble_coeff_natDegree w D dY dZ q, gsAssemble_isHeightLE w D dY dZ q, ?_⟩
  · -- Nonzero: a nonzero entry survives as a coefficient.
    intro h0
    apply hq0
    funext v
    have := gsAssemble_coeff w D dY dZ q v
    rw [h0] at this
    simpa using this.symm
  · -- The vanishing conditions.
    intro x i j hij
    set c : F[X] := ((shift2 (C (dom x)) (wordZ u₀ u₁ x)
      (gsAssemble w D dY dZ q)).coeff j).coeff i with hc
    have hdegc : c.natDegree ≤ dZ + dY := by
      rw [hc]
      exact heightLE₂_shift2 (dom x) (gsAssemble_natDegree w D dY dZ q)
        (gsAssemble_isHeightLE w D dY dZ q) (wordZ_natDegree_le u₀ u₁ x) j i
    have hcoeffs : ∀ ℓ, c.coeff ℓ = 0 := by
      intro ℓ
      rcases le_or_gt ℓ (dZ + dY) with hℓ | hℓ
      · have hj : j < m := by omega
        have hi : i < m - j := by omega
        have := congrFun hφq (⟨x, ⟨⟨⟨j, hj⟩, ⟨i, hi⟩⟩, ⟨ℓ, by omega⟩⟩⟩ : gsCon ι m dY dZ)
        simpa [hφ, hc] using this
      · exact coeff_eq_zero_of_natDegree_lt (by omega)
    exact Polynomial.ext hcoeffs

end Finite

/-! ### The root property -/

/-- **The Guruswami–Sudan root property.**  If the specialised interpolant vanishes to
order `m` at `(x₀, p(x₀))` for every `x₀` in a set `T` of size `> D/m`, and the
degree of `p` is at most the interpolation weight `w`, then `Q_z(X, p(X)) = 0`. -/
theorem eval_map_eq_zero_of_agreements
    {Q : (F[X][X])[X]} {w m D dY : ℕ}
    (hQY : Q.natDegree ≤ dY) (hwdY : w * dY ≤ D)
    (hQb : ∀ b, (Q.coeff b).natDegree ≤ D - w * b)
    {z : F} {p : F[X]} (hp : p.natDegree ≤ w)
    {T : Finset F}
    (hvan : ∀ x₀ ∈ T, vanishesTo m x₀ (p.eval x₀) (Q.map (mapRingHom (evalRingHom z))))
    (hDT : D < m * T.card) :
    (Q.map (mapRingHom (evalRingHom z))).eval p = 0 := by
  set Qz := Q.map (mapRingHom (evalRingHom z)) with hQz
  set R : F[X] := Qz.eval p with hR
  rw [← not_ne_iff]
  intro hR0
  -- Each agreement point contributes an `m`-fold factor.
  have hdvd1 : ∀ x₀ ∈ T, ((X : F[X]) - C x₀) ^ m ∣ R := by
    intro x₀ hx₀
    exact pow_dvd_eval_of_vanishesTo (hvan x₀ hx₀) rfl
  have hprod : (∏ x₀ ∈ T, ((X : F[X]) - C x₀) ^ m) ∣ R := by
    refine Finset.prod_dvd_of_coprime ?_ hdvd1
    intro a _ b _ hab
    exact (isCoprime_X_sub_C_of_isUnit_sub
      (by simpa using sub_ne_zero.mpr hab)).pow
  -- Degrees.
  have hdegprod : (∏ x₀ ∈ T, ((X : F[X]) - C x₀) ^ m).natDegree = T.card * m := by
    rw [natDegree_prod]
    · have h1 : ∀ x₀ ∈ T, (((X : F[X]) - C x₀) ^ m).natDegree = m := by
        intro x₀ _
        rw [natDegree_pow, natDegree_X_sub_C, mul_one]
      rw [Finset.sum_congr rfl h1, Finset.sum_const, smul_eq_mul]
    · intro x₀ _
      exact pow_ne_zero _ (X_sub_C_ne_zero x₀)
  have hdegR : R.natDegree ≤ D := by
    rw [hR, eval_eq_sum_range]
    refine natDegree_sum_le_of_forall_le _ _ fun b hb => ?_
    have hbdY : b ≤ dY := by
      have h1 := Finset.mem_range.mp hb
      have h2 : Qz.natDegree ≤ dY := le_trans (natDegree_map_le) hQY
      omega
    refine le_trans (natDegree_mul_le) ?_
    have h3 : (Qz.coeff b).natDegree ≤ D - w * b := by
      rw [hQz, coeff_map]
      exact le_trans (natDegree_map_le) (hQb b)
    have h4 : (p ^ b).natDegree ≤ w * b := by
      rw [natDegree_pow]
      calc b * p.natDegree ≤ b * w := Nat.mul_le_mul_left _ hp
        _ = w * b := Nat.mul_comm _ _
    have h5 : w * b ≤ D := le_trans (Nat.mul_le_mul_left _ hbdY) hwdY
    omega
  have h6 := natDegree_le_of_dvd hprod hR0
  rw [hdegprod] at h6
  have h7 : m * T.card = T.card * m := by ring
  omega

end Interpolation

end JBAgreement
