import JBAgreement.Swap
import JBAgreement.Frobenius
import JBAgreement.Recenter
import JBAgreement.Branch

/-!
# §6.2: branch selection from the Guruswami–Sudan interpolant

The only assumption of the end-to-end theorem is Guruswami–Sudan: a nonzero
`Q ∈ F[Z][X][Y]` of controlled degrees with `Q(X, p_z(X), z) = 0` for every parameter
`z ∈ S`.  This file derives, from that data alone, the entire branch package the jet
machinery consumes:

1. **Prime selection.**  Factor `Q` into primes.  For every `z` at which the
   specialisation `Q_z` is nonzero (all but `≤ D_Z` many), the linear factor
   `Y - p_z(X)` is prime, so it divides some prime factor of positive `Y`-degree.

2. **Separable extraction** (§6.6).  Each relevant prime `P` is `expand (p^f)` of an
   irreducible *separable* `S_P`; the proximate of `S_P` at `z` is `p_z^{p^f}`.  No
   separability assumption remains.

3. **The good slice.**  For each `S_P` the resultant `r_P = Res_Y(S_P, ∂_Y S_P)` is a
   *nonzero* polynomial in `(Z, X)` (Gauss's lemma moves irreducibility to the fraction
   field of `F[Z][X]`, where separability gives coprimality).  A slice `x₀` avoiding
   the `≤ 2·D_Y·D_X` roots in `X` of all the `r_P` exists whenever
   `2·D_Y·D_X < |F|`; at such a slice, `ξ(z, t_z) ≠ 0` fails for at most
   `ht(r_P) ≤ 2·D_Y·D_Z` many `z` per branch (`ringHom_resultant_eq_zero_of_common_root`).

4. **Fiber factoring and weighted selection.**  The fiber `S_P(x₀, T, Z)` is nonzero and
   factors into primes of `F[Z][T]`; each surviving `z` kills a positive-degree prime
   factor of its branch's fiber (the degree-zero factors account for `≤ D_Y·D_Z` bad
   `z`).  There are at most `D_Y` labels `(P, H)` altogether, so some label carries a
   enough surviving parameters for its exact sharp capacity — the bucket handed to
   `exists_goodCoords_sharp`.

The output collects every hypothesis of the branch argument, together with the twist
data `N = p^f` used by the Frobenius untwisting in the endgame.
-/

namespace JBAgreement

open Polynomial Finset

/-! ### Generic helpers -/

theorem multiset_sum_le_of_le {s t : Multiset ℕ} (h : s ≤ t) : s.sum ≤ t.sum := by
  obtain ⟨u, rfl⟩ := Multiset.le_iff_exists_add.mp h
  simp

/-- Sum over the deduplicated support is at most the multiset sum. -/
theorem toFinset_sum_le_multiset_sum {α : Type*} [DecidableEq α] (s : Multiset α)
    (f : α → ℕ) : ∑ a ∈ s.toFinset, f a ≤ (s.map f).sum := by
  have h1 : ∑ a ∈ s.toFinset, f a = (s.dedup.map f).sum := by
    rw [Finset.sum_eq_multiset_sum]
    rfl
  rw [h1]
  exact multiset_sum_le_of_le (Multiset.map_le_map s.dedup_le)

/-- Irreducible polynomials of positive degree over a domain are primitive. -/
theorem isPrimitive_of_irreducible' {R : Type*} [CommRing R] [IsDomain R] {H : R[X]}
    (hirr : Irreducible H) (hdeg : 1 ≤ H.natDegree) : H.IsPrimitive := by
  intro c hc
  obtain ⟨e, he⟩ := hc
  rcases hirr.isUnit_or_isUnit he with hu | hu
  · exact isUnit_C.mp hu
  · exfalso
    have hH0 : H ≠ 0 := hirr.ne_zero
    have hC0 : (C c : R[X]) ≠ 0 := fun h => hH0 (by rw [he, h, zero_mul])
    have he0 : e ≠ 0 := fun h => hH0 (by rw [he, h, mul_zero])
    have : H.natDegree = 0 := by
      rw [he, natDegree_mul hC0 he0, natDegree_C, natDegree_eq_zero_of_isUnit hu]
    omega

/-- The `Z`-height version of the Sylvester bound: if all coefficients of `H` and `g`
(as polynomials over `F[Z][X]`) have `Z`-height at most `a` and `b` respectively, then
the resultant has `Z`-height at most `n·a + m·b`. -/
theorem isHeightLE_resultant {F : Type*} [CommRing F] (H g : (F[X][X])[X]) {a b : ℕ}
    (m n : ℕ) (hH : ∀ i, IsHeightLE (H.coeff i) a) (hg : ∀ i, IsHeightLE (g.coeff i) b) :
    IsHeightLE (resultant H g m n) (n * a + m * b) := by
  rw [resultant, Matrix.det_apply]
  refine IsHeightLE.sum _ _ fun σ _ => ?_
  have hsmul : ∀ (u : ℤˣ) (x : F[X][X]) (c : ℕ), IsHeightLE x c →
      IsHeightLE (u • x) c := by
    intro u x c hx
    rcases Int.units_eq_one_or u with rfl | rfl
    · simpa using hx
    · have h1 : ((-1 : ℤˣ) • x) = -x := by
        rw [Units.smul_def]
        simp
      rw [h1]
      exact hx.neg
  refine hsmul _ _ _ ?_
  have hprod : IsHeightLE (∏ i, sylvester H g m n (σ i) i) (∑ i : Fin (m + n),
      (if (i : ℕ) < m then b else a)) := by
    classical
    induction (Finset.univ : Finset (Fin (m + n))) using Finset.induction with
    | empty =>
        simp only [Finset.prod_empty, Finset.sum_empty]
        intro i
        rw [coeff_one]
        split_ifs <;> simp
    | insert x s hx ih =>
        rw [Finset.prod_insert hx, Finset.sum_insert hx]
        refine IsHeightLE.mul ?_ ih
        rcases lt_or_ge (x : ℕ) m with hxm | hxm
        · rw [if_pos hxm]
          -- a `g`-column
          have : ∃ i : Fin m, Fin.castAdd n i = x := ⟨⟨x, hxm⟩, by simp [Fin.castAdd]⟩
          obtain ⟨i, rfl⟩ := this
          simp only [sylvester, Matrix.of_apply, Fin.addCases_left]
          split_ifs with h
          · exact hg _
          · simp
        · rw [if_neg (not_lt.mpr hxm)]
          have : ∃ i : Fin n, Fin.natAdd m i = x :=
            ⟨⟨(x : ℕ) - m, by omega⟩, by
              apply Fin.ext
              simp [Fin.natAdd]
              omega⟩
          obtain ⟨i, rfl⟩ := this
          simp only [sylvester, Matrix.of_apply, Fin.addCases_right]
          split_ifs with h
          · exact hH _
          · simp
  refine hprod.mono ?_
  have hsum : (∑ i : Fin (m + n), (if (i : ℕ) < m then b else a)) = m * b + n * a := by
    rw [Fin.sum_univ_add]
    have h1 : ∀ i : Fin m, (if ((Fin.castAdd n i : Fin (m + n)) : ℕ) < m then b else a) = b := by
      intro i
      rw [if_pos]
      simp
    have h2 : ∀ i : Fin n, (if ((Fin.natAdd m i : Fin (m + n)) : ℕ) < m then b else a) = a := by
      intro i
      rw [if_neg]
      simp [Fin.natAdd]
    simp only [h1, h2, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul]
  omega

/-- Roots in `F` of a nonzero `F[Z]`-polynomial, as a Finset, number at most its
degree. -/
theorem card_le_natDegree_of_eval_eq_zero {F : Type*} [Field F] [DecidableEq F]
    {c : F[X]} (hc : c ≠ 0) (s : Finset F) (h : ∀ x ∈ s, c.eval x = 0) :
    s.card ≤ c.natDegree := by
  refine le_trans (Finset.card_le_card ?_) (le_trans c.roots.toFinset_card_le
    (card_roots' c))
  intro x hx
  simpa [Multiset.mem_toFinset, mem_roots, hc] using h x hx



/-! ### The selection theorem -/

section Selection

variable {F : Type*} [Field F] [Fintype F]

set_option maxHeartbeats 3200000 in
open scoped Classical in
/-- **§6.2 + §6.6: branch selection.**

From the Guruswami–Sudan data alone — a nonzero interpolant `Q` with degree bounds
`(dX, dY, dZ)` and `Q(X, p_z(X), z) = 0` on `S` — produce a bucket: a subset
`S' ⊆ S` of size `> e + 1`, a separable irreducible branch `Sf` with a Frobenius twist
`N = p^f`, a good slice `x₀`, and an irreducible fiber factor `H`, such that every
`z ∈ S'` lies on the branch (with proximate `p_z^N`), is unramified at the slice, and
kills `H`.

Requires `2·dY·dX < |F|` (room for the slice).  The parameter threshold uses the
sharp total capacity `4k·dYdZ+dY`.  The binder `cols` is the number of columns
charged by the selector, not the evaluation-domain size. -/
theorem exists_bucket_sharp (S : Finset F) (p : F → F[X])
    (Q : (F[X][X])[X]) (hQ0 : Q ≠ 0) (dX dY dZ : ℕ)
    (hQY : Q.natDegree ≤ dY)
    (hQX : ∀ j, (Q.coeff j).natDegree ≤ dX)
    (hQZ : ∀ j i, ((Q.coeff j).coeff i).natDegree ≤ dZ)
    (hGS : ∀ z ∈ S, ((Q.map (mapRingHom (evalRingHom z))).eval (p z)) = 0)
    (hfield : 2 * dY * dX < Fintype.card F)
    (k cols e slack : ℕ) (hslack : 1 ≤ slack)
    (hS : dY * (e + 2) + cols * (4 * k * (dY * dZ) + dY) / slack
      + dZ + 3 * (dY * dZ) < S.card) :
    ∃ (S' : Finset F) (N d' : ℕ) (Sf : (F[X][X])[X]) (x₀ : F) (H : F[X][X]),
      S' ⊆ S ∧ e + 1 < S'.card ∧
      (∃ f : ℕ, N = ringChar F ^ f) ∧
      1 ≤ d' ∧ Sf.natDegree ≤ d' ∧ d' * N ≤ dY ∧
      (∀ j, IsHeightLE (Sf.coeff j) dZ) ∧
      Irreducible H ∧ 1 ≤ H.natDegree ∧ H.natDegree ≤ d' ∧ IsHeightLE H dZ ∧
      IsHeightLE H (swap F H).natDegree ∧
      cols * sharpFiberCapacity (k * N) d' dZ N H.natDegree (swap F H).natDegree
        < slack * S'.card ∧
      (∀ z ∈ S',
        (Sf.map (mapRingHom (evalRingHom z))).eval ((p z) ^ N) = 0 ∧
        eval₂ (chi z x₀) (((p z) ^ N).eval x₀) (derivative Sf) ≠ 0 ∧
        spec z (((p z) ^ N).eval x₀) H = 0) := by
  set pc := ringChar F with hpc
  haveI hpcP : Fact pc.Prime := ⟨CharP.char_is_prime F pc⟩
  have hpc1 : 1 ≤ pc := hpcP.out.one_lt.le
  -- ### 1. Factor the interpolant.
  obtain ⟨fs, hfsP, hfsA⟩ := UniqueFactorizationMonoid.exists_prime_factors Q hQ0
  obtain ⟨u, hu⟩ := hfsA
  have hfs0 : (0 : (F[X][X])[X]) ∉ fs := fun h => (hfsP 0 h).ne_zero rfl
  have multiset_prod_ne_zero : ∀ s : Multiset ((F[X][X])[X]),
      (∀ a ∈ s, a ≠ 0) → s.prod ≠ 0 := by
    intro s hs
    induction s using Multiset.induction_on with
    | empty => simp
    | @cons a s ih =>
        rw [Multiset.prod_cons]
        apply mul_ne_zero
        · exact hs a (Multiset.mem_cons_self a s)
        · exact ih fun b hb => hs b (Multiset.mem_cons_of_mem hb)
  have hprod0 : fs.prod ≠ 0 := multiset_prod_ne_zero fs fun a ha => (hfsP a ha).ne_zero
  have hdegsum : (fs.map natDegree).sum ≤ dY := by
    have h1 : fs.prod.natDegree = (fs.map natDegree).sum := natDegree_multiset_prod fs hfs0
    have h2 : (fs.prod * ↑u).natDegree = fs.prod.natDegree + (↑u : (F[X][X])[X]).natDegree :=
      natDegree_mul hprod0 u.ne_zero
    have h3 : (↑u : (F[X][X])[X]).natDegree = 0 := natDegree_eq_zero_of_isUnit u.isUnit
    rw [hu] at h2
    omega
  have hPdvdQ : ∀ P ∈ fs, P ∣ Q := fun P hP => dvd_trans (Multiset.dvd_prod hP)
    (Dvd.intro _ hu)
  have hPdeg_le : ∀ P ∈ fs, P.natDegree ≤ dY := by
    intro P hP
    refine le_trans ?_ hdegsum
    exact Multiset.single_le_sum (fun x _ => Nat.zero_le x) _
      (Multiset.mem_map_of_mem natDegree hP)
  -- ### 2. Bad parameters where the specialisation dies.
  obtain ⟨j₀, hj₀⟩ : ∃ j, Q.coeff j ≠ 0 := by
    exact ⟨Q.natDegree, by simpa only [coeff_natDegree] using leadingCoeff_ne_zero.mpr hQ0⟩
  obtain ⟨i₀, hi₀⟩ : ∃ i, (Q.coeff j₀).coeff i ≠ 0 := by
    exact ⟨(Q.coeff j₀).natDegree,
      by simpa only [coeff_natDegree] using leadingCoeff_ne_zero.mpr hj₀⟩
  set c₀ : F[X] := (Q.coeff j₀).coeff i₀ with hc₀
  set SbadQ : Finset F := S.filter (fun z => c₀.eval z = 0) with hSbadQ
  have hSbadQcard : SbadQ.card ≤ dZ := by
    refine le_trans (card_le_natDegree_of_eval_eq_zero hi₀ _ ?_) (hQZ j₀ i₀)
    intro z hz
    exact (Finset.mem_filter.mp hz).2
  -- ### 3. Choose a prime factor for every surviving parameter.
  have hQzne : ∀ z : F, c₀.eval z ≠ 0 → Q.map (mapRingHom (evalRingHom z)) ≠ 0 := by
    intro z hcz h0
    apply hcz
    have h1 := congrArg (fun W => ((Polynomial.coeff W j₀).coeff i₀)) h0
    simpa [coeff_map, hc₀] using h1
  have hPzchoice : ∀ z : F, ∃ P : (F[X][X])[X], z ∈ S → c₀.eval z ≠ 0 →
      (P ∈ fs ∧ (X - C (p z)) ∣ P.map (mapRingHom (evalRingHom z))) := by
    intro z
    by_cases hz : z ∈ S ∧ c₀.eval z ≠ 0
    · have hdvdQ : (X - C (p z)) ∣ Q.map (mapRingHom (evalRingHom z)) :=
        dvd_iff_isRoot.mpr (hGS z hz.1)
      have hsplit : Q.map (mapRingHom (evalRingHom z))
          = (fs.map (Polynomial.map (mapRingHom (evalRingHom z)))).prod
            * (↑u : (F[X][X])[X]).map (mapRingHom (evalRingHom z)) := by
        rw [← hu, Polynomial.map_mul]
        congr 1
        exact map_multiset_prod (mapRingHom (mapRingHom (evalRingHom z))) fs
      have hprime : Prime ((X : (F[X])[X]) - C (p z)) := prime_X_sub_C (p z)
      rw [hsplit] at hdvdQ
      rcases hprime.2.2 _ _ hdvdQ with hd | hd
      · obtain ⟨Pm, hPm, hPmdvd⟩ := hprime.exists_mem_multiset_dvd hd
        obtain ⟨P, hPfs, rfl⟩ := Multiset.mem_map.mp hPm
        exact ⟨P, fun _ _ => ⟨hPfs, hPmdvd⟩⟩
      · exfalso
        refine hprime.not_unit (isUnit_of_dvd_unit hd ?_)
        exact u.isUnit.map (mapRingHom (mapRingHom (evalRingHom z)))
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ hz⟩
  choose Pz hPz using hPzchoice
  -- ### 4. Separable extraction for every prime.
  have hextc : ∀ P : (F[X][X])[X], ∃ (fe : ℕ) (Sf : (F[X][X])[X]),
      (Prime P → 1 ≤ P.natDegree →
        (P = expand _ (pc ^ fe) Sf ∧ Sf.derivative ≠ 0 ∧ Irreducible Sf ∧
          1 ≤ Sf.natDegree ∧ Sf.natDegree * pc ^ fe = P.natDegree)) := by
    intro P
    by_cases hP : Prime P ∧ 1 ≤ P.natDegree
    · obtain ⟨fe, Sf, h⟩ :=
        exists_expand_eq pc P.natDegree P le_rfl hP.1.irreducible hP.2
      exact ⟨fe, Sf, fun _ _ => h⟩
    · exact ⟨0, 0, fun h1 h2 => absurd ⟨h1, h2⟩ hP⟩
  choose fe Sfc hext using hextc
  set PS : Finset ((F[X][X])[X]) := fs.toFinset.filter (fun P => 1 ≤ P.natDegree)
    with hPSdef
  have hPSmem : ∀ P ∈ PS, P ∈ fs ∧ Prime P ∧ 1 ≤ P.natDegree := by
    intro P hP
    rw [hPSdef, Finset.mem_filter, Multiset.mem_toFinset] at hP
    exact ⟨hP.1, hfsP P hP.1, hP.2⟩
  -- Facts about the extracted branches.
  have hSf : ∀ P ∈ PS, P = expand _ (pc ^ fe P) (Sfc P) ∧ (Sfc P).derivative ≠ 0 ∧
      Irreducible (Sfc P) ∧ 1 ≤ (Sfc P).natDegree ∧
      (Sfc P).natDegree * pc ^ fe P = P.natDegree := by
    intro P hP
    obtain ⟨_, hprime, hdeg⟩ := hPSmem P hP
    exact hext P hprime hdeg
  have hSfcoeff : ∀ P ∈ PS, ∀ j, (Sfc P).coeff j = P.coeff (j * pc ^ fe P) := by
    intro P hP j
    obtain ⟨hexp, _, _, _, _⟩ := hSf P hP
    have h1 := coeff_expand_mul (pow_pos hpcP.out.pos (fe P)) (Sfc P) j
    rw [← hexp] at h1
    exact h1.symm
  have hSfX : ∀ P ∈ PS, ∀ j, ((Sfc P).coeff j).natDegree ≤ dX := by
    intro P hP j
    rw [hSfcoeff P hP j]
    exact degX_of_dvd (hPdvdQ P (hPSmem P hP).1) hQ0 hQX _
  have hSfZ : ∀ P ∈ PS, ∀ j, IsHeightLE ((Sfc P).coeff j) dZ := by
    intro P hP j
    rw [hSfcoeff P hP j]
    intro i
    exact heightZ_of_dvd (hPdvdQ P (hPSmem P hP).1) hQ0 hQZ _ i
  have hSfdX : ∀ P ∈ PS, ∀ j, ((derivative (Sfc P)).coeff j).natDegree ≤ dX := by
    intro P hP j
    rw [coeff_derivative]
    refine le_trans (natDegree_mul_le) ?_
    have h1 := hSfX P hP (j + 1)
    have hCj : (C ((j : F[X]) + 1) : F[X][X]) = (j : F[X][X]) + 1 := by
      rw [map_add, map_natCast, map_one]
    have h2 : ((j : F[X][X]) + 1).natDegree = 0 := by
      rw [← hCj, natDegree_C]
    omega
  have hSfdZ : ∀ P ∈ PS, ∀ j, IsHeightLE ((derivative (Sfc P)).coeff j) dZ := by
    intro P hP j
    rw [coeff_derivative]
    have h1 : IsHeightLE ((j : F[X][X]) + 1) 0 := by
      have hCj : (C ((j : F[X]) + 1) : F[X][X]) = (j : F[X][X]) + 1 := by
        rw [map_add, map_natCast, map_one]
      rw [← hCj]
      intro i
      rw [coeff_C]
      split_ifs with h
      · have hCj' : (C ((j : F) + 1) : F[X]) = (j : F[X]) + 1 := by
          rw [map_add, map_natCast, map_one]
        rw [← hCj', natDegree_C]
      · simp
    have := (hSfZ P hP (j + 1)).mul h1
    simpa using this
  -- ### 5. Discriminants are nonzero.
  set rr : (F[X][X])[X] → F[X][X] := fun P =>
    resultant (Sfc P) (derivative (Sfc P)) (Sfc P).natDegree
      (derivative (Sfc P)).natDegree with hrr
  have hrr0 : ∀ P ∈ PS, rr P ≠ 0 := by
    intro P hP h0
    obtain ⟨hexp, hder, hirr, hdeg1, hdegeq⟩ := hSf P hP
    set L := FractionRing (F[X][X])
    set ψ : F[X][X] →+* L := algebraMap _ _ with hψ
    have hinj : Function.Injective ψ := IsFractionRing.injective _ _
    have hprim : (Sfc P).IsPrimitive := isPrimitive_of_irreducible' hirr hdeg1
    have hirrL : Irreducible ((Sfc P).map ψ) :=
      hprim.irreducible_iff_irreducible_map_fraction_map.mp hirr
    have hder0 : (derivative (Sfc P)).map ψ ≠ 0 := by
      rw [Ne, Polynomial.map_eq_zero_iff hinj]
      exact hder
    have hdegmap : ((Sfc P).map ψ).natDegree = (Sfc P).natDegree :=
      natDegree_map_eq_of_injective hinj _
    have hdegmapd : ((derivative (Sfc P)).map ψ).natDegree
        = (derivative (Sfc P)).natDegree := natDegree_map_eq_of_injective hinj _
    have hndvd : ¬ ((Sfc P).map ψ ∣ (derivative (Sfc P)).map ψ) := by
      intro hdvd
      have h1 := natDegree_le_of_dvd hdvd hder0
      have h2 : (derivative (Sfc P)).natDegree < (Sfc P).natDegree :=
        natDegree_derivative_lt (by omega)
      omega
    have hcop : IsCoprime ((Sfc P).map ψ) ((derivative (Sfc P)).map ψ) :=
      (hirrL.coprime_iff_not_dvd).mpr hndvd
    have hres0 : resultant ((Sfc P).map ψ) ((derivative (Sfc P)).map ψ) = 0 := by
      rw [hdegmap, hdegmapd, resultant_map_map]
      show ψ (rr P) = 0
      rw [h0, map_zero]
    have := (resultant_eq_zero_iff.mp hres0).2
    exact this hcop
  -- ### 6. The good slice.
  set badX : Finset F := PS.biUnion (fun P =>
    univ.filter (fun x₀ : F => (rr P).eval (C x₀) = 0)) with hbadXdef
  have hbadXP : ∀ P ∈ PS,
      (univ.filter (fun x₀ : F => (rr P).eval (C x₀) = 0)).card
        ≤ 2 * (Sfc P).natDegree * dX := by
    intro P hP
    obtain ⟨_, _, _, hdeg1, _⟩ := hSf P hP
    have hcard : (univ.filter (fun x₀ : F => (rr P).eval (C x₀) = 0)).card
        ≤ (rr P).natDegree := by
      refine le_trans (Finset.card_le_card_of_injOn (fun x₀ => (C x₀ : F[X])) ?_ ?_)
        (le_trans (rr P).roots.toFinset_card_le (card_roots' _))
      · intro x hx
        have hx2 : (rr P).eval (C x) = 0 := by simpa using hx
        simpa [Multiset.mem_toFinset, mem_roots, hrr0 P hP] using hx2
      · exact fun a _ b _ h => C_injective h
    refine le_trans hcard ?_
    have hbound := natDegree_resultant_le (Sfc P) (derivative (Sfc P))
      ((Sfc P).natDegree) ((derivative (Sfc P)).natDegree)
      (hSfX P hP) (hSfdX P hP)
    have hdlt : (derivative (Sfc P)).natDegree ≤ (Sfc P).natDegree :=
      le_of_lt (natDegree_derivative_lt (by omega))
    have h2 : (derivative (Sfc P)).natDegree * dX + (Sfc P).natDegree * dX
        ≤ 2 * (Sfc P).natDegree * dX := by nlinarith
    exact le_trans hbound h2
  have hdegSf_sum : ∑ P ∈ PS, (Sfc P).natDegree ≤ dY := by
    refine le_trans ?_ (le_trans (toFinset_sum_le_multiset_sum fs natDegree) hdegsum)
    have hsub : PS ⊆ fs.toFinset := Finset.filter_subset _ _
    refine le_trans (Finset.sum_le_sum fun P hP => ?_)
      (Finset.sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => Nat.zero_le _)
    obtain ⟨_, _, _, hdeg1, hdegeq⟩ := hSf P hP
    calc (Sfc P).natDegree ≤ (Sfc P).natDegree * pc ^ fe P :=
          Nat.le_mul_of_pos_right _ (pow_pos hpcP.out.pos _)
      _ = P.natDegree := hdegeq
  have hbadXcard : badX.card ≤ 2 * dY * dX := by
    refine le_trans (Finset.card_biUnion_le) ?_
    refine le_trans (Finset.sum_le_sum hbadXP) ?_
    calc ∑ P ∈ PS, 2 * (Sfc P).natDegree * dX
        = ∑ P ∈ PS, 2 * dX * (Sfc P).natDegree :=
          Finset.sum_congr rfl fun P _ => by ring
      _ = 2 * dX * ∑ P ∈ PS, (Sfc P).natDegree := by rw [← Finset.mul_sum]
      _ ≤ 2 * dX * dY := Nat.mul_le_mul_left _ hdegSf_sum
      _ = 2 * dY * dX := by ring
  obtain ⟨x₀, hx₀mem⟩ : (univ \ badX).Nonempty := by
    rw [← Finset.card_pos, card_sdiff_of_subset (subset_univ _), card_univ]
    omega
  have hx₀ : ∀ P ∈ PS, (rr P).eval (C x₀) ≠ 0 := by
    intro P hP h0
    rw [Finset.mem_sdiff] at hx₀mem
    exact hx₀mem.2 (Finset.mem_biUnion.mpr ⟨P, hP, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, h0⟩⟩)
  -- ### 7. Fiber factorisations.
  have hgchoice : ∀ P : (F[X][X])[X], ∃ gs : Multiset (F[X][X]),
      (P ∈ PS → ((∀ g ∈ gs, Prime g) ∧ Associated gs.prod (fiberAt x₀ (Sfc P)))) := by
    intro P
    by_cases hP : P ∈ PS
    · obtain ⟨_, _, hirr, hdeg1, _⟩ := hSf P hP
      have hfib0 : fiberAt x₀ (Sfc P) ≠ 0 := fiberAt_ne_zero x₀ hirr hdeg1
      obtain ⟨gs, h1, h2⟩ := UniqueFactorizationMonoid.exists_prime_factors _ hfib0
      exact ⟨gs, fun _ => ⟨h1, h2⟩⟩
    · exact ⟨0, fun h => absurd h hP⟩
  choose gsc hgsc using hgchoice
  have hfibZ : ∀ P ∈ PS, IsHeightLE (fiberAt x₀ (Sfc P)) dZ := by
    intro P hP
    exact fiberAt_isHeightLE x₀ (Sfc P) (hSfZ P hP)
  have hfib0 : ∀ P ∈ PS, fiberAt x₀ (Sfc P) ≠ 0 := by
    intro P hP
    obtain ⟨_, _, hirr, hdeg1, _⟩ := hSf P hP
    exact fiberAt_ne_zero x₀ hirr hdeg1
  have hgs0 : ∀ P ∈ PS, (0 : F[X][X]) ∉ gsc P := by
    intro P hP h
    exact (((hgsc P hP).1) 0 h).ne_zero rfl
  -- The prime factors of the fiber divide it.
  have hgdvd : ∀ P ∈ PS, ∀ g ∈ gsc P, g ∣ fiberAt x₀ (Sfc P) := by
    intro P hP g hg
    obtain ⟨v, hv⟩ := (hgsc P hP).2
    exact dvd_trans (Multiset.dvd_prod hg) (Dvd.intro _ hv)
  -- ### 8. Labels and their count.
  set LBL : Finset ((F[X][X])[X] × F[X][X]) :=
    PS.biUnion (fun P =>
      ((gsc P).toFinset.filter (fun H => 1 ≤ H.natDegree)).image (fun H => (P, H)))
    with hLBLdef
  have hLBLcount : ∀ P ∈ PS,
      (((gsc P).toFinset.filter (fun H => 1 ≤ H.natDegree)).card) ≤ (Sfc P).natDegree := by
    intro P hP
    have h1 : (((gsc P).toFinset.filter (fun H => 1 ≤ H.natDegree)).card)
        ≤ ∑ g ∈ (gsc P).toFinset.filter (fun H => 1 ≤ H.natDegree), g.natDegree := by
      rw [Finset.card_eq_sum_ones]
      refine Finset.sum_le_sum fun g hg => ?_
      exact (Finset.mem_filter.mp hg).2
    have h2 : ∑ g ∈ (gsc P).toFinset.filter (fun H => 1 ≤ H.natDegree), g.natDegree
        ≤ ∑ g ∈ (gsc P).toFinset, g.natDegree :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun _ _ _ => Nat.zero_le _)
    have h3 : ∑ g ∈ (gsc P).toFinset, g.natDegree ≤ ((gsc P).map natDegree).sum :=
      toFinset_sum_le_multiset_sum _ _
    have h4 : ((gsc P).map natDegree).sum = (gsc P).prod.natDegree :=
      (natDegree_multiset_prod _ (hgs0 P hP)).symm
    have h5 : (gsc P).prod.natDegree = (fiberAt x₀ (Sfc P)).natDegree := by
      obtain ⟨v, hv⟩ := (hgsc P hP).2
      have hp0 : (gsc P).prod ≠ 0 := Multiset.prod_ne_zero (hgs0 P hP)
      rw [← hv, natDegree_mul hp0 v.ne_zero, natDegree_eq_zero_of_isUnit v.isUnit]
      ring
    have h6 : (fiberAt x₀ (Sfc P)).natDegree ≤ (Sfc P).natDegree :=
      fiberAt_natDegree_le x₀ _ le_rfl
    omega
  have hLBLcard : LBL.card ≤ dY := by
    refine le_trans (Finset.card_biUnion_le) ?_
    refine le_trans (Finset.sum_le_sum (fun P hP =>
      le_trans (Finset.card_image_le) (hLBLcount P hP))) hdegSf_sum
  -- Exact degree and height sums for the fiber labels.  These are the data needed
  -- for degree-weighted selection; applying `dY` and `dZ` to every label separately
  -- would lose an avoidable factor of `dY`.
  have hPdeg_sum : ∑ P ∈ PS, P.natDegree ≤ dY := by
    have hsub : PS ⊆ fs.toFinset := Finset.filter_subset _ _
    exact le_trans
      (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _))
      (le_trans (toFinset_sum_le_multiset_sum fs natDegree) hdegsum)
  have hPScard : PS.card ≤ dY := by
    rw [Finset.card_eq_sum_ones]
    exact le_trans (Finset.sum_le_sum fun P hP => (hPSmem P hP).2.2) hPdeg_sum
  have hHdeg_sum : ∀ P ∈ PS,
      ∑ H ∈ (gsc P).toFinset.filter (fun H => 1 ≤ H.natDegree), H.natDegree
        ≤ (Sfc P).natDegree := by
    intro P hP
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => Nat.zero_le _)) ?_
    refine le_trans (toFinset_sum_le_multiset_sum (gsc P) natDegree) ?_
    rw [← natDegree_multiset_prod (gsc P) (hgs0 P hP)]
    obtain ⟨v, hv⟩ := (hgsc P hP).2
    have hp0 : (gsc P).prod ≠ 0 := Multiset.prod_ne_zero (hgs0 P hP)
    have hproddeg : (gsc P).prod.natDegree = (fiberAt x₀ (Sfc P)).natDegree := by
      rw [← hv, natDegree_mul hp0 v.ne_zero, natDegree_eq_zero_of_isUnit v.isUnit]
      ring
    rw [hproddeg]
    exact fiberAt_natDegree_le x₀ _ le_rfl
  have hHheight_sum : ∀ P ∈ PS,
      ∑ H ∈ (gsc P).toFinset.filter (fun H => 1 ≤ H.natDegree),
        (swap F H).natDegree ≤ dZ := by
    intro P hP
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => Nat.zero_le _)) ?_
    refine le_trans (toFinset_sum_le_multiset_sum (gsc P) (fun H => (swap F H).natDegree)) ?_
    have hswap0 : (0 : F[X][X]) ∉ (gsc P).map (swap F) := by
      intro h
      obtain ⟨g, hg, hgg⟩ := Multiset.mem_map.mp h
      exact hgs0 P hP (swap_eq_zero_iff.mp hgg ▸ hg)
    rw [show ((gsc P).map (fun H => (swap F H).natDegree)).sum =
        (((gsc P).map (swap F)).map natDegree).sum by
          simp [Multiset.map_map]]
    rw [← natDegree_multiset_prod ((gsc P).map (swap F)) hswap0,
      ← map_multiset_prod (swap F) (gsc P)]
    obtain ⟨v, hv⟩ := (hgsc P hP).2
    have hp0 : (gsc P).prod ≠ 0 := Multiset.prod_ne_zero (hgs0 P hP)
    have hv0 : (↑v : F[X][X]) ≠ 0 := v.ne_zero
    have hswapdeg : (swap F (gsc P).prod).natDegree =
        (swap F (fiberAt x₀ (Sfc P))).natDegree := by
      rw [← hv, map_mul, natDegree_mul]
      · rw [natDegree_eq_zero_of_isUnit (v.isUnit.map (swap F))]
        ring
      · intro h
        exact hp0 (swap_eq_zero_iff.mp h)
      · intro h
        exact hv0 (swap_eq_zero_iff.mp h)
    rw [hswapdeg]
    exact isHeightLE_iff_natDegree_swap_le.mp (hfibZ P hP)
  have hLBLpairwise : (↑PS : Set ((F[X][X])[X])).PairwiseDisjoint (fun P =>
      ((gsc P).toFinset.filter (fun H => 1 ≤ H.natDegree)).image (fun H => (P, H))) := by
    intro P hP P' hP' hne
    change Disjoint _ _
    rw [Finset.disjoint_left]
    intro l hl hl'
    obtain ⟨H, _, rfl⟩ := Finset.mem_image.mp hl
    obtain ⟨H', _, hpair⟩ := Finset.mem_image.mp hl'
    exact hne (congrArg Prod.fst hpair.symm)
  let cap (k : ℕ) (l : (F[X][X])[X] × F[X][X]) : ℕ :=
    sharpFiberCapacity (k * pc ^ fe l.1) (Sfc l.1).natDegree dZ (pc ^ fe l.1)
      l.2.natDegree (swap F l.2).natDegree
  have hcapP : ∀ (k : ℕ) P, P ∈ PS →
      ∑ l ∈ ((gsc P).toFinset.filter (fun H => 1 ≤ H.natDegree)).image (fun H => (P, H)),
        cap k l ≤ sharpFactorCapacity k dZ P.natDegree := by
    intro k P hP
    rw [Finset.sum_image]
    · change ∑ H ∈ (gsc P).toFinset.filter (fun H => 1 ≤ H.natDegree),
        sharpFiberCapacity (k * pc ^ fe P) (Sfc P).natDegree dZ
          (pc ^ fe P) H.natDegree (swap F H).natDegree ≤
            sharpFactorCapacity k dZ P.natDegree
      refine le_trans (sum_sharpFiberCapacity_le _ _ _ (hHdeg_sum P hP)
        (hHheight_sum P hP)) ?_
      exact sharp_extractedCapacity_le (hSf P hP).2.2.2.2
    · intro H hH H' hH' heq
      exact congrArg Prod.snd heq
  have hLBLcapacity : ∀ k : ℕ,
      ∑ l ∈ LBL, cap k l ≤ 4 * k * (dY * dZ) + dY := by
    intro k
    rw [hLBLdef, Finset.sum_biUnion hLBLpairwise]
    refine le_trans (Finset.sum_le_sum (hcapP k)) ?_
    exact sum_sharpFactorCapacity_uniform_height_le PS natDegree hPdeg_sum
  -- ### 9. Bad parameters from degree-zero fiber factors and from ramification.
  set SbadFib : Finset F := PS.biUnion (fun P =>
    ((gsc P).toFinset.filter (fun g => g.natDegree = 0)).biUnion (fun g =>
      univ.filter (fun z : F => (g.coeff 0).eval z = 0))) with hSbadFibdef
  have hSbadFibP : ∀ P ∈ PS,
      (((gsc P).toFinset.filter (fun g => g.natDegree = 0)).biUnion (fun g =>
        univ.filter (fun z : F => (g.coeff 0).eval z = 0))).card ≤ dZ := by
    intro P hP
    refine le_trans (Finset.card_biUnion_le) ?_
    -- Each degree-zero prime factor contributes at most its `Z`-degree, and those
    -- `Z`-degrees sum to at most the fiber height.
    have hterm : ∀ g ∈ (gsc P).toFinset.filter (fun g => g.natDegree = 0),
        (univ.filter (fun z : F => (g.coeff 0).eval z = 0)).card
          ≤ (swap F g).natDegree := by
      intro g hg
      rw [Finset.mem_filter, Multiset.mem_toFinset] at hg
      have hg0 : g ≠ 0 := ((hgsc P hP).1 g hg.1).ne_zero
      have hc0 : g.coeff 0 ≠ 0 := by
        intro h
        apply hg0
        have := eq_C_of_natDegree_eq_zero hg.2
        rw [this, h, map_zero]
      refine le_trans (card_le_natDegree_of_eval_eq_zero hc0 _ ?_) ?_
      · intro z hz
        exact (Finset.mem_filter.mp hz).2
      · exact natDegree_swap_le_iff.mp le_rfl 0
    refine le_trans (Finset.sum_le_sum hterm) ?_
    -- Sum of swapped degrees over the factors is the swapped degree of the fiber.
    have hsum : ∑ g ∈ (gsc P).toFinset.filter (fun g => g.natDegree = 0),
        (swap F g).natDegree ≤ ((gsc P).map (fun g => (swap F g).natDegree)).sum := by
      refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _) (fun _ _ _ => Nat.zero_le _)) ?_
      exact toFinset_sum_le_multiset_sum _ _
    refine le_trans hsum ?_
    have hswap0 : (0 : F[X][X]) ∉ (gsc P).map (swap F) := by
      intro h
      obtain ⟨g, hg, hgg⟩ := Multiset.mem_map.mp h
      have hg0 : g = 0 := swap_eq_zero_iff.mp hgg
      rw [hg0] at hg
      exact hgs0 P hP hg
    have h1 : ((gsc P).map (fun g => (swap F g).natDegree)).sum
        = (((gsc P).map (swap F)).map natDegree).sum := by
      rw [Multiset.map_map]
      rfl
    have h2 : (((gsc P).map (swap F)).map natDegree).sum
        = (((gsc P).map (swap F)).prod).natDegree :=
      (natDegree_multiset_prod _ hswap0).symm
    have h3 : ((gsc P).map (swap F)).prod = swap F ((gsc P).prod) :=
      (map_multiset_prod (swap F) (gsc P)).symm
    have h4 : (swap F ((gsc P).prod)).natDegree
        ≤ (swap F (fiberAt x₀ (Sfc P))).natDegree := by
      obtain ⟨v, hv⟩ := (hgsc P hP).2
      have : swap F (fiberAt x₀ (Sfc P)) = swap F ((gsc P).prod) * swap F ↑v := by
        rw [← map_mul, hv]
      rw [this, natDegree_mul, natDegree_eq_zero_of_isUnit (v.isUnit.map _)]
      · omega
      · rw [Ne, swap_eq_zero_iff]
        exact Multiset.prod_ne_zero (hgs0 P hP)
      · rw [Ne, swap_eq_zero_iff]
        exact v.ne_zero
    have h5 : (swap F (fiberAt x₀ (Sfc P))).natDegree ≤ dZ :=
      isHeightLE_iff_natDegree_swap_le.mp (hfibZ P hP)
    rw [h3] at h2
    omega
  have hSbadFibcard : SbadFib.card ≤ dY * dZ := by
    refine le_trans (Finset.card_biUnion_le) ?_
    refine le_trans (Finset.sum_le_sum hSbadFibP) ?_
    calc ∑ _P ∈ PS, dZ = PS.card * dZ := by rw [Finset.sum_const, smul_eq_mul]
      _ ≤ dY * dZ := Nat.mul_le_mul_right _ hPScard
  set SbadDisc : Finset F := PS.biUnion (fun P =>
    univ.filter (fun z : F => ((rr P).eval (C x₀)).eval z = 0)) with hSbadDiscdef
  have hSbadDiscP : ∀ P ∈ PS,
      (univ.filter (fun z : F => ((rr P).eval (C x₀)).eval z = 0)).card
        ≤ 2 * (Sfc P).natDegree * dZ := by
    intro P hP
    obtain ⟨_, _, _, hdeg1, _⟩ := hSf P hP
    have hρ0 : (rr P).eval (C x₀) ≠ 0 := hx₀ P hP
    refine le_trans (card_le_natDegree_of_eval_eq_zero hρ0 _
      (fun z hz => (Finset.mem_filter.mp hz).2)) ?_
    have hht : IsHeightLE (rr P) ((derivative (Sfc P)).natDegree * dZ
        + (Sfc P).natDegree * dZ) :=
      isHeightLE_resultant (Sfc P) (derivative (Sfc P)) _ _ (hSfZ P hP) (hSfdZ P hP)
    have h1 : ((rr P).eval (C x₀)).natDegree ≤ (derivative (Sfc P)).natDegree * dZ
        + (Sfc P).natDegree * dZ := natDegree_eval_C_le hht x₀
    have hdlt : (derivative (Sfc P)).natDegree ≤ (Sfc P).natDegree :=
      le_of_lt (natDegree_derivative_lt (by omega))
    nlinarith
  have hSbadDisccard : SbadDisc.card ≤ 2 * (dY * dZ) := by
    refine le_trans (Finset.card_biUnion_le) ?_
    refine le_trans (Finset.sum_le_sum hSbadDiscP) ?_
    calc ∑ P ∈ PS, 2 * (Sfc P).natDegree * dZ
        = ∑ P ∈ PS, 2 * dZ * (Sfc P).natDegree :=
          Finset.sum_congr rfl fun P _ => by ring
      _ = 2 * dZ * ∑ P ∈ PS, (Sfc P).natDegree := by rw [← Finset.mul_sum]
      _ ≤ 2 * dZ * dY := Nat.mul_le_mul_left _ hdegSf_sum
      _ = 2 * (dY * dZ) := by ring
  -- ### 10. The surviving parameters and their labels.
  set S₂ : Finset F := S \ (SbadQ ∪ SbadFib ∪ SbadDisc) with hS₂def
  have hS₂card : dY * (e + 2) + cols * (4 * k * (dY * dZ) + dY) / slack
      < S₂.card := by
    have h1 : (SbadQ ∪ SbadFib ∪ SbadDisc).card
        ≤ dZ + dY * dZ + 2 * (dY * dZ) := by
      refine le_trans (Finset.card_union_le _ _) ?_
      have h2 := Finset.card_union_le SbadQ SbadFib
      omega
    have h3 : S.card - (SbadQ ∪ SbadFib ∪ SbadDisc).card ≤ S₂.card := by
      rw [hS₂def]
      have := Finset.le_card_sdiff (SbadQ ∪ SbadFib ∪ SbadDisc) S
      omega
    omega
  -- Basic membership facts for survivors.
  have hS₂S : S₂ ⊆ S := Finset.sdiff_subset
  have hS₂c₀ : ∀ z ∈ S₂, c₀.eval z ≠ 0 := by
    intro z hz h0
    rw [hS₂def, Finset.mem_sdiff] at hz
    exact hz.2 (Finset.mem_union_left _ (Finset.mem_union_left _
      (Finset.mem_filter.mpr ⟨hz.1, h0⟩)))
  have hPzmem : ∀ z ∈ S₂, Pz z ∈ PS := by
    intro z hz
    obtain ⟨hPfs, hdvd⟩ := hPz z (hS₂S hz) (hS₂c₀ z hz)
    rw [hPSdef, Finset.mem_filter, Multiset.mem_toFinset]
    refine ⟨hPfs, ?_⟩
    -- The specialisation is nonzero, so the divisibility forces positive degree.
    have hmapne : (Pz z).map (mapRingHom (evalRingHom z)) ≠ 0 := by
      intro h0
      apply hQzne z (hS₂c₀ z hz)
      have hsplit : Q.map (mapRingHom (evalRingHom z))
          = (fs.map (Polynomial.map (mapRingHom (evalRingHom z)))).prod
            * (↑u : (F[X][X])[X]).map (mapRingHom (evalRingHom z)) := by
        rw [← hu, Polynomial.map_mul]
        congr 1
        exact map_multiset_prod (mapRingHom (mapRingHom (evalRingHom z))) fs
      have hzero : (0 : (F[X])[X]) ∈ fs.map (Polynomial.map (mapRingHom (evalRingHom z))) := by
        rw [← h0]
        exact Multiset.mem_map_of_mem _ hPfs
      rw [hsplit, Multiset.prod_eq_zero hzero, zero_mul]
    have h1 : 1 ≤ ((Pz z).map (mapRingHom (evalRingHom z))).natDegree := by
      have h2 := natDegree_le_of_dvd hdvd hmapne
      rw [natDegree_X_sub_C] at h2
      omega
    exact le_trans h1 (natDegree_map_le)
  -- The branch root property for survivors.
  have hSfroot : ∀ z ∈ S₂,
      ((Sfc (Pz z)).map (mapRingHom (evalRingHom z))).eval
        ((p z) ^ (pc ^ fe (Pz z))) = 0 := by
    intro z hz
    obtain ⟨hPfs, hdvd⟩ := hPz z (hS₂S hz) (hS₂c₀ z hz)
    obtain ⟨hexp, _, _, _, _⟩ := hSf (Pz z) (hPzmem z hz)
    have hev : ((Pz z).map (mapRingHom (evalRingHom z))).eval (p z) = 0 := by
      have := dvd_iff_isRoot.mp hdvd
      exact this
    calc ((Sfc (Pz z)).map (mapRingHom (evalRingHom z))).eval ((p z) ^ (pc ^ fe (Pz z)))
        = ((expand _ (pc ^ fe (Pz z)) (Sfc (Pz z))).map
            (mapRingHom (evalRingHom z))).eval (p z) :=
          (eval_map_expand_eq _ _ _ _).symm
      _ = ((Pz z).map (mapRingHom (evalRingHom z))).eval (p z) := by rw [← hexp]
      _ = 0 := hev
  -- The fiber kill for survivors.
  have hfibkill : ∀ z ∈ S₂,
      spec z (((p z) ^ (pc ^ fe (Pz z))).eval x₀) (fiberAt x₀ (Sfc (Pz z))) = 0 := by
    intro z hz
    rw [spec_fiberAt, ← eval_eval_map_eq, hSfroot z hz, eval_zero]
  -- The unramifiedness for survivors.
  have hxine : ∀ z ∈ S₂,
      eval₂ (chi z x₀) (((p z) ^ (pc ^ fe (Pz z))).eval x₀)
        (derivative (Sfc (Pz z))) ≠ 0 := by
    intro z hz h0
    obtain ⟨_, _, _, hdeg1, _⟩ := hSf (Pz z) (hPzmem z hz)
    have hroot : eval₂ (chi z x₀) (((p z) ^ (pc ^ fe (Pz z))).eval x₀) (Sfc (Pz z)) = 0 := by
      rw [← eval_eval_map_eq, hSfroot z hz, eval_zero]
    have hres := ringHom_resultant_eq_zero_of_common_root (chi z x₀)
      (Sfc (Pz z)) (derivative (Sfc (Pz z))) le_rfl le_rfl (Or.inl (by omega))
      _ hroot h0
    have hzS₂ := hz
    rw [hS₂def, Finset.mem_sdiff] at hz
    apply hz.2
    refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨Pz z, hPzmem z hzS₂, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩)
    · rw [← chi_apply]
      exact hres
  -- The fiber-factor label for survivors.
  have hlabchoice : ∀ z : F, ∃ Hl : F[X][X], z ∈ S₂ →
      (Hl ∈ gsc (Pz z) ∧ 1 ≤ Hl.natDegree ∧
        spec z (((p z) ^ (pc ^ fe (Pz z))).eval x₀) Hl = 0) := by
    intro z
    by_cases hz : z ∈ S₂
    · set t := ((p z) ^ (pc ^ fe (Pz z))).eval x₀ with ht
      obtain ⟨v, hv⟩ := (hgsc (Pz z) (hPzmem z hz)).2
      have hkill := hfibkill z hz
      rw [← hv, map_mul] at hkill
      have hvne : spec z t (↑v : F[X][X]) ≠ 0 := by
        have := (v.isUnit.map (spec z t)).ne_zero
        exact this
      have hprodzero : spec z t ((gsc (Pz z)).prod) = 0 := by
        rcases mul_eq_zero.mp hkill with h | h
        · exact h
        · exact absurd h hvne
      rw [map_multiset_prod] at hprodzero
      have h0mem : (0 : F) ∈ (gsc (Pz z)).map (spec z t) :=
        Multiset.prod_eq_zero_iff.mp hprodzero
      obtain ⟨g, hg, hg0⟩ := Multiset.mem_map.mp h0mem
      refine ⟨g, fun _ => ⟨hg, ?_, hg0⟩⟩
      -- Positive degree, else `z` would be a bad parameter.
      apply Nat.one_le_iff_ne_zero.mpr
      intro hdeg0
      have hgC : g = C (g.coeff 0) := eq_C_of_natDegree_eq_zero hdeg0
      have heval : (g.coeff 0).eval z = 0 := by
        have : spec z t g = (g.coeff 0).eval z := by
          rw [hgC, spec_apply, eval₂_C]
          simp
        rw [← this, hg0]
      have hzS₂ := hz
      rw [hS₂def, Finset.mem_sdiff] at hz
      apply hz.2
      refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
      refine Finset.mem_biUnion.mpr ⟨Pz z, hPzmem z hzS₂, ?_⟩
      refine Finset.mem_biUnion.mpr ⟨g, ?_, ?_⟩
      · rw [Finset.mem_filter, Multiset.mem_toFinset]
        exact ⟨hg, hdeg0⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, heval⟩
    · exact ⟨0, fun h => absurd h hz⟩
  choose Hlab hHlab using hlabchoice
  -- ### 11. Degree-weighted factor selection.
  set lab : F → ((F[X][X])[X] × F[X][X]) := fun z => (Pz z, Hlab z) with hlabdef
  have hmapsto : ∀ z ∈ S₂, lab z ∈ LBL := by
    intro z hz
    obtain ⟨hg, hdeg, _⟩ := hHlab z hz
    refine Finset.mem_biUnion.mpr ⟨Pz z, hPzmem z hz, ?_⟩
    refine Finset.mem_image.mpr ⟨Hlab z, ?_, rfl⟩
    rw [Finset.mem_filter, Multiset.mem_toFinset]
    exact ⟨hg, hdeg⟩
  have hthresholdSum :
      (∑ l ∈ LBL, incidenceThreshold cols slack e (cap k l)) < S₂.card := by
    refine lt_of_le_of_lt (sum_incidenceThreshold_le LBL (cap k) cols slack e) ?_
    refine lt_of_le_of_lt (Nat.add_le_add
      (Nat.mul_le_mul_right (e + 2) hLBLcard)
      (Nat.div_le_div_right (Nat.mul_le_mul_left cols (hLBLcapacity k)))) hS₂card
  obtain ⟨labSel, hlabmem, hfibercard, hfiberinc⟩ :=
    exists_weighted_incidence_bucket S₂ lab LBL (cap k)
      (fun l => incidenceThreshold cols slack e (cap k l)) hmapsto hslack
      (fun l _ => incidenceThreshold_min cols slack e (cap k l))
      (fun l _ => incidenceThreshold_incidence (show 0 < slack by omega)) hthresholdSum
  set Psel := labSel.1 with hPsel
  set Hsel := labSel.2 with hHsel
  set S' : Finset F := S₂.filter (fun z => lab z = labSel) with hS'def
  have hS'S₂ : S' ⊆ S₂ := Finset.filter_subset _ _
  have hS'P : ∀ z ∈ S', Pz z = Psel ∧ Hlab z = Hsel := by
    intro z hz
    have := (Finset.mem_filter.mp hz).2
    rw [hlabdef] at this
    exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
  -- The selected label's data.
  have hPselPS : Psel ∈ PS := by
    rw [hLBLdef] at hlabmem
    obtain ⟨P, hP, hPl⟩ := Finset.mem_biUnion.mp hlabmem
    obtain ⟨Hf, hHfmem, hHf⟩ := Finset.mem_image.mp hPl
    have h1 : P = Psel := congrArg Prod.fst hHf
    rw [← h1]
    exact hP
  have hHselmem : Hsel ∈ gsc Psel ∧ 1 ≤ Hsel.natDegree := by
    rw [hLBLdef] at hlabmem
    obtain ⟨P, hP, hPl⟩ := Finset.mem_biUnion.mp hlabmem
    obtain ⟨Hf, hHfmem, hHf⟩ := Finset.mem_image.mp hPl
    rw [Finset.mem_filter, Multiset.mem_toFinset] at hHfmem
    have h1 : P = Psel := congrArg Prod.fst hHf
    have h2 : Hf = Hsel := congrArg Prod.snd hHf
    rw [← h1, ← h2]
    exact hHfmem
  obtain ⟨hexpSel, hderSel, hirrSel, hdeg1Sel, hdegeqSel⟩ := hSf Psel hPselPS
  -- ### 12. Package the output.
  refine ⟨S', pc ^ fe Psel, (Sfc Psel).natDegree, Sfc Psel, x₀, Hsel,
    Finset.Subset.trans hS'S₂ hS₂S, ?_, ⟨fe Psel, rfl⟩, hdeg1Sel, le_rfl, ?_, hSfZ Psel hPselPS,
    ((hgsc Psel hPselPS).1 Hsel hHselmem.1).irreducible, hHselmem.2, ?_, ?_, ?_, ?_, ?_⟩
  · -- bucket size
    have : e + 1 < (S₂.filter (fun z => lab z = labSel)).card := hfibercard
    simpa [hS'def] using this
  · -- degree product bound
    rw [hdegeqSel]
    exact hPdeg_le Psel (hPSmem Psel hPselPS).1
  · -- `Hsel` degree bound
    have hdvd := hgdvd Psel hPselPS Hsel hHselmem.1
    refine le_trans (natDegree_le_of_dvd hdvd (hfib0 Psel hPselPS)) ?_
    exact fiberAt_natDegree_le x₀ _ le_rfl
  · -- `Hsel` height bound
    exact isHeightLE_of_dvd (hgdvd Psel hPselPS Hsel hHselmem.1) (hfib0 Psel hPselPS)
      (hfibZ Psel hPselPS)
  · -- exact `Hsel` height
    exact isHeightLE_iff_natDegree_swap_le.mpr le_rfl
  · -- selected label's exact incidence capacity
    simpa [cap, hPsel, hHsel, hS'def] using hfiberinc
  · -- the per-parameter facts
    intro z hz
    obtain ⟨hPzz, hHz⟩ := hS'P z hz
    have hz₂ := hS'S₂ hz
    refine ⟨?_, ?_, ?_⟩
    · have := hSfroot z hz₂
      rwa [hPzz] at this
    · have := hxine z hz₂
      rwa [hPzz] at this
    · have := (hHlab z hz₂).2.2
      rwa [hPzz, hHz] at this

end Selection

end JBAgreement
