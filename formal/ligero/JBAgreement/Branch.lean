import JBAgreement.ColumnBound
import JBAgreement.FactorSelection
import JBAgreement.Main
import JBAgreement.SharpClearedJet

/-!
# §3: the branch argument

This file assembles the finite-jet argument for a single branch.  The input is a
separable branch `R₀` (recentered at a good slice `x₀`, over `A = F[Z][T]` with the
free initial root `T`), an irreducible fiber factor `H`, and the proximates it
explains; the output is a set of more than `k` *good coordinates* at which every
proximate simultaneously matches the received word.

Two refinements over the naive assembly make the statement general enough to cover the
inseparable case (§6.6) with no separability hypothesis anywhere:

* **The jet order `κ` and the code dimension `k` are decoupled.**  For an inseparable
  factor the machinery runs on the separable core with proximates `q_z = p_z^{p^f}`;
  `κ = k·p^f` is a conservative truncation order, while the incidence count only needs
  `k` good coordinates because final interpolation happens *after* untwisting each
  coordinate value.  Quantitatively this supports the `η³` bound: the column
  bound is `(2κ+1)·deg_Y(S)·D_Z ≈ 2k·deg_Y(P)·D_Z`, with the `p^f` cancelling.

* **The word value is `w₀ + Z^M·w₁`.**  In the separable case `M = 1`; for the
  inseparable case `M = p^f` and `w_i = u_i^{p^f}`, which is how the affine structure
  survives the Frobenius twist.

* **The fiber factor `H` is an input**, not `R₀`'s own fiber: the fiber of an
  irreducible branch need not be irreducible, so the caller selects (by pigeonhole) an
  irreducible factor of it vanishing on the bucket.  The full fiber is still what the
  cleared-jet specialisation kills, and that is derived from `hroot` internally.

The argument: `exists_sharpClearedJet` (the Newton-skeleton estimate) →
`clearedJet_spec_exp` (the
specialised jet is the proximate) → row bound `n - e` and resultant column bound →
`card_exceptional_ge` → `dvd_of_resultant_eq_zero` at each exceptional coordinate.
-/

namespace JBAgreement

open Polynomial Finset

section Assembly

variable {F : Type*} [Field F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The two size systems on `A = F[Z][T]` used simultaneously: the `Z`-height and the
`T`-degree.  Indexing them by `Bool` lets one application of `exists_sharpClearedJet` deliver
both bounds for the *same* cleared jet. -/
noncomputable def sizePair (F : Type*) [Field F] : Bool → SizeSystem (F[X][X]) :=
  fun b => cond b (degreeSizeSystem (F[X])) (heightSizeSystem F)

/-- The twisted coordinate value `w₀ x + Z^M · w₁ x`, as an element of `A = F[Z][T]`. -/
noncomputable def wordVal (M : ℕ) (a b : F) : F[X][X] :=
  C (Polynomial.C a + Polynomial.X ^ M * Polynomial.C b)

/-- A scalar of `F`, as an element of `A = F[Z][T]`. -/
noncomputable def scal (a : F) : F[X][X] := C (Polynomial.C a)

@[simp] lemma spec_scal (z t a : F) : spec z t (scal a) = a := by
  simp [spec, scal]

@[simp] lemma spec_wordVal (M : ℕ) (z t a b : F) :
    spec z t (wordVal M a b) = a + z ^ M * b := by
  rw [wordVal, spec_apply, eval₂_C]
  simp
  ring

lemma natDegree_scal_le (a : F) : (scal a).natDegree ≤ 0 := le_of_eq (natDegree_C _)

lemma natDegree_wordVal_le (M : ℕ) (a b : F) : (wordVal M a b).natDegree ≤ 0 :=
  le_of_eq (natDegree_C _)

lemma isHeightLE_scal (a : F) : IsHeightLE (scal a) 0 := by
  intro i
  rw [scal, coeff_C]
  split_ifs <;> simp

lemma isHeightLE_wordVal (M : ℕ) (a b : F) : IsHeightLE (wordVal M a b) M := by
  intro i
  rw [wordVal, coeff_C]
  split_ifs with h
  · refine le_trans (natDegree_add_le _ _) (max_le (by simp) ?_)
    refine le_trans (natDegree_mul_le) ?_
    simp
  · simp

lemma isHeightLE_X : IsHeightLE (X : F[X][X]) 0 := by
  intro i
  rw [coeff_X]
  split_ifs <;> simp

lemma natDegree_X_le_one : (X : F[X][X]).natDegree ≤ 1 := natDegree_X_le

/-- Irreducible polynomials of positive degree over `F[Z]` are primitive. -/
theorem isPrimitive_of_irreducible {H : F[X][X]} (hirr : Irreducible H)
    (hdeg : 1 ≤ H.natDegree) : H.IsPrimitive := by
  intro c hc
  obtain ⟨e, he⟩ := hc
  rcases hirr.isUnit_or_isUnit he with hu | hu
  · exact isUnit_C.mp hu
  · exfalso
    have hH0 : H ≠ 0 := hirr.ne_zero
    have hC0 : (C c : F[X][X]) ≠ 0 := fun h => hH0 (by rw [he, h, zero_mul])
    have he0 : e ≠ 0 := fun h => hH0 (by rw [he, h, mul_zero])
    have : H.natDegree = 0 := by
      rw [he, natDegree_mul hC0 he0, natDegree_C, natDegree_eq_zero_of_isUnit hu]
    omega

/-- The incidence/divisibility endgame, abstracted from the construction of the
coordinate polynomials.  Its capacity is the exact resultant rectangle
`gT * hH + dH * gZ`. -/
theorem exists_goodCoords_of_coordinatePolynomials [Fintype F] [DecidableEq F]
    (dom : ι → F) (w₀ w₁ : ι → F) (k e M E : ℕ)
    (x₀ : F) (S : Finset F) (q : F → F[X])
    (hprox : ∀ z ∈ S,
      (disagree (fun x => w₀ x + z ^ M * w₁ x) (RSeval dom (q z))).card ≤ e)
    (ξ₀ : F[X][X])
    (hxi : ∀ z ∈ S, spec z ((q z).eval x₀) ξ₀ ≠ 0)
    (H : F[X][X]) (hH0 : ∀ z ∈ S, spec z ((q z).eval x₀) H = 0)
    (hirrH : Irreducible H) (hHdeg : 1 ≤ H.natDegree)
    (dH hH gT gZ B : ℕ) (hHT : H.natDegree ≤ dH) (hHZ : IsHeightLE H hH)
    (g : ι → F[X][X])
    (hspec : ∀ z ∈ S, ∀ x : ι,
      spec z ((q z).eval x₀) (g x) =
        spec z ((q z).eval x₀) ξ₀ ^ E *
          ((q z).eval (dom x) - (w₀ x + z ^ M * w₁ x)))
    (hgT : ∀ x, (g x).natDegree ≤ gT) (hgZ : ∀ x, IsHeightLE (g x) gZ)
    (hcap : gT * hH + dH * gZ ≤ B)
    (hcount : (Fintype.card ι - k) * B <
      (Fintype.card ι - e - k) * S.card) :
    ∃ I : Finset ι, k < I.card ∧ ∀ x ∈ I, ∀ z ∈ S,
      (q z).eval (dom x) = w₀ x + z ^ M * w₁ x := by
  have hprim : H.IsPrimitive := isPrimitive_of_irreducible hirrH hHdeg
  set P : ι → F → Prop := fun x z => ∃ t : F,
    eval₂ (evalRingHom z) t H = 0 ∧ eval₂ (evalRingHom z) t (g x) = 0 with hP
  have hrow : ∀ z ∈ S, Fintype.card ι - e ≤ (univ.filter fun x => P x z).card := by
    intro z hz
    have hsub : univ \ disagree (fun x => w₀ x + z ^ M * w₁ x) (RSeval dom (q z))
        ⊆ univ.filter fun x => P x z := by
      intro x hx
      rw [mem_sdiff, mem_disagree] at hx
      have hagree : (q z).eval (dom x) = w₀ x + z ^ M * w₁ x := by
        have h := not_not.mp hx.2
        simpa [RSeval] using h.symm
      refine mem_filter.mpr ⟨mem_univ _, ⟨(q z).eval x₀, ?_, ?_⟩⟩
      · simpa [spec] using hH0 z hz
      · have h := hspec z hz x
        rw [hagree, sub_self, mul_zero] at h
        simpa [spec] using h
    have hcard : (univ \ disagree (fun x => w₀ x + z ^ M * w₁ x) (RSeval dom (q z))).card
        = Fintype.card ι
          - (disagree (fun x => w₀ x + z ^ M * w₁ x) (RSeval dom (q z))).card := by
      rw [card_sdiff_of_subset (subset_univ _), card_univ]
    have hle := card_le_card hsub
    have hpx := hprox z hz
    omega
  set I : Finset ι := univ.filter fun x =>
    resultant H (g x) H.natDegree (g x).natDegree = 0 with hI
  have hcol : ∀ x ∉ I, (S.filter fun z => P x z).card ≤ B := by
    intro x hx
    have hres : resultant H (g x) H.natDegree (g x).natDegree ≠ 0 := by
      simpa [hI] using hx
    have hbad := card_badSpecializations_le_of_height H (g x) (le_refl _) (le_refl _)
      hHZ (hgZ x) (Or.inl (by omega)) hres
    have hsub : (S.filter fun z => P x z) ⊆ badSpecializations H (g x) := by
      intro z hz
      rw [mem_filter] at hz
      simpa [badSpecializations] using hz.2
    have h1 : (g x).natDegree * hH ≤ gT * hH := Nat.mul_le_mul_right _ (hgT x)
    have h2 : H.natDegree * gZ ≤ dH * gZ := Nat.mul_le_mul_right _ hHT
    exact le_trans (le_trans (card_le_card hsub) hbad)
      (le_trans (Nat.add_le_add h1 h2) hcap)
  have hka : k ≤ Fintype.card ι - e := by
    apply Nat.le_of_not_lt
    intro hcon
    have h0 : Fintype.card ι - e - k = 0 := by omega
    rw [h0, zero_mul] at hcount
    exact absurd hcount (Nat.not_lt_zero _)
  have hIcard : k < I.card :=
    card_exceptional_ge_rect S I P (Fintype.card ι - e) k B
      hka (Nat.sub_le _ _) hrow hcol hcount
  refine ⟨I, hIcard, ?_⟩
  intro x hx z hz
  have hres : resultant H (g x) H.natDegree (g x).natDegree = 0 := by
    simpa [hI] using hx
  obtain ⟨c, hc⟩ := dvd_of_resultant_eq_zero H (g x) hprim hirrH hHdeg hres
  have hzero : spec z ((q z).eval x₀) (g x) = 0 := by
    rw [hc, map_mul, hH0 z hz, zero_mul]
  have h := hspec z hz x
  rw [hzero] at h
  have hne : spec z ((q z).eval x₀) ξ₀ ^ E ≠ 0 := pow_ne_zero _ (hxi z hz)
  have hsub0 := (mul_eq_zero.mp h.symm).resolve_left hne
  exact sub_eq_zero.mp hsub0

/-- **Sharp branch argument.**  The derivative-sensitive Newton ledger permits the
common clearing exponent `2κ`.  Consequently the coordinate polynomial has bidegree
at most `(2κ dY, 2κ dZ + M)`, and the exact resultant rectangle is
`sharpFiberCapacity κ dY dZ M dH hH`. -/
theorem exists_goodCoords_sharp [Fintype F] [DecidableEq F]
    (dom : ι → F) (w₀ w₁ : ι → F) (k κ e M : ℕ) (hκ : 1 ≤ κ)
    (x₀ : F) (R₀ : (F[X][X])[X][X]) (dY dZ : ℕ)
    (hdY : R₀.natDegree ≤ dY) (hdYpos : 1 ≤ dY)
    (hRT : ∀ j i, ((R₀.coeff j).coeff i).natDegree ≤ 0)
    (hRZ : ∀ j i, IsHeightLE ((R₀.coeff j).coeff i) dZ)
    (S : Finset F) (q : F → F[X])
    (hqdeg : ∀ z ∈ S, (q z).natDegree ≤ κ)
    (hprox : ∀ z ∈ S,
      (disagree (fun x => w₀ x + z ^ M * w₁ x) (RSeval dom (q z))).card ≤ e)
    (hroot : ∀ z ∈ S,
      (R₀.map (mapRingHom (spec z ((q z).eval x₀)))).eval ((q z).comp (X + C x₀)) = 0)
    (hxi : ∀ z ∈ S, spec z ((q z).eval x₀) (xi R₀ (X : F[X][X])) ≠ 0)
    (H : F[X][X]) (hH0 : ∀ z ∈ S, spec z ((q z).eval x₀) H = 0)
    (hirrH : Irreducible H) (hHdeg : 1 ≤ H.natDegree)
    (dH hH : ℕ) (hHT : H.natDegree ≤ dH) (hHZ : IsHeightLE H hH)
    (hcount : (Fintype.card ι - k) *
        sharpFiberCapacity κ dY dZ M dH hH
      < (Fintype.card ι - e - k) * S.card) :
    ∃ I : Finset ι, k < I.card ∧ ∀ x ∈ I, ∀ z ∈ S,
      (q z).eval (dom x) = w₀ x + z ^ M * w₁ x := by
  set a₀ : F[X][X] := X with ha₀
  set ξ₀ : F[X][X] := xi R₀ a₀ with hξ₀
  have hSpos : 0 < S.card := by
    apply Nat.pos_of_ne_zero
    intro h
    simp [h] at hcount
  obtain ⟨z₀, hz₀⟩ := Finset.card_pos.mp hSpos
  have hξ0 : ξ₀ ≠ 0 := by
    intro h
    refine hxi z₀ hz₀ ?_
    show spec z₀ ((q z₀).eval x₀) ξ₀ = 0
    rw [h, map_zero]
  have hξT : ξ₀.natDegree ≤ dY - 1 := by
    have h1 : ξ₀.natDegree ≤ 0 + (dY - 1) * 1 :=
      size_xi_refined (degreeSizeSystem (F[X])) R₀ a₀ hdY hRT natDegree_X_le_one
    omega
  have hξZ : IsHeightLE ξ₀ dZ := by
    have h1 : IsHeightLE ξ₀ (dZ + (dY - 1) * 0) :=
      size_xi_refined (heightSizeSystem F) R₀ a₀ hdY hRZ isHeightLE_X
    exact fun j => (h1 j).trans (by omega)
  have hHzero : ∀ z ∈ S, spec z ((q z).eval x₀) (jetConst R₀ a₀) = 0 := by
    intro z hz
    have hc0 : spec z ((q z).eval x₀) a₀ = ((q z).comp (X + C x₀)).coeff 0 := by
      rw [coeff_zero_eq_eval_zero, eval_comp]
      simp [ha₀]
    have h2 : jetConst (R₀.map (mapRingHom (spec z ((q z).eval x₀))))
        (spec z ((q z).eval x₀) a₀) = 0 := by
      unfold jetConst
      rw [hc0, ← coeff_zero_eval, hroot z hz, coeff_zero]
    rw [← jetConst_map (spec z ((q z).eval x₀)) R₀ a₀]
    exact h2
  obtain ⟨γ, hγdeg, hγ0, hγsize, hγjet⟩ :=
    exists_sharpClearedJet (Idx := Bool) (sizePair F) R₀ a₀ dY κ
      (fun b => cond b 0 dZ) (fun b => cond b 1 0)
      (fun b => cond b (dY - 1) dZ) (fun b => cond b dY dZ) hdY
      (fun b => by cases b <;> [exact hRZ; exact hRT])
      (fun b => by cases b <;> [exact isHeightLE_X; exact natDegree_X_le_one])
      (fun b => by cases b <;> [exact hξZ; exact hξT])
      (fun b => by cases b <;> simp)
      (fun b => by cases b <;> simp)
      (fun b => by
        cases b
        · simp
        · simp only [cond_true]
          calc
            2 * κ * (dY - 1) + 1 ≤ 2 * κ * (dY - 1) + 2 * κ := by omega
            _ = 2 * κ * ((dY - 1) + 1) := by ring
            _ = 2 * κ * dY := by rw [Nat.sub_add_cancel hdYpos])
      hξ0
  have hγZ : ∀ i, IsHeightLE (γ.coeff i) (2 * κ * dZ) := by
    intro i
    have h := hγsize false i
    change IsHeightLE (γ.coeff i) (2 * κ * dZ) at h
    exact h
  have hγT : ∀ i, (γ.coeff i).natDegree ≤ 2 * κ * dY := by
    intro i
    have h := hγsize true i
    change (γ.coeff i).natDegree ≤ 2 * κ * dY at h
    exact h
  set g : ι → F[X][X] := fun x =>
    ghatExp γ ξ₀ (2 * κ) (scal (dom x - x₀)) (wordVal M (w₀ x) (w₁ x)) with hg
  have hgT : ∀ x, (g x).natDegree ≤ 2 * κ * dY := by
    intro x
    refine size_ghat_exp (degreeSizeSystem (F[X])) hγdeg hγT
      (natDegree_scal_le _) hξT (natDegree_wordVal_le _ _ _) ?_ ?_
    · simp
    · have hm : (2 * κ) * (dY - 1) ≤ (2 * κ) * dY :=
        Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      simpa using hm
  have hgZ : ∀ x, IsHeightLE (g x) (2 * κ * dZ + M) := by
    intro x
    refine size_ghat_exp (heightSizeSystem F) hγdeg hγZ
      (isHeightLE_scal _) hξZ (isHeightLE_wordVal _ _ _) ?_ ?_
    · simp
    · exact le_rfl
  have hspec : ∀ z ∈ S, ∀ x : ι,
      spec z ((q z).eval x₀) (g x)
        = spec z ((q z).eval x₀) ξ₀ ^ (2 * κ) *
            ((q z).eval (dom x) - (w₀ x + z ^ M * w₁ x)) := by
    intro z hz x
    set φ := spec z ((q z).eval x₀) with hφ
    set π : F[X] := (q z).comp (X + C x₀) with hπ
    have hroot' : (R₀.map (mapRingHom φ)).eval π = 0 := by
      rw [hφ, hπ]
      exact hroot z hz
    have hπ0 : π.coeff 0 = φ a₀ := by
      rw [hπ, coeff_zero_eq_eval_zero, eval_comp]
      simp [ha₀, hφ]
    have hqdeg' : ((X : F[X]) + C x₀).natDegree ≤ 1 :=
      le_trans (natDegree_add_le _ _) (by simp)
    have hπdeg : π.natDegree ≤ κ := by
      rw [hπ]
      refine le_trans natDegree_comp_le ?_
      calc
        (q z).natDegree * ((X : F[X]) + C x₀).natDegree
            ≤ κ * 1 := Nat.mul_le_mul (hqdeg z hz) hqdeg'
        _ = κ := by ring
    have hφH : φ (jetConst R₀ a₀) = 0 := by rw [hφ]; exact hHzero z hz
    have hφξ : φ ξ₀ ≠ 0 := hxi z hz
    have hkey := clearedJet_spec_exp R₀ a₀ dY κ (2 * κ) hdY γ hγdeg hγ0 hγjet
      φ hφH hφξ π hπdeg hπ0 hroot'
    have heval : φ (γ.eval (scal (dom x - x₀))) =
        φ ξ₀ ^ (2 * κ) * (q z).eval (dom x) := by
      have h2 : φ (γ.eval (scal (dom x - x₀)))
          = (γ.map φ).eval (φ (scal (dom x - x₀))) :=
        ((eval_map φ (φ (scal (dom x - x₀)))).trans
          (eval₂_hom φ (scal (dom x - x₀)))).symm
      rw [h2, ← hkey, hφ, spec_scal, ← hφ, eval_mul, eval_C, hπ, eval_comp]
      simp [← hξ₀]
    have hgx : g x = γ.eval (scal (dom x - x₀))
        - ξ₀ ^ (2 * κ) * wordVal M (w₀ x) (w₁ x) := by rfl
    rw [hgx, map_sub, heval, map_mul, map_pow, hφ, spec_wordVal]
    ring
  refine exists_goodCoords_of_coordinatePolynomials dom w₀ w₁ k e M (2 * κ)
    x₀ S q hprox ξ₀ hxi H hH0 hirrH hHdeg dH hH
    (2 * κ * dY) (2 * κ * dZ + M)
    (sharpFiberCapacity κ dY dZ M dH hH) hHT hHZ g hspec hgT hgZ ?_ hcount
  simp [sharpFiberCapacity]

end Assembly

end JBAgreement
