import JBAgreement.ScalarExtension
import JBAgreement.GS
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Data.Nat.Cast.Order.Field

/-!
# The unconditional theorem

`correlatedAgreement_unconditional_sharp_noFieldSize` constructs the
Guruswami–Sudan interpolant, uses the derivative-sensitive ledger, and selects the
good slice after finite scalar extension.  Its only hypotheses are the words, the
per-parameter proximity, and explicitly checkable numeric conditions on
`(m, D, dY, dZ)`:

* `hkdY`, `hcnt` — interpolation at degree cap `k - 1` is solvable (more
  coefficients than constraints);
* `hroot` — the agreement overwhelms the weighted degree (`D < m·(n-e)`);
* `hslack`, `hS` — positivity of the agreement slack and the weighted threshold.

The proof constructs a large enough extension internally and descends its affine
bucket, so there is no base-field size condition.  No real-valued relaxation is
defined in this module.
-/

namespace JBAgreement

open Polynomial Finset

section Unconditional

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **The Guruswami–Sudan package, for a given family of proximates.**  Here `k`
is the code dimension, so the interpolant is weighted by the degree cap `k - 1`.
It derives the root property at every parameter of `S` and is shared by the
unconditional correlated agreement theorem and the strong mutual variant. -/
theorem exists_gs_for
    (dom : ι → F) (hdom : Function.Injective dom) (u₀ u₁ : ι → F) (k e : ℕ)
    (S : Finset F) (p : F → F[X])
    (hpdeg : ∀ z ∈ S, (p z).natDegree < k)
    (hprox : ∀ z ∈ S,
      (disagree (fun x => u₀ x + z * u₁ x) (RSeval dom (p z))).card ≤ e)
    (m D dY dZ : ℕ)
    (hkdY : (k - 1) * dY ≤ D)
    (hcnt : Fintype.card ι * (m * (m + 1)) * (dZ + dY + 1)
        < ((dY + 1) * (2 * (D + 1)) - (k - 1) * (dY * (dY + 1))) * (dZ + 1))
    (hroot : D < m * (Fintype.card ι - e)) :
    ∃ Q : (F[X][X])[X], Q ≠ 0 ∧ Q.natDegree ≤ dY ∧
      (∀ j, (Q.coeff j).natDegree ≤ D) ∧
      (∀ j i, ((Q.coeff j).coeff i).natDegree ≤ dZ) ∧
      ∀ z ∈ S, ((Q.map (mapRingHom (evalRingHom z))).eval (p z)) = 0 := by
  obtain ⟨Q, hQ0, hQY, hQb, hQZ, hQvan⟩ :=
    exists_interpolant dom u₀ u₁ (k - 1) m D dY dZ hkdY hcnt
  refine ⟨Q, hQ0, hQY, fun j => le_trans (hQb j) (Nat.sub_le _ _),
    fun j => hQZ j, ?_⟩
  intro z hz
  set T : Finset F :=
    (univ \ disagree (fun x => u₀ x + z * u₁ x) (RSeval dom (p z))).image dom
    with hT
  have hTcard : Fintype.card ι - e ≤ T.card := by
    rw [hT, Finset.card_image_of_injective _ hdom,
      card_sdiff_of_subset (subset_univ _), card_univ]
    have := hprox z hz
    omega
  refine eval_map_eq_zero_of_agreements (m := m) (T := T) hQY hkdY hQb
    (Nat.le_pred_of_lt (hpdeg z hz)) ?_ ?_
  · intro x₀ hx₀
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hx₀
    rw [mem_sdiff, mem_disagree, not_not] at hx
    have hagree : (p z).eval (dom x) = u₀ x + z * u₁ x := by
      simpa [RSeval] using hx.2.symm
    have hV := vanishesTo_map (evalRingHom z) (hQvan x)
    rw [show (evalRingHom z) (C (dom x)) = dom x by simp] at hV
    rw [show (evalRingHom z) (wordZ u₀ u₁ x) = (p z).eval (dom x) by
      show (wordZ u₀ u₁ x).eval z = _
      rw [wordZ_eval, hagree]] at hV
    exact hV
  · calc D < m * (Fintype.card ι - e) := hroot
      _ ≤ m * T.card := Nat.mul_le_mul_left _ hTcard

/-- **Unconditional sharp theorem with no field-size hypothesis.**  Guruswami–Sudan
is constructed over the base field, while only the good-slice/branch stage is run in
a sufficiently large finite scalar extension and then descended. -/
theorem correlatedAgreement_unconditional_sharp_noFieldSize
    (dom : ι → F) (hdom : Function.Injective dom) (u₀ u₁ : ι → F) (k e : ℕ)
    (hk : 1 ≤ k) (S : Finset F)
    (hclose : ∀ z ∈ S, ∃ p : F[X], p.natDegree < k ∧
      (disagree (fun x => u₀ x + z * u₁ x) (RSeval dom p)).card ≤ e)
    (m D dY dZ : ℕ)
    (hkdY : (k - 1) * dY ≤ D)
    (hcnt : Fintype.card ι * (m * (m + 1)) * (dZ + dY + 1)
        < ((dY + 1) * (2 * (D + 1)) - (k - 1) * (dY * (dY + 1))) * (dZ + 1))
    (hroot : D < m * (Fintype.card ι - e))
    (hslack : 1 ≤ Fintype.card ι - e - (k))
    (hS : dY * (e + 2) +
        (Fintype.card ι - (k)) * (4 * (k) * (dY * dZ) + dY) /
          (Fintype.card ι - e - (k)) + dZ + 3 * (dY * dZ) < S.card) :
    ∃ v₀ v₁ : F[X], v₀.natDegree < k ∧ v₁.natDegree < k ∧
      (pairDisagree u₀ u₁ (RSeval dom v₀) (RSeval dom v₁)).card ≤ e ∧
      (∀ S₂ : Finset F, e + 1 < S₂.card →
        (∀ z ∈ S₂, (disagree (fun x => u₀ x + z * u₁ x)
            (fun x => (v₀ + C z * v₁).eval (dom x))).card ≤ e) →
        (S₂.filter fun z =>
          lineAgree u₀ u₁ (RSeval dom v₀) (RSeval dom v₁) z
            ≠ corrAgree u₀ u₁ (RSeval dom v₀) (RSeval dom v₁)).card ≤ e) := by
  classical
  have hchoice : ∀ z : F, ∃ p : F[X], z ∈ S → (p.natDegree < k ∧
      (disagree (fun x => u₀ x + z * u₁ x) (RSeval dom p)).card ≤ e) := by
    intro z
    by_cases hz : z ∈ S
    · obtain ⟨p, hp⟩ := hclose z hz
      exact ⟨p, fun _ => hp⟩
    · exact ⟨0, fun h => absurd h hz⟩
  choose p hp using hchoice
  obtain ⟨Q, hQ0, hQY, hQX, hQZ, hGS⟩ :=
    exists_gs_for dom hdom u₀ u₁ k e S p (fun z hz => (hp z hz).1)
      (fun z hz => (hp z hz).2) m D dY dZ hkdY hcnt hroot
  exact correlatedAgreement_of_GS_sharp_noFieldSize dom hdom u₀ u₁ k e hk S p
    (fun z hz => (hp z hz).1) (fun z hz => (hp z hz).2)
    Q hQ0 D dY dZ hQY hQX hQZ hGS hslack hS

end Unconditional

/-! ### Johnson-regime feasibility -/

section Johnson

set_option maxHeartbeats 1600000 in
/-- **Feasibility of the Guruswami–Sudan parameters in the Johnson regime.**

Under the (√-free, squared) Johnson condition `k·n ≤ (t - 4ηn)²` with
`t ≥ 4ηn`, `ηn ≥ 1`, `η ≤ 1/4`, the parameters
`m = ⌈t/(2ηn)⌉`, `D = m·t - 1`, `dY = ⌊D/k⌋`, `dZ = (m+1)(dY+1)` satisfy every
numeric hypothesis of the interpolation and root steps, with the `η`-sized bounds
`dY ≤ 3n/(4kη)`, `dZ ≤ n/(kη²)`, `D ≤ 3n/(4η)` — the shape that gives the `η³`
threshold. -/
theorem johnson_params_degreeCap (k n t : ℕ) (η : ℝ)
    (hk1 : 1 ≤ k) (hη : 0 < η) (hη4 : η ≤ 1/4)
    (hηn : 1 ≤ η * n)
    (ht4 : 4 * η * n ≤ (t : ℝ)) (htn : t ≤ n)
    (hJ : (k : ℝ) * n ≤ ((t : ℝ) - 4 * η * n) ^ 2) :
    ∃ m D dY dZ : ℕ,
      1 ≤ m ∧ k * dY ≤ D ∧ D < m * t ∧ 1 ≤ dY ∧ dZ = (m + 1) * (dY + 1) ∧
      (n * (m * (m + 1)) * (dZ + dY + 1)
        < ((dY + 1) * (2 * (D + 1)) - k * (dY * (dY + 1))) * (dZ + 1)) ∧
      (dY : ℝ) ≤ 3 * n / (4 * k * η) ∧
      (dZ : ℝ) ≤ n / (k * η ^ 2) ∧
      (D : ℝ) ≤ 3 * n / (4 * η) ∧
      (m : ℝ) ≤ (t : ℝ) / (2 * η * n) + 1 := by
  have hK1 : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk1
  have hK0 : (0 : ℝ) < (k : ℝ) := by linarith
  have hN4 : (4 : ℝ) ≤ (n : ℝ) := by nlinarith
  have hN0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hT4 : (4 : ℝ) ≤ (t : ℝ) := by linarith only [hηn, ht4]
  have hT0 : (0 : ℝ) < (t : ℝ) := by linarith
  have hTN : (t : ℝ) ≤ (n : ℝ) := by exact_mod_cast htn
  have hsub0 : (0 : ℝ) ≤ (t : ℝ) - 4 * η * n := sub_nonneg.mpr ht4
  have hKN : (k : ℝ) ≤ (n : ℝ) := by
    have h2 : (t : ℝ) - 4 * η * n ≤ (n : ℝ) := by linarith only [hTN, hηn]
    have h3 : ((t : ℝ) - 4 * η * n) ^ 2 ≤ (n : ℝ) ^ 2 :=
      pow_le_pow_left₀ hsub0 h2 2
    exact le_of_mul_le_mul_right (by simpa only [pow_two] using hJ.trans h3) hN0
  have h2ηN : (0 : ℝ) < 2 * η * n := by positivity
  -- The multiplicity.
  obtain ⟨m, hm_lb, hm_ub⟩ : ∃ m : ℕ,
      (t : ℝ) / (2 * η * n) ≤ (m : ℝ) ∧ (m : ℝ) < (t : ℝ) / (2 * η * n) + 1 :=
    ⟨⌈(t : ℝ) / (2 * η * n)⌉₊, Nat.le_ceil _, Nat.ceil_lt_add_one (by positivity)⟩
  have hm2 : (2 : ℝ) ≤ (m : ℝ) := by
    refine le_trans ?_ hm_lb
    rw [le_div_iff₀ h2ηN]
    nlinarith only [ht4]
  have hm1 : 1 ≤ m := by exact_mod_cast le_trans (by norm_num : (1:ℝ) ≤ 2) hm2
  have ht1 : 1 ≤ t := by exact_mod_cast le_trans (by norm_num : (1:ℝ) ≤ 4) hT4
  have hmt1 : 1 ≤ m * t := Nat.one_le_iff_ne_zero.mpr
    (Nat.mul_ne_zero (by omega) (by omega))
  -- The weighted degree.
  obtain ⟨D, hDdef⟩ : ∃ D : ℕ, D = m * t - 1 := ⟨_, rfl⟩
  have hDlt : D < m * t := by omega
  have hD1 : (D : ℝ) = (m : ℝ) * t - 1 := by
    rw [hDdef]
    push_cast [Nat.cast_sub hmt1]
    ring
  -- The `Y`-degree.
  obtain ⟨dY, hdYdef⟩ : ∃ dY : ℕ, dY = D / k := ⟨_, rfl⟩
  have hkdY : k * dY ≤ D := by
    rw [hdYdef, mul_comm]
    exact Nat.div_mul_le_self D k
  have hkdY1 : D + 1 ≤ k * (dY + 1) := by
    have h1 := Nat.div_add_mod D k
    have h2 : D % k < k := Nat.mod_lt _ (by omega)
    have h3 : k * (D / k + 1) = k * (D / k) + k := by ring
    rw [hdYdef, h3]
    omega
  -- `t ≥ k + 4ηn`, hence `D ≥ k` and `dY ≥ 1`.
  have hTk : (k : ℝ) + 4 * η * n ≤ (t : ℝ) := by
    have h1 : (k : ℝ) ≤ (t : ℝ) - 4 * η * n := by
      nlinarith only [hJ, hK0, hKN, hsub0, sq_nonneg ((t : ℝ) - 4 * η * n - k),
        sq_nonneg ((t : ℝ) - 4 * η * n + k)]
    linarith
  have hDk : k ≤ D := by
    have h1 : (k : ℝ) + 1 ≤ (m : ℝ) * t := by
      have h1a : 2 * (t : ℝ) ≤ (m : ℝ) * t :=
        mul_le_mul_of_nonneg_right hm2 (le_of_lt hT0)
      nlinarith only [h1a, hTk, hηn, hK1]
    have h2 : (k : ℝ) ≤ (D : ℝ) := by rw [hD1]; linarith
    exact_mod_cast h2
  have hdY1 : 1 ≤ dY := by
    rw [hdYdef]
    exact (Nat.one_le_div_iff (by omega)).mpr hDk
  -- The `Z`-degree.
  obtain ⟨dZ, hdZdef⟩ : ∃ dZ : ℕ, dZ = (m + 1) * (dY + 1) := ⟨_, rfl⟩
  -- ### The counting inequality.
  have hcnt : n * (m * (m + 1)) * (dZ + dY + 1)
      < ((dY + 1) * (2 * (D + 1)) - k * (dY * (dY + 1))) * (dZ + 1) := by
    have hfac : (dY + 1) * (2 * (D + 1)) - k * (dY * (dY + 1))
        = (dY + 1) * (2 * (D + 1) - k * dY) := by
      have h1 : k * (dY * (dY + 1)) = (dY + 1) * (k * dY) := by ring
      rw [h1, ← Nat.mul_sub]
    have hstep : n * m * (m + 2) < (D + 2) * (dY + 1) := by
      have hcast : (k : ℝ) * ((n : ℝ) * m * ((m : ℝ) + 2))
          < (k : ℝ) * (((D : ℝ) + 2) * ((dY : ℝ) + 1)) := by
        have h4m : 2 * (t : ℝ) ≤ 4 * η * n * m := by
          have h5 := hm_lb
          rw [div_le_iff₀ h2ηN] at h5
          nlinarith only [h5]
        have hkey : ((m : ℝ) + 1) * ((t : ℝ) - 4 * η * n) ≤ (m : ℝ) * t - t := by
          nlinarith only [h4m, hηn]
        have hsq : (k : ℝ) * n * ((m : ℝ) + 1) ^ 2 ≤ ((m : ℝ) * t - t) ^ 2 := by
          have h2 : (0 : ℝ) ≤ ((m : ℝ) + 1) * ((t : ℝ) - 4 * η * n) := by positivity
          calc (k : ℝ) * n * ((m : ℝ) + 1) ^ 2
              = ((m : ℝ) + 1) ^ 2 * ((k : ℝ) * n) := by ring
            _ ≤ ((m : ℝ) + 1) ^ 2 * ((t : ℝ) - 4 * η * n) ^ 2 :=
                mul_le_mul_of_nonneg_left hJ (sq_nonneg _)
            _ = (((m : ℝ) + 1) * ((t : ℝ) - 4 * η * n)) ^ 2 := by ring
            _ ≤ ((m : ℝ) * t - t) ^ 2 := pow_le_pow_left₀ h2 hkey 2
        have hmain : (k : ℝ) * n * ((m : ℝ) * ((m : ℝ) + 2)) < ((m : ℝ) * t) ^ 2 := by
          have e1 : (k : ℝ) * n * ((m : ℝ) * ((m : ℝ) + 2))
              = (k : ℝ) * n * ((m : ℝ) + 1) ^ 2 - (k : ℝ) * n := by ring
          have e2 : ((m : ℝ) * t - t) ^ 2
              = ((m : ℝ) * t) ^ 2 - (2 * m - 1) * (t : ℝ) ^ 2 := by ring
          have e4 : (0 : ℝ) < (2 * (m : ℝ) - 1) * (t : ℝ) ^ 2 := by
            exact mul_pos (by linarith only [hm2]) (sq_pos_of_pos hT0)
          have e5 : (0 : ℝ) < (k : ℝ) * n := by positivity
          rw [e2] at hsq
          linarith
        have hD1' : ((m : ℝ) * t) = (D : ℝ) + 1 := by rw [hD1]; ring
        have hkdY1' : (D : ℝ) + 1 ≤ (k : ℝ) * ((dY : ℝ) + 1) := by exact_mod_cast hkdY1
        have hDpos : (0 : ℝ) ≤ (D : ℝ) + 1 := by positivity
        calc (k : ℝ) * ((n : ℝ) * m * ((m : ℝ) + 2))
            = (k : ℝ) * n * ((m : ℝ) * ((m : ℝ) + 2)) := by ring
          _ < ((m : ℝ) * t) ^ 2 := hmain
          _ = ((D : ℝ) + 1) * ((D : ℝ) + 1) := by rw [hD1']; ring
          _ ≤ ((D : ℝ) + 1) * ((k : ℝ) * ((dY : ℝ) + 1)) :=
              mul_le_mul_of_nonneg_left hkdY1' hDpos
          _ ≤ ((D : ℝ) + 2) * ((k : ℝ) * ((dY : ℝ) + 1)) := by
              refine mul_le_mul_of_nonneg_right (by linarith) (by positivity)
          _ = (k : ℝ) * (((D : ℝ) + 2) * ((dY : ℝ) + 1)) := by ring
      have h6 := lt_of_mul_lt_mul_left hcast (le_of_lt hK0)
      exact_mod_cast h6
    have hsplit : dZ + dY + 1 = (m + 2) * (dY + 1) := by rw [hdZdef]; ring
    have hZ1 : (m + 1) * (dY + 1) ≤ dZ + 1 := by
      rw [hdZdef]
      exact Nat.le_succ _
    calc n * (m * (m + 1)) * (dZ + dY + 1)
        = (n * m * (m + 2)) * ((m + 1) * (dY + 1)) := by rw [hsplit]; ring
      _ < ((D + 2) * (dY + 1)) * ((m + 1) * (dY + 1)) := by
          have hpos : 0 < (m + 1) * (dY + 1) := by positivity
          exact mul_lt_mul_of_pos_right hstep hpos
      _ ≤ ((dY + 1) * (2 * (D + 1) - k * dY)) * (dZ + 1) := by
          refine Nat.mul_le_mul ?_ hZ1
          calc (D + 2) * (dY + 1) = (dY + 1) * (D + 2) := by ring
            _ ≤ (dY + 1) * (2 * (D + 1) - k * dY) := by
                refine Nat.mul_le_mul_left _ ?_
                omega
      _ = ((dY + 1) * (2 * (D + 1)) - k * (dY * (dY + 1))) * (dZ + 1) := by
          rw [hfac]
  -- ### The size bounds.
  have hmT : (m : ℝ) * t ≤ (t : ℝ) ^ 2 / (2 * η * n) + t := by
    have h2 : (m : ℝ) * t ≤ ((t : ℝ) / (2 * η * n) + 1) * t :=
      mul_le_mul_of_nonneg_right hm_ub.le hT0.le
    calc (m : ℝ) * t ≤ ((t : ℝ) / (2 * η * n) + 1) * t := h2
      _ = (t : ℝ) * t / (2 * η * n) + t := by ring
      _ = (t : ℝ) ^ 2 / (2 * η * n) + t := by ring
  have hDreal : (D : ℝ) ≤ 3 * n / (4 * η) := by
    have h1 : (t : ℝ) ^ 2 / (2 * η * n) ≤ (n : ℝ) / (2 * η) := by
      rw [div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith only [mul_le_mul_of_nonneg_right
        (mul_le_mul hTN hTN hT0.le hN0.le) (by positivity : (0:ℝ) ≤ 2 * η)]
    have h2 : (t : ℝ) ≤ (n : ℝ) / (4 * η) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith only [mul_le_mul_of_nonneg_right hη4 hT0.le, hTN]
    have h3 : (D : ℝ) ≤ (m : ℝ) * t := by rw [hD1]; linarith
    calc (D : ℝ) ≤ (m : ℝ) * t := h3
      _ ≤ (t : ℝ) ^ 2 / (2 * η * n) + t := hmT
      _ ≤ (n : ℝ) / (2 * η) + (n : ℝ) / (4 * η) := by linarith
      _ = 3 * n / (4 * η) := by ring
  have hdYreal : (dY : ℝ) ≤ 3 * n / (4 * k * η) := by
    have h1 : (dY : ℝ) ≤ (D : ℝ) / k := by
      rw [hdYdef]
      exact_mod_cast Nat.cast_div_le
    have h2 : (D : ℝ) / k ≤ (3 * n / (4 * η)) / k := by gcongr
    calc (dY : ℝ) ≤ (D : ℝ) / k := h1
      _ ≤ (3 * n / (4 * η)) / k := h2
      _ = 3 * n / (4 * k * η) := by
          field_simp
  have hdZreal : (dZ : ℝ) ≤ (n : ℝ) / (k * η ^ 2) := by
    have hmub : (m : ℝ) + 1 ≤ 1 / η := by
      have h1 : (t : ℝ) / (2 * η * n) ≤ 1 / (2 * η) := by
        rw [div_le_div_iff₀ h2ηN (by positivity)]
        nlinarith only [mul_le_mul_of_nonneg_left hTN (by positivity : (0:ℝ) ≤ 2 * η)]
      have h2 : (2 : ℝ) ≤ 1 / (2 * η) := by
        rw [le_div_iff₀ (by positivity)]
        nlinarith only [hη4]
      have h3 : (m : ℝ) + 1 < 1 / (2 * η) + 2 := by linarith
      have h4 : 1 / (2 * η) + 2 ≤ 1 / (2 * η) + 1 / (2 * η) := by linarith
      have h5 : 1 / (2 * η) + 1 / (2 * η) = 1 / η := by
        field_simp
        ring
      linarith
    have hdYub : (dY : ℝ) + 1 ≤ (n : ℝ) / (k * η) := by
      have h1 : (1 : ℝ) ≤ (n : ℝ) / (4 * k * η) := by
        rw [le_div_iff₀ (by positivity)]
        nlinarith only [hKN, mul_le_mul_of_nonneg_left hη4
          (by positivity : (0:ℝ) ≤ 4 * (k:ℝ))]
      have h2 : 3 * (n : ℝ) / (4 * k * η) + (n : ℝ) / (4 * k * η) = (n : ℝ) / (k * η) := by
        field_simp
        ring
      linarith
    have hcast : (dZ : ℝ) = ((m : ℝ) + 1) * ((dY : ℝ) + 1) := by
      rw [hdZdef]
      push_cast
      ring
    have hm0 : (0 : ℝ) ≤ (m : ℝ) + 1 := by positivity
    have hdY0 : (0 : ℝ) ≤ (dY : ℝ) + 1 := by positivity
    calc (dZ : ℝ) = ((m : ℝ) + 1) * ((dY : ℝ) + 1) := hcast
      _ ≤ (1 / η) * ((n : ℝ) / (k * η)) := by
          refine mul_le_mul hmub hdYub hdY0 (by positivity)
      _ = (n : ℝ) / (k * η ^ 2) := by
          field_simp
  exact ⟨m, D, dY, dZ, hm1, hkdY, hDlt, hdY1, hdZdef, hcnt, hdYreal, hdZreal, hDreal,
    le_of_lt hm_ub⟩

end Johnson

/-- The explicit `|S|`-threshold of the Johnson-regime theorem.  The
interpolation bounds use the degree cap `w = k - 1`, while the weighted selector
and agreement slack use the code dimension `k`.  The incidence term contains
one `dY·dZ` factor, not the old uniform-bucket `dY²·dZ` factor. -/
noncomputable def johnsonThreshold (k n e : ℕ) (η : ℝ) : ℝ :=
  let w := k - 1
  (3 * n / (4 * w * η)) * ((e : ℝ) + 2) +
    (n - k : ℕ) * (4 * k * (3 * n / (4 * w * η) * (n / (w * η ^ 2)))
      + 3 * n / (4 * w * η)) / ((n - e - k : ℕ) : ℝ)
    + n / (w * η ^ 2) + 3 * (3 * n / (4 * w * η) * (n / (w * η ^ 2))) + 1

section Final

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

set_option maxHeartbeats 1600000 in
/-- **The Johnson numeric package.**  From the real-parameter Johnson hypotheses and
the threshold bound, all sharp `ℕ`-side conditions (with `n` the domain size and
`cS` the parameter-set size).  Shared by the plain and strong mutual variants. -/
theorem johnson_numeric (k n e cS : ℕ) (η : ℝ)
    (hk2 : 2 ≤ k) (hη : 0 < η) (hη4 : η ≤ 1/4)
    (hηn : 1 ≤ η * n)
    (ht4 : 4 * η * n ≤ ((n - e : ℕ) : ℝ))
    (hJ : ((k - 1 : ℕ) : ℝ) * n ≤
      (((n - e : ℕ) : ℝ) - 4 * η * n) ^ 2)
    (hS : johnsonThreshold k n e η ≤ (cS : ℝ)) :
    ∃ m D dY dZ : ℕ,
      (k - 1) * dY ≤ D ∧
      (n * (m * (m + 1)) * (dZ + dY + 1)
        < ((dY + 1) * (2 * (D + 1)) - (k - 1) * (dY * (dY + 1))) *
          (dZ + 1)) ∧
      D < m * (n - e) ∧ 1 ≤ n - e - k ∧
      dY * (e + 2) + (n - k) * (4 * k * (dY * dZ) + dY) / (n - e - k) +
        dZ + 3 * (dY * dZ) < cS := by
  -- Notation.
  let w := k - 1
  have hw1 : 1 ≤ w := by simp [w]; omega
  have htn : n - e ≤ n := Nat.sub_le _ _
  -- The Guruswami–Sudan parameters.
  obtain ⟨m, D, dY, dZ, hm1, hkdY, hDlt, hdY1, hdZdef, hcnt, hdYreal, hdZreal, hDreal, -⟩ :=
    johnson_params_degreeCap w n (n - e) η hw1 hη hη4 hηn ht4 htn
      (by simpa [w] using hJ)
  -- Real abbreviations and positivity.
  have hW1 : (1 : ℝ) ≤ (w : ℝ) := by exact_mod_cast hw1
  have hW0 : (0 : ℝ) < (w : ℝ) := by linarith
  have hN4 : (4 : ℝ) ≤ (n : ℝ) := by nlinarith
  have hN0 : (0 : ℝ) < (n : ℝ) := by linarith
  have hT4 : (4 : ℝ) ≤ ((n - e : ℕ) : ℝ) := by nlinarith
  -- `n - e ≥ k + 4`, so `s ≥ 4`.
  have hsub0 : (0 : ℝ) ≤ ((n - e : ℕ) : ℝ) - 4 * η * (n) := by
    linarith
  have hWN : (w : ℝ) ≤ (n : ℝ) := by
    have hTN' : ((n - e : ℕ) : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast htn
    have h2 : ((n - e : ℕ) : ℝ) - 4 * η * (n)
        ≤ (n : ℝ) := by nlinarith
    have h3 : (((n - e : ℕ) : ℝ) - 4 * η * (n)) ^ 2
        ≤ (n : ℝ) ^ 2 := by nlinarith
    nlinarith
  have hTw : (w : ℝ) + 4 * η * n ≤ ((n - e : ℕ) : ℝ) := by
    have h1 : (w : ℝ) ≤ ((n - e : ℕ) : ℝ) - 4 * η * n := by
      nlinarith [sq_nonneg (((n - e : ℕ) : ℝ)
        - 4 * η * n - w),
        sq_nonneg (((n - e : ℕ) : ℝ)
        - 4 * η * n + w)]
    linarith
  have hw4 : w + 4 ≤ n - e := by
    have h1 : (w : ℝ) + 4 ≤ ((n - e : ℕ) : ℝ) := by nlinarith
    exact_mod_cast h1
  set s : ℕ := n - e - k with hsdef
  have hs1 : 3 ≤ s := by simp [w] at hw4; omega
  have hsR : (s : ℝ) = ((n - e : ℕ) : ℝ) - k := by
    rw [hsdef]
    push_cast [Nat.cast_sub (by omega : k ≤ n - e)]
    ring
  have hs0 : (0 : ℝ) < (s : ℝ) := by
    have : (3 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs1
    linarith
  -- The real bounds on the weighted threshold.
  have hY0 : (0 : ℝ) ≤ 3 * (n : ℝ) / (4 * w * η) := by positivity
  have hZ0 : (0 : ℝ) ≤ (n : ℝ) / (w * η ^ 2) := by positivity
  have hdY0 : (0 : ℝ) ≤ (dY : ℝ) := Nat.cast_nonneg _
  have hdZ0 : (0 : ℝ) ≤ (dZ : ℝ) := Nat.cast_nonneg _
  have hYZ : (dY : ℝ) * dZ ≤ 3 * (n : ℝ) / (4 * w * η)
        * ((n : ℝ) / (w * η ^ 2)) :=
    mul_le_mul hdYreal hdZreal hdZ0 hY0
  have hCap : ((4 * k * (dY * dZ) + dY : ℕ) : ℝ) ≤
      4 * k * (3 * (n : ℝ) / (4 * w * η)
        * ((n : ℝ) / (w * η ^ 2))) + 3 * (n : ℝ) / (4 * w * η) := by
    push_cast
    have hk : (0 : ℝ) ≤ 4 * k := by positivity
    exact add_le_add (mul_le_mul_of_nonneg_left hYZ hk) hdYreal
  -- The real threshold dominates the exact natural weighted threshold.
  have hSnat : dY * (e + 2) + (n - k) * (4 * k * (dY * dZ) + dY) / s +
      dZ + 3 * (dY * dZ) < cS := by
    have hchain : ((dY * (e + 2) + (n - k) * (4 * k * (dY * dZ) + dY) / s +
          dZ + 3 * (dY * dZ) : ℕ) : ℝ) + 1
        ≤ johnsonThreshold k (n) e η := by
      have hbase : (dY : ℝ) * ((e : ℝ) + 2) ≤
          (3 * (n : ℝ) / (4 * w * η)) * ((e : ℝ) + 2) :=
        mul_le_mul_of_nonneg_right hdYreal (by positivity)
      have hdiv : ((((n - k) * (4 * k * (dY * dZ) + dY)) / s : ℕ) : ℝ) ≤
          ((n - k : ℕ) : ℝ) * (4 * k * (3 * (n : ℝ) / (4 * w * η)
            * ((n : ℝ) / (w * η ^ 2))) + 3 * (n : ℝ) / (4 * w * η)) /
              (s : ℝ) := by
        calc ((((n - k) * (4 * k * (dY * dZ) + dY)) / s : ℕ) : ℝ)
            ≤ ((((n - k) * (4 * k * (dY * dZ) + dY) : ℕ) : ℝ) / (s : ℝ)) :=
              Nat.cast_div_le
          _ ≤ ((n - k : ℕ) : ℝ) * (4 * k * (3 * (n : ℝ) / (4 * w * η)
              * ((n : ℝ) / (w * η ^ 2))) + 3 * (n : ℝ) / (4 * w * η)) /
                (s : ℝ) := by
            push_cast
            gcongr
      have htail : (dZ : ℝ) + 3 * ((dY : ℝ) * dZ) ≤
          (n : ℝ) / (w * η ^ 2) + 3 * (3 * (n : ℝ) / (4 * w * η)
            * ((n : ℝ) / (w * η ^ 2))) := by linarith
      rw [johnsonThreshold]
      push_cast
      rw [← hsdef]
      linarith
    have h7 : ((dY * (e + 2) + (n - k) * (4 * k * (dY * dZ) + dY) / s +
        dZ + 3 * (dY * dZ) : ℕ) : ℝ) < (cS : ℝ) := by
      linarith
    exact_mod_cast h7
  -- Conclude.
  have hroot : D < m * (n - e) := hDlt
  exact ⟨m, D, dY, dZ, by simpa [w] using hkdY,
    by simpa [w] using hcnt, hroot, by omega, by simpa [hsdef] using hSnat⟩

end Final

end JBAgreement
