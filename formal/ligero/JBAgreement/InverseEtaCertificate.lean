import JBAgreement.SelectedLine

/-! Exact Johnson-regime certificates with eta = 1 / etaDenom.
The denominator is any positive integer satisfying the theorem's numerical
conditions; it is not restricted to a power of two. All protocol variants
consume the same proved selected-line interface. -/

namespace JBAgreement

open Polynomial

/-- `johnsonThreshold` at `η = 1 / etaDenom`, over `ℚ`.  The shape is copied
from `johnsonThreshold` term by term so the cast lemma below is a `ring`
identity. -/
def johnsonThresholdInverseQ (k n e etaDenom : ℕ) : ℚ :=
  let η : ℚ := etaDenom⁻¹
  let w := k - 1
  3 * n / (4 * w * η) * ((e : ℚ) + 2) +
    ((n - k : ℕ) : ℚ) * (4 * k * (3 * n / (4 * w * η) * (n / (w * η ^ 2)))
      + 3 * n / (4 * w * η)) / ((n - e - k : ℕ) : ℚ)
    + n / (w * η ^ 2) + 3 * (3 * n / (4 * w * η) * (n / (w * η ^ 2))) + 1

/-- The rational mirror is exact: no slack is introduced by leaving `ℝ`. -/
theorem johnsonThresholdInverseQ_cast (k n e etaDenom : ℕ) :
    ((johnsonThresholdInverseQ k n e etaDenom : ℚ) : ℝ)
      = johnsonThreshold k n e ((etaDenom : ℝ)⁻¹) := by
  unfold johnsonThresholdInverseQ johnsonThreshold
  push_cast
  ring

/-- **The cleared numeric hypotheses of the Johnson route.**  Each conjunct is
one hypothesis of `lineFailureBound_of_johnson` with `η = 1 / etaDenom` and
denominators cleared:

* `hk` — `2 ≤ k`, so the degree cap `k - 1` is positive;
* `hquarter` — `η ≤ 1/4`;
* `hlength` — `1 ≤ η · n`;
* `hslack` — `4 · η · n ≤ n - e`, and `k` still fits below the radius;
* `hjohnson` — the Johnson condition `(k - 1) · n ≤ (n - e - 4 η n)²`;
* `hfield` — `9 n² / (8 (k - 1) η²) < |F|`;
* `hthreshold` — the certificate's `bound` dominates the threshold. -/
structure InverseEtaConditions (n k e etaDenom bound fieldSize : ℕ) : Prop where
  hk : 2 ≤ k
  hquarter : 4 ≤ etaDenom
  hlength : etaDenom ≤ n
  hslack : 4 * n ≤ (n - e) * etaDenom
  hroom : k + 1 ≤ n - e
  hjohnson : (k - 1) * n * etaDenom ^ 2 ≤
    ((n - e) * etaDenom - 4 * n) ^ 2
  hfield : 9 * n ^ 2 * etaDenom ^ 2 < 8 * (k - 1) * fieldSize
  hthreshold : johnsonThresholdInverseQ k n e etaDenom ≤ (bound : ℚ) + 1

/-- Decidable mirror of `InverseEtaConditions`, for certificates the kernel checks.
Every conjunct is a `Nat` or `Rat` comparison, so `decide` evaluates it. -/
def inverseEtaConditionsBool (n k e etaDenom bound fieldSize : ℕ) : Bool :=
  (2 ≤ k) && (4 ≤ etaDenom) && (etaDenom ≤ n) &&
    (4 * n ≤ (n - e) * etaDenom) && (k + 1 ≤ n - e) &&
    ((k - 1) * n * etaDenom ^ 2 ≤ ((n - e) * etaDenom - 4 * n) ^ 2) &&
    (9 * n ^ 2 * etaDenom ^ 2 < 8 * (k - 1) * fieldSize) &&
    decide (johnsonThresholdInverseQ k n e etaDenom ≤ (bound : ℚ) + 1)

theorem inverseEtaConditions_of_bool {n k e etaDenom bound fieldSize : ℕ}
    (h : inverseEtaConditionsBool n k e etaDenom bound fieldSize = true) :
    InverseEtaConditions n k e etaDenom bound fieldSize := by
  simp only [inverseEtaConditionsBool, Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1.1.1.1.1.1, h.1.1.1.1.1.1.2, h.1.1.1.1.1.2, h.1.1.1.1.2,
    h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

namespace InverseEtaConditions

variable {n k e etaDenom bound fieldSize : ℕ}

theorem eta_pos (h : InverseEtaConditions n k e etaDenom bound fieldSize) :
    (0 : ℝ) < (etaDenom : ℝ)⁻¹ := by
  have hpos : 0 < etaDenom := by have := h.hquarter; omega
  positivity

theorem eta_le_quarter (h : InverseEtaConditions n k e etaDenom bound fieldSize) :
    ((etaDenom : ℝ))⁻¹ ≤ 1 / 4 := by
  have h4 : (4 : ℝ) ≤ (etaDenom : ℝ) := by exact_mod_cast h.hquarter
  rw [inv_le_comm₀ (by positivity) (by norm_num)]
  linarith

theorem one_le_eta_mul (h : InverseEtaConditions n k e etaDenom bound fieldSize) :
    (1 : ℝ) ≤ (etaDenom : ℝ)⁻¹ * n := by
  have hden : 0 < etaDenom := by have := h.hquarter; omega
  have hn : (etaDenom : ℝ) ≤ (n : ℝ) := by exact_mod_cast h.hlength
  rw [inv_mul_eq_div, le_div_iff₀ (by positivity)]
  linarith

theorem four_mul_le_sub (h : InverseEtaConditions n k e etaDenom bound fieldSize) :
    4 * ((etaDenom : ℝ))⁻¹ * n ≤ ((n - e : ℕ) : ℝ) := by
  have hden : 0 < etaDenom := by have := h.hquarter; omega
  have hslack : (4 * n : ℝ) ≤ ((n - e : ℕ) : ℝ) * (etaDenom : ℝ) := by
    exact_mod_cast h.hslack
  rw [mul_comm 4 ((etaDenom : ℝ))⁻¹, ← div_eq_inv_mul, div_mul_eq_mul_div,
    div_le_iff₀ (by positivity)]
  linarith

theorem johnson_real (h : InverseEtaConditions n k e etaDenom bound fieldSize) :
    ((k - 1 : ℕ) : ℝ) * n ≤
      (((n - e : ℕ) : ℝ) - 4 * ((etaDenom : ℝ))⁻¹ * n) ^ 2 := by
  have hden : 0 < etaDenom := by have := h.hquarter; omega
  have hpow : (0 : ℝ) < (etaDenom : ℝ) := by positivity
  have hslack : (4 * n : ℕ) ≤ (n - e) * etaDenom := h.hslack
  have hcast : (((n - e) * etaDenom - 4 * n : ℕ) : ℝ)
      = ((n - e : ℕ) : ℝ) * (etaDenom : ℝ) - 4 * (n : ℝ) := by
    push_cast [Nat.cast_sub hslack]
    ring
  have hJ : (((k - 1) * n * etaDenom ^ 2 : ℕ) : ℝ)
      ≤ ((((n - e) * etaDenom - 4 * n) ^ 2 : ℕ) : ℝ) := by
    exact_mod_cast h.hjohnson
  rw [Nat.cast_pow, hcast] at hJ
  have hscaled : ((k - 1 : ℕ) : ℝ) * n * (etaDenom : ℝ) ^ 2
      ≤ (((n - e : ℕ) : ℝ) * (etaDenom : ℝ) - 4 * (n : ℝ)) ^ 2 := by
    push_cast at hJ
    linarith
  have hexpand : (((n - e : ℕ) : ℝ) - 4 * ((etaDenom : ℝ))⁻¹ * n) ^ 2
      * (etaDenom : ℝ) ^ 2
      = (((n - e : ℕ) : ℝ) * (etaDenom : ℝ) - 4 * (n : ℝ)) ^ 2 := by
    field_simp
  have hsq : (0 : ℝ) < (etaDenom : ℝ) ^ 2 := by positivity
  rw [← hexpand] at hscaled
  exact le_of_mul_le_mul_right (by linarith) hsq

theorem field_real (h : InverseEtaConditions n k e etaDenom bound fieldSize) :
    9 * ((n : ℝ)) ^ 2 /
      (8 * (k - 1 : ℕ) * ((etaDenom : ℝ))⁻¹ ^ 2) < (fieldSize : ℝ) := by
  have hden : 0 < etaDenom := by have := h.hquarter; omega
  have hk : (1 : ℝ) ≤ ((k - 1 : ℕ) : ℝ) := by
    have hk2 := h.hk
    exact_mod_cast (show 1 ≤ k - 1 by omega)
  have hfield : (9 * n ^ 2 * etaDenom ^ 2 : ℕ) <
      8 * (k - 1) * fieldSize := h.hfield
  have hcast : (9 : ℝ) * (n : ℝ) ^ 2 * (etaDenom : ℝ) ^ 2
      < 8 * ((k - 1 : ℕ) : ℝ) * (fieldSize : ℝ) := by
    have := (Nat.cast_lt (α := ℝ)).mpr hfield
    push_cast at this
    linarith
  rw [div_lt_iff₀ (by positivity)]
  have hrewrite : 8 * ((k - 1 : ℕ) : ℝ) * ((etaDenom : ℝ))⁻¹ ^ 2
      * (etaDenom : ℝ) ^ 2 = 8 * ((k - 1 : ℕ) : ℝ) := by
    field_simp
  nlinarith [hcast, hrewrite, sq_nonneg ((etaDenom : ℝ))⁻¹]

end InverseEtaConditions

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **A checked Johnson certificate supplies the per-line interface.**  Every
hypothesis of `lineFailureBound_of_johnson` is discharged from the decidable
`InverseEtaConditions`, so a grid row can carry its Johnson witness and have the
kernel check it. -/
theorem lineFailureBound_of_inverseEtaConditions
    {n k e g bound fieldSize etaDenom : ℕ} {C : CodingTheory.LinearCode F n}
    (P : RSPresentation n k C)
    (hcard : Fintype.card F = fieldSize)
    (h : InverseEtaConditions n k e etaDenom bound fieldSize) :
    SelectedMCA.LineFailureBound C e g bound := by
  refine lineFailureBound_of_johnson P ((etaDenom : ℝ))⁻¹ h.hk
    h.eta_pos h.eta_le_quarter h.one_le_eta_mul
    h.four_mul_le_sub h.johnson_real ?_ ?_
  · rw [hcard]
    exact h.field_real
  · rw [← johnsonThresholdInverseQ_cast]
    have := h.hthreshold
    exact_mod_cast this

end JBAgreement
