import CodingTheory.ListDecoding.HahnDelsarteRange

/-! A cached evaluator for the radius-independent Hahn weights.  It is kept
separate from the certificates until a measured build shows a useful gain. -/

namespace CodingTheory.HahnDelsarte

/-- Each row contains the weights for one Hahn degree.  In particular, the
binomial coefficients in `hahnWeight` are evaluated once per `(k, x)`, rather
than once per radius and summand. -/
def weightTable (n w maxK : ℕ) : List (List ℚ) :=
  (List.range (maxK + 1)).map fun k ↦
    (List.range (k + 1)).map fun x ↦ hahnWeight n w k x

def tableWeight (weights : List (List ℚ)) (k x : ℕ) : ℚ :=
  (weights.getD k []).getD x 0

theorem tableWeight_eq (n w maxK k x : ℕ) (hk : k ≤ maxK) (hx : x ≤ k) :
    tableWeight (weightTable n w maxK) k x = hahnWeight n w k x := by
  simp [tableWeight, weightTable, List.getD_eq_getElem?_getD,
    List.getElem?_map, List.getElem?_range (by omega : k < maxK + 1),
    List.getElem?_range (by omega : x < k + 1)]

/-- The same four-cell sum, with its radius-independent weights looked up in
the table. -/
def hahnKernelTable (n w k t : ℕ) (weights : List (List ℚ)) : ℚ :=
  ∑ i ∈ Finset.range (k + 1), tableWeight weights k i *
    ∑ a ∈ Finset.range (i + 1), ((t.choose a * (w - t).choose (i - a) : ℕ) : ℚ) *
      ∑ c ∈ Finset.range (k - i + 1),
        (((w - t).choose c * (n + t - 2 * w).choose (k - i - c) : ℕ) : ℚ) *
          tableWeight weights k (a + c)

theorem hahnKernelTable_eq (n w maxK k t : ℕ) (hk : k ≤ maxK) :
    hahnKernelTable n w k t (weightTable n w maxK) = hahnKernel n w k t := by
  unfold hahnKernelTable hahnKernel
  apply Finset.sum_congr rfl
  intro i hi
  have hi' : i ≤ k := by
    have hik := Finset.mem_range.mp hi
    omega
  rw [tableWeight_eq n w maxK k i hk hi']
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  congr 1
  apply Finset.sum_congr rfl
  intro c hc
  have hax : a + c ≤ k := by
    have hai := Finset.mem_range.mp ha
    have hck := Finset.mem_range.mp hc
    omega
  rw [tableWeight_eq n w maxK k (a + c) hk hax]

def certificatePolynomialTable (n w : ℕ) (coeffs : List ℕ)
    (weights : List (List ℚ)) (t : ℕ) : ℚ :=
  (coeffs.headD 0 : ℚ) +
    ∑ k ∈ Finset.Icc 1 (coeffs.length - 1),
      (coeffs.getD k 0 : ℚ) *
        hahnKernelTable n w k t weights

theorem certificatePolynomialTable_eq (n w : ℕ) (coeffs : List ℕ) (t : ℕ) :
    certificatePolynomialTable n w coeffs
        (weightTable n w (coeffs.length - 1)) t =
      certificatePolynomial n w coeffs t := by
  unfold certificatePolynomialTable certificatePolynomial
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [hahnKernelTable_eq n w (coeffs.length - 1) k t (Finset.mem_Icc.mp hk).2]

/-- A closed range check that shares one table across all its radii. -/
def certificateRangeTableValid (n w lo hi : ℕ) (coeffs : List ℕ) : Bool :=
  let weights := weightTable n w (coeffs.length - 1)
  (List.range (hi - lo)).all fun offset ↦
    let t := lo + offset
    decide (n + t < 2 * w) ||
      decide (certificatePolynomialTable n w coeffs weights t ≤ 0)

theorem certificateRangeTableValid_eq (n w lo hi : ℕ) (coeffs : List ℕ) :
    certificateRangeTableValid n w lo hi coeffs =
      certificateRangeValid n w lo hi coeffs := by
  simp [certificateRangeTableValid, certificateRangeValid,
    certificatePolynomialTable_eq]

end CodingTheory.HahnDelsarte
