import LigeroFamily.Soundness.LiftListBound
import LigeroFamily.Soundness.ProfiledLiftList
import CodingTheory.ListDecoding.InterleavedJohnson
import Mathlib.Algebra.BigOperators.Module











namespace LigeroFamily

/-- Aggregated number of global arithmetic labels (over the fixed lift list)
which may attain agreement at least `a`. -/
structure AgreementProfile (n : ℕ) where
  labelsAtLeast : ℕ → ℕ

namespace AgreementProfile

variable {n : ℕ}

/-- The label tail clipped at probability one. -/
def tail (q : ℕ) (profile : AgreementProfile n) (a : ℕ) : ℚ :=
  min 1 ((profile.labelsAtLeast a : ℚ) / q)

theorem tail_nonnegative (q : ℕ) (profile : AgreementProfile n) (a : ℕ) :
    0 ≤ profile.tail q a := by
  unfold tail
  exact le_min (by norm_num) (div_nonneg (by positivity) (by positivity))

/-- Query success for either the far-proximity cover or the arithmetic cover
with residual size `g` and mask agreement `a`.  Encoding the alternative
covers by a maximum avoids an artificial union bound. -/
def coverRatio (n e g queryCount a : ℕ) : ℚ :=
  hypergeometricRatio
    (max (n - e - 1) (min n (g + a))) n queryCount

/-- Forward difference of the monotone query-cover function.  At zero the
predecessor is defined to have probability zero. -/
def coverIncrement (n e g queryCount a : ℕ) : ℚ :=
  coverRatio n e g queryCount a -
    if a = 0 then 0 else coverRatio n e g queryCount (a - 1)

theorem coverRatio_mono (n e g queryCount : ℕ) :
    Monotone (coverRatio n e g queryCount) := by
  intro a b hab
  unfold coverRatio hypergeometricRatio
  apply div_le_div_of_nonneg_right
  · exact_mod_cast Nat.choose_le_choose queryCount
      (max_le_max_left (n - e - 1)
        (min_le_min_left n (Nat.add_le_add_left hab g)))
  · positivity

theorem coverIncrement_nonnegative (n e g queryCount a : ℕ)
    : 0 ≤ coverIncrement n e g queryCount a := by
  unfold coverIncrement
  by_cases ha : a = 0
  · simp [ha, coverRatio]
    exact div_nonneg (by positivity) (by positivity)
  · simp only [ha, ↓reduceIte]
    exact sub_nonneg.mpr
      (coverRatio_mono n e g queryCount (Nat.sub_le a 1))

theorem sum_coverIncrement (n e g queryCount a : ℕ) :
    ∑ i ∈ Finset.range (a + 1), coverIncrement n e g queryCount i =
      coverRatio n e g queryCount a := by
  induction a with
  | zero => simp [coverIncrement]
  | succ a ih =>
      rw [Finset.sum_range_succ]
      rw [ih]
      simp only [coverIncrement, Nat.succ_ne_zero, ↓reduceIte,
        Nat.add_one_sub_one]
      ring

/-- The exact arithmetic contribution `Φ`: a finite tail sum over possible
agreement sizes. -/
def contribution (q n e g queryCount : ℕ)
    (profile : AgreementProfile n) : ℚ :=
  ∑ a ∈ Finset.range (n + 1),
    coverIncrement n e g queryCount a * profile.tail q a

theorem contribution_nonnegative (q n e g queryCount : ℕ)
    (profile : AgreementProfile n) :
    0 ≤ profile.contribution q n e g queryCount := by
  unfold contribution
  apply Finset.sum_nonneg
  intro a _
  exact mul_nonneg (coverIncrement_nonnegative n e g queryCount a)
    (tail_nonnegative q profile a)

/-- The same contribution written by summation by parts.  The guard is
computationally important: evaluating the expression requires a binomial
coefficient only where the agreement tail actually changes. -/
def compressedContribution (q n e g queryCount : ℕ)
    (profile : AgreementProfile n) : ℚ :=
  profile.tail q n * coverRatio n e g queryCount n +
    ∑ a ∈ Finset.range n,
      if profile.labelsAtLeast a = profile.labelsAtLeast (a + 1) then 0
      else (profile.tail q a - profile.tail q (a + 1)) *
        coverRatio n e g queryCount a

/-- Abel summation turns the full exact profile sum into the sparse,
computable `compressedContribution`. -/
theorem contribution_eq_compressedContribution
    (q n e g queryCount : ℕ) (profile : AgreementProfile n) :
    profile.contribution q n e g queryCount =
      profile.compressedContribution q n e g queryCount := by
  have hparts := Finset.sum_range_by_parts
    (f := fun a => profile.tail q a)
    (g := fun a => coverIncrement n e g queryCount a) (n + 1)
  have hprefix (a : ℕ) :
      ∑ i ∈ Finset.range (a + 1), coverIncrement n e g queryCount i =
        coverRatio n e g queryCount a :=
    sum_coverIncrement n e g queryCount a
  have hguard (a : ℕ) :
      (if profile.labelsAtLeast a = profile.labelsAtLeast (a + 1) then 0
       else (profile.tail q a - profile.tail q (a + 1)) *
         coverRatio n e g queryCount a) =
      (profile.tail q a - profile.tail q (a + 1)) *
        coverRatio n e g queryCount a := by
    split
    next h => simp [AgreementProfile.tail, h]
    next => rfl
  unfold contribution compressedContribution
  rw [show n + 1 - 1 = n by omega] at hparts
  simp only [smul_eq_mul] at hparts
  rw [hprefix n] at hparts
  simp_rw [hprefix] at hparts
  simp_rw [hguard]
  calc
    (∑ a ∈ Finset.range (n + 1),
        coverIncrement n e g queryCount a * profile.tail q a) =
        ∑ a ∈ Finset.range (n + 1),
          profile.tail q a * coverIncrement n e g queryCount a := by
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = profile.tail q n * coverRatio n e g queryCount n -
        ∑ a ∈ Finset.range n,
          (profile.tail q (a + 1) - profile.tail q a) *
            coverRatio n e g queryCount a := hparts
    _ = profile.tail q n * coverRatio n e g queryCount n +
        ∑ a ∈ Finset.range n,
          (profile.tail q a - profile.tail q (a + 1)) *
            coverRatio n e g queryCount a := by
      rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
      apply congrArg (profile.tail q n * coverRatio n e g queryCount n + ·)
      apply Finset.sum_congr rfl
      intro a _
      ring

section TailCounting

variable {X : Type*} [Fintype X]

noncomputable def tailSet (agreement : X → ℕ) (a : ℕ) : Finset X := by
  classical
  exact Finset.univ.filter fun x ↦ a ≤ agreement x

/-- Tail set restricted to a distinguished class of challenges.  This is the
right object for query-weighting selected-MCA failures: challenges outside
`selected` contribute no query mass at any agreement threshold. -/
noncomputable def restrictedTailSet (selected : Finset X)
    (agreement : X → ℕ) (a : ℕ) : Finset X := by
  classical
  exact selected.filter fun x ↦ a ≤ agreement x

omit [Fintype X] in
theorem coverRatio_eq_increment_sum (n e g queryCount : ℕ)
    (agreement : X → ℕ) (x : X) (hagreement : agreement x ≤ n) :
    coverRatio n e g queryCount (agreement x) =
      ∑ a ∈ Finset.range (n + 1),
        if a ≤ agreement x then coverIncrement n e g queryCount a else 0 := by
  have hfilter :
      (Finset.range (n + 1)).filter (fun a ↦ a ≤ agreement x) =
        Finset.range (agreement x + 1) := by
    ext a
    simp
    omega
  rw [← sum_coverIncrement n e g queryCount (agreement x)]
  rw [← hfilter]
  rw [Finset.sum_filter]

/-- Finite tail-sum theorem used by the common soundness master. -/
theorem average_coverRatio_le_contribution
    (q n e g queryCount : ℕ) (profile : AgreementProfile n)
    (agreement : X → ℕ) (hq : 0 < q) [Nonempty X]
    (hagreement : ∀ x, agreement x ≤ n)
    (hdensity : ∀ a ≤ n,
      q * (tailSet agreement a).card ≤
        profile.labelsAtLeast a * Fintype.card X) :
    (∑ x : X, coverRatio n e g queryCount (agreement x)) /
        Fintype.card X ≤
      profile.contribution q n e g queryCount := by
  classical
  have htotal : 0 < Fintype.card X := Fintype.card_pos
  have htail (a : ℕ) (ha : a ≤ n) :
      ((tailSet agreement a).card : ℚ) / Fintype.card X ≤
        profile.tail q a := by
    apply le_min
    · apply (div_le_one (by exact_mod_cast htotal)).mpr
      exact_mod_cast Finset.card_le_card
        (Finset.subset_univ (tailSet agreement a))
    · rw [div_le_div_iff₀ (by exact_mod_cast htotal) (by exact_mod_cast hq)]
      exact_mod_cast (by simpa [Nat.mul_comm] using hdensity a ha)
  have hsum :
      (∑ x : X, coverRatio n e g queryCount (agreement x)) =
        ∑ a ∈ Finset.range (n + 1),
          coverIncrement n e g queryCount a * (tailSet agreement a).card := by
    calc
      (∑ x : X, coverRatio n e g queryCount (agreement x)) =
          ∑ x : X, ∑ a ∈ Finset.range (n + 1),
            if a ≤ agreement x then coverIncrement n e g queryCount a else 0 := by
        apply Finset.sum_congr rfl
        intro x _
        exact coverRatio_eq_increment_sum n e g queryCount agreement x
          (hagreement x)
      _ = ∑ a ∈ Finset.range (n + 1), ∑ x : X,
            if a ≤ agreement x then coverIncrement n e g queryCount a else 0 := by
        rw [Finset.sum_comm]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro a _
        rw [← Finset.sum_filter]
        simp [tailSet, mul_comm]
  rw [hsum, div_eq_mul_inv, Finset.sum_mul]
  unfold contribution
  apply Finset.sum_le_sum
  intro a ha
  have han : a ≤ n := by
    have := Finset.mem_range.mp ha
    omega
  calc
    (coverIncrement n e g queryCount a * (tailSet agreement a).card) *
        (Fintype.card X : ℚ)⁻¹ =
      coverIncrement n e g queryCount a *
        ((tailSet agreement a).card / Fintype.card X) := by
      rw [div_eq_mul_inv]
      ring
    _ ≤ coverIncrement n e g queryCount a * profile.tail q a :=
      mul_le_mul_of_nonneg_left (htail a han)
        (coverIncrement_nonnegative n e g queryCount a)

/-- Restricted layer-cake/profile-integration theorem.  It bounds the average
query-survival probability of only the selected challenges from tail bounds
at every actual agreement size. -/
theorem restricted_average_coverRatio_le_contribution
    (q n e g queryCount : ℕ) (profile : AgreementProfile n)
    (selected : Finset X) (agreement : X → ℕ) (hq : 0 < q) [Nonempty X]
    (hagreement : ∀ x ∈ selected, agreement x ≤ n)
    (hdensity : ∀ a ≤ n,
      q * (restrictedTailSet selected agreement a).card ≤
        profile.labelsAtLeast a * Fintype.card X) :
    (∑ x ∈ selected, coverRatio n e g queryCount (agreement x)) /
        Fintype.card X ≤
      profile.contribution q n e g queryCount := by
  classical
  have htotal : 0 < Fintype.card X := Fintype.card_pos
  have htail (a : ℕ) (ha : a ≤ n) :
      ((restrictedTailSet selected agreement a).card : ℚ) /
          Fintype.card X ≤ profile.tail q a := by
    apply le_min
    · apply (div_le_one (by exact_mod_cast htotal)).mpr
      exact_mod_cast Finset.card_le_card
        ((Finset.filter_subset _ _).trans (Finset.subset_univ selected))
    · rw [div_le_div_iff₀ (by exact_mod_cast htotal) (by exact_mod_cast hq)]
      exact_mod_cast (by simpa [Nat.mul_comm] using hdensity a ha)
  have hsum :
      (∑ x ∈ selected, coverRatio n e g queryCount (agreement x)) =
        ∑ a ∈ Finset.range (n + 1),
          coverIncrement n e g queryCount a *
            (restrictedTailSet selected agreement a).card := by
    calc
      (∑ x ∈ selected, coverRatio n e g queryCount (agreement x)) =
          ∑ x ∈ selected, ∑ a ∈ Finset.range (n + 1),
            if a ≤ agreement x then coverIncrement n e g queryCount a else 0 := by
        apply Finset.sum_congr rfl
        intro x hx
        exact coverRatio_eq_increment_sum n e g queryCount agreement x
          (hagreement x hx)
      _ = ∑ a ∈ Finset.range (n + 1), ∑ x ∈ selected,
            if a ≤ agreement x then coverIncrement n e g queryCount a else 0 := by
        rw [Finset.sum_comm]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro a _
        rw [← Finset.sum_filter]
        simp [restrictedTailSet, mul_comm]
  rw [hsum, div_eq_mul_inv, Finset.sum_mul]
  unfold contribution
  apply Finset.sum_le_sum
  intro a ha
  have han : a ≤ n := by
    have := Finset.mem_range.mp ha
    omega
  calc
    (coverIncrement n e g queryCount a *
        (restrictedTailSet selected agreement a).card) *
          (Fintype.card X : ℚ)⁻¹ =
      coverIncrement n e g queryCount a *
        ((restrictedTailSet selected agreement a).card / Fintype.card X) := by
      rw [div_eq_mul_inv]
      ring
    _ ≤ coverIncrement n e g queryCount a * profile.tail q a :=
      mul_le_mul_of_nonneg_left (htail a han)
        (coverIncrement_nonnegative n e g queryCount a)

end TailCounting

theorem tail_le_one (profile : AgreementProfile n) (q a : ℕ) :
    profile.tail q a ≤ 1 := min_le_left _ _

theorem tail_antitone (profile : AgreementProfile n) (q : ℕ) (hq : 0 < q)
    (hmono : Antitone profile.labelsAtLeast) :
    Antitone (profile.tail q) := by
  intro a b hab
  unfold tail
  apply min_le_min_left
  apply div_le_div_of_nonneg_right
  · exact_mod_cast hmono hab
  · positivity

end AgreementProfile

open AgreementProfile

/-- The common lift-list master expression. Coding-theoretic certificate
failure and the far-proximity cover are common; all mask dependence is in
`profile.contribution`. -/
def profiledLiftListSoundnessBound
    (q n e g queryCount failureNumerator failureDenominator : ℕ)
  (profile : AgreementProfile n) : ℚ :=
  (failureNumerator : ℚ) / failureDenominator +
    profile.contribution q n e g queryCount

/-- V2's step profile: every label is possible through the response-code
uniqueness threshold, and at most one label per lift candidate is possible
above it. -/
def checkedAgreementProfile (q L n cutoff : ℕ) :
    AgreementProfile n where
  labelsAtLeast a := if n < a then 0 else if a ≤ cutoff then q else L

theorem checkedAgreementProfile_antitone (q L n cutoff : ℕ) (hL : L ≤ q) :
    Antitone (checkedAgreementProfile q L n cutoff).labelsAtLeast := by
    intro a b hab
    by_cases hbn : n < b
    · simp [checkedAgreementProfile, hbn]
    have han : ¬n < a := fun ha ↦ hbn (ha.trans_le hab)
    simp only [checkedAgreementProfile, han, hbn, ↓reduceIte]
    by_cases hac : a ≤ cutoff
    · simp only [hac, ↓reduceIte]
      split <;> omega
    · have hbc : ¬b ≤ cutoff := fun h ↦ hac (hab.trans h)
      simp [hac, hbc]

theorem checkedAgreementProfile_tail (q L n cutoff a : ℕ)
    (hq : 0 < q) (hL : L ≤ q) (ha : a ≤ n) :
    (checkedAgreementProfile q L n cutoff).tail q a =
      if a ≤ cutoff then 1 else (L : ℚ) / q := by
  unfold AgreementProfile.tail checkedAgreementProfile
  simp only [show ¬n < a by omega, ↓reduceIte]
  split
  · simp [show (q : ℚ) ≠ 0 by positivity]
  · rw [min_eq_right]
    apply (div_le_one (by positivity)).mpr
    exact_mod_cast hL

theorem sum_coverIncrement_if_le (n e g queryCount cutoff : ℕ) :
    ∑ a ∈ Finset.range (n + 1),
      (if a ≤ cutoff then coverIncrement n e g queryCount a else 0) =
      coverRatio n e g queryCount (min n cutoff) := by
  have hfilter :
      (Finset.range (n + 1)).filter (fun a ↦ a ≤ cutoff) =
        Finset.range (min n cutoff + 1) := by
    ext a
    simp
  rw [← sum_coverIncrement n e g queryCount (min n cutoff)]
  rw [← hfilter, Finset.sum_filter]

/-- A compact certificate for a decreasing agreement tail.  Instead of
normalizing the full finite sum, a caller bounds it on three successive
ranges.  Each range is charged to a prefix of the telescoping query-cover
increments. -/
theorem contribution_le_four_ranges
    (q n e g queryCount first middle last : ℕ)
    (profile : AgreementProfile n) (u₁ u₂ u₃ : ℚ)
    (hfirst : 0 < first) (hmiddle : first ≤ middle)
    (hlast : middle ≤ last)
    (hu₁ : 0 ≤ u₁) (hu₂ : 0 ≤ u₂) (hu₃ : 0 ≤ u₃)
    (htail₁ : ∀ a ≤ n, first ≤ a → a ≤ middle → profile.tail q a ≤ u₁)
    (htail₂ : ∀ a ≤ n, middle < a → a ≤ last → profile.tail q a ≤ u₂)
    (htail₃ : ∀ a ≤ n, last < a → profile.tail q a ≤ u₃) :
    profile.contribution q n e g queryCount ≤
      coverRatio n e g queryCount (first - 1) +
      u₁ * coverRatio n e g queryCount middle +
      u₂ * coverRatio n e g queryCount last +
      u₃ * coverRatio n e g queryCount n := by
  let Δ := coverIncrement n e g queryCount
  have henvelope (a : ℕ) (ha : a ∈ Finset.range (n + 1)) :
      profile.tail q a ≤
        (if a ≤ first - 1 then 1 else 0) +
        (if a ≤ middle then u₁ else 0) +
        (if a ≤ last then u₂ else 0) + u₃ := by
    have han : a ≤ n := by simpa using Finset.mem_range.mp ha
    by_cases hafirst : a < first
    · have hprefix : a ≤ first - 1 := by omega
      have hamiddle : a ≤ middle := by omega
      have halast : a ≤ last := by omega
      have htail := tail_le_one profile q a
      simp only [hprefix, hamiddle, halast, ↓reduceIte]
      linarith
    · have hfa : first ≤ a := by omega
      by_cases hamiddle : a ≤ middle
      · have htail := htail₁ a han hfa hamiddle
        have halast : a ≤ last := by omega
        simp only [show ¬a ≤ first - 1 by omega, ↓reduceIte, hamiddle,
          halast]
        linarith
      · have hma : middle < a := by omega
        by_cases halast : a ≤ last
        · have htail := htail₂ a han hma halast
          simp only [show ¬a ≤ first - 1 by omega, ↓reduceIte,
            show ¬a ≤ middle by omega, halast]
          linarith
        · have htail := htail₃ a han (by omega)
          simp only [show ¬a ≤ first - 1 by omega, ↓reduceIte,
            show ¬a ≤ middle by omega, show ¬a ≤ last by omega]
          linarith
  have hprefix (cutoff : ℕ) (u : ℚ) :
      (∑ a ∈ Finset.range (n + 1),
          Δ a * (if a ≤ cutoff then u else 0)) =
        u * (∑ a ∈ Finset.range (n + 1),
          if a ≤ cutoff then Δ a else 0) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : a ≤ cutoff <;> simp [ha, mul_comm]
  have hweighted :
      profile.contribution q n e g queryCount ≤
        (∑ a ∈ Finset.range (n + 1),
          if a ≤ first - 1 then Δ a else 0) +
        u₁ * (∑ a ∈ Finset.range (n + 1),
          if a ≤ middle then Δ a else 0) +
        u₂ * (∑ a ∈ Finset.range (n + 1),
          if a ≤ last then Δ a else 0) +
        u₃ * (∑ a ∈ Finset.range (n + 1), Δ a) := by
    unfold contribution
    calc
      (∑ a ∈ Finset.range (n + 1), Δ a * profile.tail q a) ≤
          ∑ a ∈ Finset.range (n + 1), Δ a *
            ((if a ≤ first - 1 then 1 else 0) +
             (if a ≤ middle then u₁ else 0) +
             (if a ≤ last then u₂ else 0) + u₃) := by
        apply Finset.sum_le_sum
        intro a ha
        exact mul_le_mul_of_nonneg_left (henvelope a ha)
          (coverIncrement_nonnegative n e g queryCount a)
      _ = _ := by
        simp only [mul_add, Finset.sum_add_distrib]
        rw [hprefix (first - 1) 1, hprefix middle u₁,
          hprefix last u₂]
        simp only [one_mul]
        rw [← Finset.sum_mul]
        ring
  calc
    profile.contribution q n e g queryCount ≤ _ := hweighted
    _ = coverRatio n e g queryCount (min n (first - 1)) +
        u₁ * coverRatio n e g queryCount (min n middle) +
        u₂ * coverRatio n e g queryCount (min n last) +
        u₃ * coverRatio n e g queryCount n := by
      rw [show (∑ a ∈ Finset.range (n + 1),
            if a ≤ first - 1 then Δ a else 0) =
          coverRatio n e g queryCount (min n (first - 1)) by
        simpa [Δ] using
          sum_coverIncrement_if_le n e g queryCount (first - 1),
        show (∑ a ∈ Finset.range (n + 1),
            if a ≤ middle then Δ a else 0) =
          coverRatio n e g queryCount (min n middle) by
        simpa [Δ] using sum_coverIncrement_if_le n e g queryCount middle,
        show (∑ a ∈ Finset.range (n + 1),
            if a ≤ last then Δ a else 0) =
          coverRatio n e g queryCount (min n last) by
        simpa [Δ] using sum_coverIncrement_if_le n e g queryCount last,
        show (∑ a ∈ Finset.range (n + 1), Δ a) =
          coverRatio n e g queryCount n by
        simpa [Δ] using sum_coverIncrement n e g queryCount n]
    _ ≤ _ := by
      have h0 := coverRatio_mono n e g queryCount (min_le_right n (first - 1))
      have h1 := coverRatio_mono n e g queryCount (min_le_right n middle)
      have h2 := coverRatio_mono n e g queryCount (min_le_right n last)
      gcongr

/-- Exact checked-profile collapse.  This is the formal bridge from the
profiled master back to V2's familiar step bound. -/
theorem checkedAgreementProfile_contribution
    (q L n e g queryCount cutoff : ℕ) (hq : 0 < q) (hL : L ≤ q) :
    (checkedAgreementProfile q L n cutoff).contribution
        q n e g queryCount =
      ((L : ℚ) / q) * coverRatio n e g queryCount n +
        (1 - (L : ℚ) / q) *
          coverRatio n e g queryCount (min n cutoff) := by
  unfold contribution
  have hterm (a : ℕ) (ha : a ∈ Finset.range (n + 1)) :
      coverIncrement n e g queryCount a *
          (checkedAgreementProfile q L n cutoff).tail q a =
        ((L : ℚ) / q) * coverIncrement n e g queryCount a +
          (1 - (L : ℚ) / q) *
            (if a ≤ cutoff then coverIncrement n e g queryCount a else 0) := by
    rw [checkedAgreementProfile_tail q L n cutoff a hq hL (by
      have := Finset.mem_range.mp ha
      omega)]
    split <;> ring
  calc
    (∑ a ∈ Finset.range (n + 1),
      coverIncrement n e g queryCount a *
        (checkedAgreementProfile q L n cutoff).tail q a) =
        ∑ a ∈ Finset.range (n + 1),
          (((L : ℚ) / q) * coverIncrement n e g queryCount a +
            (1 - (L : ℚ) / q) *
              (if a ≤ cutoff then coverIncrement n e g queryCount a else 0)) := by
      apply Finset.sum_congr rfl
      exact hterm
    _ = ((L : ℚ) / q) *
          (∑ a ∈ Finset.range (n + 1), coverIncrement n e g queryCount a) +
        (1 - (L : ℚ) / q) *
          (∑ a ∈ Finset.range (n + 1),
            if a ≤ cutoff then coverIncrement n e g queryCount a else 0) := by
      simp only [Finset.sum_add_distrib, Finset.mul_sum]
    _ = _ := by
      rw [sum_coverIncrement n e g queryCount n,
        sum_coverIncrement_if_le n e g queryCount cutoff]

theorem checkedAgreementProfile_contribution_le
    (q L n e g queryCount cutoff : ℕ) (hq : 0 < q)
    (hquery : queryCount ≤ n) :
    (checkedAgreementProfile q L n cutoff).contribution
        q n e g queryCount ≤
      coverRatio n e g queryCount cutoff + (L : ℚ) / q := by
  have hfull : coverRatio n e g queryCount n = 1 := by
    unfold coverRatio hypergeometricRatio
    rw [show min n (g + n) = n by omega,
      show max (n - e - 1) n = n by omega]
    exact div_self (by
      exact_mod_cast Nat.ne_of_gt (Nat.choose_pos hquery))
  have hcutoffNonnegative : 0 ≤ coverRatio n e g queryCount cutoff := by
    unfold coverRatio hypergeometricRatio
    positivity
  by_cases hL : L ≤ q
  · rw [checkedAgreementProfile_contribution q L n e g queryCount cutoff hq hL,
      hfull]
    have hcutoff : coverRatio n e g queryCount (min n cutoff) ≤
        coverRatio n e g queryCount cutoff :=
      coverRatio_mono n e g queryCount (min_le_right _ _)
    have hnonnegative : 0 ≤ coverRatio n e g queryCount (min n cutoff) := by
      unfold coverRatio hypergeometricRatio
      positivity
    have hratio : 0 ≤ (L : ℚ) / q := by positivity
    have hratioOne : (L : ℚ) / q ≤ 1 := by
      apply (div_le_one (by positivity)).mpr
      exact_mod_cast hL
    nlinarith
  · have hcontribution :
        (checkedAgreementProfile q L n cutoff).contribution
            q n e g queryCount ≤ 1 := by
      unfold contribution
      calc
        (∑ a ∈ Finset.range (n + 1),
            coverIncrement n e g queryCount a *
              (checkedAgreementProfile q L n cutoff).tail q a) ≤
            ∑ a ∈ Finset.range (n + 1),
              coverIncrement n e g queryCount a := by
          apply Finset.sum_le_sum
          intro a _
          simpa using mul_le_of_le_one_right
            (coverIncrement_nonnegative n e g queryCount a)
            ((checkedAgreementProfile q L n cutoff).tail_le_one q a)
        _ = coverRatio n e g queryCount n :=
          sum_coverIncrement n e g queryCount n
        _ = 1 := hfull
    have hratio : 1 ≤ (L : ℚ) / q := by
      apply (one_le_div (by positivity)).mpr
      exact_mod_cast Nat.le_of_not_ge hL
    linarith

theorem checkedAgreementProfile_contribution_ge_coverRatio
    (q L n e g queryCount cutoff : ℕ) (hq : 0 < q) (hL : L ≤ q)
    (hquery : queryCount ≤ n) :
    coverRatio n e g queryCount (min n cutoff) ≤
      (checkedAgreementProfile q L n cutoff).contribution
        q n e g queryCount := by
  rw [checkedAgreementProfile_contribution q L n e g queryCount cutoff hq hL]
  have hfull : coverRatio n e g queryCount n = 1 := by
    unfold coverRatio hypergeometricRatio
    rw [show min n (g + n) = n by omega,
      show max (n - e - 1) n = n by omega]
    exact div_self (by exact_mod_cast Nat.ne_of_gt (Nat.choose_pos hquery))
  rw [hfull]
  have hcoverNonnegative :
      0 ≤ coverRatio n e g queryCount (min n cutoff) := by
    unfold coverRatio hypergeometricRatio
    positivity
  have hcoverOne : coverRatio n e g queryCount (min n cutoff) ≤ 1 := by
    unfold coverRatio hypergeometricRatio
    apply (div_le_one (by
      exact_mod_cast Nat.choose_pos hquery)).mpr
    exact_mod_cast Nat.choose_le_choose queryCount (by omega :
      max (n - e - 1) (min n (g + min n cutoff)) ≤ n)
  have hratio : 0 ≤ (L : ℚ) / q := by positivity
  nlinarith

/-- The conventional additive presentation of the checked V2 corollary. -/
def checkedLiftListSoundnessBound
    (q L n e g queryCount cutoff failureNumerator failureDenominator : ℕ) : ℚ :=
  (failureNumerator : ℚ) / failureDenominator +
    coverRatio n e g queryCount cutoff + (L : ℚ) / q

theorem profiled_checked_le_checkedLiftListSoundnessBound
    (q L n e g queryCount cutoff failureNumerator failureDenominator : ℕ)
    (hq : 0 < q) (hquery : queryCount ≤ n) :
    profiledLiftListSoundnessBound q n e g queryCount
        failureNumerator failureDenominator
        (checkedAgreementProfile q L n cutoff) ≤
      checkedLiftListSoundnessBound q L n e g queryCount cutoff
        failureNumerator failureDenominator := by
  unfold profiledLiftListSoundnessBound checkedLiftListSoundnessBound
  have hcontribution := checkedAgreementProfile_contribution_le
    q L n e g queryCount cutoff hq hquery
  linarith

/-- At the V2 uniqueness cutoff, the checked corollary is no larger than the
original maximum-cover expression. -/
theorem checkedLiftListSoundnessBound_le_liftListSoundnessBound
    (q L n e g k queryCount failureNumerator failureDenominator : ℕ)
    (hk : 0 < k) :
    checkedLiftListSoundnessBound q L n e g queryCount (2 * k - 1)
        failureNumerator failureDenominator ≤
      liftListSoundnessBound q n e g k queryCount
        failureNumerator failureDenominator L := by
  have hcover :
      max (n - e - 1) (min n (g + (2 * k - 1))) ≤
        liftListQueryCoverBound n e g k := by
    unfold liftListQueryCoverBound
    apply max_le
    · exact le_max_left _ _
    · apply (min_le_right n _).trans
      rw [show g + (2 * k - 1) = 2 * k + g - 1 by omega]
      exact le_max_right _ _
  have hratio : coverRatio n e g queryCount (2 * k - 1) ≤
      hypergeometricRatio (liftListQueryCoverBound n e g k) n queryCount := by
    unfold coverRatio hypergeometricRatio
    apply div_le_div_of_nonneg_right
    · exact_mod_cast Nat.choose_le_choose queryCount hcover
    · positivity
  unfold checkedLiftListSoundnessBound liftListSoundnessBound
  linarith

/-- Johnson/incidence list bound for unchecked masks, written directly in
agreement coordinates.  `lambda` is the maximum agreement of two distinct
response codewords (for this repository, `2*k - 1`). -/
def uncheckedAgreementListBound (n lambda a : ℕ) : ℕ :=
  CodingTheory.InterleavedJohnson.listBound
    n (n - lambda) (n - a)

theorem unchecked_denominator_eq (n lambda a : ℕ)
    (hlambda : lambda ≤ n) (ha : a ≤ n) :
    CodingTheory.InterleavedJohnson.denominator n (n - lambda) (n - a) =
      (a : ℤ) * a - n * lambda := by
  simp only [CodingTheory.InterleavedJohnson.denominator,
    Nat.cast_sub hlambda, Nat.cast_sub ha]
  ring

theorem unchecked_numerator_eq (n lambda a : ℕ)
    (hlambda : lambda ≤ a) (ha : a ≤ n) :
    n * ((n - lambda) - (n - a)) = n * (a - lambda) := by
  congr 1
  omega

theorem uncheckedAgreementListBound_eq (n lambda a : ℕ)
    (hlambda : lambda ≤ a) (ha : a ≤ n) :
    uncheckedAgreementListBound n lambda a =
      n * (a - lambda) / (a * a - n * lambda) := by
  unfold uncheckedAgreementListBound
  simp only [CodingTheory.InterleavedJohnson.listBound]
  rw [unchecked_numerator_eq n lambda a hlambda ha,
    unchecked_denominator_eq n lambda a (hlambda.trans ha) ha]
  congr 1
  exact Int.toNat_sub (a * a) (n * lambda)

/-- A polynomial certificate for a uniform unchecked Johnson-list bound. -/
theorem uncheckedAgreementListBound_le (n lambda a bound : ℕ)
    (hlambda : lambda ≤ a) (ha : a ≤ n)
    (hpositive : n * lambda < a * a)
    (hcertificate : n * (a - lambda) <
      (bound + 1) * (a * a - n * lambda)) :
    uncheckedAgreementListBound n lambda a ≤ bound := by
  rw [uncheckedAgreementListBound_eq n lambda a hlambda ha]
  apply Nat.lt_succ_iff.mp
  rw [Nat.div_lt_iff_lt_mul (by omega)]
  simpa [Nat.succ_eq_add_one, Nat.mul_comm] using hcertificate

/-- It is enough to check the polynomial Johnson-list certificate at the
left endpoint of an interval once its derivative is nonnegative there. -/
theorem uncheckedAgreementListBound_le_of_lower
    (n lambda lower a bound : ℕ)
    (hlambda : lambda ≤ lower) (hlower : lower ≤ a) (ha : a ≤ n)
    (hpositive : n * lambda < lower * lower)
    (hslope : n ≤ (bound + 1) * (2 * lower))
    (hcertificate : n * (lower - lambda) <
      (bound + 1) * (lower * lower - n * lambda)) :
    uncheckedAgreementListBound n lambda a ≤ bound := by
  apply uncheckedAgreementListBound_le n lambda a bound
  · omega
  · exact ha
  · exact hpositive.trans_le (Nat.mul_self_le_mul_self hlower)
  · have hsub : a - lambda = (lower - lambda) + (a - lower) := by omega
    rw [hsub]
    have hsquare : lower * lower + (a - lower) * (a + lower) = a * a := by
      nlinarith [Nat.sub_add_cancel hlower]
    have hdenominator :
        a * a - n * lambda =
          (lower * lower - n * lambda) + (a - lower) * (a + lower) := by
      omega
    rw [hdenominator]
    have hslope' : n ≤ (bound + 1) * (a + lower) := by
      exact hslope.trans (Nat.mul_le_mul_left (bound + 1) (by omega))
    have hstep := Nat.mul_le_mul_right (a - lower) hslope'
    nlinarith

/-- The unchecked profile obtained by using probability one below the first
positive Johnson denominator and summing the Johnson list bound over a fixed
lift list above it.  Normally `johnsonThreshold = ⌊sqrt(n*lambda)⌋ + 1`. -/
def uncheckedAgreementProfile
    (q n lambda L johnsonThreshold : ℕ) : AgreementProfile n where
  labelsAtLeast a := if n < a then 0 else
    if a < johnsonThreshold then q else
      L * uncheckedAgreementListBound n lambda a

theorem uncheckedAgreementProfile_tail_le
    (q n lambda L johnsonThreshold a bound : ℕ)
    (ha : a ≤ n) (hthreshold : johnsonThreshold ≤ a)
    (hlist : uncheckedAgreementListBound n lambda a ≤ bound) :
    (uncheckedAgreementProfile q n lambda L johnsonThreshold).tail q a ≤
      (L * bound : ℕ) / (q : ℚ) := by
  unfold AgreementProfile.tail uncheckedAgreementProfile
  simp only [show ¬n < a by omega, ↓reduceIte,
    show ¬a < johnsonThreshold by omega]
  calc
    min 1 ((↑(L * uncheckedAgreementListBound n lambda a) : ℚ) / ↑q) ≤
        (↑(L * uncheckedAgreementListBound n lambda a) : ℚ) / ↑q :=
      min_le_right _ _
    _ ≤ (↑(L * bound) : ℚ) / ↑q := by
      apply div_le_div_of_nonneg_right
      · exact_mod_cast Nat.mul_le_mul_left L hlist
      · positivity

theorem uncheckedAgreementProfile_contribution_ge_coverRatio
    (q n e g queryCount lambda L threshold : ℕ)
    (hq : 0 < q) (hthreshold : 0 < threshold) (hthresholdN : threshold ≤ n + 1) :
    coverRatio n e g queryCount (threshold - 1) ≤
      (uncheckedAgreementProfile q n lambda L threshold).contribution
        q n e g queryCount := by
  have hsubset : Finset.range threshold ⊆ Finset.range (n + 1) :=
    Finset.range_mono hthresholdN
  have htail (a : ℕ) (ha : a ∈ Finset.range threshold) :
      (uncheckedAgreementProfile q n lambda L threshold).tail q a = 1 := by
    have hat : a < threshold := Finset.mem_range.mp ha
    have han : ¬a > n := by omega
    unfold AgreementProfile.tail uncheckedAgreementProfile
    simp only [han, hat, ↓reduceIte]
    simp [show (q : ℚ) ≠ 0 by positivity]
  rw [← sum_coverIncrement n e g queryCount (threshold - 1)]
  have hrange : threshold - 1 + 1 = threshold := by omega
  rw [hrange]
  unfold AgreementProfile.contribution
  calc
    (∑ a ∈ Finset.range threshold, coverIncrement n e g queryCount a) =
        ∑ a ∈ Finset.range threshold,
          coverIncrement n e g queryCount a *
            (uncheckedAgreementProfile q n lambda L threshold).tail q a := by
      apply Finset.sum_congr rfl
      intro a ha
      rw [htail a ha, mul_one]
    _ ≤ ∑ a ∈ Finset.range (n + 1),
          coverIncrement n e g queryCount a *
            (uncheckedAgreementProfile q n lambda L threshold).tail q a := by
      apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
      intro a _ _
      exact mul_nonneg (coverIncrement_nonnegative n e g queryCount a) (by
        unfold AgreementProfile.tail
        positivity)

/-- V1's soft soundness expression. -/
def uncheckedLiftListSoundnessBound
    (q n e g queryCount failureNumerator failureDenominator
      lambda L johnsonThreshold : ℕ) : ℚ :=
  profiledLiftListSoundnessBound q n e g queryCount
    failureNumerator failureDenominator
    (uncheckedAgreementProfile q n lambda L johnsonThreshold)

end LigeroFamily
