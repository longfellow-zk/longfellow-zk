import LfzkV1.LigeroHighMass125Lift

/-!
# Combined charge for scalar Ligero V1 high responses

The high response family can include an unsatisfying lift even if another
candidate satisfies the system. The joint bound also bounds each fixed
response's opening probability when that response appears before batching.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace LfzkV1.LigeroHighMass125

open Finset LigeroFamily LigeroFamily.AgreementProfile Ligero.V1
open CodingTheory MultiplicativeCode
open scoped Classical

/-- Total high-response upper bound. The first two terms charge the selected
MCA peak and midpoint. The second fraction charges offsets of at most two
candidate tableaux, using the base-code distance for the smaller peak. -/
def highMassBound (q n k d g r a L failureDenominator : ℕ)
    (profile : AgreementProfile n) : ℚ :=
  (truncateBelow profile a).contribution failureDenominator n n 0 r +
  (L : ℚ) * hypergeometricRatio ((n + (2 * k - 1)) / 2) n r * profile.tail failureDenominator a +
  (1 + hypergeometricRatio ((n + (n - d)) / 2 + g) n r +
    2 * (L : ℚ) * hypergeometricRatio ((n + (2 * k - 1) + g) / 2) n r) / q

variable {F Equations : Type*} [Field F] [Fintype F] [DecidableEq F]
variable [Fintype Equations] [DecidableEq Equations]
variable {r w n nw nq e g d a L : ℕ}
variable {C : MultiplicativeCode F r w n}
variable (oracle : Oracle F nw nq n 1)
variable (statement : ConstraintSystem F nw nq w Equations)

local notation "Challenge" => SchemeChallenge F NoMask nw nq 1 Equations
local notation "Reply" => Response F r w n 1
local notation "Lift" => SchemeLiftCandidate C oracle (e + g)
local notation "v1Policy" => SchemeVerifier.policy (Equations := Equations) (nw := nw)
  (nq := nq) (repetitions := 1) C scheme

noncomputable def badLifts (e g : ℕ) :
    Finset (SchemeLiftCandidate C oracle (e + g)) :=
  univ.filter fun candidate => ¬statement.Satisfies candidate.decodedMessages

/-- No-lift high responses and high responses supported by a bad lift. -/
noncomputable def badHighResponses (a e g : ℕ) (c : Challenge) : Finset Reply :=
  noLiftResponses (C := C) oracle statement a g c ∪
    (badLifts (C := C) oracle statement e g).biUnion fun x =>
      liftedResponses statement x a g c

/-- Outside the bad high family, any accepting high response has a satisfying
punctured lift among the fixed radius candidates. -/
theorem satisfying_lift_of_not_mem_badHighResponses
    (hmin : HasMinimumDistanceAtLeast C.baseCode d) (hradius : e + g < d)
    (ha : n - e ≤ a) {c : Challenge} {u : Reply}
    (hhigh : u ∈ policyResponseAgreementList v1Policy oracle statement c a)
    (hgood : u ∉ badHighResponses (C := C) oracle statement a e g c) :
    ∃ x : Lift,
      statement.Satisfies x.decodedMessages ∧
      x.proximityRow (c 0).proximity = u.proximity 0 ∧
      (x.remainingBadColumns (c 0).proximity (u.proximity 0)).card ≤ g := by
  by_cases hlift : Nonempty (SchemeGLiftWitness C oracle (c 0).proximity (u.proximity 0) g)
  · obtain ⟨lift⟩ := hlift
    obtain ⟨⟨query, hpass⟩, hagree⟩ := (mem_filter.mp hhigh).2
    have hprox := columns_subset_proximity (C := C) oracle statement c u
    have hcard : a ≤ (schemeProximityAgreement oracle (c 0).proximity (u.proximity 0)).card :=
      hagree.trans (card_le_card hprox)
    have hdist := schemeProximity_partition oracle (c 0).proximity (u.proximity 0)
    have hclose : (schemeProximityDisagreement oracle (c 0).proximity (u.proximity 0)).card ≤ e :=
      by omega
    obtain ⟨x, hrow, hremain⟩ := lift.exists_schemeLiftCandidate (hpass 0).1.1 hclose hmin hradius
    refine ⟨x, ?_, hrow, hremain⟩
    by_contra hbad
    apply hgood
    exact mem_union_right _ (mem_biUnion.mpr ⟨x, mem_filter.mpr ⟨mem_univ _, hbad⟩,
      mem_filter.mpr ⟨hhigh, hrow, hremain⟩⟩)
  · exact (hgood (mem_union_left _ (mem_filter.mpr ⟨hhigh, hlift⟩))).elim

/-- An accepting high response outside the bad high event identifies a
satisfying candidate compatible with its actual opened columns. -/
theorem satisfying_compatible_lift_of_accepts_high
    (hmin : HasMinimumDistanceAtLeast C.baseCode d) (hradius : e + g < d)
    (ha : n - e ≤ a) {c : Challenge} {u : Reply} {query : QuerySet n r}
    (hpass : (v1Policy).accepts statement c u query (openSchemeOracle oracle query))
    (hhigh : a ≤ (columns (C := C) oracle statement c u).card)
    (hgood : u ∉ badHighResponses (C := C) oracle statement a e g c) :
    ∃ x : Lift, statement.Satisfies x.decodedMessages ∧
      LiftOpening125.Compatible x query g := by
  have hmem : u ∈ policyResponseAgreementList v1Policy oracle statement c a :=
    mem_filter.mpr ⟨mem_univ _, ⟨query, hpass⟩, hhigh⟩
  obtain ⟨x, hsat, _, hremaining⟩ :=
    satisfying_lift_of_not_mem_badHighResponses oracle statement hmin hradius ha hmem hgood
  exact ⟨x, hsat, LiftOpening125.compatible_of_remainingBadColumns (hpass 0).1 hremaining⟩

/-- Uniform average over all high responses that have no punctured lift or
that admit an unsatisfying punctured lift. The list certificate depends only
on the committed oracle, and allows the statement to have satisfying lifts. -/
theorem badHigh_average_mass_le
    [Nonempty (SchemeTestedRow NoMask nw nq 1)]
    {outerBound : ℕ} {localBound : ℕ → ℕ}
    (hmin : HasMinimumDistanceAtLeast C.baseCode d)
    (conditions : IntegratedSelectedMCALineConditions C.baseCode
      (Fintype.card F) e g d outerBound localBound)
    (ha : n - e ≤ a) (hlarge : 2 * C.k - 1 < a - g)
    (hfamily : UniformFamilyBound n (a - g) (2 * C.k - 1) L)
    (hlifts : Fintype.card Lift ≤ 2) :
    (∑ c : Challenge, ∑ u ∈ badHighResponses (C := C) oracle statement a e g c,
      hypergeometricRatio (columns (C := C) oracle statement c u).card n r) /
        Fintype.card Challenge ≤
      highMassBound (Fintype.card F) n C.k d g r a L
        (SchemeSelectedMCA.selectedMCAOptimizedFailureDenominator (Fintype.card F) g)
        (SchemeSelectedMCA.selectedMCAOptimizedIntegratedFailureProfile
          (Fintype.card F) n e g d outerBound localBound) := by
  classical
  let weight (c : Challenge) (u : Reply) := hypergeometricRatio
    (columns (C := C) oracle statement c u).card n r
  let nolift := noLiftResponses (C := C) oracle statement a g
  let bad := badLifts (C := C) oracle statement e g
  let lift (x : Lift) := liftedResponses statement x a g
  let peak (x : Lift) := hypergeometricRatio (min n ((LiftOpening125.agreement x).card + g)) n r
  let mid := (L : ℚ) * hypergeometricRatio ((n + (2 * C.k - 1) + g) / 2) n r
  have hpoint (c : Challenge) :
      ∑ u ∈ badHighResponses (C := C) oracle statement a e g c, weight c u ≤
        (∑ u ∈ nolift c, weight c u) + ∑ x ∈ bad, ∑ u ∈ lift x c, weight c u := by
    have hweight : ∀ u, 0 ≤ weight c u := fun u => opening_nonneg _
    exact (sum_union_le hweight).trans
      (add_le_add le_rfl (sum_biUnion_le bad (fun x => lift x c) hweight))
  have hsum : (∑ c : Challenge, ∑ u ∈ badHighResponses (C := C) oracle statement a e g c,
      weight c u) / Fintype.card Challenge ≤
      (∑ c : Challenge, ∑ u ∈ nolift c, weight c u) / Fintype.card Challenge +
      ∑ x ∈ bad, (∑ c : Challenge, ∑ u ∈ lift x c, weight c u) / Fintype.card Challenge := by
    refine (div_le_div_of_nonneg_right (sum_le_sum fun c _ => hpoint c) (by positivity)).trans_eq ?_
    rw [sum_add_distrib, add_div]
    congr 1
    rw [sum_comm]
    simp only [div_eq_mul_inv, sum_mul]
  have hcard : bad.card ≤ 2 :=
    (card_le_univ (s := bad)).trans hlifts
  have hmid : 0 ≤ mid := mul_nonneg (by positivity) (opening_nonneg _)
  have hpeak : ∑ x ∈ bad, peak x ≤
      1 + hypergeometricRatio ((n + (n - d)) / 2 + g) n r := by
    exact two_candidate_peaks_le bad LiftOpening125.agreement hcard
      (fun _ _ _ _ hne => LiftOpening125.agreement_inter_card_le hmin hne)
  have hlift : (∑ x ∈ bad, (∑ c : Challenge, ∑ u ∈ lift x c, weight c u) / Fintype.card Challenge) ≤
      (1 + hypergeometricRatio ((n + (n - d)) / 2 + g) n r + 2 * mid) / Fintype.card F := by
    calc
      _ ≤ ∑ x ∈ bad, (peak x + mid) / Fintype.card F := by
        apply sum_le_sum
        intro x hx
        exact lifted_average_mass_le statement x (mem_filter.mp hx).2 hlarge hfamily
      _ = ((∑ x ∈ bad, peak x) + (bad.card : ℚ) * mid) / Fintype.card F := by
        simp only [div_eq_mul_inv, ← sum_mul, sum_add_distrib, sum_const, nsmul_eq_mul]
      _ ≤ _ := div_le_div_of_nonneg_right
        (add_le_add hpeak (mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hmid)) (by positivity)
  have hnone := noLift_average_mass_le (C := C) (a := a) oracle statement hmin conditions ha
    (hlarge.trans_le (Nat.sub_le _ _)) (hfamily.of_le_size (Nat.sub_le _ _) hlarge)
  refine hsum.trans ?_
  unfold highMassBound
  simpa only [mid, mul_assoc] using (add_le_add hnone hlift)

/-- Opening probability of the actual verifier against one complete response
and a uniform set of columns. -/
noncomputable def openingRate (c : Challenge) (u : Reply) : ℚ :=
  (↑(univ.filter (fun query : QuerySet n r =>
    (v1Policy).accepts statement c u query (openSchemeOracle oracle query))).card : ℚ) /
    n.choose r

/-- The average actual opening mass is bounded by the corresponding
agreement-set mass. Each response has its own opening rate. -/
theorem opening_average_le_agreement_average (replies : Challenge → Finset Reply) :
    (∑ c : Challenge, ∑ u ∈ replies c, openingRate (C := C) oracle statement c u) /
        Fintype.card Challenge ≤
      (∑ c : Challenge, ∑ u ∈ replies c,
        hypergeometricRatio (columns (C := C) oracle statement c u).card n r) /
        Fintype.card Challenge := by
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact sum_le_sum fun c _ =>
    sum_le_sum fun u _ => fixed_response_opening_density (C := C) oracle statement c u

/-- The first-opening case fixes one response before the batching answer.
Its contribution is a summand of the joint high-response opening mass. -/
theorem fixed_opening_average_le {replies : Challenge → Finset Reply} (u : Reply) :
    (∑ c : Challenge, (if u ∈ replies c then openingRate (C := C) oracle statement c u else 0)) /
        Fintype.card Challenge ≤
      (∑ c : Challenge, ∑ v ∈ replies c, openingRate (C := C) oracle statement c v) /
        Fintype.card Challenge := by
  classical
  apply div_le_div_of_nonneg_right _ (by positivity)
  apply sum_le_sum
  intro c _
  have hnonneg (v : Reply) : 0 ≤ openingRate (C := C) oracle statement c v := by
    unfold openingRate
    positivity
  split_ifs with hu
  · exact single_le_sum (fun v _ => hnonneg v) hu
  · exact sum_nonneg fun v _ => hnonneg v

end LfzkV1.LigeroHighMass125
