import LigeroFamily.Soundness.EventPartition
import LigeroFamily.Soundness.EventProfile
import LigeroFamily.Soundness.PolicyProfiledMaster

/-!
# Coarse threshold-ledger view of the profiled Ligero classifier

The existing classifier stores a selected-MCA failure branch and an ordinary
agreement profile, but its `uniform_cover` field deliberately forgets whether
the ordinary cover came from the far-proximity or arithmetic branch.  This
module gives that classifier a canonical, exact threshold partition:

* selected-MCA failure (stored in the first event slot);
* nonfailure below an agreement threshold (stored in the second event slot);
* nonfailure above the threshold (exceptional-alpha tail).

This classifier-level view is coarse because `uniform_cover` has already
erased the far/near choice and selected candidate.  Nevertheless it retains
exactly the data needed by the flat replacement theorem below: a common raised
query baseline, the selected-MCA failure tail above that baseline, and the
arithmetic agreement profile.  A richer routed certificate is still needed by
a concrete Fiat--Shamir instantiation that must expose prefix dependencies.
-/

namespace LigeroFamily

variable {F Equations CheckedMask DirectMask Challenge Response : Type*}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype Equations] [DecidableEq Equations]
variable [Fintype CheckedMask] [DecidableEq CheckedMask]
variable [Fintype Challenge] [DecidableEq Challenge]
variable [Nonempty Challenge]
variable {logicalWidth r w n nw nq e g failureDenominator profileDenominator : ℕ}

variable {C : MultiplicativeCode F r w n}
variable {layout : ConstraintLayout F logicalWidth w}
variable {policy : SchemeProtocolPolicy (Equations := Equations) C layout
  Challenge Response CheckedMask DirectMask nw nq 1}
variable {oracle : SchemeOracle F CheckedMask DirectMask nw nq n 1}
variable {statement : ConstraintSystem F nw nq logicalWidth Equations}
variable {respond : Challenge → Response}
variable {failureProfile arithmeticProfile : AgreementProfile n}

namespace PolicyDoublyProfiledSoundnessClassifier

variable (classifier : PolicyDoublyProfiledSoundnessClassifier policy oracle statement
  respond failureProfile arithmeticProfile profileDenominator failureDenominator e g)

/-- Exact classifier-level trichotomy at an agreement threshold.

The inherited field names are semantic slots; at this coarse layer the first
two slots mean selected-MCA failure and ordinary low agreement, respectively.
-/
noncomputable def eventPartition (threshold : ℕ) :
    ThreeEventPartition (Challenge × QuerySet n r) where
  win pair := pair.2 ∈ classifier.acceptingQueries pair.1
  allErrors pair := pair.2 ∈ classifier.acceptingQueries pair.1 ∧
    pair.1 ∈ classifier.failure
  linearErrors pair := pair.2 ∈ classifier.acceptingQueries pair.1 ∧
    pair.1 ∉ classifier.failure ∧ classifier.agreement pair.1 ≤ threshold
  badAlpha pair := pair.2 ∈ classifier.acceptingQueries pair.1 ∧
    pair.1 ∉ classifier.failure ∧ threshold < classifier.agreement pair.1
  win_iff pair := by
    constructor
    · intro hwin
      by_cases hfailure : pair.1 ∈ classifier.failure
      · exact Or.inl ⟨hwin, hfailure⟩
      · by_cases hagreement : classifier.agreement pair.1 ≤ threshold
        · exact Or.inr (Or.inl ⟨hwin, hfailure, hagreement⟩)
        · exact Or.inr (Or.inr
            ⟨hwin, hfailure, Nat.lt_of_not_ge hagreement⟩)
    · rintro (⟨hwin, _⟩ | ⟨hwin, _, _⟩ | ⟨hwin, _, _⟩) <;> exact hwin
  all_linear_disjoint pair hall := by
    intro hlinear
    exact hlinear.2.1 hall.2
  all_bad_disjoint pair hall := by
    intro hbad
    exact hbad.2.1 hall.2
  linear_bad_disjoint pair hlinear := by
    intro hbad
    omega

/-- Exact set of nonfailure challenges above the ordinary agreement threshold. -/
noncomputable def exceptionalChallenges (threshold : ℕ) : Finset Challenge := by
  classical
  exact AgreementProfile.tailSet classifier.agreement (threshold + 1) \
    classifier.failure

/-- The profiled classifier as a flat three-event fiber ledger. -/
noncomputable def flatEventLedger (threshold : ℕ) :
    FlatEventLedger Challenge (QuerySet n r) where
  partition := classifier.eventPartition threshold
  allBudget challenge :=
    if challenge ∈ classifier.failure then
      (classifier.failureAgreement challenge).choose r else 0
  linearBudget challenge :=
    if challenge ∉ classifier.failure ∧ classifier.agreement challenge ≤ threshold then
      (max (n - e - 1)
        (min n (g + classifier.agreement challenge))).choose r else 0
  exceptional := classifier.exceptionalChallenges threshold
  all_fiber_card challenge := by
    classical
    by_cases hfailure : challenge ∈ classifier.failure
    · have hcard := classifier.acceptingQueries_card_le challenge
      have heq : eventFiber
          (classifier.eventPartition threshold).allErrors challenge =
          classifier.acceptingQueries challenge := by
        ext query
        simp [eventFiber, eventPartition, acceptingQueries, hfailure]
      rw [heq]
      simpa [hfailure] using hcard
    · simp [eventFiber, eventPartition, hfailure]
  linear_fiber_card challenge := by
    classical
    by_cases hfailure : challenge ∈ classifier.failure
    · simp [eventFiber, eventPartition, hfailure]
    · by_cases hagreement : classifier.agreement challenge ≤ threshold
      · have hcard := classifier.acceptingQueries_card_le challenge
        have heq : eventFiber
            (classifier.eventPartition threshold).linearErrors challenge =
            classifier.acceptingQueries challenge := by
          ext query
          simp [eventFiber, eventPartition, acceptingQueries, hfailure, hagreement]
        rw [heq]
        simpa [hfailure, hagreement] using hcard
      · simp [eventFiber, eventPartition, hfailure, hagreement]
  badAlpha_exceptional challenge query hbad := by
    classical
    rcases hbad with ⟨_hwin, hfailure, hagreement⟩
    apply Finset.mem_sdiff.mpr
    constructor
    · simpa [AgreementProfile.tailSet] using hagreement
    · exact hfailure

set_option maxHeartbeats 2000000 in
omit [Fintype F] [DecidableEq F] [Fintype Equations] [DecidableEq Equations]
    [DecidableEq CheckedMask] [Nonempty Challenge] in
/-- The ledger's winning set is exactly the set of accepting challenge/query
pairs counted by the existing classifier. -/
theorem eventPartition_winSet_eq (threshold : ℕ) :
    (classifier.eventPartition threshold).winSet =
      Finset.univ.filter fun pair : Challenge × QuerySet n r =>
        pair.2 ∈ classifier.acceptingQueries pair.1 := by
  classical
  ext pair
  simp [ThreeEventPartition.winSet, eventPartition]

omit [Fintype F] [DecidableEq F] [Fintype Equations] [DecidableEq Equations]
    [DecidableEq CheckedMask] [Nonempty Challenge] in
/-- Finite flat bound exposed through the coarse three-event interface. -/
theorem acceptingPairs_card_le_eventLedger (threshold : ℕ) :
    (Finset.univ.filter fun pair : Challenge × QuerySet n r =>
      pair.2 ∈ classifier.acceptingQueries pair.1).card ≤
      (∑ challenge,
        (classifier.flatEventLedger threshold).allBudget challenge) +
      (∑ challenge,
        (classifier.flatEventLedger threshold).linearBudget challenge) +
      (classifier.exceptionalChallenges threshold).card *
        Fintype.card (QuerySet n r) := by
  rw [← classifier.eventPartition_winSet_eq threshold]
  convert (classifier.flatEventLedger threshold).win_card_le using 1 <;>
    simp [flatEventLedger]

omit [Fintype F] [DecidableEq F] [Fintype Equations] [DecidableEq Equations]
    [DecidableEq CheckedMask] in
/-- Flat soundness with the shared query baseline subtracted from the
selected-MCA failure profile.

The arithmetic agreement is raised to `baselineAgreement`.  The hypotheses
say that doing so costs nothing in its profile below that level.  On a
selected-MCA failure challenge, this raised arithmetic cover pays the common
baseline and only the remaining proximity-cover excess is charged to the
failure profile.  Thus the baseline is not paid twice.
-/
theorem acceptanceRate_le_eventPartition
    (baselineAgreement : ℕ)
    (hprofile : 0 < profileDenominator)
    (hfailureDenominator : 0 < failureDenominator)
    (hquery : r ≤ n) (hbaselineAgreement : baselineAgreement ≤ n)
    (hprofileFloor : ∀ a ≤ baselineAgreement,
      profileDenominator ≤ arithmeticProfile.labelsAtLeast a) :
    classifier.acceptanceRate ≤
      failureProfile.excessContribution failureDenominator n n 0 r
        (max (n - e - 1) (min n (g + baselineAgreement))) +
      arithmeticProfile.contribution profileDenominator n e g r := by
  classical
  let baselineCover := max (n - e - 1) (min n (g + baselineAgreement))
  -- On a failure challenge the failure excess needs only the shared
  -- arithmetic baseline.  Actual arithmetic agreement is retained solely on
  -- the disjoint nonfailure branch.
  let partitionedAgreement := fun challenge : Challenge =>
    if challenge ∈ classifier.failure then baselineAgreement
    else max baselineAgreement (classifier.agreement challenge)
  have hchallenge : 0 < Fintype.card Challenge := Fintype.card_pos
  have hqueries : 0 < n.choose r := Nat.choose_pos hquery
  have hbaselineCover : baselineCover ≤ n := by
    dsimp [baselineCover]
    exact max_le (by omega) (min_le_left _ _)
  have hpartitionedAgreement : ∀ challenge,
      partitionedAgreement challenge ≤ n := by
    intro challenge
    by_cases hfailure : challenge ∈ classifier.failure
    · simpa [partitionedAgreement, hfailure] using hbaselineAgreement
    · simpa [partitionedAgreement, hfailure] using
        max_le hbaselineAgreement (classifier.agreement_le challenge)
  have hpartitionedDensity : ∀ a ≤ n,
      profileDenominator *
          (AgreementProfile.tailSet partitionedAgreement a).card ≤
        arithmeticProfile.labelsAtLeast a * Fintype.card Challenge := by
    intro a ha
    by_cases habaseline : a ≤ baselineAgreement
    · calc
        profileDenominator *
            (AgreementProfile.tailSet partitionedAgreement a).card ≤
          profileDenominator * Fintype.card Challenge :=
            Nat.mul_le_mul_left _ (Finset.card_le_card
              (Finset.subset_univ _))
        _ ≤ arithmeticProfile.labelsAtLeast a * Fintype.card Challenge :=
          Nat.mul_le_mul_right _ (hprofileFloor a habaseline)
    · have htailSubset :
          AgreementProfile.tailSet partitionedAgreement a ⊆
            AgreementProfile.tailSet classifier.agreement a := by
        intro challenge hchallenge
        simp only [AgreementProfile.tailSet, Finset.mem_filter,
          Finset.mem_univ, true_and] at hchallenge ⊢
        by_cases hfailure : challenge ∈ classifier.failure
        · simp [partitionedAgreement, hfailure] at hchallenge
          omega
        · simp [partitionedAgreement, hfailure] at hchallenge
          omega
      exact (Nat.mul_le_mul_left profileDenominator
          (Finset.card_le_card htailSubset)).trans
        (classifier.agreement_density a ha)
  have hbaseCoverEq :
      AgreementProfile.coverRatio n n 0 r baselineCover =
        AgreementProfile.coverRatio n e g r baselineAgreement := by
    simp [AgreementProfile.coverRatio, baselineCover, hbaselineCover]
  have hperChallenge (challenge : Challenge) :
      ((classifier.acceptingQueries challenge).card : ℚ) / n.choose r ≤
        (if challenge ∈ classifier.failure then
          AgreementProfile.coverExcess n n 0 r baselineCover
            (classifier.failureAgreement challenge)
        else 0) +
          AgreementProfile.coverRatio n e g r
            (partitionedAgreement challenge) := by
    have hcard := classifier.acceptingQueries_card_le challenge
    by_cases hfailure : challenge ∈ classifier.failure
    · simp only [hfailure, ↓reduceIte] at hcard ⊢
      have hratio : ((classifier.acceptingQueries challenge).card : ℚ) /
          n.choose r ≤
          AgreementProfile.coverRatio n n 0 r
            (classifier.failureAgreement challenge) := by
        have hagreement := classifier.failureAgreement_le challenge hfailure
        have hchoose : ((classifier.acceptingQueries challenge).card : ℚ) /
            n.choose r ≤
            (((classifier.failureAgreement challenge).choose r : ℕ) : ℚ) /
              n.choose r := by
          apply div_le_div_of_nonneg_right
          · exact_mod_cast hcard
          · positivity
        simpa [AgreementProfile.coverRatio, hypergeometricRatio, hagreement]
          using hchoose
      have hfailureMono := AgreementProfile.coverRatio_mono n n 0 r
        (le_max_right baselineCover (classifier.failureAgreement challenge))
      calc
        ((classifier.acceptingQueries challenge).card : ℚ) / n.choose r
            ≤ AgreementProfile.coverRatio n n 0 r
                (classifier.failureAgreement challenge) := hratio
        _ ≤ AgreementProfile.coverRatio n n 0 r
              (max baselineCover (classifier.failureAgreement challenge)) :=
            hfailureMono
        _ = AgreementProfile.coverExcess n n 0 r baselineCover
              (classifier.failureAgreement challenge) +
            AgreementProfile.coverRatio n n 0 r baselineCover := by
              unfold AgreementProfile.coverExcess
              ring
        _ = AgreementProfile.coverExcess n n 0 r baselineCover
              (classifier.failureAgreement challenge) +
            AgreementProfile.coverRatio n e g r baselineAgreement := by
              rw [hbaseCoverEq]
        _ = AgreementProfile.coverExcess n n 0 r baselineCover
              (classifier.failureAgreement challenge) +
            AgreementProfile.coverRatio n e g r
              (partitionedAgreement challenge) := by
            simp [partitionedAgreement, hfailure]
    · simp only [hfailure, ↓reduceIte, zero_add] at hcard ⊢
      have hratio : ((classifier.acceptingQueries challenge).card : ℚ) /
          n.choose r ≤
          AgreementProfile.coverRatio n e g r
            (classifier.agreement challenge) := by
        apply div_le_div_of_nonneg_right
        · exact_mod_cast hcard
        · positivity
      exact hratio.trans (by
        simpa [partitionedAgreement, hfailure] using
          AgreementProfile.coverRatio_mono n e g r
            (le_max_right baselineAgreement (classifier.agreement challenge)))
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    fun challenge _ => hperChallenge challenge
  have hfailure :=
    AgreementProfile.restricted_average_coverExcess_le_excessContribution
      failureDenominator n n 0 r baselineCover failureProfile
      classifier.failure classifier.failureAgreement hfailureDenominator
      hbaselineCover classifier.failureAgreement_le
      classifier.failureAgreement_density
  have harithmetic := AgreementProfile.average_coverRatio_le_contribution
    profileDenominator n e g r arithmeticProfile partitionedAgreement hprofile
      hpartitionedAgreement hpartitionedDensity
  have hfailureSum :
      (∑ challenge : Challenge,
          if challenge ∈ classifier.failure then
            AgreementProfile.coverExcess n n 0 r baselineCover
              (classifier.failureAgreement challenge)
          else 0) =
        ∑ challenge ∈ classifier.failure,
          AgreementProfile.coverExcess n n 0 r baselineCover
            (classifier.failureAgreement challenge) := by
    rw [← Finset.sum_filter]
    apply Finset.sum_congr
    · ext challenge
      simp
    · intro challenge _
      rfl
  have hsumQueries :
      (∑ challenge : Challenge,
        ((classifier.acceptingQueries challenge).card : ℚ) / n.choose r) =
      (∑ challenge : Challenge,
        ((classifier.acceptingQueries challenge).card : ℚ)) / n.choose r := by
    simp only [div_eq_mul_inv, Finset.sum_mul]
  change classifier.acceptanceRate ≤
    failureProfile.excessContribution failureDenominator n n 0 r
      baselineCover +
    arithmeticProfile.contribution profileDenominator n e g r
  unfold PolicyDoublyProfiledSoundnessClassifier.acceptanceRate
  rw [show (∑ challenge,
        (classifier.acceptingQueries challenge).card : ℚ) /
          (Fintype.card Challenge * n.choose r) =
      (∑ challenge,
        ((classifier.acceptingQueries challenge).card : ℚ) / n.choose r) /
          Fintype.card Challenge by
      rw [hsumQueries, div_div]
      congr 1
      ring]
  rw [Finset.sum_add_distrib, hfailureSum] at hsum
  have hsumDiv :
      (∑ challenge,
        ((classifier.acceptingQueries challenge).card : ℚ) / n.choose r) /
          Fintype.card Challenge ≤
        (∑ challenge ∈ classifier.failure,
          AgreementProfile.coverExcess n n 0 r baselineCover
            (classifier.failureAgreement challenge)) /
              Fintype.card Challenge +
        (∑ challenge, AgreementProfile.coverRatio n e g r
          (partitionedAgreement challenge)) /
            Fintype.card Challenge := by
    rw [div_le_iff₀ (by exact_mod_cast hchallenge)]
    calc
      _ ≤ (∑ challenge ∈ classifier.failure,
            AgreementProfile.coverExcess n n 0 r baselineCover
              (classifier.failureAgreement challenge)) +
          ∑ challenge, AgreementProfile.coverRatio n e g r
            (partitionedAgreement challenge) := by
        simpa [mul_assoc] using hsum
      _ = ((∑ challenge ∈ classifier.failure,
            AgreementProfile.coverExcess n n 0 r baselineCover
              (classifier.failureAgreement challenge)) /
                Fintype.card Challenge +
          (∑ challenge, AgreementProfile.coverRatio n e g r
            (partitionedAgreement challenge)) /
                Fintype.card Challenge) * Fintype.card Challenge := by
        field_simp
  linarith

omit [Fintype F] [DecidableEq F] [Fintype Equations] [DecidableEq Equations]
    [DecidableEq CheckedMask] in
/-- Strategy-uniform form of the exact event-partition bound.  This is the
uniform interface for each fixed auxiliary datum: the response may be an
arbitrary function of the batching challenge,
but the shared query baseline is still paid only once. -/
theorem strategyUniform_acceptingPairs_density_le_eventPartition
    {Data : Type*}
    (respondBy : Data → Challenge → Response)
    (classifier : ∀ data,
      PolicyDoublyProfiledSoundnessClassifier policy oracle statement
        (respondBy data) failureProfile arithmeticProfile profileDenominator
          failureDenominator e g)
    (baselineAgreement : ℕ)
    (hprofile : 0 < profileDenominator)
    (hfailureDenominator : 0 < failureDenominator)
    (hquery : r ≤ n) (hbaselineAgreement : baselineAgreement ≤ n)
    (hprofileFloor : ∀ a ≤ baselineAgreement,
      profileDenominator ≤ arithmeticProfile.labelsAtLeast a)
    (data : Data) :
    (strategyAcceptingPairs (policy := policy) (oracle := oracle)
      (statement := statement) (respondBy data)).card /
        (Fintype.card (QuerySet n r) * Fintype.card Challenge) ≤
      failureProfile.excessContribution failureDenominator n n 0 r
          (max (n - e - 1) (min n (g + baselineAgreement))) +
        arithmeticProfile.contribution profileDenominator n e g r := by
  classical
  let current := classifier data
  have hevent :
      (strategyAcceptingPairs (policy := policy) (oracle := oracle)
        (statement := statement) (respondBy data)).card =
        current.acceptingPairs.card := by
    let left := strategyAcceptingPairs (policy := policy) (oracle := oracle)
      (statement := statement) (respondBy data)
    let right := current.acceptingPairs
    let swap : (↥left) ≃ (↥right) := {
      toFun := fun pair => ⟨(pair.1.2, pair.1.1), by
        have hp := (Finset.mem_filter.mp pair.2).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩⟩
      invFun := fun pair => ⟨(pair.1.2, pair.1.1), by
        have hp := (Finset.mem_filter.mp pair.2).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    calc
      left.card = Fintype.card ↥left := by simp
      _ = Fintype.card ↥right := Fintype.card_congr swap
      _ = right.card := by simp
  rw [hevent, mul_comm, current.acceptingPairs_density_eq_acceptanceRate]
  exact current.acceptanceRate_le_eventPartition baselineAgreement hprofile
    hfailureDenominator hquery hbaselineAgreement hprofileFloor

end PolicyDoublyProfiledSoundnessClassifier

end LigeroFamily
