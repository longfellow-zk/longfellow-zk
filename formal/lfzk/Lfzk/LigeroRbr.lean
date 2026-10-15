import LigeroFamily.Soundness.PolicyProfiledMaster

/-!
# Round-by-round soundness of one Ligero layer

The soundness theorems in this development are *flat*: they bound
`acceptanceRate` over the challenge and the query set jointly.  Fiat–Shamir cannot
consume that — a non-interactive prover grinds each hash separately, so what a
compiler needs is a bound per round, against an adversary that may retry any
partial transcript.

Round-by-round soundness supplies it.  A **state function** marks each partial
transcript doomed or not, and doom may only be escaped by a rare challenge.  For
one Ligero layer the two stages are:

* after the commitment — doomed when no member of the oracle's lift list
  satisfies the statement, i.e. `NoDecodedSolution`;
* after the challenge — doomed when the challenge is outside the certificate's
  failure set *and* its agreement is at most a chosen threshold `θ`.

Nothing new has to be proved about Ligero.  Both obligations are already fields
of `PolicyDoublyProfiledSoundnessClassifier`, which the existing analysis
constructs; they were simply integrated into a single expression rather than
kept apart.  This file keeps them apart.

## The one real cost

`AgreementProfile.contribution` integrates the query-cover ratio against the
whole agreement profile.  A round-by-round statement must name a single
threshold `θ` and take the cover ratio *there*, so it keeps one point of that
curve instead of the integral.  At the certified grid the profile is one
dominant band plus tails with coefficients around `2^-116` (the rows of
`Gero.Concrete`, in the sibling `gero` development), so choosing `θ` at the
dominant band loses almost nothing — but it is a genuine loss, and it is the
price of a statement that survives Fiat–Shamir.
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

/-- **The state function's second stage**: a challenge is doomed at threshold `θ` when the lift
applies to it and its agreement is small. -/
def DoomedAfter (θ : ℕ) (challenge : Challenge) : Prop :=
  challenge ∉ classifier.failure ∧ classifier.agreement challenge ≤ θ

/-- The challenges that escape doom: the certificate's failures, plus those whose agreement
exceeds the threshold. -/
noncomputable def escaping (θ : ℕ) : Finset Challenge := by
  classical
  exact classifier.failure ∪ AgreementProfile.tailSet classifier.agreement (θ + 1)

omit [Fintype F] [DecidableEq F] [Fintype Equations] [DecidableEq Equations]
    [DecidableEq CheckedMask] [Nonempty Challenge] in
theorem not_doomedAfter_mem_escaping {θ : ℕ} {challenge : Challenge}
    (h : ¬ classifier.DoomedAfter θ challenge) : challenge ∈ classifier.escaping θ := by
  classical
  rw [DoomedAfter, not_and_or] at h
  rcases h with hfail | hag
  · exact Finset.mem_union_left _ (by simpa using hfail)
  · refine Finset.mem_union_right _ ?_
    simpa [AgreementProfile.tailSet] using Nat.lt_of_not_le hag

omit [Fintype F] [DecidableEq F] [Fintype Equations] [DecidableEq Equations]
    [DecidableEq CheckedMask] [Nonempty Challenge] in
/-- **Doom preservation at the query round.**

From a doomed challenge the accepting queries occupy at most a `coverRatio n e g r θ` fraction —
*whatever the prover answered*, since `respond` is arbitrary and the cover is built from the
transcript it produced.  This is the round-by-round obligation that Fiat–Shamir grinds against,
and it is `acceptingQueries_card_le` with the threshold substituted for the actual agreement. -/
theorem query_density_le_of_doomedAfter (θ : ℕ) (challenge : Challenge)
    (hdoom : classifier.DoomedAfter θ challenge) :
    ((classifier.acceptingQueries challenge).card : ℚ) / (n.choose r)
      ≤ AgreementProfile.coverRatio n e g r θ := by
  classical
  obtain ⟨hfail, hag⟩ := hdoom
  have hcard := classifier.acceptingQueries_card_le challenge
  simp only [hfail, if_false] at hcard
  have hmono : max (n - e - 1) (min n (g + classifier.agreement challenge))
      ≤ max (n - e - 1) (min n (g + θ)) := by
    apply max_le_max (le_refl _)
    exact min_le_min (le_refl _) (by omega)
  have hchoose : (classifier.acceptingQueries challenge).card
      ≤ (max (n - e - 1) (min n (g + θ))).choose r :=
    hcard.trans (Nat.choose_le_choose r hmono)
  rw [AgreementProfile.coverRatio, hypergeometricRatio]
  exact div_le_div_of_nonneg_right (by exact_mod_cast hchoose) (by positivity)

omit [Fintype F] [DecidableEq F] [Fintype Equations] [DecidableEq Equations]
    [DecidableEq CheckedMask] in
/-- **Doom preservation at the challenge round.**

The density of challenges that escape doom is at most the failure profile's total mass plus the
arithmetic profile's tail above the threshold.  Both come straight from the classifier's density
fields — the first at `a = 0`, the second at `a = θ + 1`. -/
theorem escaping_density_le (θ : ℕ) (hθ : θ + 1 ≤ n)
    (hfd : 0 < failureDenominator) (hpd : 0 < profileDenominator) :
    ((classifier.escaping θ).card : ℚ) / Fintype.card Challenge
      ≤ (failureProfile.labelsAtLeast 0 : ℚ) / failureDenominator
        + (arithmeticProfile.labelsAtLeast (θ + 1) : ℚ) / profileDenominator := by
  classical
  have hchal : (0 : ℚ) < Fintype.card Challenge := by
    exact_mod_cast Fintype.card_pos
  -- the failure set, at agreement threshold zero
  have hfailEq : AgreementProfile.restrictedTailSet classifier.failure
      classifier.failureAgreement 0 = classifier.failure := by
    simp [AgreementProfile.restrictedTailSet]
  have hfailCard : (failureDenominator : ℚ) * (classifier.failure.card : ℚ)
      ≤ (failureProfile.labelsAtLeast 0 : ℚ) * Fintype.card Challenge := by
    have := classifier.failureAgreement_density 0 (Nat.zero_le n)
    rw [hfailEq] at this
    exact_mod_cast this
  -- the agreement tail, at threshold `θ + 1`
  have htailCard : (profileDenominator : ℚ) *
      ((AgreementProfile.tailSet classifier.agreement (θ + 1)).card : ℚ)
      ≤ (arithmeticProfile.labelsAtLeast (θ + 1) : ℚ) * Fintype.card Challenge := by
    have := classifier.agreement_density (θ + 1) hθ
    exact_mod_cast this
  have hunion : ((classifier.escaping θ).card : ℚ)
      ≤ (classifier.failure.card : ℚ)
        + ((AgreementProfile.tailSet classifier.agreement (θ + 1)).card : ℚ) := by
    have := Finset.card_union_le classifier.failure
      (AgreementProfile.tailSet classifier.agreement (θ + 1))
    exact_mod_cast this
  have hfdQ : (0 : ℚ) < failureDenominator := by exact_mod_cast hfd
  have hpdQ : (0 : ℚ) < profileDenominator := by exact_mod_cast hpd
  have h1 : (classifier.failure.card : ℚ) / Fintype.card Challenge
      ≤ (failureProfile.labelsAtLeast 0 : ℚ) / failureDenominator := by
    rw [div_le_div_iff₀ hchal hfdQ]
    nlinarith [hfailCard]
  have h2 : ((AgreementProfile.tailSet classifier.agreement (θ + 1)).card : ℚ)
      / Fintype.card Challenge
      ≤ (arithmeticProfile.labelsAtLeast (θ + 1) : ℚ) / profileDenominator := by
    rw [div_le_div_iff₀ hchal hpdQ]
    nlinarith [htailCard]
  calc ((classifier.escaping θ).card : ℚ) / Fintype.card Challenge
      ≤ ((classifier.failure.card : ℚ)
          + ((AgreementProfile.tailSet classifier.agreement (θ + 1)).card : ℚ))
            / Fintype.card Challenge :=
        div_le_div_of_nonneg_right hunion (le_of_lt hchal)
    _ = (classifier.failure.card : ℚ) / Fintype.card Challenge
          + ((AgreementProfile.tailSet classifier.agreement (θ + 1)).card : ℚ)
            / Fintype.card Challenge := by ring
    _ ≤ _ := add_le_add h1 h2

/-! ## Profiled doom

The one-threshold state above treats every lift failure as an escaped first-round
challenge.  That is convenient, but it discards the failure-agreement profile which
the flat proof already established.  The profiled state keeps a failure challenge
doomed whenever its own accepting-query cover is small. -/

/-- A challenge is doomed when the applicable cover certificate is below its own
threshold: `failureThreshold` on selected-MCA failures and `arithmeticThreshold`
on the ordinary arithmetic branch. -/
def ProfiledDoomedAfter (failureThreshold arithmeticThreshold : ℕ)
    (challenge : Challenge) : Prop :=
  if challenge ∈ classifier.failure then
    classifier.failureAgreement challenge ≤ failureThreshold
  else
    classifier.agreement challenge ≤ arithmeticThreshold

/-- Challenges escaping on the arithmetic branch.  The subtraction by the
selected-MCA failure set makes the two semantic branches disjoint. -/
noncomputable def profiledArithmeticEscaping (arithmeticThreshold : ℕ) :
    Finset Challenge := by
  classical
  exact (AgreementProfile.tailSet classifier.agreement
    (arithmeticThreshold + 1)) \ classifier.failure

/-- Challenges escaping the profiled doom state are precisely covered by two
disjoint agreement tails: selected-MCA failures, and ordinary arithmetic
challenges outside the failure set. -/
noncomputable def profiledEscaping (failureThreshold arithmeticThreshold : ℕ) :
    Finset Challenge := by
  classical
  exact AgreementProfile.restrictedTailSet classifier.failure
      classifier.failureAgreement (failureThreshold + 1) ∪
    classifier.profiledArithmeticEscaping arithmeticThreshold

omit [Fintype F] [DecidableEq F] [Fintype Equations] [DecidableEq Equations]
    [DecidableEq CheckedMask] [Nonempty Challenge] in
theorem profiledEscaping_branches_disjoint
    (failureThreshold arithmeticThreshold : ℕ) :
    Disjoint
      (AgreementProfile.restrictedTailSet classifier.failure
        classifier.failureAgreement (failureThreshold + 1))
      (classifier.profiledArithmeticEscaping arithmeticThreshold) := by
  classical
  rw [Finset.disjoint_left]
  intro challenge hfailure harithmetic
  exact (Finset.mem_sdiff.mp harithmetic).2
    (Finset.mem_filter.mp hfailure).1

omit [Fintype F] [DecidableEq F] [Fintype Equations] [DecidableEq Equations]
    [DecidableEq CheckedMask] [Nonempty Challenge] in
theorem not_profiledDoomedAfter_mem_profiledEscaping
    {failureThreshold arithmeticThreshold : ℕ} {challenge : Challenge}
    (h : ¬ classifier.ProfiledDoomedAfter failureThreshold arithmeticThreshold challenge) :
    challenge ∈ classifier.profiledEscaping failureThreshold arithmeticThreshold := by
  classical
  unfold ProfiledDoomedAfter at h
  split at h
  next hfailure =>
    apply Finset.mem_union_left
    simp only [AgreementProfile.restrictedTailSet, Finset.mem_filter]
    exact ⟨hfailure, Nat.lt_of_not_le h⟩
  next hfailure =>
    apply Finset.mem_union_right
    simp only [profiledArithmeticEscaping, Finset.mem_sdiff]
    exact ⟨by simpa [AgreementProfile.tailSet] using Nat.lt_of_not_le h,
      hfailure⟩

omit [Fintype F] [DecidableEq F] [Fintype Equations] [DecidableEq Equations]
    [DecidableEq CheckedMask] [Nonempty Challenge] in
/-- Query-round preservation for the profiled state.  The cover is the larger of
the selected-MCA failure cover and the ordinary arithmetic cover. -/
theorem query_density_le_of_profiledDoomedAfter
    (failureThreshold arithmeticThreshold : ℕ) (challenge : Challenge)
    (hdoom : classifier.ProfiledDoomedAfter
      failureThreshold arithmeticThreshold challenge) :
    ((classifier.acceptingQueries challenge).card : ℚ) / (n.choose r) ≤
      hypergeometricRatio
        (max failureThreshold
          (max (n - e - 1) (min n (g + arithmeticThreshold)))) n r := by
  classical
  have hcard := classifier.acceptingQueries_card_le challenge
  unfold ProfiledDoomedAfter at hdoom
  by_cases hfailure : challenge ∈ classifier.failure
  · simp only [hfailure, ↓reduceIte] at hcard hdoom
    have hchoose : (classifier.acceptingQueries challenge).card ≤
        (max failureThreshold
          (max (n - e - 1) (min n (g + arithmeticThreshold)))).choose r :=
      hcard.trans (Nat.choose_le_choose r
        (hdoom.trans (le_max_left _ _)))
    unfold hypergeometricRatio
    exact div_le_div_of_nonneg_right (by exact_mod_cast hchoose) (by positivity)
  · simp only [hfailure, ↓reduceIte] at hcard hdoom
    have hmono : max (n - e - 1) (min n (g + classifier.agreement challenge)) ≤
        max (n - e - 1) (min n (g + arithmeticThreshold)) := by
      apply max_le_max (le_refl _)
      exact min_le_min (le_refl _) (by omega)
    have hchoose : (classifier.acceptingQueries challenge).card ≤
        (max failureThreshold
          (max (n - e - 1) (min n (g + arithmeticThreshold)))).choose r :=
      hcard.trans (Nat.choose_le_choose r
        (hmono.trans (le_max_right _ _)))
    unfold hypergeometricRatio
    exact div_le_div_of_nonneg_right (by exact_mod_cast hchoose) (by positivity)

omit [Fintype F] [DecidableEq F] [Fintype Equations] [DecidableEq Equations]
    [DecidableEq CheckedMask] in
/-- Challenge-round preservation retaining both proved agreement tails. -/
theorem profiledEscaping_density_le
    (failureThreshold arithmeticThreshold : ℕ)
    (hfailureThreshold : failureThreshold + 1 ≤ n)
    (harithmeticThreshold : arithmeticThreshold + 1 ≤ n)
    (hfd : 0 < failureDenominator) (hpd : 0 < profileDenominator) :
    ((classifier.profiledEscaping failureThreshold arithmeticThreshold).card : ℚ) /
        Fintype.card Challenge ≤
      (failureProfile.labelsAtLeast (failureThreshold + 1) : ℚ) /
          failureDenominator +
        (arithmeticProfile.labelsAtLeast (arithmeticThreshold + 1) : ℚ) /
          profileDenominator := by
  classical
  have hchal : (0 : ℚ) < Fintype.card Challenge := by
    exact_mod_cast Fintype.card_pos
  let failureTail := AgreementProfile.restrictedTailSet classifier.failure
    classifier.failureAgreement (failureThreshold + 1)
  let fullArithmeticTail := AgreementProfile.tailSet classifier.agreement
    (arithmeticThreshold + 1)
  let arithmeticTail := classifier.profiledArithmeticEscaping arithmeticThreshold
  have hfailCard : (failureDenominator : ℚ) * (failureTail.card : ℚ) ≤
      (failureProfile.labelsAtLeast (failureThreshold + 1) : ℚ) *
        Fintype.card Challenge := by
    have := classifier.failureAgreement_density
      (failureThreshold + 1) hfailureThreshold
    exact_mod_cast this
  have harithmeticCard : (profileDenominator : ℚ) * (arithmeticTail.card : ℚ) ≤
      (arithmeticProfile.labelsAtLeast (arithmeticThreshold + 1) : ℚ) *
        Fintype.card Challenge := by
    have hfull := classifier.agreement_density
      (arithmeticThreshold + 1) harithmeticThreshold
    have hsub : arithmeticTail.card ≤ fullArithmeticTail.card := by
      apply Finset.card_le_card
      intro challenge hchallenge
      exact (Finset.mem_sdiff.mp hchallenge).1
    have hcast : (profileDenominator : ℚ) * (arithmeticTail.card : ℚ) ≤
        (profileDenominator : ℚ) * (fullArithmeticTail.card : ℚ) := by
      gcongr
    exact hcast.trans (by exact_mod_cast hfull)
  have hunion :
      ((classifier.profiledEscaping failureThreshold arithmeticThreshold).card : ℚ) ≤
        (failureTail.card : ℚ) + (arithmeticTail.card : ℚ) := by
    have := Finset.card_union_le failureTail arithmeticTail
    exact_mod_cast this
  have hfdQ : (0 : ℚ) < failureDenominator := by exact_mod_cast hfd
  have hpdQ : (0 : ℚ) < profileDenominator := by exact_mod_cast hpd
  have h1 : (failureTail.card : ℚ) / Fintype.card Challenge ≤
      (failureProfile.labelsAtLeast (failureThreshold + 1) : ℚ) /
        failureDenominator := by
    rw [div_le_div_iff₀ hchal hfdQ]
    nlinarith [hfailCard]
  have h2 : (arithmeticTail.card : ℚ) / Fintype.card Challenge ≤
      (arithmeticProfile.labelsAtLeast (arithmeticThreshold + 1) : ℚ) /
        profileDenominator := by
    rw [div_le_div_iff₀ hchal hpdQ]
    nlinarith [harithmeticCard]
  calc
    ((classifier.profiledEscaping failureThreshold arithmeticThreshold).card : ℚ) /
          Fintype.card Challenge ≤
        ((failureTail.card : ℚ) + (arithmeticTail.card : ℚ)) /
          Fintype.card Challenge :=
      div_le_div_of_nonneg_right hunion (le_of_lt hchal)
    _ = (failureTail.card : ℚ) / Fintype.card Challenge +
          (arithmeticTail.card : ℚ) / Fintype.card Challenge := by ring
    _ ≤ _ := add_le_add h1 h2

end PolicyDoublyProfiledSoundnessClassifier

end LigeroFamily
