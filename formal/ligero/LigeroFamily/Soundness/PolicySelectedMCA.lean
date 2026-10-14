import LigeroFamily.Soundness.PolicyLiftList
import LigeroFamily.Soundness.SchemeSelectedMCA
import LigeroFamily.Soundness.FiniteCounting
import LigeroFamily.Soundness.SelectedMCAParameters









namespace LigeroFamily

open CodingTheory MultiplicativeCode

variable {F Equations CheckedMask DirectMask Challenge Response Tail : Type*}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype Equations] [DecidableEq Equations]
variable [Fintype CheckedMask] [DecidableEq CheckedMask]
variable [Fintype Challenge] [DecidableEq Challenge]
variable [Fintype Tail] [DecidableEq Tail]
variable {q r w n nw nq e g d threshold : ℕ}

variable {C : MultiplicativeCode F r w n}
variable {layout : ConstraintLayout F q w}
variable {policy : SchemeProtocolPolicy (Equations := Equations) C layout
  Challenge Response CheckedMask DirectMask nw nq 1}
variable {oracle : SchemeOracle F CheckedMask DirectMask nw nq n 1}
variable {respond : Challenge → Response}

/-- Split one simultaneous challenge into its opaque arithmetic tail and the
proximity weights consumed by selected-MCA. -/
structure SchemeExtractorPolicy
    (policy : SchemeProtocolPolicy (Equations := Equations) C layout
      Challenge Response CheckedMask DirectMask nw nq 1)
    (Tail : Type*) where
  challengeProductEquiv : Challenge ≃
    Tail × SchemeSelectedMCA.Weights F CheckedMask nw nq
  weights_eq : ∀ challenge,
    (challengeProductEquiv challenge).2 = policy.proximityWeights challenge 0

namespace SchemeExtractorPolicy

variable (extractor : SchemeExtractorPolicy policy Tail)

noncomputable def responseAtTail
    (tail : Tail) (weights : SchemeSelectedMCA.Weights F CheckedMask nw nq) :
    EvaluationRow F r w n :=
  policy.proximityResponse
    (respond (extractor.challengeProductEquiv.symm (tail, weights))) 0

noncomputable def badChallengePairs :
    Finset (Tail × SchemeSelectedMCA.Weights F CheckedMask nw nq) := by
  classical
  exact Finset.univ.filter fun pair => pair.2 ∈
    SchemeSelectedMCA.badWeights (C := C) (oracle := oracle) (e := e) (g := g)
      (extractor.responseAtTail (respond := respond) pair.1)

noncomputable def badChallenges : Finset Challenge := by
  classical
  exact (extractor.badChallengePairs (oracle := oracle) (respond := respond)
    (e := e) (g := g)).map extractor.challengeProductEquiv.symm.toEmbedding

noncomputable def failureAgreement (challenge : Challenge) : ℕ :=
  (schemeProximityAgreement oracle (policy.proximityWeights challenge 0)
    (policy.proximityResponse (respond challenge) 0)).card

noncomputable def badChallengePairsAtAgreement (a : ℕ) :
    Finset (Tail × SchemeSelectedMCA.Weights F CheckedMask nw nq) := by
  classical
  exact Finset.univ.filter fun pair => pair.2 ∈
    SchemeSelectedMCA.badWeightsAtAgreement
      (C := C) (oracle := oracle) (e := e) (g := g)
      (extractor.responseAtTail (respond := respond) pair.1) a

noncomputable def badChallengesAtAgreement (a : ℕ) : Finset Challenge := by
  classical
  exact (extractor.badChallengePairsAtAgreement (oracle := oracle)
    (respond := respond) (e := e) (g := g) a).map
      extractor.challengeProductEquiv.symm.toEmbedding

omit [Fintype Equations] [DecidableEq Equations] [Fintype Challenge]
    [DecidableEq Challenge] in
theorem badChallengePairsAtAgreement_card_eq_sum (a : ℕ) :
    (extractor.badChallengePairsAtAgreement (oracle := oracle)
      (respond := respond) (e := e) (g := g) a).card =
      ∑ tail : Tail,
        (SchemeSelectedMCA.badWeightsAtAgreement
          (C := C) (oracle := oracle) (e := e) (g := g)
          (extractor.responseAtTail (respond := respond) tail) a).card := by
  classical
  simpa [badChallengePairsAtAgreement] using
    (Internal.card_filter_product_eq_sum
      (First := Tail)
      (Second := SchemeSelectedMCA.Weights F CheckedMask nw nq)
      (fun tail weights => weights ∈
        SchemeSelectedMCA.badWeightsAtAgreement
          (C := C) (oracle := oracle) (e := e) (g := g)
          (extractor.responseAtTail (respond := respond) tail) a))

omit [Fintype Equations] [DecidableEq Equations] [Fintype Challenge]
    [DecidableEq Challenge] [DecidableEq Tail] in
theorem badChallengesAtAgreement_eq_restrictedTailSet (a : ℕ) :
    extractor.badChallengesAtAgreement (oracle := oracle)
        (respond := respond) (e := e) (g := g) a =
      AgreementProfile.restrictedTailSet
        (extractor.badChallenges (oracle := oracle)
          (respond := respond) (e := e) (g := g))
        (failureAgreement (policy := policy) (oracle := oracle)
          (respond := respond)) a := by
  classical
  ext challenge
  simp [badChallengesAtAgreement, badChallengePairsAtAgreement,
    badChallenges, badChallengePairs, SchemeSelectedMCA.badWeightsAtAgreement,
    AgreementProfile.restrictedTailSet, failureAgreement, responseAtTail]
  intro _hbad
  rw [extractor.weights_eq]

omit [Fintype Equations] [DecidableEq Equations] [DecidableEq Challenge] in
private theorem badChallenges_agreement_density_of_fibers
    [Nonempty (SchemeTestedRow CheckedMask nw nq 1)]
    (failureDenominator : ℕ) (profile : AgreementProfile n) (a : ℕ)
    (hfiber : ∀ tail : Tail,
      failureDenominator *
          (SchemeSelectedMCA.badWeightsAtAgreement
            (C := C) (oracle := oracle) (e := e) (g := g)
            (extractor.responseAtTail (respond := respond) tail) a).card ≤
        profile.labelsAtLeast a *
          Fintype.card (SchemeSelectedMCA.Weights F CheckedMask nw nq)) :
    failureDenominator *
        (AgreementProfile.restrictedTailSet
          (extractor.badChallenges (oracle := oracle)
            (respond := respond) (e := e) (g := g))
          (failureAgreement (policy := policy) (oracle := oracle)
            (respond := respond)) a).card ≤
      profile.labelsAtLeast a * Fintype.card Challenge := by
  classical
  have hpairDensity :
      failureDenominator *
          (extractor.badChallengePairsAtAgreement (oracle := oracle)
            (respond := respond) (e := e) (g := g) a).card ≤
        profile.labelsAtLeast a *
          Fintype.card
            (Tail × SchemeSelectedMCA.Weights F CheckedMask nw nq) := by
    rw [extractor.badChallengePairsAtAgreement_card_eq_sum]
    simpa [Fintype.card_prod, Nat.mul_comm] using
      SelectedMCA.fiberwise_density_sum
        (fun tail : Tail =>
          SchemeSelectedMCA.badWeightsAtAgreement
            (C := C) (oracle := oracle) (e := e) (g := g)
            (extractor.responseAtTail (respond := respond) tail) a)
        (profile.labelsAtLeast a) failureDenominator hfiber
  rw [← extractor.badChallengesAtAgreement_eq_restrictedTailSet
    (oracle := oracle) (respond := respond) (e := e) (g := g) a]
  have hcard :
      (extractor.badChallengesAtAgreement (oracle := oracle)
        (respond := respond) (e := e) (g := g) a).card =
      (extractor.badChallengePairsAtAgreement (oracle := oracle)
        (respond := respond) (e := e) (g := g) a).card := by
    simp [badChallengesAtAgreement]
  rw [hcard]
  rw [show Fintype.card Challenge =
      Fintype.card (Tail × SchemeSelectedMCA.Weights F CheckedMask nw nq) from
    Fintype.card_congr extractor.challengeProductEquiv]
  exact hpairDensity

omit [Fintype Equations] [DecidableEq Equations] [DecidableEq Challenge] in
/-- The challenge-side density, from a per-line bound supplied by any proximity
theorem.  `SelectedMCA.LineFailureBound` is the whole interface; `bound` is the
line-failure count it certifies. -/
theorem badChallenges_agreement_density_ofLineFailure {bound : ℕ}
    [Nonempty (SchemeTestedRow CheckedMask nw nq 1)]
    (hmin : HasMinimumDistanceAtLeast C.baseCode d)
    (hline : SelectedMCA.LineFailureBound C.baseCode e g bound)
    (hthree : 3 * g < d - e) (hfield : g + 1 < Fintype.card F)
    (a : ℕ) :
    (Fintype.card F - (g + 1)) *
        (AgreementProfile.restrictedTailSet
          (extractor.badChallenges (oracle := oracle)
            (respond := respond) (e := e) (g := g))
          (failureAgreement (policy := policy) (oracle := oracle)
            (respond := respond)) a).card ≤
      (SchemeSelectedMCA.selectedMCAFailureProfile n g d
        bound).labelsAtLeast a *
        Fintype.card Challenge := by
  apply extractor.badChallenges_agreement_density_of_fibers
    (Fintype.card F - (g + 1))
    (SchemeSelectedMCA.selectedMCAFailureProfile n g d bound) a
  intro tail
  exact
    SchemeSelectedMCA.badWeightsAtAgreement_density
      (C := C) (oracle := oracle)
      (extractor.responseAtTail (respond := respond) tail) hmin
      hline hthree hfield a

omit [Fintype Equations] [DecidableEq Equations] [DecidableEq Challenge] in
/-- The clique-route specialization, which is what the parameter bundle of a
committed certificate supplies. -/
theorem badChallenges_agreement_density
    [Nonempty (SchemeTestedRow CheckedMask nw nq 1)]
    (hmin : HasMinimumDistanceAtLeast C.baseCode d)
    (conditions : SelectedMCAParameterConditions
      (Fintype.card F) n e g d threshold)
    (a : ℕ) :
    (Fintype.card F - (g + 1)) *
        (AgreementProfile.restrictedTailSet
          (extractor.badChallenges (oracle := oracle)
            (respond := respond) (e := e) (g := g))
          (failureAgreement (policy := policy) (oracle := oracle)
            (respond := respond)) a).card ≤
      (SchemeSelectedMCA.selectedMCAFailureProfile n g d
        (SelectedMCA.directLineFailureBound threshold)).labelsAtLeast a *
        Fintype.card Challenge :=
  badChallenges_agreement_density_ofLineFailure extractor hmin
    (conditions.direct.lineFailure hmin)
    conditions.punctured.punctured_three_radius
    conditions.punctured.field_large a

omit [Fintype Equations] [DecidableEq Equations] [DecidableEq Challenge] in
/-- Policy-level density theorem for the agreement-local selected-MCA
profile. -/
theorem badChallenges_agreement_density_refined
    [Nonempty (SchemeTestedRow CheckedMask nw nq 1)]
    {localThreshold cutoff : ℕ}
    (hmin : HasMinimumDistanceAtLeast C.baseCode d)
    (conditions : RefinedSelectedMCAParameterConditions
      (Fintype.card F) n e g d threshold cutoff localThreshold)
    (a : ℕ) :
    (Fintype.card F - (g + 1)) *
        (AgreementProfile.restrictedTailSet
          (extractor.badChallenges (oracle := oracle)
            (respond := respond) (e := e) (g := g))
          (failureAgreement (policy := policy) (oracle := oracle)
            (respond := respond)) a).card ≤
      (SchemeSelectedMCA.selectedMCARefinedFailureProfile n g d
        (SelectedMCA.directLineFailureBound threshold) cutoff
        (SelectedMCA.directLineFailureBound localThreshold)).labelsAtLeast a *
        Fintype.card Challenge := by
  apply extractor.badChallenges_agreement_density_of_fibers
    (Fintype.card F - (g + 1))
    (SchemeSelectedMCA.selectedMCARefinedFailureProfile n g d
      (SelectedMCA.directLineFailureBound threshold) cutoff
      (SelectedMCA.directLineFailureBound localThreshold)) a
  intro tail
  exact
    SchemeSelectedMCA.badWeightsAtAgreement_density_refined
      (C := C) (oracle := oracle)
      (extractor.responseAtTail (respond := respond) tail) hmin conditions a

omit [Fintype Equations] [DecidableEq Equations] [DecidableEq Challenge] in
/-- Route-agnostic version of the agreement-local density theorem. -/
theorem badChallenges_agreement_density_refinedOfLine
    [Nonempty (SchemeTestedRow CheckedMask nw nq 1)]
    {outerBound localBound cutoff : ℕ}
    (hmin : HasMinimumDistanceAtLeast C.baseCode d)
    (conditions : RefinedSelectedMCALineConditions C.baseCode
      (Fintype.card F) e g d outerBound cutoff localBound)
    (a : ℕ) :
    (Fintype.card F - (g + 1)) *
        (AgreementProfile.restrictedTailSet
          (extractor.badChallenges (oracle := oracle)
            (respond := respond) (e := e) (g := g))
          (failureAgreement (policy := policy) (oracle := oracle)
            (respond := respond)) a).card ≤
      (SchemeSelectedMCA.selectedMCARefinedFailureProfile n g d
        outerBound cutoff localBound).labelsAtLeast a *
        Fintype.card Challenge := by
  apply extractor.badChallenges_agreement_density_of_fibers
    (Fintype.card F - (g + 1))
    (SchemeSelectedMCA.selectedMCARefinedFailureProfile n g d
      outerBound cutoff localBound) a
  intro tail
  exact SchemeSelectedMCA.badWeightsAtAgreement_density_refinedOfLine
    (C := C) (oracle := oracle)
    (extractor.responseAtTail (respond := respond) tail) hmin conditions a

omit [Fintype Equations] [DecidableEq Equations] [DecidableEq Challenge] in
/-- Policy-level threshold-free pointwise density theorem. -/
theorem badChallenges_agreement_density_endpointOptimizedIntegratedOfLine
    [Nonempty (SchemeTestedRow CheckedMask nw nq 1)]
    {outerBound : ℕ} {localBound : ℕ → ℕ}
    (hmin : HasMinimumDistanceAtLeast C.baseCode d)
    (conditions : IntegratedSelectedMCALineConditions C.baseCode
      (Fintype.card F) e g d outerBound localBound)
    (a : ℕ) :
    (Fintype.card F * (Fintype.card F - (g + 1))) *
        (AgreementProfile.restrictedTailSet
          (extractor.badChallenges (oracle := oracle)
            (respond := respond) (e := e) (g := g))
          (failureAgreement (policy := policy) (oracle := oracle)
            (respond := respond)) a).card ≤
      (SchemeSelectedMCA.endpointOptimizedProfile (Fintype.card F) g
        (SchemeSelectedMCA.selectedMCAIntegratedFailureProfile n e g d
          outerBound localBound)).labelsAtLeast a *
        Fintype.card Challenge := by
  apply extractor.badChallenges_agreement_density_of_fibers
    (Fintype.card F * (Fintype.card F - (g + 1)))
    (SchemeSelectedMCA.endpointOptimizedProfile (Fintype.card F) g
      (SchemeSelectedMCA.selectedMCAIntegratedFailureProfile n e g d
        outerBound localBound)) a
  intro tail
  exact SchemeSelectedMCA.badWeightsAtAgreement_density_endpointOptimizedIntegratedOfLine
    (C := C) (oracle := oracle)
    (extractor.responseAtTail (respond := respond) tail) hmin conditions a

omit [Fintype Equations] [DecidableEq Equations] [DecidableEq Challenge] in
/-- Compatibility form of the threshold-free pointwise density theorem.
The endpoint-optimized theorem above is the public sharp form. -/
theorem badChallenges_agreement_density_integratedOfLine
    [Nonempty (SchemeTestedRow CheckedMask nw nq 1)]
    {outerBound : ℕ} {localBound : ℕ → ℕ}
    (hmin : HasMinimumDistanceAtLeast C.baseCode d)
    (conditions : IntegratedSelectedMCALineConditions C.baseCode
      (Fintype.card F) e g d outerBound localBound)
    (a : ℕ) :
    (Fintype.card F - (g + 1)) *
        (AgreementProfile.restrictedTailSet
          (extractor.badChallenges (oracle := oracle)
            (respond := respond) (e := e) (g := g))
          (failureAgreement (policy := policy) (oracle := oracle)
            (respond := respond)) a).card ≤
      (SchemeSelectedMCA.selectedMCAIntegratedFailureProfile n e g d
        outerBound localBound).labelsAtLeast a *
        Fintype.card Challenge := by
  apply extractor.badChallenges_agreement_density_of_fibers
    (Fintype.card F - (g + 1))
    (SchemeSelectedMCA.selectedMCAIntegratedFailureProfile n e g d
      outerBound localBound) a
  intro tail
  exact SchemeSelectedMCA.badWeightsAtAgreement_density_integratedOfLine
    (C := C) (oracle := oracle)
    (extractor.responseAtTail (respond := respond) tail) hmin conditions a

omit [Fintype Equations] [DecidableEq Equations] [Fintype Challenge]
    [DecidableEq Challenge] [DecidableEq Tail] in
/-- The common selected-MCA extractor constructs the fixed lift list for any
arithmetic policy admitting the challenge split above. -/
theorem exists_policyLiftList_of_selectedMCA
    [Nonempty (SchemeTestedRow CheckedMask nw nq 1)]
    (hmin : HasMinimumDistanceAtLeast C.baseCode d)
    (hradius : e + g < d)
    (hden : 0 < CodingTheory.InterleavedJohnson.denominator n d (e + g)) :
    ∃ certificate : PolicyLiftListCertificate policy oracle respond e g (e + g)
      (CodingTheory.InterleavedJohnson.listBound n d (e + g)),
      certificate.failure = extractor.badChallenges (oracle := oracle)
        (respond := respond) (e := e) (g := g) := by
  classical
  let failure := extractor.badChallenges (oracle := oracle)
    (respond := respond) (e := e) (g := g)
  have hwitness (challenge : Challenge)
      (hnotFailure : challenge ∉ failure)
      (hresponse : policy.proximityResponse (respond challenge) 0 ∈ C.base)
      (hsmall : (schemeProximityDisagreement oracle
        (policy.proximityWeights challenge 0)
        (policy.proximityResponse (respond challenge) 0)).card ≤ e) :
      Nonempty (SchemeGLiftWitness C oracle
        (policy.proximityWeights challenge 0)
        (policy.proximityResponse (respond challenge) 0) g) := by
    let pair := extractor.challengeProductEquiv challenge
    have hweights : pair.2 = policy.proximityWeights challenge 0 :=
      extractor.weights_eq challenge
    have hresponseEq :
        extractor.responseAtTail (respond := respond) pair.1 pair.2 =
          policy.proximityResponse (respond challenge) 0 := by
      unfold responseAtTail
      rw [show (pair.1, pair.2) = pair from Prod.eta pair]
      change policy.proximityResponse
        (respond (extractor.challengeProductEquiv.symm
          (extractor.challengeProductEquiv challenge))) 0 = _
      rw [extractor.challengeProductEquiv.symm_apply_apply]
    have hnotBadWeight : pair.2 ∉
        SchemeSelectedMCA.badWeights
          (C := C) (oracle := oracle) (e := e) (g := g)
          (extractor.responseAtTail (respond := respond) pair.1) := by
      intro hbadWeight
      apply hnotFailure
      apply Finset.mem_map.mpr
      refine ⟨pair, ?_, extractor.challengeProductEquiv.symm_apply_apply challenge⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbadWeight⟩
    have hwitnessPair :=
      SchemeSelectedMCA.gLiftWitness_nonempty_of_not_mem_badWeights
        (respond := extractor.responseAtTail (respond := respond) pair.1)
        pair.2 hnotBadWeight
        (by rw [hresponseEq]; exact hresponse)
        (by rw [hresponseEq, hweights]; exact hsmall)
    rw [hresponseEq, hweights] at hwitnessPair
    exact hwitnessPair
  obtain ⟨certificate, hcertificate⟩ :=
    PolicyLiftListCertificate.exists_of_gLiftWitnesses hmin hradius
      hden failure hwitness
  refine ⟨certificate, ?_⟩
  simpa [failure] using hcertificate

omit [Fintype Equations] [DecidableEq Equations] [Fintype Challenge]
    [DecidableEq Challenge] [DecidableEq Tail] in
/-- Unique-decoding version of the common selected-MCA extractor.  The bad
challenge set and its selected-MCA proof are unchanged; only the fixed lift
list is sharpened from the Johnson bound to cardinality one. -/
theorem exists_policyLiftList_of_selectedMCA_unique
    [Nonempty (SchemeTestedRow CheckedMask nw nq 1)]
    (hmin : HasMinimumDistanceAtLeast C.baseCode d)
    (hunique : 2 * (e + g) < d) :
    ∃ certificate : PolicyLiftListCertificate policy oracle respond e g (e + g) 1,
      certificate.failure = extractor.badChallenges (oracle := oracle)
        (respond := respond) (e := e) (g := g) := by
  classical
  let failure := extractor.badChallenges (oracle := oracle)
    (respond := respond) (e := e) (g := g)
  have hwitness (challenge : Challenge)
      (hnotFailure : challenge ∉ failure)
      (hresponse : policy.proximityResponse (respond challenge) 0 ∈ C.base)
      (hsmall : (schemeProximityDisagreement oracle
        (policy.proximityWeights challenge 0)
        (policy.proximityResponse (respond challenge) 0)).card ≤ e) :
      Nonempty (SchemeGLiftWitness C oracle
        (policy.proximityWeights challenge 0)
        (policy.proximityResponse (respond challenge) 0) g) := by
    let pair := extractor.challengeProductEquiv challenge
    have hweights : pair.2 = policy.proximityWeights challenge 0 :=
      extractor.weights_eq challenge
    have hresponseEq :
        extractor.responseAtTail (respond := respond) pair.1 pair.2 =
          policy.proximityResponse (respond challenge) 0 := by
      unfold responseAtTail
      rw [show (pair.1, pair.2) = pair from Prod.eta pair]
      change policy.proximityResponse
        (respond (extractor.challengeProductEquiv.symm
          (extractor.challengeProductEquiv challenge))) 0 = _
      rw [extractor.challengeProductEquiv.symm_apply_apply]
    have hnotBadWeight : pair.2 ∉
        SchemeSelectedMCA.badWeights
          (C := C) (oracle := oracle) (e := e) (g := g)
          (extractor.responseAtTail (respond := respond) pair.1) := by
      intro hbadWeight
      apply hnotFailure
      apply Finset.mem_map.mpr
      refine ⟨pair, ?_, extractor.challengeProductEquiv.symm_apply_apply challenge⟩
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbadWeight⟩
    have hwitnessPair :=
      SchemeSelectedMCA.gLiftWitness_nonempty_of_not_mem_badWeights
        (respond := extractor.responseAtTail (respond := respond) pair.1)
        pair.2 hnotBadWeight
        (by rw [hresponseEq]; exact hresponse)
        (by rw [hresponseEq, hweights]; exact hsmall)
    rw [hresponseEq, hweights] at hwitnessPair
    exact hwitnessPair
  obtain ⟨certificate, hcertificate⟩ :=
    PolicyLiftListCertificate.exists_of_gLiftWitnesses_unique hmin
      (by omega) hunique failure hwitness
  refine ⟨certificate, ?_⟩
  simpa [failure] using hcertificate

omit [Fintype Equations] [DecidableEq Equations] [DecidableEq Challenge] in
/-- Construct the fixed lift list together with the selected-MCA density
bound consumed by the profiled soundness theorem. -/
theorem exists_profiledPolicyLiftList_of_selectedMCA {bound : ℕ}
    (extractor : SchemeExtractorPolicy policy Tail)
    [Nonempty (SchemeTestedRow CheckedMask nw nq 1)]
    (hmin : HasMinimumDistanceAtLeast C.baseCode d)
    (conditions : SelectedMCALineConditions C.baseCode
      (Fintype.card F) e g d bound) :
    ∃ certificate : PolicyLiftListCertificate policy oracle respond e g (e + g)
        (CodingTheory.InterleavedJohnson.listBound n d (e + g)),
      ∀ a ≤ n,
        (Fintype.card F - (g + 1)) *
            (AgreementProfile.restrictedTailSet certificate.failure
              (fun challenge =>
                (schemeProximityAgreement oracle
                  (policy.proximityWeights challenge 0)
                  (policy.proximityResponse (respond challenge) 0)).card) a).card ≤
          (SchemeSelectedMCA.selectedMCAFailureProfile n g d
            bound).labelsAtLeast a *
            Fintype.card Challenge := by
  obtain ⟨certificate, hfailure⟩ :=
    exists_policyLiftList_of_selectedMCA (extractor := extractor)
      (oracle := oracle) (respond := respond) hmin
      (by have := conditions.punctured.punctured_three_radius; omega)
      conditions.johnson.list_denominator_positive
  refine ⟨certificate, ?_⟩
  intro a _ha
  rw [hfailure]
  exact extractor.badChallenges_agreement_density_ofLineFailure
    (oracle := oracle) (respond := respond) hmin conditions.line
    conditions.punctured.punctured_three_radius
    conditions.punctured.field_large a

omit [Fintype Equations] [DecidableEq Equations] [DecidableEq Challenge] in
/-- Profiled selected-MCA extraction with a genuine singleton fixed lift list.
The line-failure profile is still proved by selected MCA; unique decoding is
used only for the list cardinality. -/
theorem exists_profiledPolicyLiftList_of_selectedMCA_unique {bound : ℕ}
    (extractor : SchemeExtractorPolicy policy Tail)
    [Nonempty (SchemeTestedRow CheckedMask nw nq 1)]
    (hmin : HasMinimumDistanceAtLeast C.baseCode d)
    (conditions : SelectedMCALineConditions C.baseCode
      (Fintype.card F) e g d bound)
    (hunique : 2 * (e + g) < d) :
    ∃ certificate : PolicyLiftListCertificate policy oracle respond e g (e + g) 1,
      ∀ a ≤ n,
        (Fintype.card F - (g + 1)) *
            (AgreementProfile.restrictedTailSet certificate.failure
              (fun challenge =>
                (schemeProximityAgreement oracle
                  (policy.proximityWeights challenge 0)
                  (policy.proximityResponse (respond challenge) 0)).card) a).card ≤
          (SchemeSelectedMCA.selectedMCAFailureProfile n g d
            bound).labelsAtLeast a * Fintype.card Challenge := by
  obtain ⟨certificate, hfailure⟩ :=
    exists_policyLiftList_of_selectedMCA_unique (extractor := extractor)
      (oracle := oracle) (respond := respond) hmin hunique
  refine ⟨certificate, ?_⟩
  intro a _ha
  rw [hfailure]
  exact extractor.badChallenges_agreement_density_ofLineFailure
    (oracle := oracle) (respond := respond) hmin conditions.line
    conditions.punctured.punctured_three_radius
    conditions.punctured.field_large a

omit [Fintype Equations] [DecidableEq Equations] [DecidableEq Challenge] in
/-- Construct the fixed lift list with the agreement-local failure profile. -/
theorem exists_profiledPolicyLiftList_of_refinedSelectedMCA
    (extractor : SchemeExtractorPolicy policy Tail)
    [Nonempty (SchemeTestedRow CheckedMask nw nq 1)]
    {localThreshold cutoff : ℕ}
    (hmin : HasMinimumDistanceAtLeast C.baseCode d)
    (conditions : RefinedSelectedMCAParameterConditions
      (Fintype.card F) n e g d threshold cutoff localThreshold) :
    ∃ certificate : PolicyLiftListCertificate policy oracle respond e g (e + g)
        (CodingTheory.InterleavedJohnson.listBound n d (e + g)),
      ∀ a ≤ n,
        (Fintype.card F - (g + 1)) *
            (AgreementProfile.restrictedTailSet certificate.failure
              (fun challenge =>
                (schemeProximityAgreement oracle
                  (policy.proximityWeights challenge 0)
                  (policy.proximityResponse (respond challenge) 0)).card) a).card ≤
          (SchemeSelectedMCA.selectedMCARefinedFailureProfile n g d
            (SelectedMCA.directLineFailureBound threshold) cutoff
            (SelectedMCA.directLineFailureBound localThreshold)).labelsAtLeast a *
            Fintype.card Challenge := by
  obtain ⟨certificate, hfailure⟩ :=
    exists_policyLiftList_of_selectedMCA (extractor := extractor)
      (oracle := oracle) (respond := respond) hmin
      (by
        have := conditions.toSelectedMCAParameterConditions.punctured.punctured_three_radius
        omega)
      conditions.toSelectedMCAParameterConditions.johnson.list_denominator_positive
  refine ⟨certificate, ?_⟩
  intro a _ha
  rw [hfailure]
  exact extractor.badChallenges_agreement_density_refined
    (oracle := oracle) (respond := respond) hmin conditions a

omit [Fintype Equations] [DecidableEq Equations] [DecidableEq Challenge] in
/-- Route-agnostic refined extractor used by public protocol and grid
theorems.  The unrefined selected-MCA construction remains an internal step
that constructs the oracle-fixed lift list. -/
theorem exists_profiledPolicyLiftList_of_refinedLine
    (extractor : SchemeExtractorPolicy policy Tail)
    [Nonempty (SchemeTestedRow CheckedMask nw nq 1)]
    {outerBound localBound cutoff : ℕ}
    (hmin : HasMinimumDistanceAtLeast C.baseCode d)
    (conditions : RefinedSelectedMCALineConditions C.baseCode
      (Fintype.card F) e g d outerBound cutoff localBound) :
    ∃ certificate : PolicyLiftListCertificate policy oracle respond e g (e + g)
        (CodingTheory.InterleavedJohnson.listBound n d (e + g)),
      ∀ a ≤ n,
        (Fintype.card F - (g + 1)) *
            (AgreementProfile.restrictedTailSet certificate.failure
              (fun challenge =>
                (schemeProximityAgreement oracle
                  (policy.proximityWeights challenge 0)
                  (policy.proximityResponse (respond challenge) 0)).card) a).card ≤
          (SchemeSelectedMCA.selectedMCARefinedFailureProfile n g d
            outerBound cutoff localBound).labelsAtLeast a *
            Fintype.card Challenge := by
  obtain ⟨certificate, hfailure⟩ :=
    exists_policyLiftList_of_selectedMCA (extractor := extractor)
      (oracle := oracle) (respond := respond) hmin
      (by
        have := conditions.outer.punctured.punctured_three_radius
        omega)
      conditions.outer.johnson.list_denominator_positive
  refine ⟨certificate, ?_⟩
  intro a _ha
  rw [hfailure]
  exact extractor.badChallenges_agreement_density_refinedOfLine
    (oracle := oracle) (respond := respond) hmin conditions a

omit [Fintype Equations] [DecidableEq Equations] [DecidableEq Challenge] in
/-- Threshold-free profiled extractor.  The exact agreement integral consumes
the pointwise line-bound family without introducing a cutoff. -/
theorem exists_profiledPolicyLiftList_of_endpointOptimizedIntegratedLine
    (extractor : SchemeExtractorPolicy policy Tail)
    [Nonempty (SchemeTestedRow CheckedMask nw nq 1)]
    {outerBound : ℕ} {localBound : ℕ → ℕ}
    (hmin : HasMinimumDistanceAtLeast C.baseCode d)
    (conditions : IntegratedSelectedMCALineConditions C.baseCode
      (Fintype.card F) e g d outerBound localBound) :
    ∃ certificate : PolicyLiftListCertificate policy oracle respond e g (e + g)
        (CodingTheory.InterleavedJohnson.listBound n d (e + g)),
      ∀ a ≤ n,
        (Fintype.card F * (Fintype.card F - (g + 1))) *
            (AgreementProfile.restrictedTailSet certificate.failure
              (fun challenge ↦
                (schemeProximityAgreement oracle
                  (policy.proximityWeights challenge 0)
                  (policy.proximityResponse (respond challenge) 0)).card) a).card ≤
          (SchemeSelectedMCA.endpointOptimizedProfile (Fintype.card F) g
            (SchemeSelectedMCA.selectedMCAIntegratedFailureProfile n e g d
              outerBound localBound)).labelsAtLeast a *
            Fintype.card Challenge := by
  obtain ⟨certificate, hfailure⟩ :=
    exists_policyLiftList_of_selectedMCA (extractor := extractor)
      (oracle := oracle) (respond := respond) hmin
      (by
        have := conditions.outer.punctured.punctured_three_radius
        omega)
      conditions.outer.johnson.list_denominator_positive
  refine ⟨certificate, ?_⟩
  intro a _ha
  rw [hfailure]
  exact extractor.badChallenges_agreement_density_endpointOptimizedIntegratedOfLine
    (oracle := oracle) (respond := respond) hmin conditions a

omit [Fintype Equations] [DecidableEq Equations] [DecidableEq Challenge] in
/-- Threshold-free profiled extractor.  The exact agreement integral consumes
the pointwise line-bound family without introducing a cutoff. -/
theorem exists_profiledPolicyLiftList_of_endpointOptimizedIntegratedLine_of_card
    (extractor : SchemeExtractorPolicy policy Tail)
    [Nonempty (SchemeTestedRow CheckedMask nw nq 1)]
    {outerBound : ℕ} {localBound : ℕ → ℕ}
    (hmin : HasMinimumDistanceAtLeast C.baseCode d)
    (conditions : IntegratedSelectedMCALineConditions C.baseCode
      (Fintype.card F) e g d outerBound localBound) {L : ℕ}
    (hcard : (Finset.univ : Finset (SchemeLiftCandidate C oracle (e + g))).card ≤ L) :
    ∃ certificate : PolicyLiftListCertificate policy oracle respond e g (e + g)
        L,
      ∀ a ≤ n,
        (Fintype.card F * (Fintype.card F - (g + 1))) *
            (AgreementProfile.restrictedTailSet certificate.failure
              (fun challenge ↦
                (schemeProximityAgreement oracle
                  (policy.proximityWeights challenge 0)
                  (policy.proximityResponse (respond challenge) 0)).card) a).card ≤
          (SchemeSelectedMCA.endpointOptimizedProfile (Fintype.card F) g
            (SchemeSelectedMCA.selectedMCAIntegratedFailureProfile n e g d
              outerBound localBound)).labelsAtLeast a *
            Fintype.card Challenge := by
  obtain ⟨certificate, hdensity⟩ :=
    exists_profiledPolicyLiftList_of_endpointOptimizedIntegratedLine
      extractor hmin conditions
  let sharpened : PolicyLiftListCertificate policy oracle respond e g (e + g) L := {
    candidates := certificate.candidates
    failure := certificate.failure
    list_card := (Finset.card_le_card (Finset.subset_univ _)).trans hcard
    lift := certificate.lift }
  exact ⟨sharpened, by simpa [sharpened] using hdensity⟩

omit [Fintype Equations] [DecidableEq Equations] [DecidableEq Challenge] in
/-- Threshold-free profiled extractor with a singleton oracle-fixed lift list.
Unique decoding changes only the list cardinality; the full pointwise MCA tail
is retained. -/
theorem exists_profiledPolicyLiftList_of_endpointOptimizedIntegratedLine_unique
    (extractor : SchemeExtractorPolicy policy Tail)
    [Nonempty (SchemeTestedRow CheckedMask nw nq 1)]
    {outerBound : ℕ} {localBound : ℕ → ℕ}
    (hmin : HasMinimumDistanceAtLeast C.baseCode d)
    (conditions : IntegratedSelectedMCALineConditions C.baseCode
      (Fintype.card F) e g d outerBound localBound)
    (hunique : 2 * (e + g) < d) :
    ∃ certificate : PolicyLiftListCertificate policy oracle respond e g (e + g) 1,
      ∀ a ≤ n,
        (Fintype.card F * (Fintype.card F - (g + 1))) *
            (AgreementProfile.restrictedTailSet certificate.failure
              (fun challenge ↦
                (schemeProximityAgreement oracle
                  (policy.proximityWeights challenge 0)
                  (policy.proximityResponse (respond challenge) 0)).card) a).card ≤
          (SchemeSelectedMCA.endpointOptimizedProfile (Fintype.card F) g
            (SchemeSelectedMCA.selectedMCAIntegratedFailureProfile n e g d
              outerBound localBound)).labelsAtLeast a *
            Fintype.card Challenge := by
  obtain ⟨certificate, hfailure⟩ :=
    exists_policyLiftList_of_selectedMCA_unique (extractor := extractor)
      (oracle := oracle) (respond := respond) hmin hunique
  refine ⟨certificate, ?_⟩
  intro a _ha
  rw [hfailure]
  exact extractor.badChallenges_agreement_density_endpointOptimizedIntegratedOfLine
    (oracle := oracle) (respond := respond) hmin conditions a

omit [Fintype Equations] [DecidableEq Equations] [DecidableEq Challenge] in
/-- Compatibility threshold-free extractor using the generic normalization. -/
theorem exists_profiledPolicyLiftList_of_integratedLine
    (extractor : SchemeExtractorPolicy policy Tail)
    [Nonempty (SchemeTestedRow CheckedMask nw nq 1)]
    {outerBound : ℕ} {localBound : ℕ → ℕ}
    (hmin : HasMinimumDistanceAtLeast C.baseCode d)
    (conditions : IntegratedSelectedMCALineConditions C.baseCode
      (Fintype.card F) e g d outerBound localBound) :
    ∃ certificate : PolicyLiftListCertificate policy oracle respond e g (e + g)
        (CodingTheory.InterleavedJohnson.listBound n d (e + g)),
      ∀ a ≤ n,
        (Fintype.card F - (g + 1)) *
            (AgreementProfile.restrictedTailSet certificate.failure
              (fun challenge ↦
                (schemeProximityAgreement oracle
                  (policy.proximityWeights challenge 0)
                  (policy.proximityResponse (respond challenge) 0)).card) a).card ≤
          (SchemeSelectedMCA.selectedMCAIntegratedFailureProfile n e g d
            outerBound localBound).labelsAtLeast a *
            Fintype.card Challenge := by
  obtain ⟨certificate, hfailure⟩ :=
    exists_policyLiftList_of_selectedMCA (extractor := extractor)
      (oracle := oracle) (respond := respond) hmin
      (by
        have := conditions.outer.punctured.punctured_three_radius
        omega)
      conditions.outer.johnson.list_denominator_positive
  refine ⟨certificate, ?_⟩
  intro a _ha
  rw [hfailure]
  exact extractor.badChallenges_agreement_density_integratedOfLine
    (oracle := oracle) (respond := respond) hmin conditions a

omit [Fintype Equations] [DecidableEq Equations] [DecidableEq Challenge] in
/-- Compatibility singleton extractor using the generic normalization. -/
theorem exists_profiledPolicyLiftList_of_integratedLine_unique
    (extractor : SchemeExtractorPolicy policy Tail)
    [Nonempty (SchemeTestedRow CheckedMask nw nq 1)]
    {outerBound : ℕ} {localBound : ℕ → ℕ}
    (hmin : HasMinimumDistanceAtLeast C.baseCode d)
    (conditions : IntegratedSelectedMCALineConditions C.baseCode
      (Fintype.card F) e g d outerBound localBound)
    (hunique : 2 * (e + g) < d) :
    ∃ certificate : PolicyLiftListCertificate policy oracle respond e g (e + g) 1,
      ∀ a ≤ n,
        (Fintype.card F - (g + 1)) *
            (AgreementProfile.restrictedTailSet certificate.failure
              (fun challenge ↦
                (schemeProximityAgreement oracle
                  (policy.proximityWeights challenge 0)
                  (policy.proximityResponse (respond challenge) 0)).card) a).card ≤
          (SchemeSelectedMCA.selectedMCAIntegratedFailureProfile n e g d
            outerBound localBound).labelsAtLeast a *
            Fintype.card Challenge := by
  obtain ⟨certificate, hfailure⟩ :=
    exists_policyLiftList_of_selectedMCA_unique (extractor := extractor)
      (oracle := oracle) (respond := respond) hmin hunique
  refine ⟨certificate, ?_⟩
  intro a _ha
  rw [hfailure]
  exact extractor.badChallenges_agreement_density_integratedOfLine
    (oracle := oracle) (respond := respond) hmin conditions a

end SchemeExtractorPolicy

end LigeroFamily
