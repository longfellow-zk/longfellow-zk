import LigeroFamily.Soundness.PolicyLiftList
import LigeroFamily.Soundness.AgreementProfile
import LigeroFamily.Soundness.FiniteCounting

/-! # Protocol-order soundness counting for every arithmetic policy -/

namespace LigeroFamily

variable {F Equations CheckedMask DirectMask Challenge Response : Type*}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype Equations] [DecidableEq Equations]
variable [Fintype CheckedMask] [DecidableEq CheckedMask]
variable [Fintype Challenge] [DecidableEq Challenge]
variable [Nonempty Challenge]
variable {logicalWidth r w n nw nq e g radius failureDenominator profileDenominator L : ℕ}

variable {C : MultiplicativeCode F r w n}
variable {layout : ConstraintLayout F logicalWidth w}
variable {policy : SchemeProtocolPolicy (Equations := Equations) C layout
  Challenge Response CheckedMask DirectMask nw nq 1}
variable {oracle : SchemeOracle F CheckedMask DirectMask nw nq n 1}
variable {statement : ConstraintSystem F nw nq logicalWidth Equations}
variable {respond : Challenge → Response}

structure PolicyAcceptingQueryCover
    (policy : SchemeProtocolPolicy (Equations := Equations) C layout
      Challenge Response CheckedMask DirectMask nw nq 1)
    (oracle : SchemeOracle F CheckedMask DirectMask nw nq n 1)
    (statement : ConstraintSystem F nw nq logicalWidth Equations)
    (challenge : Challenge) (response : Response) (bound : ℕ) where
  allowed : Finset (Fin n)
  allowed_card : allowed.card ≤ bound
  covers : ∀ query : QuerySet n r,
    policy.accepts statement challenge response query
      (openSchemeOracle oracle query) → query.coordinates ⊆ allowed





noncomputable def policyAcceptingCoordinates
    (policy : SchemeProtocolPolicy (Equations := Equations) C layout
      Challenge Response CheckedMask DirectMask nw nq 1)
    (oracle : SchemeOracle F CheckedMask DirectMask nw nq n 1)
    (statement : ConstraintSystem F nw nq logicalWidth Equations)
    (challenge : Challenge) (response : Response) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter fun coordinate ↦
    ∃ query : QuerySet n r,
      policy.accepts statement challenge response query
        (openSchemeOracle oracle query) ∧ coordinate ∈ query.coordinates

/-- Responses that both occur in an accepting query and have actual response
agreement at least `agreement`. -/
noncomputable def policyResponseAgreementList
    [Fintype Response]
    (policy : SchemeProtocolPolicy (Equations := Equations) C layout
      Challenge Response CheckedMask DirectMask nw nq 1)
    (oracle : SchemeOracle F CheckedMask DirectMask nw nq n 1)
    (statement : ConstraintSystem F nw nq logicalWidth Equations)
    (challenge : Challenge) (agreement : ℕ) : Finset Response := by
  classical
  exact Finset.univ.filter fun response ↦
    (∃ query : QuerySet n r,
      policy.accepts statement challenge response query
        (openSchemeOracle oracle query)) ∧
    agreement ≤
      (policyAcceptingCoordinates policy oracle statement challenge response).card

omit [Fintype F] [DecidableEq F] [Fintype Equations] [DecidableEq Equations]
    [DecidableEq CheckedMask] [Fintype Challenge] [DecidableEq Challenge]
    [Nonempty Challenge] in
theorem query_subset_policyAcceptingCoordinates_of_accepts
    (policy : SchemeProtocolPolicy (Equations := Equations) C layout
      Challenge Response CheckedMask DirectMask nw nq 1)
    (oracle : SchemeOracle F CheckedMask DirectMask nw nq n 1)
    (statement : ConstraintSystem F nw nq logicalWidth Equations)
    (challenge : Challenge) (response : Response) (query : QuerySet n r)
    (haccept : policy.accepts statement challenge response query
      (openSchemeOracle oracle query)) :
    query.coordinates ⊆
      policyAcceptingCoordinates policy oracle statement challenge response := by
  classical
  intro coordinate hcoordinate
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, ⟨query, haccept, hcoordinate⟩⟩

omit [Fintype F] [DecidableEq F] [Fintype Equations] [DecidableEq Equations]
    [DecidableEq CheckedMask] [Fintype Challenge] [DecidableEq Challenge]
    [Nonempty Challenge] in
theorem policyAcceptingCoordinates_subset_cover
    (policy : SchemeProtocolPolicy (Equations := Equations) C layout
      Challenge Response CheckedMask DirectMask nw nq 1)
    (oracle : SchemeOracle F CheckedMask DirectMask nw nq n 1)
    (statement : ConstraintSystem F nw nq logicalWidth Equations)
    (challenge : Challenge) (response : Response) (bound : ℕ)
    (cover : PolicyAcceptingQueryCover policy oracle statement challenge
      response bound) :
    policyAcceptingCoordinates policy oracle statement challenge response ⊆
      cover.allowed := by
  classical
  intro coordinate hcoordinate
  obtain ⟨query, haccept, hmem⟩ :=
    (Finset.mem_filter.mp hcoordinate).2
  exact cover.covers query haccept hmem

omit [Fintype F] [DecidableEq F] [Fintype Equations] [DecidableEq Equations]
    [DecidableEq CheckedMask] [Fintype Challenge] [DecidableEq Challenge]
    [Nonempty Challenge] in
theorem policyAcceptingCoordinates_card_le
    (policy : SchemeProtocolPolicy (Equations := Equations) C layout
      Challenge Response CheckedMask DirectMask nw nq 1)
    (oracle : SchemeOracle F CheckedMask DirectMask nw nq n 1)
    (statement : ConstraintSystem F nw nq logicalWidth Equations)
    (challenge : Challenge) (response : Response) :
    (policyAcceptingCoordinates policy oracle statement challenge response).card
      ≤ n := by
  classical
  simpa using Finset.card_le_card
    (show policyAcceptingCoordinates policy oracle statement challenge response ⊆
        (Finset.univ : Finset (Fin n)) from Finset.subset_univ _)

structure PolicyDoublyProfiledSoundnessClassifier
    (policy : SchemeProtocolPolicy (Equations := Equations) C layout
      Challenge Response CheckedMask DirectMask nw nq 1)
    (oracle : SchemeOracle F CheckedMask DirectMask nw nq n 1)
    (statement : ConstraintSystem F nw nq logicalWidth Equations)
    (respond : Challenge → Response)
    (failureProfile arithmeticProfile : AgreementProfile n)
    (profileDenominator failureDenominator e g : ℕ) where
  failure : Finset Challenge
  failureAgreement : Challenge → ℕ
  failureAgreement_le : ∀ challenge ∈ failure,
    failureAgreement challenge ≤ n
  failureAgreement_density : ∀ a ≤ n,
    failureDenominator *
        (AgreementProfile.restrictedTailSet failure failureAgreement a).card ≤
      failureProfile.labelsAtLeast a * Fintype.card Challenge
  failure_cover : ∀ challenge, challenge ∈ failure →
    Nonempty (PolicyAcceptingQueryCover policy oracle statement challenge
      (respond challenge) (failureAgreement challenge))
  agreement : Challenge → ℕ
  agreement_le : ∀ challenge, agreement challenge ≤ n
  agreement_density : ∀ a ≤ n,
    profileDenominator * (AgreementProfile.tailSet agreement a).card ≤
      arithmeticProfile.labelsAtLeast a * Fintype.card Challenge
  uniform_cover : ∀ challenge, challenge ∉ failure →
    (∃ query : QuerySet n r,
      policy.accepts statement challenge (respond challenge) query
        (openSchemeOracle oracle query)) →
    Nonempty (PolicyAcceptingQueryCover policy oracle statement challenge
      (respond challenge) (n - e - 1)) ∨
    Nonempty (PolicyAcceptingQueryCover policy oracle statement challenge
      (respond challenge) (min n (g + agreement challenge)))

namespace PolicyDoublyProfiledSoundnessClassifier

variable {failureProfile arithmeticProfile : AgreementProfile n}

/-- Actual pointwise response agreement for the classifier's response
strategy: the number of coordinates occurring in some accepting query. -/
noncomputable def responseAgreement
    (_classifier : PolicyDoublyProfiledSoundnessClassifier policy oracle statement
      respond failureProfile arithmeticProfile profileDenominator
        failureDenominator e g)
    (challenge : Challenge) : ℕ :=
  (policyAcceptingCoordinates policy oracle statement challenge
    (respond challenge)).card

omit [Fintype F] [DecidableEq F] [Fintype Equations] [DecidableEq Equations]
    [DecidableEq CheckedMask] [DecidableEq Challenge] [Nonempty Challenge] in
theorem responseAgreement_le
    (classifier : PolicyDoublyProfiledSoundnessClassifier policy oracle statement
      respond failureProfile arithmeticProfile profileDenominator
        failureDenominator e g)
    (challenge : Challenge) : classifier.responseAgreement challenge ≤ n := by
  exact policyAcceptingCoordinates_card_le policy oracle statement challenge
    (respond challenge)

omit [Fintype F] [DecidableEq F] [Fintype Equations] [DecidableEq Equations]
    [DecidableEq CheckedMask] [DecidableEq Challenge] [Nonempty Challenge] in
theorem responseAgreement_le_failureAgreement
    (classifier : PolicyDoublyProfiledSoundnessClassifier policy oracle statement
      respond failureProfile arithmeticProfile profileDenominator
        failureDenominator e g)
    (challenge : Challenge) (hfailure : challenge ∈ classifier.failure) :
    classifier.responseAgreement challenge ≤
      classifier.failureAgreement challenge := by
  let cover := Classical.choice (classifier.failure_cover challenge hfailure)
  exact (Finset.card_le_card
    (policyAcceptingCoordinates_subset_cover policy oracle statement challenge
      (respond challenge) _ cover)).trans cover.allowed_card

omit [Fintype F] [DecidableEq F] [Fintype Equations] [DecidableEq Equations]
    [DecidableEq CheckedMask] [DecidableEq Challenge] [Nonempty Challenge] in
theorem responseAgreement_le_goodCap
    (classifier : PolicyDoublyProfiledSoundnessClassifier policy oracle statement
      respond failureProfile arithmeticProfile profileDenominator
        failureDenominator e g)
    (challenge : Challenge) (hfailure : challenge ∉ classifier.failure) :
    classifier.responseAgreement challenge ≤
      max (n - e - 1) (min n (g + classifier.agreement challenge)) := by
  classical
  by_cases hexecution : ∃ query : QuerySet n r,
      policy.accepts statement challenge (respond challenge) query
        (openSchemeOracle oracle query)
  · rcases classifier.uniform_cover challenge hfailure hexecution with
      hfar | harithmetic
    · let cover := Classical.choice hfar
      exact (Finset.card_le_card
        (policyAcceptingCoordinates_subset_cover policy oracle statement
          challenge (respond challenge) _ cover)).trans
        (cover.allowed_card.trans (le_max_left _ _))
    · let cover := Classical.choice harithmetic
      exact (Finset.card_le_card
        (policyAcceptingCoordinates_subset_cover policy oracle statement
          challenge (respond challenge) _ cover)).trans
        (cover.allowed_card.trans (le_max_right _ _))
  · have hcoordinates : policyAcceptingCoordinates policy oracle statement
        challenge (respond challenge) = ∅ := by
      ext coordinate
      constructor
      · intro hcoordinate
        obtain ⟨query, haccept, _hmem⟩ :=
          (Finset.mem_filter.mp hcoordinate).2
        exact (hexecution ⟨query, haccept⟩).elim
      · simp
    simp [responseAgreement, hcoordinates]

noncomputable def acceptingQueries
    (_classifier : PolicyDoublyProfiledSoundnessClassifier policy oracle statement
      respond failureProfile arithmeticProfile profileDenominator
        failureDenominator e g)
    (challenge : Challenge) : Finset (QuerySet n r) := by
  classical
  exact Finset.univ.filter fun query =>
    policy.accepts statement challenge (respond challenge) query
      (openSchemeOracle oracle query)

/-- The actual independent `(challenge, query)` accepting pairs represented
by a profiled classifier. -/
noncomputable def acceptingPairs
    (_classifier : PolicyDoublyProfiledSoundnessClassifier policy oracle statement
      respond failureProfile arithmeticProfile profileDenominator
        failureDenominator e g) : Finset (Challenge × QuerySet n r) := by
  classical
  exact Finset.univ.filter fun pair =>
    policy.accepts statement pair.1 (respond pair.1) pair.2
      (openSchemeOracle oracle pair.2)

omit [Fintype F] [DecidableEq F] [Fintype Equations] [DecidableEq Equations]
    [DecidableEq CheckedMask] [Nonempty Challenge] in
theorem acceptingPairs_card_eq_sum
    (classifier : PolicyDoublyProfiledSoundnessClassifier policy oracle statement
      respond failureProfile arithmeticProfile profileDenominator
        failureDenominator e g) :
    classifier.acceptingPairs.card =
      ∑ challenge, (classifier.acceptingQueries challenge).card := by
  classical
  exact Internal.card_filter_product_eq_sum
    (fun challenge query =>
      policy.accepts statement challenge (respond challenge) query
        (openSchemeOracle oracle query))

noncomputable def acceptanceRate
    (classifier : PolicyDoublyProfiledSoundnessClassifier policy oracle statement
      respond failureProfile arithmeticProfile profileDenominator
        failureDenominator e g) : ℚ :=
  (∑ challenge, (classifier.acceptingQueries challenge).card : ℚ) /
    (Fintype.card Challenge * n.choose r)

omit [Fintype F] [DecidableEq F] [Fintype Equations] [DecidableEq Equations]
    [DecidableEq CheckedMask] [Nonempty Challenge] in
/-- The classifier's acceptance rate is literally the density of its actual
independent accepting-pair set. -/
theorem acceptingPairs_density_eq_acceptanceRate
    (classifier : PolicyDoublyProfiledSoundnessClassifier policy oracle statement
      respond failureProfile arithmeticProfile profileDenominator
        failureDenominator e g) :
    (classifier.acceptingPairs.card : ℚ) /
        (Fintype.card Challenge * Fintype.card (QuerySet n r)) =
      classifier.acceptanceRate := by
  rw [classifier.acceptingPairs_card_eq_sum, QuerySet.fintype_card]
  unfold acceptanceRate
  push_cast
  rfl

/-- Accepting pairs in the `(query, challenge)` order used by the typed
two-oracle tape kernel. -/
noncomputable def strategyAcceptingPairs
    (respond' : Challenge → Response) : Finset (QuerySet n r × Challenge) := by
  classical
  exact Finset.univ.filter fun pair =>
    policy.accepts statement pair.2 (respond' pair.2) pair.1
      (openSchemeOracle oracle pair.1)

omit [Fintype F] [DecidableEq F] [Fintype Equations] [DecidableEq Equations]
    [DecidableEq CheckedMask] [DecidableEq Challenge] [Nonempty Challenge] in
private theorem acceptingQueries_subset
    {bound : ℕ}
    (classifier : PolicyDoublyProfiledSoundnessClassifier policy oracle statement
      respond failureProfile arithmeticProfile profileDenominator
        failureDenominator e g)
    (challenge : Challenge)
    (cover : PolicyAcceptingQueryCover policy oracle statement challenge
      (respond challenge) bound) :
    classifier.acceptingQueries challenge ⊆ queriesWithin cover.allowed := by
  classical
  intro query hquery
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, cover.covers query
    (Finset.mem_filter.mp hquery).2⟩

omit [Fintype F] [DecidableEq F] [Fintype Equations] [DecidableEq Equations]
    [DecidableEq CheckedMask] [Nonempty Challenge] in
theorem acceptingQueries_card_le
    (classifier : PolicyDoublyProfiledSoundnessClassifier policy oracle statement
      respond failureProfile arithmeticProfile profileDenominator
        failureDenominator e g)
    (challenge : Challenge) :
    (classifier.acceptingQueries challenge).card ≤
      if challenge ∈ classifier.failure then
        (classifier.failureAgreement challenge).choose r
      else
        (max (n - e - 1)
          (min n (g + classifier.agreement challenge))).choose r := by
  classical
  by_cases hfailure : challenge ∈ classifier.failure
  · simp only [hfailure, ↓reduceIte]
    let cover := Classical.choice (classifier.failure_cover challenge hfailure)
    exact (Finset.card_le_card
      (acceptingQueries_subset classifier challenge cover)).trans
        (card_queriesWithin_le cover.allowed cover.allowed_card)
  · simp only [hfailure, ↓reduceIte]
    by_cases hempty : classifier.acceptingQueries challenge = ∅
    · simp [hempty]
    · obtain ⟨query, hquery⟩ := Finset.nonempty_iff_ne_empty.mpr hempty
      have hexecution : ∃ query : QuerySet n r,
          policy.accepts statement challenge (respond challenge) query
            (openSchemeOracle oracle query) :=
        ⟨query, (Finset.mem_filter.mp hquery).2⟩
      rcases classifier.uniform_cover challenge hfailure hexecution with
        hfar | harithmetic
      · let far := Classical.choice hfar
        have hcard := Finset.card_le_card
          (acceptingQueries_subset classifier challenge far)
        have hwithin := hcard.trans
          (card_queriesWithin_le far.allowed far.allowed_card)
        exact hwithin.trans (Nat.choose_le_choose r (le_max_left _ _))
      · let arithmetic := Classical.choice harithmetic
        have hcard := Finset.card_le_card
          (acceptingQueries_subset classifier challenge arithmetic)
        have hwithin := hcard.trans
          (card_queriesWithin_le arithmetic.allowed arithmetic.allowed_card)
        exact hwithin.trans (Nat.choose_le_choose r (le_max_right _ _))

/-! Agreement bands retain both pieces of information needed by a graded
Fiat–Shamir count: the number of challenges in a band and the maximum number
of queries accepted at any challenge in that band.  In particular, the tail
bound is evaluated at the lower endpoint and the cover at the upper endpoint.
The upper tail bound alone cannot be subtracted at adjacent endpoints to
obtain a bound for an exact agreement value. -/

noncomputable def failureBand
    (classifier : PolicyDoublyProfiledSoundnessClassifier policy oracle statement
      respond failureProfile arithmeticProfile profileDenominator
        failureDenominator e g) (lo hi : ℕ) : Finset Challenge := by
  classical
  exact Finset.univ.filter fun challenge =>
    challenge ∈ classifier.failure ∧ lo ≤ classifier.failureAgreement challenge ∧
      classifier.failureAgreement challenge ≤ hi

noncomputable def arithmeticBand
    (classifier : PolicyDoublyProfiledSoundnessClassifier policy oracle statement
      respond failureProfile arithmeticProfile profileDenominator
        failureDenominator e g) (lo hi : ℕ) : Finset Challenge := by
  classical
  exact Finset.univ.filter fun challenge =>
    challenge ∉ classifier.failure ∧ lo ≤ classifier.agreement challenge ∧
      classifier.agreement challenge ≤ hi

omit [Fintype F] [DecidableEq F] [Fintype Equations] [DecidableEq Equations]
    [DecidableEq CheckedMask] [Nonempty Challenge] in
theorem failureBand_card_le
    (classifier : PolicyDoublyProfiledSoundnessClassifier policy oracle statement
      respond failureProfile arithmeticProfile profileDenominator
        failureDenominator e g) (lo hi : ℕ) (hlo : lo ≤ n) :
    failureDenominator * (classifier.failureBand lo hi).card ≤
      failureProfile.labelsAtLeast lo * Fintype.card Challenge := by
  classical
  have hsub : classifier.failureBand lo hi ⊆
      AgreementProfile.restrictedTailSet classifier.failure
        classifier.failureAgreement lo := by
    intro challenge hmem
    simp only [failureBand, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    exact Finset.mem_filter.mpr ⟨hmem.1, hmem.2.1⟩
  exact (Nat.mul_le_mul_left _ (Finset.card_le_card hsub)).trans
    (classifier.failureAgreement_density lo hlo)

omit [Fintype F] [DecidableEq F] [Fintype Equations] [DecidableEq Equations]
    [DecidableEq CheckedMask] [Nonempty Challenge] in
theorem arithmeticBand_card_le
    (classifier : PolicyDoublyProfiledSoundnessClassifier policy oracle statement
      respond failureProfile arithmeticProfile profileDenominator
        failureDenominator e g) (lo hi : ℕ) (hlo : lo ≤ n) :
    profileDenominator * (classifier.arithmeticBand lo hi).card ≤
      arithmeticProfile.labelsAtLeast lo * Fintype.card Challenge := by
  classical
  have hsub : classifier.arithmeticBand lo hi ⊆
      AgreementProfile.tailSet classifier.agreement lo := by
    intro challenge hmem
    simp only [arithmeticBand, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem.2.1⟩
  exact (Nat.mul_le_mul_left _ (Finset.card_le_card hsub)).trans
    (classifier.agreement_density lo hlo)

omit [Fintype F] [DecidableEq F] [Fintype Equations] [DecidableEq Equations]
    [DecidableEq CheckedMask] [Nonempty Challenge] in
theorem acceptingQueries_card_le_of_mem_failureBand
    (classifier : PolicyDoublyProfiledSoundnessClassifier policy oracle statement
      respond failureProfile arithmeticProfile profileDenominator
        failureDenominator e g) (lo hi : ℕ) (challenge : Challenge)
    (hmem : challenge ∈ classifier.failureBand lo hi) :
    (classifier.acceptingQueries challenge).card ≤ hi.choose r := by
  classical
  simp only [failureBand, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
  have hcover := classifier.acceptingQueries_card_le challenge
  simp only [hmem.1, ↓reduceIte] at hcover
  exact hcover.trans (Nat.choose_le_choose r hmem.2.2)

omit [Fintype F] [DecidableEq F] [Fintype Equations] [DecidableEq Equations]
    [DecidableEq CheckedMask] [Nonempty Challenge] in
theorem acceptingQueries_card_le_of_mem_arithmeticBand
    (classifier : PolicyDoublyProfiledSoundnessClassifier policy oracle statement
      respond failureProfile arithmeticProfile profileDenominator
        failureDenominator e g) (lo hi : ℕ) (challenge : Challenge)
    (hmem : challenge ∈ classifier.arithmeticBand lo hi) :
    (classifier.acceptingQueries challenge).card ≤
      (max (n - e - 1) (min n (g + hi))).choose r := by
  classical
  simp only [arithmeticBand, Finset.mem_filter, Finset.mem_univ, true_and] at hmem
  have hcover := classifier.acceptingQueries_card_le challenge
  simp only [hmem.1, ↓reduceIte] at hcover
  exact hcover.trans (Nat.choose_le_choose r
    (max_le_max_left (n - e - 1)
      (min_le_min_left n (Nat.add_le_add_left hmem.2.2 g))))

omit [Fintype F] [DecidableEq F] [Fintype Equations] [DecidableEq Equations]
    [DecidableEq CheckedMask] in
theorem acceptanceRate_le
    (classifier : PolicyDoublyProfiledSoundnessClassifier policy oracle statement
      respond failureProfile arithmeticProfile profileDenominator
        failureDenominator e g)
    (hprofile : 0 < profileDenominator)
    (hfailureDenominator : 0 < failureDenominator)
    (hquery : r ≤ n) :
    classifier.acceptanceRate ≤
      failureProfile.contribution failureDenominator n n 0 r +
        arithmeticProfile.contribution profileDenominator n e g r := by
  classical
  have hchallenge : 0 < Fintype.card Challenge := Fintype.card_pos
  have hqueries : 0 < n.choose r := Nat.choose_pos hquery
  have hperChallenge (challenge : Challenge) :
      ((classifier.acceptingQueries challenge).card : ℚ) / n.choose r ≤
        (if challenge ∈ classifier.failure then
          AgreementProfile.coverRatio n n 0 r
            (classifier.failureAgreement challenge)
        else 0) +
          AgreementProfile.coverRatio n e g r
            (classifier.agreement challenge) := by
    have hcard := classifier.acceptingQueries_card_le challenge
    by_cases hfailure : challenge ∈ classifier.failure
    · simp only [hfailure, ↓reduceIte] at hcard ⊢
      have hratio : ((classifier.acceptingQueries challenge).card : ℚ) /
          n.choose r ≤
          (((classifier.failureAgreement challenge).choose r : ℕ) : ℚ) /
            n.choose r := by
        apply div_le_div_of_nonneg_right
        · exact_mod_cast hcard
        · positivity
      have hcover : 0 ≤ AgreementProfile.coverRatio n e g r
          (classifier.agreement challenge) := by
        unfold AgreementProfile.coverRatio hypergeometricRatio
        positivity
      have hagreement := classifier.failureAgreement_le challenge hfailure
      have heq : AgreementProfile.coverRatio n n 0 r
          (classifier.failureAgreement challenge) =
          (((classifier.failureAgreement challenge).choose r : ℕ) : ℚ) /
            n.choose r := by
        simp [AgreementProfile.coverRatio, hypergeometricRatio, hagreement]
      rw [heq]
      linarith
    · simp only [hfailure, ↓reduceIte, zero_add] at hcard ⊢
      have hratio : ((classifier.acceptingQueries challenge).card : ℚ) /
          n.choose r ≤ (((max (n - e - 1)
            (min n (g + classifier.agreement challenge))).choose r : ℕ) : ℚ) /
              n.choose r := by
        apply div_le_div_of_nonneg_right
        · exact_mod_cast hcard
        · positivity
      simpa [hypergeometricRatio, AgreementProfile.coverRatio] using hratio
  have hsum := Finset.sum_le_sum (s := Finset.univ)
    fun challenge _ => hperChallenge challenge
  have hfailure := AgreementProfile.restricted_average_coverRatio_le_contribution
    failureDenominator n n 0 r failureProfile classifier.failure
      classifier.failureAgreement hfailureDenominator
      classifier.failureAgreement_le classifier.failureAgreement_density
  have hagreement := AgreementProfile.average_coverRatio_le_contribution
    profileDenominator n e g r arithmeticProfile classifier.agreement hprofile
      classifier.agreement_le classifier.agreement_density
  have hfailureSum :
      (∑ challenge : Challenge,
          if challenge ∈ classifier.failure then
            AgreementProfile.coverRatio n n 0 r
              (classifier.failureAgreement challenge)
          else 0) =
        ∑ challenge ∈ classifier.failure,
          AgreementProfile.coverRatio n n 0 r
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
  unfold acceptanceRate
  rw [show (∑ challenge, (classifier.acceptingQueries challenge).card : ℚ) /
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
          AgreementProfile.coverRatio n n 0 r
            (classifier.failureAgreement challenge)) /
              Fintype.card Challenge +
          (∑ challenge, AgreementProfile.coverRatio n e g r
            (classifier.agreement challenge)) /
              Fintype.card Challenge := by
    rw [div_le_iff₀ (by exact_mod_cast hchallenge)]
    calc
      _ ≤ (∑ challenge ∈ classifier.failure,
            AgreementProfile.coverRatio n n 0 r
              (classifier.failureAgreement challenge)) +
          ∑ challenge, AgreementProfile.coverRatio n e g r
            (classifier.agreement challenge) := by
        simpa [mul_assoc] using hsum
      _ = ((∑ challenge ∈ classifier.failure,
            AgreementProfile.coverRatio n n 0 r
              (classifier.failureAgreement challenge)) /
                Fintype.card Challenge +
          (∑ challenge, AgreementProfile.coverRatio n e g r
            (classifier.agreement challenge)) /
                Fintype.card Challenge) * Fintype.card Challenge := by
        field_simp
  linarith

omit [Fintype F] [DecidableEq F] [Fintype Equations] [DecidableEq Equations]
    [DecidableEq CheckedMask] [Nonempty Challenge] in
theorem protocol_acceptanceRate_eq
    (classifier : PolicyDoublyProfiledSoundnessClassifier policy oracle statement
      respond failureProfile arithmeticProfile profileDenominator
        failureDenominator e g)
    (prover : IPCPProver
      (ConstraintSystem F nw nq logicalWidth Equations)
      (SchemeOracle F CheckedMask DirectMask nw nq n 1)
      Challenge Response)
    (horacle : prover.commit statement = oracle)
    (hrespond : ∀ challenge,
      prover.respond statement oracle challenge = respond challenge) :
    policy.protocol.acceptanceRate prover statement =
      classifier.acceptanceRate := by
  classical
  have hfilter :
      (Finset.univ.filter fun coins : Challenge × QuerySet n r =>
        policy.protocol.accepts prover statement coins = true) =
      Finset.univ.filter fun coins =>
        policy.accepts statement coins.1 (respond coins.1)
          coins.2 (openSchemeOracle oracle coins.2) := by
    ext coins
    simp [PublicCoinIPCP.accepts, PublicCoinIPCP.run,
      SchemeProtocolPolicy.protocol, horacle, hrespond]
  have hnumerator :
      (Finset.univ.filter fun coins : Challenge × QuerySet n r =>
        policy.protocol.accepts prover statement coins = true).card =
        ∑ challenge, (classifier.acceptingQueries challenge).card := by
    rw [hfilter]
    simpa only [acceptingQueries] using
      (Internal.card_filter_product_eq_sum
        (accepts := fun challenge query =>
          policy.accepts statement challenge (respond challenge)
            query (openSchemeOracle oracle query)))
  have hdenominator :
      Fintype.card (Challenge × QuerySet n r) =
        Fintype.card Challenge * n.choose r := by
    rw [Fintype.card_prod, QuerySet.fintype_card]
  unfold PublicCoinIPCP.acceptanceRate finiteProtocolAcceptanceRate acceptanceRate
  rw [hnumerator, hdenominator]
  push_cast
  rfl

omit [Fintype F] [DecidableEq F] [Fintype Equations] [DecidableEq Equations]
    [DecidableEq CheckedMask] in
/-- A family of classifiers indexed by arbitrary fixed auxiliary data gives
the same accepting-pair density bound for every resulting response strategy.
The bound remains uniform over the auxiliary data used to select the response
strategy. -/
theorem strategyUniform_acceptingPairs_density_le
    {Data : Type*}
    (respondBy : Data → Challenge → Response)
    (classifier : ∀ data,
      PolicyDoublyProfiledSoundnessClassifier policy oracle statement
        (respondBy data) failureProfile arithmeticProfile profileDenominator
          failureDenominator e g)
    (hprofile : 0 < profileDenominator)
    (hfailureDenominator : 0 < failureDenominator)
    (hquery : r ≤ n) (data : Data) :
    (strategyAcceptingPairs (policy := policy) (oracle := oracle)
      (statement := statement) (respondBy data)).card /
        (Fintype.card (QuerySet n r) * Fintype.card Challenge) ≤
      failureProfile.contribution failureDenominator n n 0 r +
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
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩
        ⟩
      invFun := fun pair => ⟨(pair.1.2, pair.1.1), by
        have hp := (Finset.mem_filter.mp pair.2).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hp⟩
        ⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
    calc
      left.card = Fintype.card ↥left := by simp
      _ = Fintype.card ↥right := Fintype.card_congr swap
      _ = right.card := by simp
  rw [hevent, mul_comm,
    current.acceptingPairs_density_eq_acceptanceRate]
  exact current.acceptanceRate_le hprofile hfailureDenominator hquery

end PolicyDoublyProfiledSoundnessClassifier

structure PolicyArithmeticCertificate
    (policy : SchemeProtocolPolicy (Equations := Equations) C layout
      Challenge Response CheckedMask DirectMask nw nq 1)
    (oracle : SchemeOracle F CheckedMask DirectMask nw nq n 1)
    (statement : ConstraintSystem F nw nq logicalWidth Equations)
    (respond : Challenge → Response)
    (liftList : PolicyLiftListCertificate policy oracle respond e g radius L)
    (profile : AgreementProfile n) (profileDenominator : ℕ) where
  agreement : Challenge → ℕ
  agreement_le : ∀ challenge, agreement challenge ≤ n
  agreement_density : ∀ a ≤ n,
    profileDenominator * (AgreementProfile.tailSet agreement a).card ≤
      profile.labelsAtLeast a * Fintype.card Challenge
  constraint_cover : ∀ challenge candidate,
    candidate ∈ liftList.candidates →
    candidate.proximityRow (policy.proximityWeights challenge 0) =
      policy.proximityResponse (respond challenge) 0 →
    (candidate.remainingBadColumns (policy.proximityWeights challenge 0)
      (policy.proximityResponse (respond challenge) 0)).card ≤ g →
    (schemeProximityDisagreement oracle (policy.proximityWeights challenge 0)
      (policy.proximityResponse (respond challenge) 0)).card ≤ e →
    Nonempty (PolicyAcceptingQueryCover policy oracle statement challenge
      (respond challenge) (min n (g + agreement challenge)))

namespace PolicyLiftListCertificate

omit [Fintype F] [Fintype Equations] [DecidableEq Equations]
    [DecidableEq CheckedMask] [Nonempty Challenge] in
/-- Assemble the checked agreement profile from candidate-local exceptional
sets and query covers. This is shared by checked masks and direct products. -/
theorem exceptionalArithmeticCertificate_nonempty
    (certificate : PolicyLiftListCertificate policy oracle respond
      e g radius L)
    (cutoff profileDenominator : ℕ)
    (special : SchemeLiftCandidate C oracle radius → Finset Challenge)
    (hspecial : ∀ candidate,
      profileDenominator * (special candidate).card ≤ Fintype.card Challenge)
    (hcover : ∀ candidate challenge, challenge ∉ special candidate →
      ∀ remaining : Finset (Fin n), remaining.card ≤ g →
      (∀ query : QuerySet n r,
        policy.accepts statement challenge (respond challenge) query
          (openSchemeOracle oracle query) →
        query.coordinates ∩ candidate.badColumns ⊆ remaining) →
      Nonempty (PolicyAcceptingQueryCover policy oracle statement challenge
        (respond challenge) (min n (g + cutoff)))) :
    Nonempty (PolicyArithmeticCertificate policy oracle statement respond
      certificate (checkedAgreementProfile profileDenominator L n cutoff)
      profileDenominator) := by
  classical
  let arithmeticSpecial := certificate.candidates.biUnion special
  have harithmeticDensity :
      profileDenominator * arithmeticSpecial.card ≤
        L * Fintype.card Challenge := by
    calc
      profileDenominator * arithmeticSpecial.card ≤
          profileDenominator * ∑ candidate ∈ certificate.candidates,
            (special candidate).card :=
        Nat.mul_le_mul_left _ Finset.card_biUnion_le
      _ = ∑ candidate ∈ certificate.candidates,
          profileDenominator * (special candidate).card := by
        simp_rw [Finset.mul_sum]
      _ ≤ ∑ _candidate ∈ certificate.candidates,
          Fintype.card Challenge :=
        Finset.sum_le_sum fun candidate _ => hspecial candidate
      _ = certificate.candidates.card * Fintype.card Challenge := by simp
      _ ≤ L * Fintype.card Challenge :=
        Nat.mul_le_mul_right _ certificate.list_card
  let agreement := fun challenge =>
    if challenge ∈ arithmeticSpecial then n else min n cutoff
  have hagreementLe : ∀ challenge, agreement challenge ≤ n := by
    intro challenge
    simp only [agreement]
    split <;> omega
  have hagreementDensity : ∀ a ≤ n,
      profileDenominator * (AgreementProfile.tailSet agreement a).card ≤
        (checkedAgreementProfile profileDenominator L n cutoff).labelsAtLeast a *
          Fintype.card Challenge := by
    intro a ha
    by_cases hacutoff : a ≤ cutoff
    · have hcard := Finset.card_le_card
        (Finset.subset_univ (AgreementProfile.tailSet agreement a))
      simpa [checkedAgreementProfile, show ¬n < a by omega, hacutoff] using
        Nat.mul_le_mul_left profileDenominator hcard
    · have hsubset : AgreementProfile.tailSet agreement a ⊆
          arithmeticSpecial := by
        intro challenge hchallenge
        have hagreement := (Finset.mem_filter.mp hchallenge).2
        by_cases harithmetic : challenge ∈ arithmeticSpecial
        · exact harithmetic
        · simp [agreement, harithmetic] at hagreement
          omega
      calc
        profileDenominator * (AgreementProfile.tailSet agreement a).card ≤
            profileDenominator * arithmeticSpecial.card :=
          Nat.mul_le_mul_left _ (Finset.card_le_card hsubset)
        _ ≤ L * Fintype.card Challenge := harithmeticDensity
        _ = (checkedAgreementProfile profileDenominator L n cutoff).labelsAtLeast a *
              Fintype.card Challenge := by
          simp [checkedAgreementProfile, show ¬n < a by omega, hacutoff]
  refine ⟨{
    agreement := agreement
    agreement_le := hagreementLe
    agreement_density := hagreementDensity
    constraint_cover := ?_ }⟩
  intro challenge candidate hcandidate _hresponse hremaining _hsmall
  by_cases hcandidateSpecial : challenge ∈ special candidate
  · have hglobal : challenge ∈ arithmeticSpecial :=
      Finset.mem_biUnion.mpr ⟨candidate, hcandidate, hcandidateSpecial⟩
    exact ⟨{
      allowed := Finset.univ
      allowed_card := by simp [agreement, hglobal]
      covers := fun _ _ => Finset.subset_univ _ }⟩
  · let remaining := candidate.remainingBadColumns
      (policy.proximityWeights challenge 0)
      (policy.proximityResponse (respond challenge) 0)
    have hbad : ∀ query : QuerySet n r,
        policy.accepts statement challenge (respond challenge) query
          (openSchemeOracle oracle query) →
        query.coordinates ∩ candidate.badColumns ⊆ remaining := by
      intro query haccept
      exact candidate.query_bad_subset_remaining
        (policy.proximityWeights challenge 0)
        (policy.proximityResponse (respond challenge) 0) query
        (policy.accepts_proximity statement challenge (respond challenge)
          query (openSchemeOracle oracle query) haccept 0)
    obtain ⟨cover⟩ := hcover candidate challenge hcandidateSpecial remaining
      hremaining hbad
    exact ⟨{
      allowed := cover.allowed
      allowed_card := by
        by_cases hglobal : challenge ∈ arithmeticSpecial
        · simpa [agreement, hglobal] using Finset.card_le_univ cover.allowed
        · simp only [agreement, hglobal, ↓reduceIte]
          exact cover.allowed_card.trans (by omega)
      covers := cover.covers }⟩

end PolicyLiftListCertificate

namespace PolicyArithmeticCertificate

variable {failureProfile arithmeticProfile : AgreementProfile n}

omit [Fintype F] [Fintype Equations] [DecidableEq Equations]
    [DecidableEq CheckedMask] [DecidableEq Challenge] [Nonempty Challenge] in
theorem doublyProfiledClassifier_nonempty
    (liftList : PolicyLiftListCertificate policy oracle respond e g radius L)
    (arithmetic : PolicyArithmeticCertificate policy oracle statement respond
      liftList arithmeticProfile profileDenominator)
    (hfailureDensity : ∀ a ≤ n,
      failureDenominator *
          (AgreementProfile.restrictedTailSet liftList.failure
            (fun challenge =>
              (schemeProximityAgreement oracle
                (policy.proximityWeights challenge 0)
                (policy.proximityResponse (respond challenge) 0)).card) a).card ≤
        failureProfile.labelsAtLeast a * Fintype.card Challenge) :
    Nonempty (PolicyDoublyProfiledSoundnessClassifier policy oracle statement
      respond failureProfile arithmeticProfile profileDenominator
        failureDenominator e g) := by
  classical
  let failureAgreement := fun challenge : Challenge =>
    (schemeProximityAgreement oracle (policy.proximityWeights challenge 0)
      (policy.proximityResponse (respond challenge) 0)).card
  refine ⟨{
    failure := liftList.failure
    failureAgreement := failureAgreement
    failureAgreement_le := ?_
    failureAgreement_density := ?_
    failure_cover := ?_
    agreement := arithmetic.agreement
    agreement_le := arithmetic.agreement_le
    agreement_density := arithmetic.agreement_density
    uniform_cover := ?_ }⟩
  · intro challenge _
    dsimp [failureAgreement]
    simpa using Finset.card_le_univ
      (schemeProximityAgreement oracle (policy.proximityWeights challenge 0)
        (policy.proximityResponse (respond challenge) 0))
  · intro a ha
    simpa [failureAgreement] using hfailureDensity a ha
  · intro challenge _
    exact ⟨{
      allowed := schemeProximityAgreement oracle
        (policy.proximityWeights challenge 0)
        (policy.proximityResponse (respond challenge) 0)
      allowed_card := by rfl
      covers := fun query haccept =>
        policyProximity_query_subset_agreement statement challenge
          (respond challenge) query haccept }⟩
  · intro challenge hnotFailure hexecution
    obtain ⟨query₀, haccept₀⟩ := hexecution
    by_cases hsmall :
        (schemeProximityDisagreement oracle
          (policy.proximityWeights challenge 0)
          (policy.proximityResponse (respond challenge) 0)).card ≤ e
    · obtain ⟨candidate, hcandidate, hresponse, hremaining⟩ :=
        liftList.lift challenge hnotFailure
          (policy.accepts_proximity statement challenge (respond challenge)
            query₀ (openSchemeOracle oracle query₀) haccept₀ 0).1 hsmall
      right
      exact arithmetic.constraint_cover challenge candidate
        hcandidate hresponse hremaining hsmall
    · left
      have hfar := policyProximity_far_cover statement challenge
        (respond challenge) query₀ haccept₀ (Nat.lt_of_not_ge hsmall)
      exact ⟨{
        allowed := schemeProximityAgreement oracle
          (policy.proximityWeights challenge 0)
          (policy.proximityResponse (respond challenge) 0)
        allowed_card := hfar.2
        covers := fun query haccept =>
          policyProximity_query_subset_agreement statement challenge
            (respond challenge) query haccept }⟩

end PolicyArithmeticCertificate

end LigeroFamily
