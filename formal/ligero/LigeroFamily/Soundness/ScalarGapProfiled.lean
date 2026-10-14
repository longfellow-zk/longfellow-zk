import LigeroFamily.Soundness.ScalarGapExtraction
import LigeroFamily.Soundness.PolicyEventPartition

/-! Agreement-dependent extraction soundness. The verifier below is a proof
restriction: its accepting event is exactly acceptance and failure of the
original response-assisted extractor. It does not change the protocol. -/
namespace LigeroFamily.ScalarGapExtraction
open Finset CodingTheory MultiplicativeCode
open scoped BigOperators Classical
set_option linter.unusedSectionVars false
variable {F CheckedMask DirectMask Equations Challenge Response Tail : Type*}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype CheckedMask] [DecidableEq CheckedMask]
variable [Fintype Equations] [DecidableEq Equations]
variable [Fintype Challenge] [DecidableEq Challenge] [Nonempty Challenge]
variable [Fintype Tail] [DecidableEq Tail]
variable {q r w n nw nq e g d L : ℕ}
variable {C : MultiplicativeCode F r w n}
variable {oracle : SchemeOracle F CheckedMask DirectMask nw nq n 1}
variable {layout : ConstraintLayout F q w}
variable (policy : SchemeProtocolPolicy (Equations := Equations) C layout
  Challenge Response CheckedMask DirectMask nw nq 1)
variable (messages : SchemeLiftCandidate C oracle (e + g) → CoreMessages F nw nq q)

/-- Restrict the event counted, retaining the original policy and extractor. -/
noncomputable def failingPolicy : SchemeProtocolPolicy (Equations := Equations) C layout
    Challenge Response CheckedMask DirectMask nw nq 1 where
  proximityWeights := policy.proximityWeights
  proximityResponse := policy.proximityResponse
  accepts statement challenge response query opening :=
    policy.accepts statement challenge response query opening ∧
      extract policy messages statement challenge response = none
  accepts_proximity statement challenge response query opening h :=
    policy.accepts_proximity statement challenge response query opening h.1

noncomputable def failingExtractor (extractor : SchemeExtractorPolicy policy Tail) :
    SchemeExtractorPolicy (failingPolicy policy messages) Tail where
  challengeProductEquiv := extractor.challengeProductEquiv
  weights_eq := extractor.weights_eq

/-- Candidate arithmetic covers are needed only on close failing responses.
Valid candidates therefore need no false-statement assumption. -/
theorem profiledArithmeticCertificate
    {statement : ConstraintSystem F nw nq q Equations} {respond : Challenge → Response}
    (certificate : PolicyLiftListCertificate (failingPolicy policy messages) oracle
      respond e g (e + g) L)
    (hmin : HasMinimumDistanceAtLeast C.baseCode d) (hradius : e + 2 * g < d)
    (cutoff : ℕ) (labels : ℕ → ℕ) (profile : AgreementProfile n)
    (hfloor : ∀ a ≤ n, a ≤ cutoff → profile.labelsAtLeast a = Fintype.card F)
    (hlabels : ∀ a ≤ n, cutoff < a → profile.labelsAtLeast a = L * labels a)
    (agreement : SchemeLiftCandidate C oracle (e + g) → Challenge → ℕ)
    (hle : ∀ candidate challenge, agreement candidate challenge ≤ n)
    (hdensity : ∀ candidate a, a ≤ n → cutoff < a →
      Fintype.card F * (AgreementProfile.tailSet (agreement candidate) a).card ≤
        labels a * Fintype.card Challenge)
    (hcover : ∀ candidate, ¬statement.Satisfies (messages candidate) →
      ∀ challenge, Compatible policy candidate challenge (respond challenge) →
      Nonempty (PolicyAcceptingQueryCover policy oracle statement challenge
        (respond challenge) (min n (g + agreement candidate challenge)))) :
    Nonempty (PolicyArithmeticCertificate (failingPolicy policy messages) oracle
      statement respond certificate profile (Fintype.card F)) := by
  classical
  let total := fun challenge => certificate.candidates.sup fun candidate =>
    agreement candidate challenge
  have htotal : ∀ challenge, total challenge ≤ n := by
    intro challenge; exact Finset.sup_le fun candidate _ => hle candidate challenge
  refine ⟨{
    agreement := total
    agreement_le := htotal
    agreement_density := ?_
    constraint_cover := ?_ }⟩
  · intro a ha
    by_cases hbelow : a ≤ cutoff
    · rw [hfloor a ha hbelow]
      exact Nat.mul_le_mul_left _ (Finset.card_le_card (Finset.subset_univ _))
    · have hpositive : 0 < a := by omega
      let tails := fun candidate => AgreementProfile.tailSet (agreement candidate) a
      have hsubset : AgreementProfile.tailSet total a ⊆ certificate.candidates.biUnion tails := by
        intro challenge hmem
        obtain ⟨candidate, hcandidate, hle⟩ :=
          (Finset.le_sup_iff hpositive).mp (Finset.mem_filter.mp hmem).2
        exact Finset.mem_biUnion.mpr ⟨candidate, hcandidate,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hle⟩⟩
      calc
        _ ≤ Fintype.card F * (certificate.candidates.biUnion tails).card :=
          Nat.mul_le_mul_left _ (Finset.card_le_card hsubset)
        _ ≤ Fintype.card F * ∑ candidate ∈ certificate.candidates, (tails candidate).card :=
          Nat.mul_le_mul_left _ Finset.card_biUnion_le
        _ = ∑ candidate ∈ certificate.candidates, Fintype.card F * (tails candidate).card := by
          simp_rw [Finset.mul_sum]
        _ ≤ ∑ _candidate ∈ certificate.candidates, labels a * Fintype.card Challenge :=
          Finset.sum_le_sum fun candidate _ => hdensity candidate a ha (by omega)
        _ = certificate.candidates.card * (labels a * Fintype.card Challenge) := by simp
        _ ≤ L * (labels a * Fintype.card Challenge) :=
          Nat.mul_le_mul_right _ certificate.list_card
        _ = profile.labelsAtLeast a * Fintype.card Challenge := by
          rw [hlabels a ha (by omega)]; simp only [Nat.mul_assoc]
  · intro challenge candidate hcandidate hresponse hremaining hsmall
    by_cases hex : ∃ query : QuerySet n r, (failingPolicy policy messages).accepts
        statement challenge (respond challenge) query (openSchemeOracle oracle query)
    · obtain ⟨query, hacc⟩ := hex
      have hc : Compatible policy candidate challenge (respond challenge) := ⟨hresponse, hremaining⟩
      have hns := extract_none_invalid_of_compatible policy messages statement hmin hradius
        challenge (respond challenge) hsmall candidate hc hacc.2
      obtain ⟨cover⟩ := hcover candidate hns challenge hc
      refine ⟨{ allowed := cover.allowed, allowed_card := ?_, covers := ?_ }⟩
      · exact cover.allowed_card.trans (min_le_min_left n (Nat.add_le_add_left
          (Finset.le_sup (f := fun candidate => agreement candidate challenge) hcandidate) g))
      · intro query hacc; exact cover.covers query hacc.1
    · exact ⟨{
        allowed := ∅
        allowed_card := by simp
        covers := fun query hacc => False.elim (hex ⟨query, hacc⟩) }⟩

/-- Checked arithmetic retains its complete profile on failing responses. -/
theorem checkedProfiledArithmeticCertificate
    {statement : ConstraintSystem F nw nq q Equations} {respond : Challenge → Response}
    (certificate : PolicyLiftListCertificate (failingPolicy policy messages) oracle
      respond e g (e + g) L)
    (hmin : HasMinimumDistanceAtLeast C.baseCode d) (hradius : e + 2 * g < d)
    (cutoff : ℕ)
    (special : SchemeLiftCandidate C oracle (e + g) → Finset Challenge)
    (hdensity : ∀ candidate, Fintype.card F * (special candidate).card ≤ Fintype.card Challenge)
    (hcover : ∀ candidate, ¬statement.Satisfies (messages candidate) →
      ∀ challenge, challenge ∉ special candidate →
      Compatible policy candidate challenge (respond challenge) →
      Nonempty (PolicyAcceptingQueryCover policy oracle statement challenge
        (respond challenge) (min n (g + cutoff)))) :
    Nonempty (PolicyArithmeticCertificate (failingPolicy policy messages) oracle
      statement respond certificate
      (checkedAgreementProfile (Fintype.card F) L n cutoff) (Fintype.card F)) := by
  classical
  let agreement := fun candidate challenge =>
    if challenge ∈ special candidate then n else min n cutoff
  refine profiledArithmeticCertificate policy messages certificate hmin hradius cutoff
    (fun _ => 1) (checkedAgreementProfile (Fintype.card F) L n cutoff)
    ?_ ?_ agreement ?_ ?_ ?_
  · intro a ha hbelow; simp [checkedAgreementProfile, show ¬ n < a by omega, hbelow]
  · intro a ha habove; simp [checkedAgreementProfile, show ¬ n < a by omega, show ¬ a ≤ cutoff by omega]
  · intro candidate challenge; dsimp only [agreement]; split <;> omega
  · intro candidate a ha habove
    have hsubset : AgreementProfile.tailSet (agreement candidate) a ⊆ special candidate := by
      intro challenge hmem
      have hle := (Finset.mem_filter.mp hmem).2
      by_contra hnot; simp only [agreement, hnot, ↓reduceIte] at hle; omega
    exact (Nat.mul_le_mul_left _ (Finset.card_le_card hsubset)).trans
      (by simpa using hdensity candidate)
  · intro candidate hns challenge hc
    by_cases hspecial : challenge ∈ special candidate
    · exact ⟨{ allowed := univ
               allowed_card := by simp [agreement, hspecial]
               covers := fun _ _ => Finset.subset_univ _ }⟩
    · obtain ⟨cover⟩ := hcover candidate hns challenge hspecial hc
      exact ⟨{ allowed := cover.allowed
               allowed_card := by
                 simp only [agreement, hspecial, ↓reduceIte]
                 exact cover.allowed_card.trans (by omega)
               covers := cover.covers }⟩

/-- The refined all-statement bound. Every proximity exception is weighted by
its actual agreement; arithmetic pays the common query baseline once. -/
theorem profiled_extraction_failure
    [Nonempty (SchemeTestedRow CheckedMask nw nq 1)]
    {statement : ConstraintSystem F nw nq q Equations}
    {outerBound : ℕ} {localBound : ℕ → ℕ}
    (extractor : SchemeExtractorPolicy policy Tail)
    (hmin : HasMinimumDistanceAtLeast C.baseCode d)
    (conditions : IntegratedSelectedMCALineConditions C.baseCode
      (Fintype.card F) e g d outerBound localBound)
    (arithmeticProfile : AgreementProfile n) (cutoff : ℕ)
    (hcutoff : cutoff ≤ n)
    (hfloor : ∀ a ≤ cutoff, Fintype.card F ≤ arithmeticProfile.labelsAtLeast a)
    (respond : Challenge → Response)
    (harithmetic : ∀ certificate : PolicyLiftListCertificate
      (failingPolicy policy messages) oracle respond e g (e + g)
      (InterleavedJohnson.listBound n d (e + g)),
      Nonempty (PolicyArithmeticCertificate (failingPolicy policy messages)
        oracle statement respond certificate arithmeticProfile (Fintype.card F))) :
    ((univ.filter fun pair : Challenge × QuerySet n r =>
      policy.accepts statement pair.1 (respond pair.1) pair.2
        (openSchemeOracle oracle pair.2) ∧
      extract policy messages statement pair.1 (respond pair.1) = none).card : ℚ) /
        Fintype.card (Challenge × QuerySet n r) ≤
      (SchemeSelectedMCA.selectedMCAOptimizedIntegratedFailureProfile
        (Fintype.card F) n e g d outerBound localBound).excessContribution
          (SchemeSelectedMCA.selectedMCAOptimizedFailureDenominator (Fintype.card F) g)
          n n 0 r (max (n - e - 1) (min n (g + cutoff))) +
      arithmeticProfile.contribution (Fintype.card F) n e g r := by
  obtain ⟨certificate, hdensity⟩ := (failingExtractor policy messages extractor).exists_profiledPolicyLiftList_of_endpointOptimizedIntegratedLine
      (oracle := oracle) (respond := respond) hmin conditions
  obtain ⟨arithmetic⟩ := harithmetic certificate
  obtain ⟨classifier⟩ := arithmetic.doublyProfiledClassifier_nonempty certificate hdensity
  let prover : IPCPProver (ConstraintSystem F nw nq q Equations)
      (SchemeOracle F CheckedMask DirectMask nw nq n 1) Challenge Response :=
    ⟨fun _ => oracle, fun _ _ => respond⟩
  have hr := classifier.acceptanceRate_le_eventPartition cutoff Fintype.card_pos
    (Nat.mul_pos Fintype.card_pos (Nat.sub_pos_of_lt conditions.outer.punctured.field_large))
    C.query_le_length hcutoff hfloor
  rw [← classifier.protocol_acceptanceRate_eq prover rfl (fun _ => rfl)] at hr
  simpa [PublicCoinIPCP.acceptanceRate, finiteProtocolAcceptanceRate,
    PublicCoinIPCP.accepts, PublicCoinIPCP.run, SchemeProtocolPolicy.protocol,
    failingPolicy, prover, SchemeSelectedMCA.selectedMCAOptimizedIntegratedFailureProfile,
    SchemeSelectedMCA.selectedMCAOptimizedFailureDenominator] using hr

section UniformEnvelope
variable [Fintype Response] [Nonempty Response]
variable (statement : ConstraintSystem F nw nq q Equations)

noncomputable def failingQueries (challenge : Challenge) (response : Response) : Finset (QuerySet n r) :=
  univ.filter fun query => policy.accepts statement challenge response query
    (openSchemeOracle oracle query) ∧ extract policy messages statement challenge response = none

/-- One envelope fixed from the oracle and statement, dominating every response.
Its maximum is a proof device and is not used by the witness extractor. -/
noncomputable def profiledUniformEnvelope (challenge : Challenge) : ℚ :=
  (((univ : Finset Response).sup fun response =>
    (failingQueries policy messages statement challenge response).card : ℕ) : ℚ) / n.choose r

theorem response_fraction_le_profiledUniformEnvelope (challenge : Challenge) (response : Response) :
    ((failingQueries policy messages statement challenge response).card : ℚ) / n.choose r ≤
      profiledUniformEnvelope policy messages statement challenge := by
  classical
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  exact_mod_cast (Finset.le_sup (f := fun response =>
    (failingQueries policy messages statement challenge response).card) (Finset.mem_univ response))

private theorem maximizingResponse_exists (challenge : Challenge) : ∃ response : Response,
    (univ : Finset Response).sup (fun response =>
      (failingQueries policy messages statement challenge response).card) =
    (failingQueries policy messages statement challenge response).card := by
  classical
  obtain ⟨response, _, heq⟩ := Finset.exists_mem_eq_sup (univ : Finset Response)
    Finset.univ_nonempty (fun response => (failingQueries policy messages statement challenge response).card)
  exact ⟨response, heq⟩

/-- Strategy-uniform bounds imply a response-uniform envelope bound without
counting responses. Select a maximizing response separately at each challenge. -/
theorem profiledUniformEnvelope_mean_of_strategies (epsilon : ℚ)
    (hstrategy : ∀ respond : Challenge → Response,
      ((univ.filter fun pair : Challenge × QuerySet n r =>
        policy.accepts statement pair.1 (respond pair.1) pair.2 (openSchemeOracle oracle pair.2) ∧
        extract policy messages statement pair.1 (respond pair.1) = none).card : ℚ) /
          Fintype.card (Challenge × QuerySet n r) ≤ epsilon) :
    (∑ challenge : Challenge, profiledUniformEnvelope policy messages statement challenge) /
      Fintype.card Challenge ≤ epsilon := by
  classical
  let respond := fun challenge => (maximizingResponse_exists policy messages statement challenge).choose
  have hmax : ∀ challenge, (univ : Finset Response).sup (fun response =>
      (failingQueries policy messages statement challenge response).card) =
      (failingQueries policy messages statement challenge (respond challenge)).card := by
    intro challenge; exact (maximizingResponse_exists policy messages statement challenge).choose_spec
  have hr := hstrategy respond
  have hcount := Internal.card_filter_product_eq_sum (First := Challenge) (Second := QuerySet n r)
    (fun challenge query => policy.accepts statement challenge (respond challenge) query
      (openSchemeOracle oracle query) ∧ extract policy messages statement challenge (respond challenge) = none)
  rw [hcount, Fintype.card_prod, QuerySet.fintype_card, Nat.cast_mul, Nat.cast_sum] at hr
  have heq : (∑ challenge : Challenge, profiledUniformEnvelope policy messages statement challenge) /
      Fintype.card Challenge =
      (∑ challenge : Challenge, ((failingQueries policy messages statement challenge
        (respond challenge)).card : ℚ)) / ((Fintype.card Challenge : ℚ) * n.choose r) := by
    simp only [profiledUniformEnvelope, hmax, div_eq_mul_inv, ← Finset.sum_mul]
    ring
  rw [heq]
  exact hr
end UniformEnvelope

end LigeroFamily.ScalarGapExtraction
