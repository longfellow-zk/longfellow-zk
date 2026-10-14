import Ligero.V2.Soundness.CheckedSoundness
import LigeroFamily.Soundness.ChallengeCounting
import LigeroFamily.Soundness.PolicyEventPartition

/-!
# Direct checked-mask profile

The checked-mask specialization of the common lift-list theorem.  A false
statement fixes one nonzero residual per decoded candidate.  The only
exceptional challenges are those annihilating that residual.
-/

namespace Ligero.V2

open LigeroFamily

open CodingTheory MultiplicativeCode SchemeLiftCandidate

variable {F Equations : Type*} [Field F] [Fintype F] [DecidableEq F]
variable [Fintype Equations] [DecidableEq Equations]
variable {r w n nw nq e g radius failureDenominator L : ℕ}
variable {C : MultiplicativeCode F r w n} {M : C.MaskingBasis}
variable {oracle : Oracle F nw nq n 1}
variable {statement : ConstraintSystem F nw nq w Equations}
variable {respond : Challenge F nw nq 1 Equations → Response F r w n 1}

local notation "checkedPolicy" =>
  SchemeVerifier.policy (Equations := Equations) (nw := nw) (nq := nq)
    (repetitions := 1) C (scheme C M)

/-- One candidate's exceptional arithmetic challenges and its uniform cover
outside that set. -/
structure UniformCheckedCandidateArithmetic
    (candidate : SchemeLiftCandidate C oracle radius) where
  special : Finset (Challenge F nw nq 1 Equations)
  density : Fintype.card F * special.card ≤
    Fintype.card (Challenge F nw nq 1 Equations)
  cover : ∀ challenge (response : Response F r w n 1), challenge ∉ special →
    ∀ remaining : Finset (Fin n), remaining.card ≤ g →
    (∀ query : QuerySet n r,
      SchemeVerifier.Accepts C (scheme C M) statement challenge
        response query (openSchemeOracle oracle query) →
      query.coordinates ∩ candidate.badColumns ⊆ remaining) →
    0 < C.k →
    Nonempty (PolicyAcceptingQueryCover checkedPolicy oracle statement challenge
      response (min n (g + (2 * C.k - 1))))

namespace UniformCheckedCandidateArithmetic

omit [DecidableEq Equations] in
theorem nonempty_of_false
    (candidate : SchemeLiftCandidate C oracle radius)
    (hns : ¬statement.Satisfies candidate.decodedMessages) :
    Nonempty (UniformCheckedCandidateArithmetic (M := M) (g := g)
      (statement := statement) candidate) := by
  classical
  rcases candidate.residual_of_not_satisfies statement hns with
    hlinear | ⟨i, hquadratic⟩
  · let equations := affineEquationSolutions
      (candidate.checkedLinearResidual statement)
      (-candidate.checkedLinearZRCoefficientSum)
    let special := SchemeInternal.liftLinear
      (CheckedMask := Mask) (nw := nw) (nq := nq) equations
    refine ⟨{
      special := special
      density := ?_
      cover := ?_ }⟩
    · rw [← Nat.card_eq_fintype_card
        (α := Challenge F nw nq 1 Equations)]
      simpa [special] using SchemeInternal.liftLinear_density
        (CheckedMask := Mask) (nw := nw) (nq := nq)
        (Fintype.card F) 1 equations (by
          simpa [Nat.card_eq_fintype_card] using
            affineEquationSolutions_density
              (candidate.checkedLinearResidual statement)
              (-candidate.checkedLinearZRCoefficientSum) hlinear)
    · intro challenge response hnotSpecial remaining hremaining hbad hk
      have hnotEquation : (challenge 0).linear ∉ equations := by
        intro hmem
        apply hnotSpecial
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem⟩
      have hnonexceptional : finiteDot (challenge 0).linear
          (candidate.checkedLinearResidual statement) ≠
            -candidate.checkedLinearZRCoefficientSum := by
        simpa [equations, affineEquationSolutions] using hnotEquation
      by_cases hexecution : ∃ query : QuerySet n r,
          SchemeVerifier.Accepts C (scheme C M) statement challenge
            response query (openSchemeOracle oracle query)
      · obtain ⟨query₀, haccept₀⟩ := hexecution
        let allowed := remaining ∪ responseAgreement
          (response.linear 0)
          (candidate.checkedLinearCanonical M statement (challenge 0).linear)
        have hcover₀ := candidate.checked_linear_query_cover M statement
          (challenge 0).linear (response.linear 0) query₀
          (haccept₀ 0).2.1 remaining hremaining hk (hbad query₀ haccept₀)
          hnonexceptional
        refine ⟨{
          allowed := allowed
          allowed_card := ?_
          covers := ?_ }⟩
        · apply Nat.le_min.mpr
          constructor
          · simpa using Finset.card_le_univ allowed
          · change (remaining ∪ responseAgreement
              (response.linear 0)
              (candidate.checkedLinearCanonical M statement
                (challenge 0).linear)).card ≤ g + (2 * C.k - 1)
            calc
              _ ≤ 2 * C.k + g - 1 := hcover₀.2
              _ = g + (2 * C.k - 1) := by omega
        · intro query haccept
          exact (candidate.checked_linear_query_cover M statement
            (challenge 0).linear (response.linear 0) query
            (haccept 0).2.1 remaining hremaining hk (hbad query haccept)
            hnonexceptional).1
      · exact ⟨{
          allowed := ∅
          allowed_card := by simp
          covers := fun query haccept ↦ False.elim
            (hexecution ⟨query, haccept⟩) }⟩
  · let equations := affineEquationSolutions
      (fun row ↦ candidate.checkedQuadraticResidual row i) 0
    let special := SchemeInternal.liftQuadratic
      (CheckedMask := Mask) (Equations := Equations)
      (nw := nw) equations
    refine ⟨{
      special := special
      density := ?_
      cover := ?_ }⟩
    · rw [← Nat.card_eq_fintype_card
        (α := Challenge F nw nq 1 Equations)]
      simpa [special] using SchemeInternal.liftQuadratic_density
        (CheckedMask := Mask) (Equations := Equations) (nw := nw)
        (Fintype.card F) 1 equations (by
          simpa [Nat.card_eq_fintype_card] using
            affineEquationSolutions_density
              (fun row ↦ candidate.checkedQuadraticResidual row i) 0
              hquadratic)
    · intro challenge response hnotSpecial remaining hremaining hbad hk
      have hnotEquation : (challenge 0).quadratic ∉ equations := by
        intro hmem
        apply hnotSpecial
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem⟩
      have hnonexceptional : finiteDot (challenge 0).quadratic
          (fun row ↦ candidate.checkedQuadraticResidual row i) ≠ 0 := by
        simpa [equations, affineEquationSolutions] using hnotEquation
      by_cases hexecution : ∃ query : QuerySet n r,
          SchemeVerifier.Accepts C (scheme C M) statement challenge
            response query (openSchemeOracle oracle query)
      · obtain ⟨query₀, haccept₀⟩ := hexecution
        let allowed := remaining ∪ responseAgreement
          (response.quadratic 0)
          (candidate.checkedQuadraticCanonical M (challenge 0).quadratic)
        have hcover₀ := candidate.checked_quadratic_query_cover M
          (challenge 0).quadratic i (response.quadratic 0) query₀
          (haccept₀ 0).2.2 remaining hremaining hk (hbad query₀ haccept₀)
          hnonexceptional
        refine ⟨{
          allowed := allowed
          allowed_card := ?_
          covers := ?_ }⟩
        · apply Nat.le_min.mpr
          constructor
          · simpa using Finset.card_le_univ allowed
          · change (remaining ∪ responseAgreement
              (response.quadratic 0)
              (candidate.checkedQuadraticCanonical M
                (challenge 0).quadratic)).card ≤ g + (2 * C.k - 1)
            calc
              _ ≤ 2 * C.k + g - 1 := hcover₀.2
              _ = g + (2 * C.k - 1) := by omega
        · intro query haccept
          exact (candidate.checked_quadratic_query_cover M
            (challenge 0).quadratic i (response.quadratic 0) query
            (haccept 0).2.2 remaining hremaining hk (hbad query haccept)
            hnonexceptional).1
      · exact ⟨{
          allowed := ∅
          allowed_card := by simp
          covers := fun query haccept ↦ False.elim
            (hexecution ⟨query, haccept⟩) }⟩

end UniformCheckedCandidateArithmetic

structure CheckedCandidateArithmetic
    (candidate : SchemeLiftCandidate C oracle radius) where
  special : Finset (Challenge F nw nq 1 Equations)
  density : Fintype.card F * special.card ≤
    Fintype.card (Challenge F nw nq 1 Equations)
  cover : ∀ challenge, challenge ∉ special →
    ∀ remaining : Finset (Fin n), remaining.card ≤ g →
    (∀ query : QuerySet n r,
      SchemeVerifier.Accepts C (scheme C M) statement challenge
        (respond challenge) query (openSchemeOracle oracle query) →
      query.coordinates ∩ candidate.badColumns ⊆ remaining) →
    0 < C.k →
    Nonempty (PolicyAcceptingQueryCover checkedPolicy oracle statement challenge
      (respond challenge) (min n (g + (2 * C.k - 1))))

namespace CheckedCandidateArithmetic

omit [DecidableEq Equations] in
theorem nonempty_of_false
    (candidate : SchemeLiftCandidate C oracle radius)
    (hns : ¬statement.Satisfies candidate.decodedMessages) :
    Nonempty (CheckedCandidateArithmetic (M := M) (g := g)
      (statement := statement) (respond := respond) candidate) := by
  obtain ⟨arithmetic⟩ := UniformCheckedCandidateArithmetic.nonempty_of_false (M := M) (g := g) candidate hns
  exact ⟨{
    special := arithmetic.special
    density := arithmetic.density
    cover := fun challenge hnotSpecial remaining hremaining hbad hk =>
      arithmetic.cover challenge (respond challenge) hnotSpecial remaining hremaining hbad hk }⟩

end CheckedCandidateArithmetic

namespace PolicyLiftListCertificate

/-- Checked arithmetic evidence attached to this exact lift-list
certificate. -/
theorem checkedArithmeticCertificate_nonempty
    (certificate : PolicyLiftListCertificate checkedPolicy oracle respond
      e g radius L)
    (hfalse : NoDecodedSolution C oracle radius statement) (hk : 0 < C.k) :
    Nonempty (PolicyArithmeticCertificate checkedPolicy oracle statement respond
      certificate
      (checkedAgreementProfile (Fintype.card F) L n (2 * C.k - 1))
      (Fintype.card F)) := by
  classical
  let arithmetic := fun candidate : SchemeLiftCandidate C oracle radius ↦
    Classical.choice (CheckedCandidateArithmetic.nonempty_of_false
      (M := M) (g := g) (statement := statement) (respond := respond)
      candidate (hfalse candidate))
  apply certificate.exceptionalArithmeticCertificate_nonempty
    (cutoff := 2 * C.k - 1) (profileDenominator := Fintype.card F)
    (special := fun candidate ↦ (arithmetic candidate).special)
  · exact fun candidate ↦ (arithmetic candidate).density
  · intro candidate challenge hspecial remaining hremaining hbad
    exact (arithmetic candidate).cover challenge hspecial remaining hremaining
      hbad hk

/-- Checked V2 soundness through the disjoint event partition.

The checked arithmetic profile pays the shared proximity/arithmetic baseline.
Selected-MCA failure therefore contributes only its query-cover excess above
that baseline.
-/
theorem ligerov2_scheme_soundness_of_eventPartition
    (certificate : PolicyLiftListCertificate checkedPolicy oracle respond
      e g radius L)
    (failureProfile : AgreementProfile n)
    (hfailureDensity : ∀ a ≤ n,
      failureDenominator *
          (AgreementProfile.restrictedTailSet certificate.failure
            (fun challenge ↦
              (schemeProximityAgreement oracle (challenge 0).proximity
                ((respond challenge).proximity 0)).card) a).card ≤
        failureProfile.labelsAtLeast a *
          Fintype.card (Challenge F nw nq 1 Equations))
    (hfalse : NoDecodedSolution C oracle radius statement)
    (prover : IPCPProver
      (ConstraintSystem F nw nq w Equations)
      (Oracle F nw nq n 1) (Challenge F nw nq 1 Equations)
      (Response F r w n 1))
    (horacle : prover.commit statement = oracle)
    (hrespond : ∀ challenge,
      prover.respond statement oracle challenge = respond challenge)
    (hk : 0 < C.k) (hfailureDenominator : 0 < failureDenominator) :
    (Verifier.protocol C M).acceptanceRate prover statement ≤
      failureProfile.excessContribution failureDenominator n n 0 r
        (max (n - e - 1) (min n (g + (2 * C.k - 1)))) +
      (checkedAgreementProfile (Fintype.card F) L n
        (2 * C.k - 1)).contribution (Fintype.card F) n e g r := by
  have hquery : r ≤ n := C.query_le_length
  obtain ⟨arithmetic⟩ :=
    Ligero.V2.PolicyLiftListCertificate.checkedArithmeticCertificate_nonempty
      certificate (M := M) hfalse hk
  let classifier := Classical.choice
    (arithmetic.doublyProfiledClassifier_nonempty certificate hfailureDensity)
  have hfloor : ∀ a ≤ min n (2 * C.k - 1),
      Fintype.card F ≤
        (checkedAgreementProfile (Fintype.card F) L n
          (2 * C.k - 1)).labelsAtLeast a := by
    intro a ha
    simp [checkedAgreementProfile, show ¬n < a by omega,
      show a ≤ 2 * C.k - 1 by omega]
  calc
    (Verifier.protocol C M).acceptanceRate prover statement =
        classifier.acceptanceRate :=
      classifier.protocol_acceptanceRate_eq prover horacle hrespond
    _ ≤ failureProfile.excessContribution failureDenominator n n 0 r
          (max (n - e - 1) (min n (g + min n (2 * C.k - 1)))) +
        (checkedAgreementProfile (Fintype.card F) L n
          (2 * C.k - 1)).contribution (Fintype.card F) n e g r :=
      classifier.acceptanceRate_le_eventPartition
        (min n (2 * C.k - 1)) Fintype.card_pos hfailureDenominator
        hquery (min_le_left _ _) hfloor
    _ = _ := by
      congr 3
      omega

end PolicyLiftListCertificate

end Ligero.V2
