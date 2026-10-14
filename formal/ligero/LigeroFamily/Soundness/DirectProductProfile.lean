import LigeroFamily.Soundness.DirectProductSoundness
import LigeroFamily.Soundness.PolicyEventPartition

/-! # Arithmetic profile for challenge-free direct products -/

namespace LigeroFamily

open CodingTheory MultiplicativeCode SchemeLiftCandidate

variable {F Equations : Type*} [Field F] [Fintype F] [DecidableEq F]
variable [Fintype Equations] [DecidableEq Equations]
variable {logicalWidth r w n nw nq e g radius L failureDenominator : ℕ}
variable {C : MultiplicativeCode F r w n} {M : C.MaskingBasis}
variable {layout : ConstraintLayout F logicalWidth w}
variable {oracle : SchemeOracle F LinearConstraintMask NoMask nw nq n 1}
variable {statement : ConstraintSystem F nw nq logicalWidth Equations}
variable {respond : DirectChallenge F Equations nw nq 1 → DirectResponse F r w n 1}

local notation "directPolicy" =>
  DirectVerifier.policy (Equations := Equations) (nw := nw) (nq := nq)
    (repetitions := 1) C M layout

structure UniformDirectCandidateArithmetic
    (candidate : SchemeLiftCandidate C oracle radius) where
  special : Finset (DirectChallenge F Equations nw nq 1)
  density : Fintype.card F * special.card ≤
    Fintype.card (DirectChallenge F Equations nw nq 1)
  cover : ∀ challenge (response : DirectResponse F r w n 1), challenge ∉ special →
    ∀ remaining : Finset (Fin n), remaining.card ≤ g →
    (∀ query : QuerySet n r,
      DirectVerifier.Accepts C M layout statement challenge
        response query (openSchemeOracle oracle query) →
      query.coordinates ∩ candidate.badColumns ⊆ remaining) →
    0 < C.k →
    Nonempty (PolicyAcceptingQueryCover directPolicy oracle statement challenge
      response (min n (g + (2 * C.k - 1))))

namespace UniformDirectCandidateArithmetic

theorem nonempty_of_false
    (candidate : SchemeLiftCandidate C oracle radius)
    (hns : ¬statement.Satisfies (candidate.directMessages (layout := layout))) :
    Nonempty (UniformDirectCandidateArithmetic (M := M) (layout := layout)
      (g := g) (statement := statement) candidate) := by
  classical
  rcases candidate.direct_residual_of_not_satisfies (layout := layout) statement hns with
    hlinear | ⟨i, hquadratic⟩
  · let equations := affineEquationSolutions
      (candidate.directLinearResidual (layout := layout) statement)
      (-candidate.directLinearZRCoefficientSum (layout := layout))
    let special := DirectChallengeCounting.liftLinear
      (nw := nw) (nq := nq) equations
    refine ⟨{
      special := special
      density := ?_
      cover := ?_ }⟩
    · simpa [special] using DirectChallengeCounting.liftLinear_density
        (nw := nw) (nq := nq) (Fintype.card F) 1 equations (by
          simpa using affineEquationSolutions_density
            (candidate.directLinearResidual (layout := layout) statement)
            (-candidate.directLinearZRCoefficientSum (layout := layout)) hlinear)
    · intro challenge response hnotSpecial remaining hremaining hbad hk
      have hnotEquation : (challenge 0).linear ∉ equations := by
        intro hmem
        apply hnotSpecial
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmem⟩
      have hnonexceptional : finiteDot (challenge 0).linear
          (candidate.directLinearResidual (layout := layout) statement) ≠
            -candidate.directLinearZRCoefficientSum (layout := layout) := by
        simpa [equations, affineEquationSolutions] using hnotEquation
      by_cases hexecution : ∃ query : QuerySet n r,
          DirectVerifier.Accepts C M layout statement challenge
            response query (openSchemeOracle oracle query)
      · obtain ⟨query₀, haccept₀⟩ := hexecution
        let allowed := remaining ∪ responseAgreement
          (response.linear 0)
          (candidate.directLinearCanonical (M := M) (layout := layout)
            statement (challenge 0).linear)
        have hcover₀ := candidate.direct_linear_query_cover
          (M := M) (layout := layout) statement (challenge 0).linear
          (response.linear 0) query₀ (haccept₀.1 0).2
          remaining hremaining hk (hbad query₀ haccept₀) hnonexceptional
        refine ⟨{
          allowed := allowed
          allowed_card := ?_
          covers := ?_ }⟩
        · apply Nat.le_min.mpr
          constructor
          · simpa using Finset.card_le_univ allowed
          · change (remaining ∪ responseAgreement
              (response.linear 0)
              (candidate.directLinearCanonical (M := M) (layout := layout)
                statement (challenge 0).linear)).card ≤ g + (2 * C.k - 1)
            calc
              _ ≤ 2 * C.k + g - 1 := hcover₀.2
              _ = g + (2 * C.k - 1) := by omega
        · intro query haccept
          exact (candidate.direct_linear_query_cover
            (M := M) (layout := layout) statement (challenge 0).linear
            (response.linear 0) query (haccept.1 0).2
            remaining hremaining hk (hbad query haccept)
            hnonexceptional).1
      · exact ⟨{
          allowed := ∅
          allowed_card := by simp
          covers := fun query haccept => False.elim
            (hexecution ⟨query, haccept⟩) }⟩
  · obtain ⟨row, hrow⟩ : ∃ row, candidate.directQuadraticResidual
        (layout := layout) row i ≠ 0 := by
      simpa [Function.ne_iff] using hquadratic
    refine ⟨{
      special := ∅
      density := by simp
      cover := ?_ }⟩
    intro challenge response _ remaining hremaining hbad hk
    by_cases hexecution : ∃ query : QuerySet n r,
        DirectVerifier.Accepts C M layout statement challenge
          response query (openSchemeOracle oracle query)
    · obtain ⟨query₀, haccept₀⟩ := hexecution
      let allowed := remaining ∪
        responseAgreement (candidate.directQuadraticWord row) 0
      have hcover₀ := candidate.direct_quadratic_query_cover
        (layout := layout) row i hrow query₀ haccept₀.2 remaining hremaining
        hk (hbad query₀ haccept₀)
      refine ⟨{
        allowed := allowed
        allowed_card := ?_
        covers := ?_ }⟩
      · apply Nat.le_min.mpr
        constructor
        · simpa using Finset.card_le_univ allowed
        · change (remaining ∪ responseAgreement
            (candidate.directQuadraticWord row) 0).card ≤ g + (2 * C.k - 1)
          calc
            _ ≤ 2 * C.k + g - 1 := hcover₀.2
            _ = g + (2 * C.k - 1) := by omega
      · intro query haccept
        exact (candidate.direct_quadratic_query_cover
          (layout := layout) row i hrow query haccept.2 remaining hremaining
          hk (hbad query haccept)).1
    · exact ⟨{
        allowed := ∅
        allowed_card := by simp
        covers := fun query haccept => False.elim
          (hexecution ⟨query, haccept⟩) }⟩

end UniformDirectCandidateArithmetic

structure DirectCandidateArithmetic
    (candidate : SchemeLiftCandidate C oracle radius) where
  special : Finset (DirectChallenge F Equations nw nq 1)
  density : Fintype.card F * special.card ≤
    Fintype.card (DirectChallenge F Equations nw nq 1)
  cover : ∀ challenge, challenge ∉ special →
    ∀ remaining : Finset (Fin n), remaining.card ≤ g →
    (∀ query : QuerySet n r,
      DirectVerifier.Accepts C M layout statement challenge
        (respond challenge) query (openSchemeOracle oracle query) →
      query.coordinates ∩ candidate.badColumns ⊆ remaining) →
    0 < C.k →
    Nonempty (PolicyAcceptingQueryCover directPolicy oracle statement challenge
      (respond challenge) (min n (g + (2 * C.k - 1))))

namespace DirectCandidateArithmetic

theorem nonempty_of_false
    (candidate : SchemeLiftCandidate C oracle radius)
    (hns : ¬statement.Satisfies (candidate.directMessages (layout := layout))) :
    Nonempty (DirectCandidateArithmetic (M := M) (layout := layout)
      (g := g) (statement := statement) (respond := respond) candidate) := by
  obtain ⟨arithmetic⟩ := UniformDirectCandidateArithmetic.nonempty_of_false (M := M) (layout := layout) (g := g) candidate hns
  exact ⟨{
    special := arithmetic.special
    density := arithmetic.density
    cover := fun challenge hnotSpecial remaining hremaining hbad hk =>
      arithmetic.cover challenge (respond challenge) hnotSpecial remaining hremaining hbad hk }⟩

end DirectCandidateArithmetic

namespace PolicyLiftListCertificate

theorem directArithmeticCertificate_nonempty
    (certificate : PolicyLiftListCertificate directPolicy oracle respond
      e g radius L)
    (hfalse : NoDirectSolution C layout oracle radius statement) (hk : 0 < C.k) :
    Nonempty (PolicyArithmeticCertificate directPolicy oracle statement respond
      certificate
      (checkedAgreementProfile (Fintype.card F) L n (2 * C.k - 1))
      (Fintype.card F)) := by
  classical
  let arithmetic := fun candidate : SchemeLiftCandidate C oracle radius =>
    Classical.choice (DirectCandidateArithmetic.nonempty_of_false
      (M := M) (layout := layout) (g := g) (statement := statement)
      (respond := respond) candidate (hfalse candidate))
  apply certificate.exceptionalArithmeticCertificate_nonempty
    (cutoff := 2 * C.k - 1) (profileDenominator := Fintype.card F)
    (special := fun candidate => (arithmetic candidate).special)
  · exact fun candidate => (arithmetic candidate).density
  · intro candidate challenge hspecial remaining hremaining hbad
    exact (arithmetic candidate).cover challenge hspecial remaining hremaining
      hbad hk

/-- Direct-product soundness through the disjoint event partition. -/
theorem direct_scheme_soundness_of_eventPartition
    (certificate : PolicyLiftListCertificate directPolicy oracle respond
      e g radius L)
    (failureProfile : AgreementProfile n)
    (hfailureDensity : ∀ a ≤ n,
      failureDenominator *
          (AgreementProfile.restrictedTailSet certificate.failure
            (fun challenge =>
              (schemeProximityAgreement oracle (challenge 0).proximity
                ((respond challenge).proximity 0)).card) a).card ≤
        failureProfile.labelsAtLeast a *
          Fintype.card (DirectChallenge F Equations nw nq 1))
    (hfalse : NoDirectSolution C layout oracle radius statement)
    (prover : IPCPProver
      (ConstraintSystem F nw nq logicalWidth Equations)
      (SchemeOracle F LinearConstraintMask NoMask nw nq n 1)
      (DirectChallenge F Equations nw nq 1) (DirectResponse F r w n 1))
    (horacle : prover.commit statement = oracle)
    (hrespond : ∀ challenge,
      prover.respond statement oracle challenge = respond challenge)
    (hk : 0 < C.k) (hfailureDenominator : 0 < failureDenominator) :
    (DirectVerifier.protocol C M layout).acceptanceRate prover statement ≤
      failureProfile.excessContribution failureDenominator n n 0 r
        (max (n - e - 1) (min n (g + (2 * C.k - 1)))) +
        (checkedAgreementProfile (Fintype.card F) L n
          (2 * C.k - 1)).contribution (Fintype.card F) n e g r := by
  have hquery : r ≤ n := C.query_le_length
  obtain ⟨arithmetic⟩ := certificate.directArithmeticCertificate_nonempty
    (M := M) (layout := layout) hfalse hk
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
    (DirectVerifier.protocol C M layout).acceptanceRate prover statement =
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

end LigeroFamily
