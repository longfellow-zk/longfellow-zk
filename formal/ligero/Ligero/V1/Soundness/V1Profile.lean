import Ligero.V1.Soundness.LabelCounting
import LigeroFamily.Soundness.PolicyEventPartition
import Ligero.V1.Soundness.V1Soundness

/-!
# V1-mask agreement profiles

For every decoded core candidate of a false statement, one violated global
constraint is fixed before the public challenge.  Its direct response mask is
then compared with the response-code offset claimed by the prover.  The
resulting agreement size is the V1 protocol instance of the common
profiled soundness classifier.
-/

namespace Ligero.V1

open LigeroFamily

open CodingTheory
open MultiplicativeCode
open SchemeLiftCandidate

variable {F Equations : Type*} [Field F] [Fintype F] [DecidableEq F]
variable [Fintype Equations] [DecidableEq Equations]
variable {r w n nw nq radius g : ℕ}
variable {C : MultiplicativeCode F r w n}
variable {oracle : Oracle F nw nq n 1}
variable {statement : ConstraintSystem F nw nq w Equations}

local notation "v1Policy" =>
  SchemeVerifier.policy (Equations := Equations) (nw := nw) (nq := nq)
    (repetitions := 1) C scheme

/-- Which false global equation is charged for one decoded core candidate. -/
inductive V1ViolationKind (w : ℕ)
  | linear
  | quadratic (i : Fin w)

/-- A selected nonzero residual.  This is the only candidate-specific choice
needed by the V1 arithmetic argument. -/
structure V1Violation
    (candidate : SchemeLiftCandidate C oracle radius)
    (statement : ConstraintSystem F nw nq w Equations) where
  kind : V1ViolationKind w
  nonzero : match kind with
    | .linear => v1LinearResidual candidate statement ≠ 0
    | .quadratic i =>
        (fun row ↦ v1QuadraticResidual candidate row i) ≠ 0

namespace V1Violation

omit [Fintype F] [Fintype Equations] [DecidableEq Equations] in
theorem nonempty_of_false
    (candidate : SchemeLiftCandidate C oracle radius)
    (hns : ¬statement.Satisfies candidate.decodedMessages) :
    Nonempty (V1Violation candidate statement) := by
  rcases candidate.residual_of_not_satisfies statement hns with
    hlinear | ⟨i, hquadratic⟩
  · exact ⟨⟨.linear, hlinear⟩⟩
  · exact ⟨⟨.quadratic i, hquadratic⟩⟩

end V1Violation

namespace SchemeLiftCandidate

/-- Agreement supplied by one decoded core and its fixed violated equation.
It is zero when the claimed arithmetic response already fails its global
response-code check, since such a challenge has no accepting query. -/
noncomputable def v1Agreement
    (candidate : SchemeLiftCandidate C oracle radius)
    (violation : V1Violation candidate statement)
    (respond : SchemeChallenge F NoMask nw nq 1 Equations → Response F r w n 1)
    (challenge : SchemeChallenge F NoMask nw nq 1 Equations) : ℕ := by
  classical
  exact match violation.kind with
  | .linear =>
      if (respond challenge).linear 0 ∈ C.response ∧
          (∑ i : Fin w,
            (respond challenge).linear 0 (witnessPosition i)) =
              statement.combinedTarget (challenge 0).linear then
        (wordAgreement (oracle.directMask 0 .linear)
          (codeword ((respond challenge).linear 0 -
            v1LinearCanonical candidate statement
              (challenge 0).linear))).card
      else 0
  | .quadratic i =>
      if (respond challenge).quadratic 0 ∈ C.response ∧
          (respond challenge).quadratic 0 (witnessPosition i) = 0 then
        (wordAgreement (oracle.directMask 0 .quadratic)
          (codeword ((respond challenge).quadratic 0 -
            v1QuadraticCanonical candidate
              (challenge 0).quadratic))).card
      else 0

omit [Fintype F] [DecidableEq Equations] in
theorem v1Agreement_le
    (candidate : SchemeLiftCandidate C oracle radius)
    (violation : V1Violation candidate statement)
    (respond : SchemeChallenge F NoMask nw nq 1 Equations → Response F r w n 1)
    (challenge : SchemeChallenge F NoMask nw nq 1 Equations) :
    v1Agreement candidate violation respond challenge ≤ n := by
  classical
  cases hkind : violation.kind with
  | linear =>
      simp only [v1Agreement, hkind]
      split
      · simpa using Finset.card_le_card
          (Finset.subset_univ (wordAgreement (oracle.directMask 0 .linear)
            (codeword ((respond challenge).linear 0 -
              v1LinearCanonical candidate statement
                (challenge 0).linear))))
      · exact Nat.zero_le _
  | quadratic i =>
      simp only [v1Agreement, hkind]
      split
      · simpa using Finset.card_le_card
          (Finset.subset_univ (wordAgreement (oracle.directMask 0 .quadratic)
            (codeword ((respond challenge).quadratic 0 -
              v1QuadraticCanonical candidate
                (challenge 0).quadratic))))
      · exact Nat.zero_le _

omit [Fintype F] [DecidableEq Equations] in
/-- Every accepted query is covered by the common lift residual plus the
V1 direct-mask agreement selected for this candidate. -/
theorem v1_constraint_cover
    (candidate : SchemeLiftCandidate C oracle radius)
    (violation : V1Violation candidate statement)
    (respond : SchemeChallenge F NoMask nw nq 1 Equations → Response F r w n 1)
    (challenge : SchemeChallenge F NoMask nw nq 1 Equations)
    (remaining : Finset (Fin n)) (hremaining : remaining.card ≤ g)
    (hbad : ∀ query : QuerySet n r,
      SchemeVerifier.Accepts C scheme statement challenge
        (respond challenge) query (openSchemeOracle oracle query) →
      query.coordinates ∩ candidate.badColumns ⊆ remaining) :
    Nonempty (PolicyAcceptingQueryCover v1Policy oracle statement challenge
      (respond challenge)
      (min n (g + v1Agreement candidate violation respond challenge))) := by
  classical
  by_cases hexecution : ∃ query : QuerySet n r,
      SchemeVerifier.Accepts C scheme statement challenge
        (respond challenge) query (openSchemeOracle oracle query)
  · obtain ⟨query₀, haccept₀⟩ := hexecution
    cases hkind : violation.kind with
    | linear =>
        let agreement := wordAgreement (oracle.directMask 0 .linear)
          (codeword ((respond challenge).linear 0 -
            v1LinearCanonical candidate statement (challenge 0).linear))
        let allowed := remaining ∪ agreement
        have hagreement :
            v1Agreement candidate violation respond challenge =
              agreement.card := by
          have hlinear := (haccept₀ 0).2.1
          simp [v1Agreement, hkind, hlinear.1, hlinear.2.1, agreement]
        refine ⟨{
          allowed := allowed
          allowed_card := ?_
          covers := ?_ }⟩
        · apply Nat.le_min.mpr
          constructor
          · simpa [allowed] using Finset.card_le_card
              (Finset.subset_univ allowed)
          · calc
              allowed.card ≤ remaining.card + agreement.card :=
                Finset.card_union_le _ _
              _ ≤ g + agreement.card := Nat.add_le_add_right hremaining _
              _ = g + v1Agreement candidate violation respond challenge :=
                congrArg (g + ·) hagreement.symm
        · intro query haccept
          have hcover := v1_linear_query_cover candidate statement
            (challenge 0).linear ((respond challenge).linear 0) query
            (haccept 0).2.1 remaining (hbad query haccept)
          simpa [allowed, agreement] using hcover
    | quadratic i =>
        let agreement := wordAgreement (oracle.directMask 0 .quadratic)
          (codeword ((respond challenge).quadratic 0 -
            v1QuadraticCanonical candidate (challenge 0).quadratic))
        let allowed := remaining ∪ agreement
        have hagreement :
            v1Agreement candidate violation respond challenge =
              agreement.card := by
          have hquadratic := (haccept₀ 0).2.2
          simp [v1Agreement, hkind, hquadratic.1,
            hquadratic.2.1 i, agreement]
        refine ⟨{
          allowed := allowed
          allowed_card := ?_
          covers := ?_ }⟩
        · apply Nat.le_min.mpr
          constructor
          · simpa [allowed] using Finset.card_le_card
              (Finset.subset_univ allowed)
          · calc
              allowed.card ≤ remaining.card + agreement.card :=
                Finset.card_union_le _ _
              _ ≤ g + agreement.card := Nat.add_le_add_right hremaining _
              _ = g + v1Agreement candidate violation respond challenge :=
                congrArg (g + ·) hagreement.symm
        · intro query haccept
          have hcover := v1_quadratic_query_cover candidate
            (challenge 0).quadratic ((respond challenge).quadratic 0) query
            (haccept 0).2.2 remaining (hbad query haccept)
          simpa [allowed, agreement] using hcover
  · let emptyCover : PolicyAcceptingQueryCover v1Policy oracle statement
        challenge (respond challenge)
        (min n (g + v1Agreement candidate violation respond challenge)) := {
      allowed := ∅
      allowed_card := by simp
      covers := fun query haccept ↦ False.elim (hexecution ⟨query, haccept⟩) }
    exact ⟨emptyCover⟩

/-- A fixed violated linear residual has the Johnson-bounded challenge tail.
The direct mask is arbitrary; only the response offset is code constrained. -/
theorem v1Agreement_linear_density
    (candidate : SchemeLiftCandidate C oracle radius)
    (violation : V1Violation candidate statement)
    (hkind : violation.kind = .linear)
    (respond : SchemeChallenge F NoMask nw nq 1 Equations → Response F r w n 1)
    (a : ℕ) (hpositive : 0 < a) (h2k : 2 * C.k ≤ n) (ha : a ≤ n)
    (hclose : n - a < n - (2 * C.k - 1))
    (hden : 0 < CodingTheory.InterleavedJohnson.denominator
      n (n - (2 * C.k - 1)) (n - a)) :
    Fintype.card F *
        (AgreementProfile.tailSet
          (v1Agreement candidate violation respond) a).card ≤
      uncheckedAgreementListBound n (2 * C.k - 1) a *
        Fintype.card (SchemeChallenge F NoMask nw nq 1 Equations) := by
  classical
  let label : EvaluationRow F r w n → F :=
    fun row ↦ -(∑ i : Fin w, row (witnessPosition i))
  let labels := responseLabelsAgreeingAtLeast C
    (oracle.directMask 0 .linear) label a
  let special := finiteDotLabelPreimage
    (v1LinearResidual candidate statement) labels
  have hnonzero : v1LinearResidual candidate statement ≠ 0 := by
    simpa [hkind] using violation.nonzero
  have hsubset : AgreementProfile.tailSet
      (v1Agreement candidate violation respond) a ⊆
      SchemeInternal.liftLinear
        (CheckedMask := NoMask) (nw := nw) (nq := nq) special := by
    intro challenge hchallenge
    have hagreement := (Finset.mem_filter.mp hchallenge).2
    simp only [v1Agreement, hkind] at hagreement
    split at hagreement
    next hvalid =>
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      exact v1_linear_label_mem candidate statement
        (challenge 0).linear ((respond challenge).linear 0) hvalid a
        hagreement
    next hvalid => omega
  have hspecial : Fintype.card F * special.card ≤
      labels.card * Fintype.card (Equations → F) := by
    simpa [special] using finiteDotLabelPreimage_density
      (v1LinearResidual candidate statement) labels hnonzero
  have hlabels : labels.card ≤
      uncheckedAgreementListBound n (2 * C.k - 1) a := by
    simpa [labels, label] using responseLabelsAgreeingAtLeast_card_le C
      (oracle.directMask 0 .linear) label a h2k ha hclose hden
  have hspecialBound : Fintype.card F * special.card ≤
      uncheckedAgreementListBound n (2 * C.k - 1) a *
        Nat.card (Equations → F) := by
    rw [Nat.card_eq_fintype_card]
    exact hspecial.trans (Nat.mul_le_mul_right _ hlabels)
  rw [← Nat.card_eq_fintype_card
    (α := SchemeChallenge F NoMask nw nq 1 Equations)]
  exact (Nat.mul_le_mul_left _ (Finset.card_le_card hsubset)).trans
    (SchemeInternal.liftLinear_density
      (CheckedMask := NoMask) (nw := nw) (nq := nq)
      (Fintype.card F) (uncheckedAgreementListBound n (2 * C.k - 1) a)
      special hspecialBound)

/-- Quadratic violated coordinates satisfy the identical Johnson tail bound. -/
theorem v1Agreement_quadratic_density
    (candidate : SchemeLiftCandidate C oracle radius)
    (violation : V1Violation candidate statement)
    (i : Fin w) (hkind : violation.kind = .quadratic i)
    (respond : SchemeChallenge F NoMask nw nq 1 Equations → Response F r w n 1)
    (a : ℕ) (hpositive : 0 < a) (h2k : 2 * C.k ≤ n) (ha : a ≤ n)
    (hclose : n - a < n - (2 * C.k - 1))
    (hden : 0 < CodingTheory.InterleavedJohnson.denominator
      n (n - (2 * C.k - 1)) (n - a)) :
    Fintype.card F *
        (AgreementProfile.tailSet
          (v1Agreement candidate violation respond) a).card ≤
      uncheckedAgreementListBound n (2 * C.k - 1) a *
        Fintype.card (SchemeChallenge F NoMask nw nq 1 Equations) := by
  classical
  let label : EvaluationRow F r w n → F :=
    fun row ↦ -row (witnessPosition i)
  let labels := responseLabelsAgreeingAtLeast C
    (oracle.directMask 0 .quadratic) label a
  let residual := fun row ↦ v1QuadraticResidual candidate row i
  let special := finiteDotLabelPreimage residual labels
  have hnonzero : residual ≠ 0 := by
    simpa [hkind, residual] using violation.nonzero
  have hsubset : AgreementProfile.tailSet
      (v1Agreement candidate violation respond) a ⊆
      SchemeInternal.liftQuadratic
        (CheckedMask := NoMask) (Equations := Equations) (nw := nw)
          special := by
    intro challenge hchallenge
    have hagreement := (Finset.mem_filter.mp hchallenge).2
    simp only [v1Agreement, hkind] at hagreement
    split at hagreement
    next hvalid =>
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      exact v1_quadratic_label_mem candidate
        (challenge 0).quadratic i ((respond challenge).quadratic 0) hvalid a
        hagreement
    next hvalid => omega
  have hspecial : Fintype.card F * special.card ≤
      labels.card * Fintype.card (Fin nq → F) := by
    simpa [special, residual] using finiteDotLabelPreimage_density
      residual labels hnonzero
  have hlabels : labels.card ≤
      uncheckedAgreementListBound n (2 * C.k - 1) a := by
    simpa [labels, label] using responseLabelsAgreeingAtLeast_card_le C
      (oracle.directMask 0 .quadratic) label a h2k ha hclose hden
  have hspecialBound : Fintype.card F * special.card ≤
      uncheckedAgreementListBound n (2 * C.k - 1) a *
        Nat.card (Fin nq → F) := by
    rw [Nat.card_eq_fintype_card]
    exact hspecial.trans (Nat.mul_le_mul_right _ hlabels)
  rw [← Nat.card_eq_fintype_card
    (α := SchemeChallenge F NoMask nw nq 1 Equations)]
  exact (Nat.mul_le_mul_left _ (Finset.card_le_card hsubset)).trans
    (SchemeInternal.liftQuadratic_density
      (CheckedMask := NoMask) (Equations := Equations) (nw := nw)
      (Fintype.card F) (uncheckedAgreementListBound n (2 * C.k - 1) a)
      special hspecialBound)

end SchemeLiftCandidate

/-- Uniform Johnson hypotheses above the unchecked-profile threshold. -/
structure V1JohnsonRange
    (C : MultiplicativeCode F r w n) (threshold : ℕ) where
  threshold_pos : 0 < threshold
  response_injective : 2 * C.k ≤ n
  close : ∀ a, threshold ≤ a → a ≤ n →
    n - a < n - (2 * C.k - 1)
  denominator_pos : ∀ a, threshold ≤ a → a ≤ n →
    0 < CodingTheory.InterleavedJohnson.denominator
      n (n - (2 * C.k - 1)) (n - a)

namespace V1JohnsonRange

/-- The usual `floor(sqrt(n*lambda))+1` choice discharges the whole Johnson
range from its two elementary integer inequalities. -/
def ofSquare
    (C : MultiplicativeCode F r w n) (threshold : ℕ)
    (hthreshold : 0 < threshold) (h2k : 2 * C.k ≤ n)
    (hcutoff : 2 * C.k - 1 < threshold)
    (hsquare : n * (2 * C.k - 1) < threshold * threshold) :
    V1JohnsonRange C threshold where
  threshold_pos := hthreshold
  response_injective := h2k
  close a hta ha := by omega
  denominator_pos a hta ha := by
    rw [unchecked_denominator_eq n (2 * C.k - 1) a (by omega) ha]
    have hnat : n * (2 * C.k - 1) < a * a := by nlinarith
    have hcast : ((n * (2 * C.k - 1) : ℕ) : ℤ) < ((a * a : ℕ) : ℤ) := by
      exact_mod_cast hnat
    push_cast at hcast
    nlinarith

end V1JohnsonRange

namespace PolicyLiftListCertificate

variable {respond : SchemeChallenge F NoMask nw nq 1 Equations →
  Response F r w n 1}
variable {e failureDenominator L threshold : ℕ}




theorem v1ArithmeticCertificate_nonempty
    (certificate : PolicyLiftListCertificate v1Policy oracle respond
      e g radius L)
    (hfalse : NoDecodedSolution C oracle radius statement)
    (johnson : V1JohnsonRange C threshold) :
    Nonempty (PolicyArithmeticCertificate v1Policy oracle statement respond
      certificate
      (uncheckedAgreementProfile (Fintype.card F) n (2 * C.k - 1) L threshold)
      (Fintype.card F)) := by
  classical
  let violation := fun candidate : SchemeLiftCandidate C oracle radius ↦
    Classical.choice (V1Violation.nonempty_of_false candidate (hfalse candidate))
  let agreement := fun challenge ↦ certificate.candidates.sup fun candidate ↦
    v1Agreement candidate (violation candidate) respond challenge
  have hagreementLe : ∀ challenge, agreement challenge ≤ n := by
    intro challenge
    exact Finset.sup_le fun candidate _ ↦
      v1Agreement_le candidate (violation candidate) respond challenge
  have hagreementDensity : ∀ a ≤ n,
      Fintype.card F * (AgreementProfile.tailSet agreement a).card ≤
        (uncheckedAgreementProfile (Fintype.card F) n (2 * C.k - 1) L
          threshold).labelsAtLeast a *
            Fintype.card (SchemeChallenge F NoMask nw nq 1 Equations) := by
    intro a ha
    by_cases hbelow : a < threshold
    · have hcard := Finset.card_le_card
        (Finset.subset_univ (AgreementProfile.tailSet agreement a))
      have hna : ¬n < a := by omega
      simpa [uncheckedAgreementProfile, hna, hbelow] using
        Nat.mul_le_mul_left (Fintype.card F) hcard
    · have hthreshold : threshold ≤ a := Nat.le_of_not_gt hbelow
      have hpositive : 0 < a := johnson.threshold_pos.trans_le hthreshold
      let candidateTail := fun candidate : SchemeLiftCandidate C oracle radius ↦
        AgreementProfile.tailSet
          (v1Agreement candidate (violation candidate) respond) a
      have hsubset : AgreementProfile.tailSet agreement a ⊆
          certificate.candidates.biUnion candidateTail := by
        intro challenge hchallenge
        have hle := (Finset.mem_filter.mp hchallenge).2
        obtain ⟨candidate, hcandidate, hcandLe⟩ :=
          (Finset.le_sup_iff hpositive).mp hle
        exact Finset.mem_biUnion.mpr ⟨candidate, hcandidate,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcandLe⟩⟩
      have hcandidate (candidate : SchemeLiftCandidate C oracle radius) :
          Fintype.card F * (candidateTail candidate).card ≤
            uncheckedAgreementListBound n (2 * C.k - 1) a *
              Fintype.card
                (SchemeChallenge F NoMask nw nq 1 Equations) := by
        cases hkind : (violation candidate).kind with
        | linear =>
            exact v1Agreement_linear_density candidate
              (violation candidate) hkind respond a hpositive
              johnson.response_injective ha
              (johnson.close a hthreshold ha)
              (johnson.denominator_pos a hthreshold ha)
        | quadratic i =>
            exact v1Agreement_quadratic_density candidate
              (violation candidate) i hkind respond a hpositive
              johnson.response_injective ha
              (johnson.close a hthreshold ha)
              (johnson.denominator_pos a hthreshold ha)
      calc
        Fintype.card F * (AgreementProfile.tailSet agreement a).card ≤
            Fintype.card F *
              (certificate.candidates.biUnion candidateTail).card :=
          Nat.mul_le_mul_left _ (Finset.card_le_card hsubset)
        _ ≤ Fintype.card F *
              ∑ candidate ∈ certificate.candidates,
                (candidateTail candidate).card :=
          Nat.mul_le_mul_left _ Finset.card_biUnion_le
        _ = ∑ candidate ∈ certificate.candidates,
              Fintype.card F * (candidateTail candidate).card := by
          simp_rw [Finset.mul_sum]
        _ ≤ ∑ _candidate ∈ certificate.candidates,
              uncheckedAgreementListBound n (2 * C.k - 1) a *
                Fintype.card
                  (SchemeChallenge F NoMask nw nq 1 Equations) :=
          Finset.sum_le_sum fun candidate _ ↦ hcandidate candidate
        _ = certificate.candidates.card *
              uncheckedAgreementListBound n (2 * C.k - 1) a *
                Fintype.card
                  (SchemeChallenge F NoMask nw nq 1 Equations) := by
          simp [mul_comm, mul_left_comm]
        _ = certificate.candidates.card *
              (uncheckedAgreementListBound n (2 * C.k - 1) a *
                Fintype.card
                  (SchemeChallenge F NoMask nw nq 1 Equations)) := by
          rw [Nat.mul_assoc]
        _ ≤ L * (uncheckedAgreementListBound n (2 * C.k - 1) a *
              Fintype.card
                (SchemeChallenge F NoMask nw nq 1 Equations)) := by
          exact Nat.mul_le_mul_right _ certificate.list_card
        _ = (uncheckedAgreementProfile (Fintype.card F) n
              (2 * C.k - 1) L threshold).labelsAtLeast a *
                Fintype.card
                  (SchemeChallenge F NoMask nw nq 1 Equations) := by
          have hna : ¬n < a := by omega
          simp [uncheckedAgreementProfile, hna, hbelow, Nat.mul_assoc]
  refine ⟨{
    agreement := agreement
    agreement_le := hagreementLe
    agreement_density := hagreementDensity
    constraint_cover := ?_ }⟩
  intro challenge candidate hcandidate _hresponse hremaining _hsmall
  let remaining := candidate.remainingBadColumns (challenge 0).proximity
    ((respond challenge).proximity 0)
  have hbad : ∀ query : QuerySet n r,
      SchemeVerifier.Accepts C scheme statement challenge
        (respond challenge) query (openSchemeOracle oracle query) →
      query.coordinates ∩ candidate.badColumns ⊆ remaining := by
    intro query haccept
    exact candidate.query_bad_subset_remaining (challenge 0).proximity
      ((respond challenge).proximity 0) query (haccept 0).1
  obtain ⟨cover⟩ := v1_constraint_cover candidate
    (violation candidate) respond challenge remaining hremaining hbad
  have hcandAgreement :
      v1Agreement candidate (violation candidate) respond challenge ≤
        agreement challenge := by
    simpa [agreement] using (Finset.le_sup
      (f := fun candidate ↦ v1Agreement candidate
        (violation candidate) respond challenge) hcandidate)
  exact ⟨{
    allowed := cover.allowed
    allowed_card := cover.allowed_card.trans
      (min_le_min_left n (Nat.add_le_add_left hcandAgreement g))
    covers := cover.covers }⟩

end PolicyLiftListCertificate

open PolicyLiftListCertificate

/-- V1 soundness through the disjoint event partition.  The unchecked
arithmetic profile has full mass below its Johnson threshold, so it pays the
shared baseline through `threshold - 1`; selected-MCA failures pay only their
excess above that baseline. -/
theorem v1_ligero_soundness_of_eventPartition
    {respond : SchemeChallenge F NoMask nw nq 1 Equations →
      Response F r w n 1}
    {e failureDenominator L threshold : ℕ}
    (certificate : PolicyLiftListCertificate v1Policy oracle respond
      e g radius L)
    (failureProfile : AgreementProfile n)
    (hfailureDensity : ∀ a ≤ n,
      failureDenominator *
          (AgreementProfile.restrictedTailSet certificate.failure
            (fun challenge ↦
              (schemeProximityAgreement oracle (challenge 0).proximity
                ((respond challenge).proximity 0)).card) a).card ≤
        failureProfile.labelsAtLeast a *
          Fintype.card (SchemeChallenge F NoMask nw nq 1 Equations))
    (hfalse : NoDecodedSolution C oracle radius statement)
    (johnson : V1JohnsonRange C threshold)
    (prover : IPCPProver
      (ConstraintSystem F nw nq w Equations)
      (Oracle F nw nq n 1)
      (SchemeChallenge F NoMask nw nq 1 Equations)
      (Response F r w n 1))
    (horacle : prover.commit statement = oracle)
    (hrespond : ∀ challenge,
      prover.respond statement oracle challenge = respond challenge)
    (hfailureDenominator : 0 < failureDenominator) :
    (SchemeVerifier.protocol C scheme).acceptanceRate prover statement ≤
      failureProfile.excessContribution failureDenominator n n 0 r
        (max (n - e - 1) (min n (g + (threshold - 1)))) +
        (uncheckedAgreementProfile (Fintype.card F) n (2 * C.k - 1) L
          threshold).contribution (Fintype.card F) n e g r := by
  obtain ⟨arithmetic⟩ :=
    PolicyLiftListCertificate.v1ArithmeticCertificate_nonempty certificate
      hfalse johnson
  let classifier := Classical.choice
    (arithmetic.doublyProfiledClassifier_nonempty certificate hfailureDensity)
  have hfloor : ∀ a ≤ min n (threshold - 1),
      Fintype.card F ≤
        (uncheckedAgreementProfile (Fintype.card F) n (2 * C.k - 1) L
          threshold).labelsAtLeast a := by
    intro a ha
    have hthreshold := johnson.threshold_pos
    simp [uncheckedAgreementProfile, show ¬n < a by omega,
      show a < threshold by omega]
  calc
    (SchemeVerifier.protocol C scheme).acceptanceRate prover statement =
        classifier.acceptanceRate :=
      classifier.protocol_acceptanceRate_eq prover horacle hrespond
    _ ≤ failureProfile.excessContribution failureDenominator n n 0 r
          (max (n - e - 1) (min n (g + min n (threshold - 1)))) +
        (uncheckedAgreementProfile (Fintype.card F) n (2 * C.k - 1) L
          threshold).contribution (Fintype.card F) n e g r :=
      classifier.acceptanceRate_le_eventPartition
        (min n (threshold - 1)) Fintype.card_pos hfailureDenominator
        C.query_le_length (min_le_left _ _) hfloor
    _ = _ := by
      congr 3
      omega

end Ligero.V1
