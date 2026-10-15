import Lfzk.LigeroRbr
import Ligero.V1.ScalarGapProfiled

/-!
# Profiled round-by-round soundness for Ligero V1, on the `formal/ligero` analysis

`Lfzk.LigeroRbr` keeps the two tails of a `PolicyDoublyProfiledSoundnessClassifier` apart.  This
file builds that classifier for Ligero V1 from the same three ingredients the flat theorem
`Ligero.V1.scalarGap_profiled_extraction_failure` uses — the optimized integrated lift-list
certificate, the V1 arithmetic certificate, and `doublyProfiledClassifier_nonempty` — and
concludes with the three round-by-round facts instead of the flat integral:

* from a doomed challenge, the accepting queries have density at most the cover ratio at the
  query threshold;
* the challenges that escape doom have density at most the failure profile's tail plus the
  arithmetic profile's tail, each above its own threshold;
* every challenge that is not doomed is in the escaping set.

The failure profile is `formal/ligero`'s `selectedMCAOptimizedIntegratedFailureProfile`, over the
denominator `selectedMCAOptimizedFailureDenominator`, which is what the lift-list certificate is
stated against.  Nothing about Ligero is re-proved here.

`ligerov1_roundByRound_mask_profiled` allows any certified `V1MaskRange`, including the
Hahn/Delsarte certificates. `ligerov1_roundByRound_profiled` retains the Johnson-only interface.
-/

namespace Ligero.V1

open LigeroFamily CodingTheory

variable {F Equations : Type*} [Field F] [Fintype F] [DecidableEq F]
variable [Fintype Equations] [DecidableEq Equations]
variable {r w n nw nq e g d outerBound threshold : ℕ} {localBound : ℕ → ℕ}

/-- **V1 round-by-round soundness**, profiled, at a false statement (`NoDecodedSolution`: no
member of the committed oracle's lift list at radius `e + g` satisfies the statement).  `L` is any
bound on that lift list (`hcard`): the Johnson count, or a packing refinement of it. The mask range may also use a
Hahn/Delsarte certificate below the Johnson threshold. -/
theorem ligerov1_roundByRound_mask_profiled
    (hrows : CoreRowsNonempty nw nq)
    (C : MultiplicativeCode F r w n)
    (statement : ConstraintSystem F nw nq w Equations)
    (prover : IPCPProver
      (ConstraintSystem F nw nq w Equations)
      (Oracle F nw nq n 1)
      (Challenge F nw nq 1 Equations)
      (Response F r w n 1))
    (hfalse : NoDecodedSolution C (prover.commit statement) (e + g) statement)
    (hmin : HasMinimumDistanceAtLeast C.baseCode d)
    (conditions : IntegratedSelectedMCALineConditions C.baseCode
      (Fintype.card F) e g d outerBound localBound)
    {L : ℕ} (hcard : (Finset.univ : Finset
      (SchemeLiftCandidate C (prover.commit statement) (e + g))).card ≤ L)
    {bound : ℕ → ℕ} (mask : V1MaskRange C threshold bound)
    (failureThreshold arithmeticThreshold : ℕ)
    (hfailureThreshold : failureThreshold + 1 ≤ n)
    (harithmeticThreshold : arithmeticThreshold + 1 ≤ n) :
    ∃ classifier : PolicyDoublyProfiledSoundnessClassifier
        (SchemeVerifier.policy (Equations := Equations) (nw := nw) (nq := nq)
          (repetitions := 1) C scheme)
        (prover.commit statement) statement
        (fun challenge ↦ prover.respond statement (prover.commit statement) challenge)
        (SchemeSelectedMCA.selectedMCAOptimizedIntegratedFailureProfile
          (Fintype.card F) n e g d outerBound localBound)
        (maskAgreementProfile (Fintype.card F) n L threshold bound)
        (Fintype.card F)
        (SchemeSelectedMCA.selectedMCAOptimizedFailureDenominator (Fintype.card F) g) e g,
      (∀ challenge, classifier.ProfiledDoomedAfter
          failureThreshold arithmeticThreshold challenge →
        ((classifier.acceptingQueries challenge).card : ℚ) / (n.choose r) ≤
          hypergeometricRatio
            (max failureThreshold
              (max (n - e - 1) (min n (g + arithmeticThreshold)))) n r)
      ∧ ((classifier.profiledEscaping
            failureThreshold arithmeticThreshold).card : ℚ) /
            Fintype.card (Challenge F nw nq 1 Equations) ≤
          ((SchemeSelectedMCA.selectedMCAOptimizedIntegratedFailureProfile
              (Fintype.card F) n e g d outerBound localBound).labelsAtLeast
                (failureThreshold + 1) : ℚ) /
              ((SchemeSelectedMCA.selectedMCAOptimizedFailureDenominator
                (Fintype.card F) g : ℕ) : ℚ) +
            ((maskAgreementProfile (Fintype.card F) n L threshold bound).labelsAtLeast (arithmeticThreshold + 1) : ℚ) / Fintype.card F
      ∧ (∀ challenge, ¬ classifier.ProfiledDoomedAfter
            failureThreshold arithmeticThreshold challenge →
          challenge ∈ classifier.profiledEscaping
            failureThreshold arithmeticThreshold) := by
  letI : Nonempty (SchemeTestedRow NoMask nw nq 1) :=
    schemeTestedRowNonemptyOfCoreRows hrows
  let respond := fun challenge ↦
    prover.respond statement (prover.commit statement) challenge
  let extractor := schemeExtractorPolicy (Equations := Equations)
    (nw := nw) (nq := nq) C scheme
  obtain ⟨certificate, hdensity⟩ :=
    extractor.exists_profiledPolicyLiftList_of_endpointOptimizedIntegratedLine_of_card
      (oracle := prover.commit statement) (respond := respond) hmin conditions hcard
  obtain ⟨arithmetic⟩ :=
    Ligero.V1.PolicyLiftListCertificate.v1ArithmeticCertificate_nonempty
      certificate hfalse mask
  obtain ⟨classifier⟩ :=
    arithmetic.doublyProfiledClassifier_nonempty
      (failureProfile := SchemeSelectedMCA.selectedMCAOptimizedIntegratedFailureProfile
        (Fintype.card F) n e g d outerBound localBound)
      (failureDenominator := SchemeSelectedMCA.selectedMCAOptimizedFailureDenominator
        (Fintype.card F) g)
      certificate hdensity
  refine ⟨classifier, ?_, ?_, ?_⟩
  · intro challenge hdoom
    exact classifier.query_density_le_of_profiledDoomedAfter
      failureThreshold arithmeticThreshold challenge hdoom
  · refine classifier.profiledEscaping_density_le
      failureThreshold arithmeticThreshold
      hfailureThreshold harithmeticThreshold ?_ ?_
    · exact Nat.mul_pos Fintype.card_pos
        (Nat.sub_pos_of_lt conditions.outer.punctured.field_large)
    · exact Fintype.card_pos
  · intro challenge hdoom
    exact classifier.not_profiledDoomedAfter_mem_profiledEscaping hdoom

/-- **V1 round-by-round soundness**, profiled, at a false statement (`NoDecodedSolution`: no
member of the committed oracle's lift list at radius `e + g` satisfies the statement).  `L` is any
bound on that lift list (`hcard`): the Johnson count, or a packing refinement of it. -/
theorem ligerov1_roundByRound_profiled
    (hrows : CoreRowsNonempty nw nq)
    (C : MultiplicativeCode F r w n)
    (statement : ConstraintSystem F nw nq w Equations)
    (prover : IPCPProver
      (ConstraintSystem F nw nq w Equations)
      (Oracle F nw nq n 1)
      (Challenge F nw nq 1 Equations)
      (Response F r w n 1))
    (hfalse : NoDecodedSolution C (prover.commit statement) (e + g) statement)
    (hmin : HasMinimumDistanceAtLeast C.baseCode d)
    (conditions : IntegratedSelectedMCALineConditions C.baseCode
      (Fintype.card F) e g d outerBound localBound)
    {L : ℕ} (hcard : (Finset.univ : Finset
      (SchemeLiftCandidate C (prover.commit statement) (e + g))).card ≤ L)
    (johnson : V1JohnsonRange C threshold)
    (failureThreshold arithmeticThreshold : ℕ)
    (hfailureThreshold : failureThreshold + 1 ≤ n)
    (harithmeticThreshold : arithmeticThreshold + 1 ≤ n) :
    ∃ classifier : PolicyDoublyProfiledSoundnessClassifier
        (SchemeVerifier.policy (Equations := Equations) (nw := nw) (nq := nq)
          (repetitions := 1) C scheme)
        (prover.commit statement) statement
        (fun challenge ↦ prover.respond statement (prover.commit statement) challenge)
        (SchemeSelectedMCA.selectedMCAOptimizedIntegratedFailureProfile
          (Fintype.card F) n e g d outerBound localBound)
        (uncheckedAgreementProfile (Fintype.card F) n (2 * C.k - 1) L threshold)
        (Fintype.card F)
        (SchemeSelectedMCA.selectedMCAOptimizedFailureDenominator (Fintype.card F) g) e g,
      (∀ challenge, classifier.ProfiledDoomedAfter
          failureThreshold arithmeticThreshold challenge →
        ((classifier.acceptingQueries challenge).card : ℚ) / (n.choose r) ≤
          hypergeometricRatio
            (max failureThreshold
              (max (n - e - 1) (min n (g + arithmeticThreshold)))) n r)
      ∧ ((classifier.profiledEscaping
            failureThreshold arithmeticThreshold).card : ℚ) /
            Fintype.card (Challenge F nw nq 1 Equations) ≤
          ((SchemeSelectedMCA.selectedMCAOptimizedIntegratedFailureProfile
              (Fintype.card F) n e g d outerBound localBound).labelsAtLeast
                (failureThreshold + 1) : ℚ) /
              ((SchemeSelectedMCA.selectedMCAOptimizedFailureDenominator
                (Fintype.card F) g : ℕ) : ℚ) +
            ((uncheckedAgreementProfile (Fintype.card F) n (2 * C.k - 1) L
              threshold).labelsAtLeast (arithmeticThreshold + 1) : ℚ) / Fintype.card F
      ∧ (∀ challenge, ¬ classifier.ProfiledDoomedAfter
            failureThreshold arithmeticThreshold challenge →
          challenge ∈ classifier.profiledEscaping
            failureThreshold arithmeticThreshold) := by
  exact ligerov1_roundByRound_mask_profiled hrows C statement prover hfalse hmin conditions
    hcard johnson.toMaskRange failureThreshold arithmeticThreshold
    hfailureThreshold harithmeticThreshold

end Ligero.V1
