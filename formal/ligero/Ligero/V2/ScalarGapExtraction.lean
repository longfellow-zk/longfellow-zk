import LigeroFamily.Soundness.ScalarGapChecked
import Ligero.V2.Soundness.CheckedProfile
import LigeroFamily.Soundness.SchemePolicyExtractor

/-! Scalar proximity-gap IOP extraction for V2. The arithmetic exceptional
set is fixed before the response; all checked masks are retained. No FS or
polynomial batching is introduced. -/

set_option linter.unusedSectionVars false
namespace Ligero.V2
open LigeroFamily CodingTheory MultiplicativeCode Finset
open scoped Classical

variable {F Equations : Type*} [Field F] [Fintype F] [DecidableEq F]
variable [Fintype Equations] [DecidableEq Equations]
variable {r w n nw nq e g d lineBound : ℕ}
variable (C : MultiplicativeCode F r w n) (M : C.MaskingBasis)
variable (oracle : SchemeOracle F Ligero.V2.Mask NoMask nw nq n 1)
variable (statement : (ConstraintSystem F nw nq w Equations))

local notation "gapPolicy" => SchemeVerifier.policy (Equations := Equations) (nw := nw) (nq := nq)
  (repetitions := 1) C (scheme C M)

noncomputable def scalarGapExtract (challenge : Ligero.V2.Challenge F nw nq 1 Equations) (response : Response F r w n 1) :=
  ScalarGapExtraction.extract (oracle := oracle) (e := e) (g := g) gapPolicy (fun candidate => candidate.decodedMessages) statement challenge response

/-- Only the variant's arithmetic residual test is supplied here. Shared
modules assemble proximity, candidate lists and extraction soundness. -/
theorem scalarGap_arithmeticBudget
    (candidate : SchemeLiftCandidate C oracle (e + g))
    (hns : ¬statement.Satisfies (candidate.decodedMessages)) (hk : 0 < C.k) :
    Nonempty (ScalarGapExtraction.CheckedArithmeticBudget gapPolicy candidate statement (2 * C.k - 1)) := by
  obtain ⟨evidence⟩ := UniformCheckedCandidateArithmetic.nonempty_of_false (M := M) (g := g) candidate hns
  refine ⟨{
    special := evidence.special
    density := evidence.density
    cover := ?_ }⟩
  intro challenge response hnot hc
  apply evidence.cover challenge response hnot
    (candidate.remainingBadColumns ((gapPolicy).proximityWeights challenge 0)
      ((gapPolicy).proximityResponse response 0)) hc.2 _ hk
  intro query hacc
  exact candidate.query_bad_subset_remaining _ _ query
    ((gapPolicy).accepts_proximity statement challenge response query _ hacc 0)

/-- The concrete verifier supplies every arithmetic budget and the common
witness-list bound. There is no assumed extraction-success premise. -/
theorem scalarGap_extraction_certificate
    (hmin : HasMinimumDistanceAtLeast C.baseCode d)
    (conditions : SelectedMCALineConditions C.baseCode (Fintype.card F) e g d lineBound)
    (hk : 0 < C.k) :
    Nonempty (ScalarGapExtraction.Certificate (oracle := oracle) (e := e) (g := g) gapPolicy (fun candidate => candidate.decodedMessages) statement
      (max (n - e - 1) (min n (g + (2 * C.k - 1))))
      ((lineBound : ℚ) / (Fintype.card F - (g + 1) : ℕ) +
        (InterleavedJohnson.listBound n d (e + g) : ℚ) / Fintype.card F)) := by
  letI : Nonempty (SchemeTestedRow Ligero.V2.Mask nw nq 1) := ⟨Sum.inr (0, Ligero.V2.Mask.linearZRCoefficient)⟩
  exact ScalarGapExtraction.checked_gap_certificate gapPolicy (fun candidate => candidate.decodedMessages) statement
    (2 * C.k - 1) (fun candidate hns => scalarGap_arithmeticBudget C M oracle statement candidate hns hk)
    (schemeExtractorPolicy (Equations := Equations) (nw := nw) (nq := nq) C (scheme C M)) hmin conditions hk

/-- Acceptance together with failure of the actual response-assisted extractor,
for any statement and any scalar response strategy. -/
theorem scalarGap_extraction_failure
    (hmin : HasMinimumDistanceAtLeast C.baseCode d)
    (conditions : SelectedMCALineConditions C.baseCode (Fintype.card F) e g d lineBound)
    (hk : 0 < C.k)
    (respond : Ligero.V2.Challenge F nw nq 1 Equations → Response F r w n 1) :
    ((univ.filter fun pair : (Ligero.V2.Challenge F nw nq 1 Equations) × QuerySet n r =>
      (gapPolicy).accepts statement pair.1 (respond pair.1) pair.2 (openSchemeOracle oracle pair.2) ∧
      ScalarGapExtraction.extract (oracle := oracle) (e := e) (g := g) gapPolicy (fun candidate => candidate.decodedMessages) statement pair.1 (respond pair.1) = none).card : ℚ) /
      Fintype.card ((Ligero.V2.Challenge F nw nq 1 Equations) × QuerySet n r) ≤
    let delta := hypergeometricRatio
      (max (n - e - 1) (min n (g + (2 * C.k - 1)))) n r
    delta + (1 - delta) *
      ((lineBound : ℚ) / (Fintype.card F - (g + 1) : ℕ) +
        (InterleavedJohnson.listBound n d (e + g) : ℚ) / Fintype.card F) := by
  obtain ⟨cert⟩ := scalarGap_extraction_certificate C M oracle statement hmin conditions hk
  exact cert.extraction_failure (by omega) respond


/-- The same bound on the concrete IOP run, for every prover. -/
theorem scalarGap_iop_extraction_failure
    (hmin : HasMinimumDistanceAtLeast C.baseCode d)
    (conditions : SelectedMCALineConditions C.baseCode (Fintype.card F) e g d lineBound)
    (hk : 0 < C.k)
    (prover : IPCPProver (ConstraintSystem F nw nq w Equations)
      (SchemeOracle F Ligero.V2.Mask NoMask nw nq n 1) (Ligero.V2.Challenge F nw nq 1 Equations) (Response F r w n 1))
    (hcommit : prover.commit statement = oracle) :
    ((univ.filter fun pair : (Ligero.V2.Challenge F nw nq 1 Equations) × QuerySet n r =>
      (gapPolicy).protocol.accepts prover statement pair = true ∧
      ScalarGapExtraction.extract (oracle := oracle) (e := e) (g := g) gapPolicy (fun candidate => candidate.decodedMessages) statement pair.1 (prover.respond statement oracle pair.1) = none).card : ℚ) /
      Fintype.card ((Ligero.V2.Challenge F nw nq 1 Equations) × QuerySet n r) ≤
    let delta := hypergeometricRatio
      (max (n - e - 1) (min n (g + (2 * C.k - 1)))) n r
    delta + (1 - delta) *
      ((lineBound : ℚ) / (Fintype.card F - (g + 1) : ℕ) +
        (InterleavedJohnson.listBound n d (e + g) : ℚ) / Fintype.card F) := by
  obtain ⟨cert⟩ := scalarGap_extraction_certificate C M oracle statement hmin conditions hk
  exact cert.iop_extraction_failure (by omega) prover hcommit

end Ligero.V2
