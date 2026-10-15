import examples.Ligero.Longfellow.IOPParameters
import examples.Ligero.Grid.InverseJohnson
import Ligero.V1.ScalarGapProfiled
import Ligero.V2.ScalarGapProfiled
import Ligero.V3.ScalarGapProfiled
import LigeroFamily.Protocol.FiniteResponse

/-! Exact refined scalar extraction and interactive bounds for actual RS domains.
The finite response instances are used only to state the uniform envelope. -/
namespace Ligero.Examples.Grid.LongfellowProfiledExtraction
open LigeroFamily CodingTheory Finset
open scoped BigOperators Classical
set_option maxHeartbeats 10000000
open LongfellowIOP (Variant Route)
structure Result where
  variant : Variant
  certificate : Certificate
  route : Route
  etaBits : ℕ := 0
  /-- Use independently checked inverse denominators at each agreement. -/
  adaptiveEta : Bool := false

def Result.etaDenominators (s : Result) : ℕ → ℕ :=
  if s.adaptiveEta then s.certificate.inverseEtaDenominator else fun _ => 2 ^ s.etaBits

def Result.localBound (s : Result) : ℕ → ℕ :=
  match s.route with
  | .triples => s.certificate.integratedLocalLineBound
  | .johnson => if s.adaptiveEta then
      s.certificate.inverseJohnsonLocalLineBound s.etaDenominators
    else s.certificate.johnsonLocalLineBound s.etaBits

def Result.failureProfile (s : Result) : AgreementProfile s.certificate.n :=
  let c := s.certificate
  SchemeSelectedMCA.selectedMCAOptimizedIntegratedFailureProfile c.fieldSize c.n c.e c.g c.d
    c.lineBound s.localBound

def Result.cutoff (s : Result) : ℕ :=
  if s.variant = .v1 then s.certificate.maskStart - 1 else 2 * s.certificate.k - 1

def Result.arithmeticProfile (s : Result) : AgreementProfile s.certificate.n :=
  let c := s.certificate
  if s.variant = .v1 then
    maskAgreementProfile c.fieldSize c.n c.listSize c.maskStart c.maskBound
  else checkedAgreementProfile c.fieldSize c.listSize c.n (2 * c.k - 1)

def Result.baseline (s : Result) : ℕ :=
  let c := s.certificate
  max (c.n - c.e - 1) (min c.n (c.g + s.cutoff))

def Result.bound (s : Result) : ℚ :=
  let c := s.certificate
  s.failureProfile.excessContribution c.optimizedFailureDenominator c.n c.n 0 c.openings s.baseline +
    s.arithmeticProfile.contribution c.fieldSize c.n c.e c.g c.openings

def Result.compressedBound (s : Result) : ℚ :=
  let c := s.certificate
  s.failureProfile.compressedExcessContribution c.optimizedFailureDenominator c.n c.n 0 c.openings s.baseline +
    s.arithmeticProfile.compressedContribution c.fieldSize c.n c.e c.g c.openings

theorem Result.compressedBound_eq (s : Result) : s.compressedBound = s.bound := by
  simp only [compressedBound, bound, AgreementProfile.compressedExcessContribution_eq,
    AgreementProfile.contribution_eq_compressedContribution]

def Result.ParametersValid (s : Result) : Prop :=
  let c := s.certificate
  0 < c.k ∧ c.k ≤ c.n ∧ c.d = c.n - c.k + 1 ∧ 2 * c.k ≤ c.n ∧ (if s.variant = .v1 then c.maskValid = true else True) ∧
  (match s.route with
   | .triples => c.conditions
   | .johnson => if s.adaptiveEta then
       c.inverseJohnsonConditions (s.etaDenominators (c.n - c.e)) s.etaDenominators = true
     else c.johnsonConditions s.etaBits = true)

theorem Result.lineConditions (s : Result) (hp : s.ParametersValid)
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {C : LinearCode F s.certificate.n}
    (hf : Fintype.card F = s.certificate.fieldSize)
    (hm : HasMinimumDistanceAtLeast C s.certificate.d)
    (P : JBAgreement.RSPresentation s.certificate.n s.certificate.k C) :
    IntegratedSelectedMCALineConditions C (Fintype.card F) s.certificate.e s.certificate.g
      s.certificate.d s.certificate.lineBound s.localBound := by
  rcases hp with ⟨_, _, _, _, _, hroute⟩
  cases hr : s.route with
  | triples =>
      have hc : s.certificate.conditions := by simpa [hr] using hroute
      have numeric : IntegratedSelectedMCAParameterConditions (Fintype.card F)
          s.certificate.n s.certificate.e s.certificate.g s.certificate.d s.certificate.m
          s.certificate.integratedLocalM := by simpa [Certificate.conditions, hf] using hc
      have h := numeric.lineConditions hm
      have hlocal : (fun a => SelectedMCA.directLineFailureBound
        (s.certificate.integratedLocalM a)) = s.certificate.integratedLocalLineBound := rfl
      rw [hlocal] at h
      simpa only [Result.localBound, hr, Certificate.lineBound] using h
  | johnson =>
      by_cases ha : s.adaptiveEta = true
      · have hc : s.certificate.inverseJohnsonConditions
            (s.etaDenominators (s.certificate.n - s.certificate.e)) s.etaDenominators = true := by
          simpa [hr, ha] using hroute
        have h := s.certificate.inverseJohnsonLineConditions _ _ P hf hc
        rw [← hf] at h
        simpa only [Result.localBound, hr, ha, ite_true] using h
      · have hc : s.certificate.johnsonConditions s.etaBits = true := by
          simpa [hr, ha] using hroute
        have h := s.certificate.johnsonLineConditions P hf hc
        rw [← hf] at h
        simpa [Result.localBound, hr, ha] using h

noncomputable def Result.code (s : Result) {F : Type*} [Field F] [DecidableEq F] {w : ℕ}
    (D : ReedSolomon.Domain F s.certificate.openings w s.certificate.n)
    (hkn : s.certificate.openings + w ≤ s.certificate.n) :=
  LongfellowIOP.certificateCode s.certificate D hkn

theorem Result.codeFacts (s : Result) (hp : s.ParametersValid)
    {F : Type*} [Field F] [DecidableEq F] {w : ℕ}
    (hdim : s.certificate.openings + w = s.certificate.k)
    (D : ReedSolomon.Domain F s.certificate.openings w s.certificate.n)
    (hkn : s.certificate.openings + w ≤ s.certificate.n) :
    (s.code D hkn).k = s.certificate.k ∧
    HasMinimumDistanceAtLeast (s.code D hkn).baseCode s.certificate.d ∧
    Nonempty (JBAgreement.RSPresentation s.certificate.n s.certificate.k (s.code D hkn).baseCode) := by
  exact LongfellowIOP.certificateCodeFacts s.certificate hp.1 hp.2.2.1 hdim D hkn

theorem Result.v1_strategy
    (s : Result) (hp : s.ParametersValid) (hv : s.variant = .v1)
    {F Equations : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Fintype Equations] [DecidableEq Equations] {w nw nq : ℕ}
    (hf : Fintype.card F = s.certificate.fieldSize)
    (hdim : s.certificate.openings + w = s.certificate.k)
    (D : ReedSolomon.Domain F s.certificate.openings w s.certificate.n)
    (hkn : s.certificate.openings + w ≤ s.certificate.n)
    (hrows : CoreRowsNonempty nw nq)
    (statement : ConstraintSystem F nw nq w Equations)
    (oracle : SchemeOracle F NoMask Ligero.V1.Mask nw nq s.certificate.n 1) (respond : Ligero.V1.Challenge F nw nq 1 Equations → Response F s.certificate.openings w s.certificate.n 1) :
    ((univ.filter fun pair : (Ligero.V1.Challenge F nw nq 1 Equations) × QuerySet s.certificate.n s.certificate.openings =>
      (SchemeVerifier.policy (Equations := Equations) (nw := nw) (nq := nq) (repetitions := 1) (s.code D hkn) Ligero.V1.scheme).accepts statement pair.1 (respond pair.1) pair.2 (openSchemeOracle oracle pair.2) ∧
      ScalarGapExtraction.extract (oracle := oracle) (e := s.certificate.e) (g := s.certificate.g)
        (SchemeVerifier.policy (Equations := Equations) (nw := nw) (nq := nq) (repetitions := 1) (s.code D hkn) Ligero.V1.scheme) (fun candidate => candidate.decodedMessages) statement pair.1 (respond pair.1) = none).card : ℚ) /
      Fintype.card ((Ligero.V1.Challenge F nw nq 1 Equations) × QuerySet s.certificate.n s.certificate.openings) ≤ s.bound := by
  obtain ⟨hk, hm, ⟨P⟩⟩ := s.codeFacts hp hdim D hkn
  have hc := s.lineConditions hp hf hm P
  have hkpos : 0 < (s.code D hkn).k := by rw [hk]; exact hp.1
  have h2k : 2 * (s.code D hkn).k ≤ s.certificate.n := by rw [hk]; exact hp.2.2.2.1
  have hmaskValid : s.certificate.maskValid = true := by
    simpa [hv] using hp.2.2.2.2.1
  have mask := V1Certificate.v1MaskRange s.certificate hp.1 hp.2.2.2.1 hmaskValid
    (s.code D hkn) hk
  have ht : s.certificate.maskStart ≤ s.certificate.n := by
    have hn : 0 < s.certificate.n := hp.1.trans_le hp.2.1
    have hlt : 2 * s.certificate.k - 1 < s.certificate.n := by have := hp.1; have := hp.2.2.2.1; omega
    have hs : Nat.sqrt (s.certificate.n * (2 * s.certificate.k - 1)) < s.certificate.n := by
      rw [Nat.sqrt_lt]; nlinarith
    have hvalid := hmaskValid
    simp only [Certificate.maskValid, Bool.and_eq_true, decide_eq_true_eq] at hvalid
    have hmask := hvalid.1.1
    unfold Certificate.v1Threshold at hmask
    omega
  have hradius : s.certificate.e + s.certificate.g < s.certificate.d := by
    have := hc.outer.punctured.punctured_three_radius
    omega
  have hlist := SchemeLiftCandidate.univ_card_le_uniformFamilyBound
    (s.code D hkn) oracle hm hradius
    (s.certificate.listFamily hradius hm.distance_le_length
      hc.outer.johnson.list_denominator_positive)
  have h := Ligero.V1.scalarGap_profiled_extraction_failure_of_card (s.code D hkn)
    oracle statement hm hc hlist hrows mask ht respond
  simpa [Result.bound, Result.failureProfile, Result.arithmeticProfile, Result.baseline,
    Result.cutoff, Certificate.optimizedFailureDenominator, Certificate.listSize, hv, hf, hk] using h

/-- Concrete IOP extraction: no false-statement or auxiliary farness premise. -/
theorem Result.v1_extraction
    (s : Result) (hp : s.ParametersValid) (hv : s.variant = .v1)
    {F Equations : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Fintype Equations] [DecidableEq Equations] {w nw nq : ℕ}
    (hf : Fintype.card F = s.certificate.fieldSize)
    (hdim : s.certificate.openings + w = s.certificate.k)
    (D : ReedSolomon.Domain F s.certificate.openings w s.certificate.n)
    (hkn : s.certificate.openings + w ≤ s.certificate.n)
    (hrows : CoreRowsNonempty nw nq)
    (statement : ConstraintSystem F nw nq w Equations)
    (hb : s.bound ≤ (1 : ℚ) / 2 ^ s.certificate.targetBits)
    (prover : IPCPProver (ConstraintSystem F nw nq w Equations) (SchemeOracle F NoMask Ligero.V1.Mask nw nq s.certificate.n 1) (Ligero.V1.Challenge F nw nq 1 Equations) (Response F s.certificate.openings w s.certificate.n 1)) :
    extractionFailureRate (SchemeVerifier.policy (Equations := Equations) (nw := nw) (nq := nq) (repetitions := 1) (s.code D hkn) Ligero.V1.scheme).protocol prover statement (Ligero.V1.scalarGapExtract (e := s.certificate.e) (g := s.certificate.g) (s.code D hkn) (prover.commit statement) statement) ≤
      (1 : ℚ) / 2 ^ s.certificate.targetBits := by
  have h := Result.v1_strategy s hp hv hf hdim D hkn hrows statement (prover.commit statement)
    (prover.respond statement (prover.commit statement))
  have hr : extractionFailureRate (SchemeVerifier.policy (Equations := Equations) (nw := nw) (nq := nq) (repetitions := 1) (s.code D hkn) Ligero.V1.scheme).protocol prover statement (Ligero.V1.scalarGapExtract (e := s.certificate.e) (g := s.certificate.g) (s.code D hkn) (prover.commit statement) statement) ≤ s.bound := by
    simpa [extractionFailureRate, PublicCoinIPCP.accepts, PublicCoinIPCP.run,
      SchemeProtocolPolicy.protocol, Ligero.V1.scalarGapExtract] using h
  exact hr.trans hb

/-- False-statement interactive soundness follows from extraction validity. -/
theorem Result.v1_interactive
    (s : Result) (hp : s.ParametersValid) (hv : s.variant = .v1)
    {F Equations : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Fintype Equations] [DecidableEq Equations] {w nw nq : ℕ}
    (hf : Fintype.card F = s.certificate.fieldSize)
    (hdim : s.certificate.openings + w = s.certificate.k)
    (D : ReedSolomon.Domain F s.certificate.openings w s.certificate.n)
    (hkn : s.certificate.openings + w ≤ s.certificate.n)
    (hrows : CoreRowsNonempty nw nq)
    (statement : ConstraintSystem F nw nq w Equations)
    (hb : s.bound ≤ (1 : ℚ) / 2 ^ s.certificate.targetBits)
    (hfalse : ¬statement.Language)
    (prover : IPCPProver (ConstraintSystem F nw nq w Equations) (SchemeOracle F NoMask Ligero.V1.Mask nw nq s.certificate.n 1) (Ligero.V1.Challenge F nw nq 1 Equations) (Response F s.certificate.openings w s.certificate.n 1)) :
    (SchemeVerifier.policy (Equations := Equations) (nw := nw) (nq := nq) (repetitions := 1) (s.code D hkn) Ligero.V1.scheme).protocol.acceptanceRate prover statement ≤
      (1 : ℚ) / 2 ^ s.certificate.targetBits := by
  have h := Result.v1_extraction s hp hv hf hdim D hkn hrows statement hb prover
  have hext : ∀ challenge, (Ligero.V1.scalarGapExtract (e := s.certificate.e) (g := s.certificate.g) (s.code D hkn) (prover.commit statement) statement) challenge
      (prover.respond statement (prover.commit statement) challenge) = none := by
    intro challenge
    apply ScalarGapExtraction.extract_none_of_no_valid (SchemeVerifier.policy (Equations := Equations) (nw := nw) (nq := nq) (repetitions := 1) (s.code D hkn) Ligero.V1.scheme) (fun candidate => candidate.decodedMessages) statement
    intro candidate hsat; exact hfalse ⟨_, hsat⟩
  simpa only [extractionFailureRate, hext, and_true, PublicCoinIPCP.acceptanceRate,
    finiteProtocolAcceptanceRate] using h

/-- The same bound for a single oracle-fixed envelope over every response. -/
theorem Result.v1_uniform_envelope
    (s : Result) (hp : s.ParametersValid) (hv : s.variant = .v1)
    {F Equations : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Fintype Equations] [DecidableEq Equations] {w nw nq : ℕ}
    (hf : Fintype.card F = s.certificate.fieldSize)
    (hdim : s.certificate.openings + w = s.certificate.k)
    (D : ReedSolomon.Domain F s.certificate.openings w s.certificate.n)
    (hkn : s.certificate.openings + w ≤ s.certificate.n)
    (hrows : CoreRowsNonempty nw nq)
    (statement : ConstraintSystem F nw nq w Equations)
    (oracle : SchemeOracle F NoMask Ligero.V1.Mask nw nq s.certificate.n 1)
    (hb : s.bound ≤ (1 : ℚ) / 2 ^ s.certificate.targetBits) :
    (∑ challenge : Ligero.V1.Challenge F nw nq 1 Equations,
      ScalarGapExtraction.profiledUniformEnvelope (oracle := oracle)
        (e := s.certificate.e) (g := s.certificate.g) (SchemeVerifier.policy (Equations := Equations) (nw := nw) (nq := nq) (repetitions := 1) (s.code D hkn) Ligero.V1.scheme) (fun candidate => candidate.decodedMessages) statement challenge) /
      Fintype.card (Ligero.V1.Challenge F nw nq 1 Equations) ≤ (1 : ℚ) / 2 ^ s.certificate.targetBits := by
  letI : Nonempty (Response F s.certificate.openings w s.certificate.n 1) := ⟨⟨fun _ => 0, fun _ => 0, fun _ => 0⟩⟩
  apply ScalarGapExtraction.profiledUniformEnvelope_mean_of_strategies (SchemeVerifier.policy (Equations := Equations) (nw := nw) (nq := nq) (repetitions := 1) (s.code D hkn) Ligero.V1.scheme) (fun candidate => candidate.decodedMessages)
    statement ((1 : ℚ) / 2 ^ s.certificate.targetBits)
  intro respond
  exact (Result.v1_strategy s hp hv hf hdim D hkn hrows statement oracle respond).trans hb

/-- The same response-uniform envelope at the certificate's exact rational
bound, before rounding it to a whole number of bits. -/
theorem Result.v1_uniform_envelope_exact
    (s : Result) (hp : s.ParametersValid) (hv : s.variant = .v1)
    {F Equations : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Fintype Equations] [DecidableEq Equations] {w nw nq : ℕ}
    (hf : Fintype.card F = s.certificate.fieldSize)
    (hdim : s.certificate.openings + w = s.certificate.k)
    (D : ReedSolomon.Domain F s.certificate.openings w s.certificate.n)
    (hkn : s.certificate.openings + w ≤ s.certificate.n)
    (hrows : CoreRowsNonempty nw nq)
    (statement : ConstraintSystem F nw nq w Equations)
    (oracle : SchemeOracle F NoMask Ligero.V1.Mask nw nq s.certificate.n 1) :
    (∑ challenge : Ligero.V1.Challenge F nw nq 1 Equations,
      ScalarGapExtraction.profiledUniformEnvelope (oracle := oracle)
        (e := s.certificate.e) (g := s.certificate.g)
        (SchemeVerifier.policy (Equations := Equations) (nw := nw) (nq := nq)
          (repetitions := 1) (s.code D hkn) Ligero.V1.scheme)
        (fun candidate => candidate.decodedMessages) statement challenge) /
      Fintype.card (Ligero.V1.Challenge F nw nq 1 Equations) ≤ s.bound := by
  letI : Nonempty (Response F s.certificate.openings w s.certificate.n 1) :=
    ⟨⟨fun _ => 0, fun _ => 0, fun _ => 0⟩⟩
  apply ScalarGapExtraction.profiledUniformEnvelope_mean_of_strategies
    (SchemeVerifier.policy (Equations := Equations) (nw := nw) (nq := nq)
      (repetitions := 1) (s.code D hkn) Ligero.V1.scheme)
    (fun candidate => candidate.decodedMessages) statement s.bound
  intro respond
  exact Result.v1_strategy s hp hv hf hdim D hkn hrows statement oracle respond

/-- The certified flat envelope also bounds raw acceptance when no member of the
committed lift list solves the encoded statement.  In this case the extractor
returns `none` for every challenge and response, so the failing-query envelope
is exactly the acceptance envelope. -/
theorem Result.v1_uniform_acceptance_of_noDecoded
    (s : Result) (hp : s.ParametersValid) (hv : s.variant = .v1)
    {F Equations : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Fintype Equations] [DecidableEq Equations] {w nw nq : ℕ}
    (hf : Fintype.card F = s.certificate.fieldSize)
    (hdim : s.certificate.openings + w = s.certificate.k)
    (D : ReedSolomon.Domain F s.certificate.openings w s.certificate.n)
    (hkn : s.certificate.openings + w ≤ s.certificate.n)
    (hrows : CoreRowsNonempty nw nq)
    (statement : ConstraintSystem F nw nq w Equations)
    (oracle : SchemeOracle F NoMask Ligero.V1.Mask nw nq s.certificate.n 1)
    (hb : s.bound ≤ (1 : ℚ) / 2 ^ s.certificate.targetBits)
    (hnd : NoDecodedSolution (s.code D hkn) oracle
      (s.certificate.e + s.certificate.g) statement) :
    (∑ challenge : Ligero.V1.Challenge F nw nq 1 Equations,
      (((Finset.univ : Finset (Response F s.certificate.openings w s.certificate.n 1)).sup
        fun response => (Finset.univ.filter fun query : QuerySet s.certificate.n
          s.certificate.openings =>
          (SchemeVerifier.policy (Equations := Equations) (nw := nw) (nq := nq)
            (repetitions := 1) (s.code D hkn) Ligero.V1.scheme).accepts
            statement challenge response query (openSchemeOracle oracle query)).card : ℕ) : ℚ)
        / s.certificate.n.choose s.certificate.openings) /
      Fintype.card (Ligero.V1.Challenge F nw nq 1 Equations)
      ≤ (1 : ℚ) / 2 ^ s.certificate.targetBits := by
  letI : Nonempty (Response F s.certificate.openings w s.certificate.n 1) :=
    ⟨⟨fun _ => 0, fun _ => 0, fun _ => 0⟩⟩
  have hnone (challenge : Ligero.V1.Challenge F nw nq 1 Equations)
      (response : Response F s.certificate.openings w s.certificate.n 1) :
      ScalarGapExtraction.extract (oracle := oracle) (e := s.certificate.e)
        (g := s.certificate.g)
        (SchemeVerifier.policy (Equations := Equations) (nw := nw) (nq := nq)
          (repetitions := 1) (s.code D hkn) Ligero.V1.scheme)
        (fun candidate => candidate.decodedMessages) statement challenge response = none := by
    exact ScalarGapExtraction.extract_none_of_no_valid _ _ _ challenge response hnd
  have h := s.v1_uniform_envelope hp hv hf hdim D hkn hrows statement oracle hb
  simpa only [ScalarGapExtraction.profiledUniformEnvelope,
    ScalarGapExtraction.failingQueries, hnone, and_true] using h

/-- The candidate-count certificate at the same radius as the flat envelope. -/
theorem Result.v1_lift_card_le (s : Result) (hp : s.ParametersValid)
    {F : Type*} [Field F] [Fintype F] [DecidableEq F] {w nw nq : ℕ}
    (hf : Fintype.card F = s.certificate.fieldSize)
    (hdim : s.certificate.openings + w = s.certificate.k)
    (D : ReedSolomon.Domain F s.certificate.openings w s.certificate.n)
    (hkn : s.certificate.openings + w ≤ s.certificate.n)
    (oracle : SchemeOracle F NoMask Ligero.V1.Mask nw nq s.certificate.n 1) :
    Fintype.card (SchemeLiftCandidate (s.code D hkn) oracle
      (s.certificate.e + s.certificate.g)) ≤ s.certificate.listSize := by
  obtain ⟨_, hm, ⟨P⟩⟩ := s.codeFacts hp hdim D hkn
  have hc := s.lineConditions hp hf hm P
  have hradius : s.certificate.e + s.certificate.g < s.certificate.d := by
    have := hc.outer.punctured.punctured_three_radius
    omega
  exact SchemeLiftCandidate.univ_card_le_uniformFamilyBound
    (s.code D hkn) oracle hm hradius
    (s.certificate.listFamily hradius hm.distance_le_length
      hc.outer.johnson.list_denominator_positive)

theorem Result.v2_strategy
    (s : Result) (hp : s.ParametersValid) (hv : s.variant = .v2)
    {F Equations : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Fintype Equations] [DecidableEq Equations] {w nw nq : ℕ}
    (hf : Fintype.card F = s.certificate.fieldSize)
    (hdim : s.certificate.openings + w = s.certificate.k)
    (D : ReedSolomon.Domain F s.certificate.openings w s.certificate.n)
    (hkn : s.certificate.openings + w ≤ s.certificate.n)
    (M : (s.code D hkn).MaskingBasis)
    (statement : ConstraintSystem F nw nq w Equations)
    (oracle : SchemeOracle F Ligero.V2.Mask NoMask nw nq s.certificate.n 1) (respond : Ligero.V2.Challenge F nw nq 1 Equations → Response F s.certificate.openings w s.certificate.n 1) :
    ((univ.filter fun pair : (Ligero.V2.Challenge F nw nq 1 Equations) × QuerySet s.certificate.n s.certificate.openings =>
      (SchemeVerifier.policy (Equations := Equations) (nw := nw) (nq := nq) (repetitions := 1) (s.code D hkn) (Ligero.V2.scheme (s.code D hkn) M)).accepts statement pair.1 (respond pair.1) pair.2 (openSchemeOracle oracle pair.2) ∧
      ScalarGapExtraction.extract (oracle := oracle) (e := s.certificate.e) (g := s.certificate.g)
        (SchemeVerifier.policy (Equations := Equations) (nw := nw) (nq := nq) (repetitions := 1) (s.code D hkn) (Ligero.V2.scheme (s.code D hkn) M)) (fun candidate => candidate.decodedMessages) statement pair.1 (respond pair.1) = none).card : ℚ) /
      Fintype.card ((Ligero.V2.Challenge F nw nq 1 Equations) × QuerySet s.certificate.n s.certificate.openings) ≤ s.bound := by
  obtain ⟨hk, hm, ⟨P⟩⟩ := s.codeFacts hp hdim D hkn
  have hc := s.lineConditions hp hf hm P
  have hkpos : 0 < (s.code D hkn).k := by rw [hk]; exact hp.1
  have h2k : 2 * (s.code D hkn).k ≤ s.certificate.n := by rw [hk]; exact hp.2.2.2.1
  have hradius : s.certificate.e + s.certificate.g < s.certificate.d := by
    have := hc.outer.punctured.punctured_three_radius
    omega
  have hlist := SchemeLiftCandidate.univ_card_le_uniformFamilyBound
    (s.code D hkn) oracle hm hradius
    (s.certificate.listFamily hradius hm.distance_le_length
      hc.outer.johnson.list_denominator_positive)
  have h := Ligero.V2.scalarGap_profiled_extraction_failure_of_card (s.code D hkn) M oracle statement hm hc hlist hkpos h2k respond
  simpa [Result.bound, Result.failureProfile, Result.arithmeticProfile, Result.baseline,
    Result.cutoff, Certificate.optimizedFailureDenominator, Certificate.listSize, hv, hf, hk] using h

/-- Concrete IOP extraction: no false-statement or auxiliary farness premise. -/
theorem Result.v2_extraction
    (s : Result) (hp : s.ParametersValid) (hv : s.variant = .v2)
    {F Equations : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Fintype Equations] [DecidableEq Equations] {w nw nq : ℕ}
    (hf : Fintype.card F = s.certificate.fieldSize)
    (hdim : s.certificate.openings + w = s.certificate.k)
    (D : ReedSolomon.Domain F s.certificate.openings w s.certificate.n)
    (hkn : s.certificate.openings + w ≤ s.certificate.n)
    (M : (s.code D hkn).MaskingBasis)
    (statement : ConstraintSystem F nw nq w Equations)
    (hb : s.bound ≤ (1 : ℚ) / 2 ^ s.certificate.targetBits)
    (prover : IPCPProver (ConstraintSystem F nw nq w Equations) (SchemeOracle F Ligero.V2.Mask NoMask nw nq s.certificate.n 1) (Ligero.V2.Challenge F nw nq 1 Equations) (Response F s.certificate.openings w s.certificate.n 1)) :
    extractionFailureRate (SchemeVerifier.policy (Equations := Equations) (nw := nw) (nq := nq) (repetitions := 1) (s.code D hkn) (Ligero.V2.scheme (s.code D hkn) M)).protocol prover statement (Ligero.V2.scalarGapExtract (e := s.certificate.e) (g := s.certificate.g) (s.code D hkn) M (prover.commit statement) statement) ≤
      (1 : ℚ) / 2 ^ s.certificate.targetBits := by
  have h := Result.v2_strategy s hp hv hf hdim D hkn M statement (prover.commit statement)
    (prover.respond statement (prover.commit statement))
  have hr : extractionFailureRate (SchemeVerifier.policy (Equations := Equations) (nw := nw) (nq := nq) (repetitions := 1) (s.code D hkn) (Ligero.V2.scheme (s.code D hkn) M)).protocol prover statement (Ligero.V2.scalarGapExtract (e := s.certificate.e) (g := s.certificate.g) (s.code D hkn) M (prover.commit statement) statement) ≤ s.bound := by
    simpa [extractionFailureRate, PublicCoinIPCP.accepts, PublicCoinIPCP.run,
      SchemeProtocolPolicy.protocol, Ligero.V2.scalarGapExtract] using h
  exact hr.trans hb

/-- False-statement interactive soundness follows from extraction validity. -/
theorem Result.v2_interactive
    (s : Result) (hp : s.ParametersValid) (hv : s.variant = .v2)
    {F Equations : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Fintype Equations] [DecidableEq Equations] {w nw nq : ℕ}
    (hf : Fintype.card F = s.certificate.fieldSize)
    (hdim : s.certificate.openings + w = s.certificate.k)
    (D : ReedSolomon.Domain F s.certificate.openings w s.certificate.n)
    (hkn : s.certificate.openings + w ≤ s.certificate.n)
    (M : (s.code D hkn).MaskingBasis)
    (statement : ConstraintSystem F nw nq w Equations)
    (hb : s.bound ≤ (1 : ℚ) / 2 ^ s.certificate.targetBits)
    (hfalse : ¬statement.Language)
    (prover : IPCPProver (ConstraintSystem F nw nq w Equations) (SchemeOracle F Ligero.V2.Mask NoMask nw nq s.certificate.n 1) (Ligero.V2.Challenge F nw nq 1 Equations) (Response F s.certificate.openings w s.certificate.n 1)) :
    (SchemeVerifier.policy (Equations := Equations) (nw := nw) (nq := nq) (repetitions := 1) (s.code D hkn) (Ligero.V2.scheme (s.code D hkn) M)).protocol.acceptanceRate prover statement ≤
      (1 : ℚ) / 2 ^ s.certificate.targetBits := by
  have h := Result.v2_extraction s hp hv hf hdim D hkn M statement hb prover
  have hext : ∀ challenge, (Ligero.V2.scalarGapExtract (e := s.certificate.e) (g := s.certificate.g) (s.code D hkn) M (prover.commit statement) statement) challenge
      (prover.respond statement (prover.commit statement) challenge) = none := by
    intro challenge
    apply ScalarGapExtraction.extract_none_of_no_valid (SchemeVerifier.policy (Equations := Equations) (nw := nw) (nq := nq) (repetitions := 1) (s.code D hkn) (Ligero.V2.scheme (s.code D hkn) M)) (fun candidate => candidate.decodedMessages) statement
    intro candidate hsat; exact hfalse ⟨_, hsat⟩
  simpa only [extractionFailureRate, hext, and_true, PublicCoinIPCP.acceptanceRate,
    finiteProtocolAcceptanceRate] using h

/-- The same bound for a single oracle-fixed envelope over every response. -/
theorem Result.v2_uniform_envelope
    (s : Result) (hp : s.ParametersValid) (hv : s.variant = .v2)
    {F Equations : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Fintype Equations] [DecidableEq Equations] {w nw nq : ℕ}
    (hf : Fintype.card F = s.certificate.fieldSize)
    (hdim : s.certificate.openings + w = s.certificate.k)
    (D : ReedSolomon.Domain F s.certificate.openings w s.certificate.n)
    (hkn : s.certificate.openings + w ≤ s.certificate.n)
    (M : (s.code D hkn).MaskingBasis)
    (statement : ConstraintSystem F nw nq w Equations)
    (oracle : SchemeOracle F Ligero.V2.Mask NoMask nw nq s.certificate.n 1)
    (hb : s.bound ≤ (1 : ℚ) / 2 ^ s.certificate.targetBits) :
    (∑ challenge : Ligero.V2.Challenge F nw nq 1 Equations,
      ScalarGapExtraction.profiledUniformEnvelope (oracle := oracle)
        (e := s.certificate.e) (g := s.certificate.g) (SchemeVerifier.policy (Equations := Equations) (nw := nw) (nq := nq) (repetitions := 1) (s.code D hkn) (Ligero.V2.scheme (s.code D hkn) M)) (fun candidate => candidate.decodedMessages) statement challenge) /
      Fintype.card (Ligero.V2.Challenge F nw nq 1 Equations) ≤ (1 : ℚ) / 2 ^ s.certificate.targetBits := by
  letI : Nonempty (Response F s.certificate.openings w s.certificate.n 1) := ⟨⟨fun _ => 0, fun _ => 0, fun _ => 0⟩⟩
  apply ScalarGapExtraction.profiledUniformEnvelope_mean_of_strategies (SchemeVerifier.policy (Equations := Equations) (nw := nw) (nq := nq) (repetitions := 1) (s.code D hkn) (Ligero.V2.scheme (s.code D hkn) M)) (fun candidate => candidate.decodedMessages)
    statement ((1 : ℚ) / 2 ^ s.certificate.targetBits)
  intro respond
  exact (Result.v2_strategy s hp hv hf hdim D hkn M statement oracle respond).trans hb

theorem Result.v3_strategy
    (s : Result) (hp : s.ParametersValid) (hv : s.variant = .v3)
    {F Equations : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Fintype Equations] [DecidableEq Equations] {w nw nq : ℕ}
    (hf : Fintype.card F = s.certificate.fieldSize)
    (hdim : s.certificate.openings + w = s.certificate.k)
    (D : ReedSolomon.Domain F s.certificate.openings w s.certificate.n)
    (hkn : s.certificate.openings + w ≤ s.certificate.n)
    (M : (s.code D hkn).MaskingBasis)
    (statement : ConstraintSystem F nw nq w Equations)
    (oracle : SchemeOracle F LinearConstraintMask NoMask nw nq s.certificate.n 1) (respond : DirectChallenge F Equations nw nq 1 → DirectResponse F s.certificate.openings w s.certificate.n 1) :
    ((univ.filter fun pair : (DirectChallenge F Equations nw nq 1) × QuerySet s.certificate.n s.certificate.openings =>
      (DirectVerifier.policy (Equations := Equations) (nw := nw) (nq := nq) (repetitions := 1) (s.code D hkn) M (ConstraintLayout.identity (F := F) w)).accepts statement pair.1 (respond pair.1) pair.2 (openSchemeOracle oracle pair.2) ∧
      ScalarGapExtraction.extract (oracle := oracle) (e := s.certificate.e) (g := s.certificate.g)
        (DirectVerifier.policy (Equations := Equations) (nw := nw) (nq := nq) (repetitions := 1) (s.code D hkn) M (ConstraintLayout.identity (F := F) w)) (fun candidate => candidate.directMessages (layout := ConstraintLayout.identity (F := F) w)) statement pair.1 (respond pair.1) = none).card : ℚ) /
      Fintype.card ((DirectChallenge F Equations nw nq 1) × QuerySet s.certificate.n s.certificate.openings) ≤ s.bound := by
  obtain ⟨hk, hm, ⟨P⟩⟩ := s.codeFacts hp hdim D hkn
  have hc := s.lineConditions hp hf hm P
  have hkpos : 0 < (s.code D hkn).k := by rw [hk]; exact hp.1
  have h2k : 2 * (s.code D hkn).k ≤ s.certificate.n := by rw [hk]; exact hp.2.2.2.1
  have hradius : s.certificate.e + s.certificate.g < s.certificate.d := by
    have := hc.outer.punctured.punctured_three_radius
    omega
  have hlist := SchemeLiftCandidate.univ_card_le_uniformFamilyBound
    (s.code D hkn) oracle hm hradius
    (s.certificate.listFamily hradius hm.distance_le_length
      hc.outer.johnson.list_denominator_positive)
  have h := Ligero.V3.scalarGap_profiled_extraction_failure_of_card (s.code D hkn) M (ConstraintLayout.identity (F := F) w) oracle statement hm hc hlist hkpos h2k respond
  simpa [Result.bound, Result.failureProfile, Result.arithmeticProfile, Result.baseline,
    Result.cutoff, Certificate.optimizedFailureDenominator, Certificate.listSize, hv, hf, hk] using h

/-- Concrete IOP extraction: no false-statement or auxiliary farness premise. -/
theorem Result.v3_extraction
    (s : Result) (hp : s.ParametersValid) (hv : s.variant = .v3)
    {F Equations : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Fintype Equations] [DecidableEq Equations] {w nw nq : ℕ}
    (hf : Fintype.card F = s.certificate.fieldSize)
    (hdim : s.certificate.openings + w = s.certificate.k)
    (D : ReedSolomon.Domain F s.certificate.openings w s.certificate.n)
    (hkn : s.certificate.openings + w ≤ s.certificate.n)
    (M : (s.code D hkn).MaskingBasis)
    (statement : ConstraintSystem F nw nq w Equations)
    (hb : s.bound ≤ (1 : ℚ) / 2 ^ s.certificate.targetBits)
    (prover : IPCPProver (ConstraintSystem F nw nq w Equations) (SchemeOracle F LinearConstraintMask NoMask nw nq s.certificate.n 1) (DirectChallenge F Equations nw nq 1) (DirectResponse F s.certificate.openings w s.certificate.n 1)) :
    extractionFailureRate (DirectVerifier.policy (Equations := Equations) (nw := nw) (nq := nq) (repetitions := 1) (s.code D hkn) M (ConstraintLayout.identity (F := F) w)).protocol prover statement (Ligero.V3.scalarGapExtract (e := s.certificate.e) (g := s.certificate.g) (s.code D hkn) M (ConstraintLayout.identity (F := F) w) (prover.commit statement) statement) ≤
      (1 : ℚ) / 2 ^ s.certificate.targetBits := by
  have h := Result.v3_strategy s hp hv hf hdim D hkn M statement (prover.commit statement)
    (prover.respond statement (prover.commit statement))
  have hr : extractionFailureRate (DirectVerifier.policy (Equations := Equations) (nw := nw) (nq := nq) (repetitions := 1) (s.code D hkn) M (ConstraintLayout.identity (F := F) w)).protocol prover statement (Ligero.V3.scalarGapExtract (e := s.certificate.e) (g := s.certificate.g) (s.code D hkn) M (ConstraintLayout.identity (F := F) w) (prover.commit statement) statement) ≤ s.bound := by
    simpa [extractionFailureRate, PublicCoinIPCP.accepts, PublicCoinIPCP.run,
      SchemeProtocolPolicy.protocol, Ligero.V3.scalarGapExtract] using h
  exact hr.trans hb

/-- False-statement interactive soundness follows from extraction validity. -/
theorem Result.v3_interactive
    (s : Result) (hp : s.ParametersValid) (hv : s.variant = .v3)
    {F Equations : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Fintype Equations] [DecidableEq Equations] {w nw nq : ℕ}
    (hf : Fintype.card F = s.certificate.fieldSize)
    (hdim : s.certificate.openings + w = s.certificate.k)
    (D : ReedSolomon.Domain F s.certificate.openings w s.certificate.n)
    (hkn : s.certificate.openings + w ≤ s.certificate.n)
    (M : (s.code D hkn).MaskingBasis)
    (statement : ConstraintSystem F nw nq w Equations)
    (hb : s.bound ≤ (1 : ℚ) / 2 ^ s.certificate.targetBits)
    (hfalse : ¬statement.Language)
    (prover : IPCPProver (ConstraintSystem F nw nq w Equations) (SchemeOracle F LinearConstraintMask NoMask nw nq s.certificate.n 1) (DirectChallenge F Equations nw nq 1) (DirectResponse F s.certificate.openings w s.certificate.n 1)) :
    (DirectVerifier.policy (Equations := Equations) (nw := nw) (nq := nq) (repetitions := 1) (s.code D hkn) M (ConstraintLayout.identity (F := F) w)).protocol.acceptanceRate prover statement ≤
      (1 : ℚ) / 2 ^ s.certificate.targetBits := by
  have h := Result.v3_extraction s hp hv hf hdim D hkn M statement hb prover
  have hext : ∀ challenge, (Ligero.V3.scalarGapExtract (e := s.certificate.e) (g := s.certificate.g) (s.code D hkn) M (ConstraintLayout.identity (F := F) w) (prover.commit statement) statement) challenge
      (prover.respond statement (prover.commit statement) challenge) = none := by
    intro challenge
    apply ScalarGapExtraction.extract_none_of_no_valid (DirectVerifier.policy (Equations := Equations) (nw := nw) (nq := nq) (repetitions := 1) (s.code D hkn) M (ConstraintLayout.identity (F := F) w)) (fun candidate => candidate.directMessages (layout := ConstraintLayout.identity (F := F) w)) statement
    intro candidate hsat; exact hfalse ⟨_, hsat⟩
  simpa only [extractionFailureRate, hext, and_true, PublicCoinIPCP.acceptanceRate,
    finiteProtocolAcceptanceRate] using h

/-- The same bound for a single oracle-fixed envelope over every response. -/
theorem Result.v3_uniform_envelope
    (s : Result) (hp : s.ParametersValid) (hv : s.variant = .v3)
    {F Equations : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Fintype Equations] [DecidableEq Equations] {w nw nq : ℕ}
    (hf : Fintype.card F = s.certificate.fieldSize)
    (hdim : s.certificate.openings + w = s.certificate.k)
    (D : ReedSolomon.Domain F s.certificate.openings w s.certificate.n)
    (hkn : s.certificate.openings + w ≤ s.certificate.n)
    (M : (s.code D hkn).MaskingBasis)
    (statement : ConstraintSystem F nw nq w Equations)
    (oracle : SchemeOracle F LinearConstraintMask NoMask nw nq s.certificate.n 1)
    (hb : s.bound ≤ (1 : ℚ) / 2 ^ s.certificate.targetBits) :
    (∑ challenge : DirectChallenge F Equations nw nq 1,
      ScalarGapExtraction.profiledUniformEnvelope (oracle := oracle)
        (e := s.certificate.e) (g := s.certificate.g) (DirectVerifier.policy (Equations := Equations) (nw := nw) (nq := nq) (repetitions := 1) (s.code D hkn) M (ConstraintLayout.identity (F := F) w)) (fun candidate => candidate.directMessages (layout := ConstraintLayout.identity (F := F) w)) statement challenge) /
      Fintype.card (DirectChallenge F Equations nw nq 1) ≤ (1 : ℚ) / 2 ^ s.certificate.targetBits := by
  letI : Nonempty (DirectResponse F s.certificate.openings w s.certificate.n 1) := ⟨⟨fun _ => 0, fun _ => 0⟩⟩
  apply ScalarGapExtraction.profiledUniformEnvelope_mean_of_strategies (DirectVerifier.policy (Equations := Equations) (nw := nw) (nq := nq) (repetitions := 1) (s.code D hkn) M (ConstraintLayout.identity (F := F) w)) (fun candidate => candidate.directMessages (layout := ConstraintLayout.identity (F := F) w))
    statement ((1 : ℚ) / 2 ^ s.certificate.targetBits)
  intro respond
  exact (Result.v3_strategy s hp hv hf hdim D hkn M statement oracle respond).trans hb

structure CertifiedResult where
  result : Result
  parameters : result.ParametersValid
  bound : result.bound ≤ (1 : ℚ) / 2 ^ result.certificate.targetBits

theorem CertifiedResult.v1_extraction
    (s : CertifiedResult) (hv : s.result.variant = .v1)
    {F Equations : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Fintype Equations] [DecidableEq Equations] {w nw nq : ℕ}
    (hf : Fintype.card F = s.result.certificate.fieldSize)
    (hdim : s.result.certificate.openings + w = s.result.certificate.k)
    (D : ReedSolomon.Domain F s.result.certificate.openings w s.result.certificate.n)
    (hkn : s.result.certificate.openings + w ≤ s.result.certificate.n)
    (hrows : CoreRowsNonempty nw nq)
    (statement : ConstraintSystem F nw nq w Equations)
    (prover : IPCPProver (ConstraintSystem F nw nq w Equations) (SchemeOracle F NoMask Ligero.V1.Mask nw nq s.result.certificate.n 1) (Ligero.V1.Challenge F nw nq 1 Equations) (Response F s.result.certificate.openings w s.result.certificate.n 1)) :
    extractionFailureRate (SchemeVerifier.policy (Equations := Equations) (nw := nw) (nq := nq) (repetitions := 1) (s.result.code D hkn) Ligero.V1.scheme).protocol prover statement (Ligero.V1.scalarGapExtract (e := s.result.certificate.e) (g := s.result.certificate.g) (s.result.code D hkn) (prover.commit statement) statement) ≤
      (1 : ℚ) / 2 ^ s.result.certificate.targetBits := by
  exact Result.v1_extraction s.result s.parameters hv hf hdim D hkn hrows statement s.bound prover

theorem CertifiedResult.v1_interactive
    (s : CertifiedResult) (hv : s.result.variant = .v1)
    {F Equations : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Fintype Equations] [DecidableEq Equations] {w nw nq : ℕ}
    (hf : Fintype.card F = s.result.certificate.fieldSize)
    (hdim : s.result.certificate.openings + w = s.result.certificate.k)
    (D : ReedSolomon.Domain F s.result.certificate.openings w s.result.certificate.n)
    (hkn : s.result.certificate.openings + w ≤ s.result.certificate.n)
    (hrows : CoreRowsNonempty nw nq)
    (statement : ConstraintSystem F nw nq w Equations)
    (hfalse : ¬statement.Language)
    (prover : IPCPProver (ConstraintSystem F nw nq w Equations) (SchemeOracle F NoMask Ligero.V1.Mask nw nq s.result.certificate.n 1) (Ligero.V1.Challenge F nw nq 1 Equations) (Response F s.result.certificate.openings w s.result.certificate.n 1)) :
    (SchemeVerifier.policy (Equations := Equations) (nw := nw) (nq := nq) (repetitions := 1) (s.result.code D hkn) Ligero.V1.scheme).protocol.acceptanceRate prover statement ≤
      (1 : ℚ) / 2 ^ s.result.certificate.targetBits := by
  exact Result.v1_interactive s.result s.parameters hv hf hdim D hkn hrows statement s.bound hfalse prover

theorem CertifiedResult.v1_uniform_envelope
    (s : CertifiedResult) (hv : s.result.variant = .v1)
    {F Equations : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Fintype Equations] [DecidableEq Equations] {w nw nq : ℕ}
    (hf : Fintype.card F = s.result.certificate.fieldSize)
    (hdim : s.result.certificate.openings + w = s.result.certificate.k)
    (D : ReedSolomon.Domain F s.result.certificate.openings w s.result.certificate.n)
    (hkn : s.result.certificate.openings + w ≤ s.result.certificate.n)
    (hrows : CoreRowsNonempty nw nq)
    (statement : ConstraintSystem F nw nq w Equations)
    (oracle : SchemeOracle F NoMask Ligero.V1.Mask nw nq s.result.certificate.n 1)
 :
    (∑ challenge : Ligero.V1.Challenge F nw nq 1 Equations,
      ScalarGapExtraction.profiledUniformEnvelope (oracle := oracle)
        (e := s.result.certificate.e) (g := s.result.certificate.g) (SchemeVerifier.policy (Equations := Equations) (nw := nw) (nq := nq) (repetitions := 1) (s.result.code D hkn) Ligero.V1.scheme) (fun candidate => candidate.decodedMessages) statement challenge) /
      Fintype.card (Ligero.V1.Challenge F nw nq 1 Equations) ≤ (1 : ℚ) / 2 ^ s.result.certificate.targetBits := by
  exact Result.v1_uniform_envelope s.result s.parameters hv hf hdim D hkn hrows statement oracle s.bound

theorem CertifiedResult.v2_extraction
    (s : CertifiedResult) (hv : s.result.variant = .v2)
    {F Equations : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Fintype Equations] [DecidableEq Equations] {w nw nq : ℕ}
    (hf : Fintype.card F = s.result.certificate.fieldSize)
    (hdim : s.result.certificate.openings + w = s.result.certificate.k)
    (D : ReedSolomon.Domain F s.result.certificate.openings w s.result.certificate.n)
    (hkn : s.result.certificate.openings + w ≤ s.result.certificate.n)
    (M : (s.result.code D hkn).MaskingBasis)
    (statement : ConstraintSystem F nw nq w Equations)
    (prover : IPCPProver (ConstraintSystem F nw nq w Equations) (SchemeOracle F Ligero.V2.Mask NoMask nw nq s.result.certificate.n 1) (Ligero.V2.Challenge F nw nq 1 Equations) (Response F s.result.certificate.openings w s.result.certificate.n 1)) :
    extractionFailureRate (SchemeVerifier.policy (Equations := Equations) (nw := nw) (nq := nq) (repetitions := 1) (s.result.code D hkn) (Ligero.V2.scheme (s.result.code D hkn) M)).protocol prover statement (Ligero.V2.scalarGapExtract (e := s.result.certificate.e) (g := s.result.certificate.g) (s.result.code D hkn) M (prover.commit statement) statement) ≤
      (1 : ℚ) / 2 ^ s.result.certificate.targetBits := by
  exact Result.v2_extraction s.result s.parameters hv hf hdim D hkn M statement s.bound prover

theorem CertifiedResult.v2_interactive
    (s : CertifiedResult) (hv : s.result.variant = .v2)
    {F Equations : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Fintype Equations] [DecidableEq Equations] {w nw nq : ℕ}
    (hf : Fintype.card F = s.result.certificate.fieldSize)
    (hdim : s.result.certificate.openings + w = s.result.certificate.k)
    (D : ReedSolomon.Domain F s.result.certificate.openings w s.result.certificate.n)
    (hkn : s.result.certificate.openings + w ≤ s.result.certificate.n)
    (M : (s.result.code D hkn).MaskingBasis)
    (statement : ConstraintSystem F nw nq w Equations)
    (hfalse : ¬statement.Language)
    (prover : IPCPProver (ConstraintSystem F nw nq w Equations) (SchemeOracle F Ligero.V2.Mask NoMask nw nq s.result.certificate.n 1) (Ligero.V2.Challenge F nw nq 1 Equations) (Response F s.result.certificate.openings w s.result.certificate.n 1)) :
    (SchemeVerifier.policy (Equations := Equations) (nw := nw) (nq := nq) (repetitions := 1) (s.result.code D hkn) (Ligero.V2.scheme (s.result.code D hkn) M)).protocol.acceptanceRate prover statement ≤
      (1 : ℚ) / 2 ^ s.result.certificate.targetBits := by
  exact Result.v2_interactive s.result s.parameters hv hf hdim D hkn M statement s.bound hfalse prover

theorem CertifiedResult.v2_uniform_envelope
    (s : CertifiedResult) (hv : s.result.variant = .v2)
    {F Equations : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Fintype Equations] [DecidableEq Equations] {w nw nq : ℕ}
    (hf : Fintype.card F = s.result.certificate.fieldSize)
    (hdim : s.result.certificate.openings + w = s.result.certificate.k)
    (D : ReedSolomon.Domain F s.result.certificate.openings w s.result.certificate.n)
    (hkn : s.result.certificate.openings + w ≤ s.result.certificate.n)
    (M : (s.result.code D hkn).MaskingBasis)
    (statement : ConstraintSystem F nw nq w Equations)
    (oracle : SchemeOracle F Ligero.V2.Mask NoMask nw nq s.result.certificate.n 1)
 :
    (∑ challenge : Ligero.V2.Challenge F nw nq 1 Equations,
      ScalarGapExtraction.profiledUniformEnvelope (oracle := oracle)
        (e := s.result.certificate.e) (g := s.result.certificate.g) (SchemeVerifier.policy (Equations := Equations) (nw := nw) (nq := nq) (repetitions := 1) (s.result.code D hkn) (Ligero.V2.scheme (s.result.code D hkn) M)) (fun candidate => candidate.decodedMessages) statement challenge) /
      Fintype.card (Ligero.V2.Challenge F nw nq 1 Equations) ≤ (1 : ℚ) / 2 ^ s.result.certificate.targetBits := by
  exact Result.v2_uniform_envelope s.result s.parameters hv hf hdim D hkn M statement oracle s.bound

theorem CertifiedResult.v3_extraction
    (s : CertifiedResult) (hv : s.result.variant = .v3)
    {F Equations : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Fintype Equations] [DecidableEq Equations] {w nw nq : ℕ}
    (hf : Fintype.card F = s.result.certificate.fieldSize)
    (hdim : s.result.certificate.openings + w = s.result.certificate.k)
    (D : ReedSolomon.Domain F s.result.certificate.openings w s.result.certificate.n)
    (hkn : s.result.certificate.openings + w ≤ s.result.certificate.n)
    (M : (s.result.code D hkn).MaskingBasis)
    (statement : ConstraintSystem F nw nq w Equations)
    (prover : IPCPProver (ConstraintSystem F nw nq w Equations) (SchemeOracle F LinearConstraintMask NoMask nw nq s.result.certificate.n 1) (DirectChallenge F Equations nw nq 1) (DirectResponse F s.result.certificate.openings w s.result.certificate.n 1)) :
    extractionFailureRate (DirectVerifier.policy (Equations := Equations) (nw := nw) (nq := nq) (repetitions := 1) (s.result.code D hkn) M (ConstraintLayout.identity (F := F) w)).protocol prover statement (Ligero.V3.scalarGapExtract (e := s.result.certificate.e) (g := s.result.certificate.g) (s.result.code D hkn) M (ConstraintLayout.identity (F := F) w) (prover.commit statement) statement) ≤
      (1 : ℚ) / 2 ^ s.result.certificate.targetBits := by
  exact Result.v3_extraction s.result s.parameters hv hf hdim D hkn M statement s.bound prover

theorem CertifiedResult.v3_interactive
    (s : CertifiedResult) (hv : s.result.variant = .v3)
    {F Equations : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Fintype Equations] [DecidableEq Equations] {w nw nq : ℕ}
    (hf : Fintype.card F = s.result.certificate.fieldSize)
    (hdim : s.result.certificate.openings + w = s.result.certificate.k)
    (D : ReedSolomon.Domain F s.result.certificate.openings w s.result.certificate.n)
    (hkn : s.result.certificate.openings + w ≤ s.result.certificate.n)
    (M : (s.result.code D hkn).MaskingBasis)
    (statement : ConstraintSystem F nw nq w Equations)
    (hfalse : ¬statement.Language)
    (prover : IPCPProver (ConstraintSystem F nw nq w Equations) (SchemeOracle F LinearConstraintMask NoMask nw nq s.result.certificate.n 1) (DirectChallenge F Equations nw nq 1) (DirectResponse F s.result.certificate.openings w s.result.certificate.n 1)) :
    (DirectVerifier.policy (Equations := Equations) (nw := nw) (nq := nq) (repetitions := 1) (s.result.code D hkn) M (ConstraintLayout.identity (F := F) w)).protocol.acceptanceRate prover statement ≤
      (1 : ℚ) / 2 ^ s.result.certificate.targetBits := by
  exact Result.v3_interactive s.result s.parameters hv hf hdim D hkn M statement s.bound hfalse prover

theorem CertifiedResult.v3_uniform_envelope
    (s : CertifiedResult) (hv : s.result.variant = .v3)
    {F Equations : Type*} [Field F] [Fintype F] [DecidableEq F]
    [Fintype Equations] [DecidableEq Equations] {w nw nq : ℕ}
    (hf : Fintype.card F = s.result.certificate.fieldSize)
    (hdim : s.result.certificate.openings + w = s.result.certificate.k)
    (D : ReedSolomon.Domain F s.result.certificate.openings w s.result.certificate.n)
    (hkn : s.result.certificate.openings + w ≤ s.result.certificate.n)
    (M : (s.result.code D hkn).MaskingBasis)
    (statement : ConstraintSystem F nw nq w Equations)
    (oracle : SchemeOracle F LinearConstraintMask NoMask nw nq s.result.certificate.n 1)
 :
    (∑ challenge : DirectChallenge F Equations nw nq 1,
      ScalarGapExtraction.profiledUniformEnvelope (oracle := oracle)
        (e := s.result.certificate.e) (g := s.result.certificate.g) (DirectVerifier.policy (Equations := Equations) (nw := nw) (nq := nq) (repetitions := 1) (s.result.code D hkn) M (ConstraintLayout.identity (F := F) w)) (fun candidate => candidate.directMessages (layout := ConstraintLayout.identity (F := F) w)) statement challenge) /
      Fintype.card (DirectChallenge F Equations nw nq 1) ≤ (1 : ℚ) / 2 ^ s.result.certificate.targetBits := by
  exact Result.v3_uniform_envelope s.result s.parameters hv hf hdim D hkn M statement oracle s.bound

end Ligero.Examples.Grid.LongfellowProfiledExtraction
