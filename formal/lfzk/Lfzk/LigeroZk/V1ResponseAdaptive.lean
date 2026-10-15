import Lfzk.LigeroZk.V1TapeTranslation
import Lfzk.LigeroZk.ResponseAdaptiveView

-- Ported verbatim from `proofs/ligero/Ligero/V1/ZeroKnowledge/ResponseAdaptive.lean` (only the import paths are rewritten);
-- `formal/ligero/` must not change, so the module lives under `Lfzk.LigeroZk`.
set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Perfect response-adaptive zero knowledge for V1

The verifier may choose queried columns after seeing the complete response.
The V1 tape equivalence preserves that response and the resulting opening.
Unlike V2, no masking-rate premise is required: the direct response-mask
spaces contain the complete canonical-response differences.
-/

namespace Ligero.V1.ZeroKnowledge

open LigeroFamily.ZeroKnowledge

open LigeroFamily MultiplicativeCode

variable {F Equations VerifierCoins : Type*}
variable [Field F] [Fintype F] [DecidableEq F]
variable [Fintype Equations] [DecidableEq Equations]
variable {r w n nw nq repetitions : ℕ}
variable {C : MultiplicativeCode F r w n}
variable {statement : ConstraintSystem F nw nq w Equations}

/-- Response-adaptive V1 view from one satisfying witness and joint uniform
prover/verifier tape. -/
noncomputable def v1SatisfyingResponseAdaptiveView
    (messages : CoreMessages F nw nq w)
    (hsatisfies : statement.Satisfies messages)
    (verifier : ResponseAdaptiveVerifier VerifierCoins
      (Challenge F nw nq repetitions Equations) (Response F r w n repetitions)
      (QuerySet n r))
    (randomness : V1ProverRandomness C nw nq repetitions × VerifierCoins) :
    ResponseAdaptiveVerifierView VerifierCoins
      (Challenge F nw nq repetitions Equations) (Response F r w n repetitions)
      (QuerySet n r) (Opening F nw nq repetitions n r) :=
  responseAdaptiveVerifierView (SchemeVerifier.protocol C scheme)
    (randomness.1.prover messages hsatisfies) statement verifier randomness.2

/-- Query-dependent change of variables on the joint V1 tape. -/
noncomputable def v1ResponseAdaptiveTranslate
    (fromMessages toMessages : CoreMessages F nw nq w)
    (fromSatisfies : statement.Satisfies fromMessages)
    (toSatisfies : statement.Satisfies toMessages)
    (verifier : ResponseAdaptiveVerifier VerifierCoins
      (Challenge F nw nq repetitions Equations) (Response F r w n repetitions)
      (QuerySet n r))
    (randomness : V1ProverRandomness C nw nq repetitions × VerifierCoins) :
    V1ProverRandomness C nw nq repetitions × VerifierCoins :=
  responseAdaptiveTapeTranslate verifier
    (fun seed challenge ↦
      (seed.encoding fromMessages fromSatisfies).response challenge)
    (fun query challenge seed ↦
      V1ProverRandomness.translateRandomness fromMessages toMessages fromSatisfies
        toSatisfies query challenge seed)
    randomness

omit [Fintype F] [DecidableEq F] [DecidableEq Equations] in
theorem v1ResponseAdaptiveTranslate_response
    (fromMessages toMessages : CoreMessages F nw nq w)
    (fromSatisfies : statement.Satisfies fromMessages)
    (toSatisfies : statement.Satisfies toMessages)
    (verifier : ResponseAdaptiveVerifier VerifierCoins
      (Challenge F nw nq repetitions Equations) (Response F r w n repetitions)
      (QuerySet n r))
    (randomness : V1ProverRandomness C nw nq repetitions × VerifierCoins) :
    let challenge := verifier.challenge randomness.2
    let response :=
      (randomness.1.encoding fromMessages fromSatisfies).response challenge
    ((v1ResponseAdaptiveTranslate (C := C) fromMessages toMessages fromSatisfies
        toSatisfies verifier randomness).1.encoding toMessages toSatisfies).response
      challenge = response := by
  dsimp only
  exact V1ProverRandomness.translateRandomness_response fromMessages toMessages
    fromSatisfies toSatisfies _ _ randomness.1

omit [Fintype F] [DecidableEq F] [DecidableEq Equations] in
theorem v1ResponseAdaptiveTranslate_view
    (fromMessages toMessages : CoreMessages F nw nq w)
    (fromSatisfies : statement.Satisfies fromMessages)
    (toSatisfies : statement.Satisfies toMessages)
    (verifier : ResponseAdaptiveVerifier VerifierCoins
      (Challenge F nw nq repetitions Equations) (Response F r w n repetitions)
      (QuerySet n r))
    (randomness : V1ProverRandomness C nw nq repetitions × VerifierCoins) :
    v1SatisfyingResponseAdaptiveView (C := C) fromMessages fromSatisfies
        verifier randomness =
      v1SatisfyingResponseAdaptiveView (C := C) toMessages toSatisfies verifier
        (v1ResponseAdaptiveTranslate (C := C) fromMessages toMessages
          fromSatisfies toSatisfies verifier randomness) := by
  let challenge := verifier.challenge randomness.2
  let response :=
    (randomness.1.encoding fromMessages fromSatisfies).response challenge
  let query := verifier.query randomness.2 response
  have hresponse := V1ProverRandomness.translateRandomness_response
    fromMessages toMessages fromSatisfies toSatisfies query challenge randomness.1
  have hopening := V1ProverRandomness.translateRandomness_opening
    fromMessages toMessages fromSatisfies toSatisfies query challenge randomness.1
  unfold v1SatisfyingResponseAdaptiveView responseAdaptiveVerifierView
  dsimp only [V1ProverRandomness.prover, V1HonestEncoding.prover,
    v1ResponseAdaptiveTranslate, responseAdaptiveTapeTranslate,
    challenge, response, query]
  rw [hresponse]
  simp only [SchemeVerifier.protocol]
  rw [hopening]

omit [Fintype F] [DecidableEq F] [DecidableEq Equations] in
theorem v1ResponseAdaptiveTranslate_injective
    (fromMessages toMessages : CoreMessages F nw nq w)
    (fromSatisfies : statement.Satisfies fromMessages)
    (toSatisfies : statement.Satisfies toMessages)
    (verifier : ResponseAdaptiveVerifier VerifierCoins
      (Challenge F nw nq repetitions Equations) (Response F r w n repetitions)
      (QuerySet n r)) :
    Function.Injective
      (v1ResponseAdaptiveTranslate (C := C) fromMessages toMessages
        fromSatisfies toSatisfies verifier) := by
  let responseFrom : V1ProverRandomness C nw nq repetitions →
      Challenge F nw nq repetitions Equations → Response F r w n repetitions :=
    fun seed challenge ↦
      (seed.encoding fromMessages fromSatisfies).response challenge
  let responseTo : V1ProverRandomness C nw nq repetitions →
      Challenge F nw nq repetitions Equations → Response F r w n repetitions :=
    fun seed challenge ↦
      (seed.encoding toMessages toSatisfies).response challenge
  let translate : QuerySet n r → Challenge F nw nq repetitions Equations →
      V1ProverRandomness C nw nq repetitions →
        V1ProverRandomness C nw nq repetitions :=
    fun query challenge seed ↦
      V1ProverRandomness.translateRandomness fromMessages toMessages fromSatisfies
        toSatisfies query challenge seed
  have hresponse : ∀ query challenge seed,
      responseTo (translate query challenge seed) challenge =
        responseFrom seed challenge := by
    intro query challenge seed
    exact V1ProverRandomness.translateRandomness_response fromMessages toMessages
      fromSatisfies toSatisfies query challenge seed
  have hinjective : ∀ query challenge, Function.Injective
      (translate query challenge) := by
    intro query challenge
    exact V1ProverRandomness.translateRandomness_injective fromMessages toMessages
      fromSatisfies toSatisfies query challenge
  change Function.Injective
    (responseAdaptiveTapeTranslate verifier responseFrom translate)
  exact responseAdaptiveTapeTranslate_injective verifier responseFrom responseTo
    translate hresponse hinjective

/-- Response-adaptive V1 change of variables as an equivalence of finite
uniform joint tapes. -/
noncomputable def v1ResponseAdaptiveTranslateEquiv
    [Fintype VerifierCoins]
    (fromMessages toMessages : CoreMessages F nw nq w)
    (fromSatisfies : statement.Satisfies fromMessages)
    (toSatisfies : statement.Satisfies toMessages)
    (verifier : ResponseAdaptiveVerifier VerifierCoins
      (Challenge F nw nq repetitions Equations) (Response F r w n repetitions)
      (QuerySet n r)) :
    (V1ProverRandomness C nw nq repetitions × VerifierCoins) ≃
      (V1ProverRandomness C nw nq repetitions × VerifierCoins) :=
  Equiv.ofBijective
    (v1ResponseAdaptiveTranslate (C := C) fromMessages toMessages fromSatisfies
      toSatisfies verifier)
    (v1ResponseAdaptiveTranslate_injective fromMessages toMessages fromSatisfies
      toSatisfies verifier).bijective_of_finite

omit [DecidableEq F] [DecidableEq Equations] in
/-- The exact V1 response-adaptive view distribution is independent of the
satisfying witness. -/
theorem v1SatisfyingResponseAdaptiveView_sameDistribution
    [Fintype VerifierCoins]
    [DecidableEq
      (ResponseAdaptiveVerifierView VerifierCoins
        (Challenge F nw nq repetitions Equations) (Response F r w n repetitions)
        (QuerySet n r) (Opening F nw nq repetitions n r))]
    (fromMessages toMessages : CoreMessages F nw nq w)
    (fromSatisfies : statement.Satisfies fromMessages)
    (toSatisfies : statement.Satisfies toMessages)
    (verifier : ResponseAdaptiveVerifier VerifierCoins
      (Challenge F nw nq repetitions Equations) (Response F r w n repetitions)
      (QuerySet n r)) :
    SameDistribution
      (v1SatisfyingResponseAdaptiveView (C := C) fromMessages fromSatisfies
        verifier)
      (v1SatisfyingResponseAdaptiveView (C := C) toMessages toSatisfies
        verifier) := by
  apply sameDistribution_of_equiv
    (v1ResponseAdaptiveTranslateEquiv (C := C) fromMessages toMessages
      fromSatisfies toSatisfies verifier)
  intro randomness
  exact v1ResponseAdaptiveTranslate_view fromMessages toMessages fromSatisfies
    toSatisfies verifier randomness

/-- A harmless total V1 prover outside the language relation. -/
noncomputable def v1NullProver
    (_statement : ConstraintSystem F nw nq w Equations) :
    IPCPProver (ConstraintSystem F nw nq w Equations)
      (Oracle F nw nq n repetitions)
      (Challenge F nw nq repetitions Equations)
      (Response F r w n repetitions) where
  commit _ := {
    core := fun _ _ _ ↦ 0
    checkedMask := fun _ impossible ↦ NoMask.elim impossible
    directMask := fun _ _ _ ↦ 0
    proximityBlind := fun _ _ ↦ 0 }
  respond _ _ _ := ⟨fun _ _ ↦ 0, fun _ _ ↦ 0, fun _ _ ↦ 0⟩

/-- Total V1 honest-prover family. -/
noncomputable def v1HonestProver
    (C : MultiplicativeCode F r w n)
    (statement : ConstraintSystem F nw nq w Equations)
    (messages : CoreMessages F nw nq w)
    (seed : V1ProverRandomness C nw nq repetitions) := by
  classical
  exact if hsatisfies : statement.Satisfies messages then
    seed.prover messages hsatisfies
  else v1NullProver statement

/-- Unbounded V1 simulator using the canonical satisfying witness selected
from the public statement. -/
noncomputable def v1ResponseAdaptiveSimulator
    (verifier : ResponseAdaptiveVerifier VerifierCoins
      (Challenge F nw nq repetitions Equations) (Response F r w n repetitions)
      (QuerySet n r))
    (statement : ConstraintSystem F nw nq w Equations)
    (randomness : V1ProverRandomness C nw nq repetitions × VerifierCoins) :=
  randomizedResponseAdaptiveView (SchemeVerifier.protocol C scheme)
    (v1HonestProver C) statement (referenceMessages statement)
    verifier randomness

noncomputable local instance v1ResponseAdaptiveViewDecidableEq :
    DecidableEq
      (ResponseAdaptiveVerifierView VerifierCoins
        (Challenge F nw nq repetitions Equations) (Response F r w n repetitions)
        (QuerySet n r) (Opening F nw nq repetitions n r)) :=
  Classical.decEq _

omit [DecidableEq F] [DecidableEq Equations] in
/-- End-to-end unbounded perfect response-adaptive zero knowledge of V1. -/
theorem v1_unbounded_perfect_response_adaptive_zero_knowledge
    [Fintype VerifierCoins] :
    UnboundedPerfectResponseAdaptiveZeroKnowledge
      (SchemeVerifier.protocol (nw := nw) (nq := nq)
        (repetitions := repetitions) (Equations := Equations) C scheme)
      (fun statement messages ↦ statement.Satisfies messages)
      (v1HonestProver (nw := nw) (nq := nq) (repetitions := repetitions)
        (Equations := Equations) C)
      (v1ResponseAdaptiveSimulator (C := C)
        (VerifierCoins := VerifierCoins)) := by
  intro verifier publicStatement messages hsatisfies
  have hreference : publicStatement.Satisfies
      (referenceMessages publicStatement) :=
    referenceMessages_satisfies publicStatement ⟨messages, hsatisfies⟩
  change SameDistribution
    (randomizedResponseAdaptiveView
      (SchemeVerifier.protocol (nw := nw) (nq := nq)
        (repetitions := repetitions) (Equations := Equations) C scheme)
      (v1HonestProver (nw := nw) (nq := nq) (repetitions := repetitions)
        (Equations := Equations) C) publicStatement messages verifier)
    (randomizedResponseAdaptiveView
      (SchemeVerifier.protocol (nw := nw) (nq := nq)
        (repetitions := repetitions) (Equations := Equations) C scheme)
      (v1HonestProver (nw := nw) (nq := nq) (repetitions := repetitions)
        (Equations := Equations) C) publicStatement
        (referenceMessages publicStatement) verifier)
  have hdistribution := v1SatisfyingResponseAdaptiveView_sameDistribution
    (C := C) messages (referenceMessages publicStatement)
    hsatisfies hreference verifier
  convert hdistribution using 1
  · funext randomness
    unfold randomizedResponseAdaptiveView v1SatisfyingResponseAdaptiveView
    simp [v1HonestProver, hsatisfies]
  · funext randomness
    unfold randomizedResponseAdaptiveView v1SatisfyingResponseAdaptiveView
    simp [v1HonestProver, hreference]

end Ligero.V1.ZeroKnowledge
