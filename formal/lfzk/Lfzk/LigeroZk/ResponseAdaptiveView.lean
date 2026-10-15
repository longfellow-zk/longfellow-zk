import LigeroFamily.Protocol.IPCP
import Lfzk.LigeroZk.Distribution
import Lfzk.LigeroZk.Witness

-- Ported verbatim from `proofs/ligero/LigeroFamily/ZeroKnowledge/ResponseAdaptiveView.lean` (only the import paths are rewritten);
-- `formal/ligero/` must not change, so the module lives under `Lfzk.LigeroZk`.
set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Response-adaptive finite verifier views

Generic response-adaptive-view and exact-distribution definitions used by the
concrete LigeroFamily zero-knowledge proof.  The verifier chooses one complete
batch query after seeing the response; this model does not make later query
coordinates depend on earlier openings.
-/

namespace LigeroFamily.ZeroKnowledge

open LigeroFamily

/-- A verifier whose single second-stage bounded batch query may depend on the
complete prover response. -/
structure ResponseAdaptiveVerifier
    (VerifierCoins Challenge Response Query : Type*) where
  challenge : VerifierCoins → Challenge
  query : VerifierCoins → Response → Query

structure ResponseAdaptiveVerifierView
    (VerifierCoins Challenge Response Query : Type*)
    (Opening : Query → Type*) where
  verifierCoins : VerifierCoins
  challenge : Challenge
  response : Response
  query : Query
  opening : Opening query

variable {Statement Oracle Challenge Response Query VerifierCoins : Type*}
variable {Opening : Query → Type*}

def responseAdaptiveVerifierView
    (protocol : PublicCoinIPCP Statement Oracle Challenge Response Query Opening)
    (prover : IPCPProver Statement Oracle Challenge Response)
    (statement : Statement)
    (verifier : ResponseAdaptiveVerifier VerifierCoins Challenge Response Query)
    (coins : VerifierCoins) :
    ResponseAdaptiveVerifierView VerifierCoins Challenge Response Query Opening :=
  let oracle := prover.commit statement
  let challenge := verifier.challenge coins
  let response := prover.respond statement oracle challenge
  let query := verifier.query coins response
  { verifierCoins := coins
    challenge
    response
    query
    opening := protocol.openOracle oracle query }

def randomizedResponseAdaptiveView
    {Witness ProverCoins : Type*}
    (protocol : PublicCoinIPCP Statement Oracle Challenge Response Query Opening)
    (honestProver : Statement → Witness → ProverCoins →
      IPCPProver Statement Oracle Challenge Response)
    (statement : Statement) (witness : Witness)
    (verifier : ResponseAdaptiveVerifier VerifierCoins Challenge Response Query)
    (randomness : ProverCoins × VerifierCoins) :
    ResponseAdaptiveVerifierView VerifierCoins Challenge Response Query Opening :=
  responseAdaptiveVerifierView protocol
    (honestProver statement witness randomness.1) statement verifier randomness.2

/-- Exact witness-independence against one finite response-adaptive verifier.  This is
an unbounded, information-theoretic definition: no computational cost model is
attached to the simulator. -/
def UnboundedPerfectResponseAdaptiveZeroKnowledgeAgainst
    {Witness ProverCoins SimulatorCoins : Type*}
    [Fintype ProverCoins] [Fintype VerifierCoins] [Fintype SimulatorCoins]
    [DecidableEq
      (ResponseAdaptiveVerifierView VerifierCoins Challenge Response Query Opening)]
    (protocol : PublicCoinIPCP Statement Oracle Challenge Response Query Opening)
    (relation : Statement → Witness → Prop)
    (honestProver : Statement → Witness → ProverCoins →
      IPCPProver Statement Oracle Challenge Response)
    (verifier : ResponseAdaptiveVerifier VerifierCoins Challenge Response Query)
    (simulator : Statement → SimulatorCoins →
      ResponseAdaptiveVerifierView VerifierCoins Challenge Response Query Opening) : Prop :=
  ∀ statement witness, relation statement witness →
    SameDistribution
      (randomizedResponseAdaptiveView protocol honestProver statement witness verifier)
      (simulator statement)

/-- Exact witness-independence against every finite response-adaptive verifier.  The
simulator may be noncomputable; this does not assert efficient cryptographic
simulation. -/
def UnboundedPerfectResponseAdaptiveZeroKnowledge
    {Witness ProverCoins SimulatorCoins : Type*}
    [Fintype ProverCoins] [Fintype VerifierCoins] [Fintype SimulatorCoins]
    [DecidableEq
      (ResponseAdaptiveVerifierView VerifierCoins Challenge Response Query Opening)]
    (protocol : PublicCoinIPCP Statement Oracle Challenge Response Query Opening)
    (relation : Statement → Witness → Prop)
    (honestProver : Statement → Witness → ProverCoins →
      IPCPProver Statement Oracle Challenge Response)
    (simulator : ResponseAdaptiveVerifier VerifierCoins Challenge Response Query →
      Statement → SimulatorCoins →
        ResponseAdaptiveVerifierView VerifierCoins Challenge Response Query Opening) : Prop :=
  ∀ verifier, UnboundedPerfectResponseAdaptiveZeroKnowledgeAgainst protocol relation
    honestProver verifier (simulator verifier)

def publicCoinResponseAdaptiveVerifier :
    ResponseAdaptiveVerifier (Challenge × Query) Challenge Response Query where
  challenge := Prod.fst
  query := fun coins _ ↦ coins.2

section AdaptiveTapeTranslation

variable {Tape View : Type*}

/-- Lift a fixed-query prover-tape translation to a joint prover/verifier tape,
choosing the query from the response produced by the source tape. -/
def responseAdaptiveTapeTranslate
    (verifier : ResponseAdaptiveVerifier VerifierCoins Challenge Response Query)
    (response : Tape → Challenge → Response)
    (translate : Query → Challenge → Tape → Tape)
    (randomness : Tape × VerifierCoins) : Tape × VerifierCoins :=
  let challenge := verifier.challenge randomness.2
  let proverResponse := response randomness.1 challenge
  let query := verifier.query randomness.2 proverResponse
  (translate query challenge randomness.1, randomness.2)

/-- Response preservation turns injectivity of every fixed-query translation
into injectivity of the response-adaptive joint-tape translation. -/
theorem responseAdaptiveTapeTranslate_injective
    (verifier : ResponseAdaptiveVerifier VerifierCoins Challenge Response Query)
    (responseFrom responseTo : Tape → Challenge → Response)
    (translate : Query → Challenge → Tape → Tape)
    (hresponse : ∀ query challenge tape,
      responseTo (translate query challenge tape) challenge =
        responseFrom tape challenge)
    (hinjective : ∀ query challenge, Function.Injective (translate query challenge)) :
    Function.Injective
      (responseAdaptiveTapeTranslate verifier responseFrom translate) := by
  rintro ⟨first, firstCoins⟩ ⟨second, secondCoins⟩ hequal
  have hcoins : firstCoins = secondCoins := congrArg Prod.snd hequal
  subst secondCoins
  have htapes := congrArg Prod.fst hequal
  let challenge := verifier.challenge firstCoins
  let firstResponse := responseFrom first challenge
  let secondResponse := responseFrom second challenge
  let firstQuery := verifier.query firstCoins firstResponse
  let secondQuery := verifier.query firstCoins secondResponse
  have htranslated :
      translate firstQuery challenge first =
        translate secondQuery challenge second := by
    simpa only [responseAdaptiveTapeTranslate, challenge, firstResponse,
      secondResponse, firstQuery, secondQuery] using htapes
  have hresponses : firstResponse = secondResponse := by
    dsimp only [firstResponse, secondResponse]
    rw [← hresponse firstQuery challenge first,
      ← hresponse secondQuery challenge second]
    exact congrArg (fun tape ↦ responseTo tape challenge) htranslated
  have hqueries : firstQuery = secondQuery := by
    dsimp only [firstQuery, secondQuery]
    rw [hresponses]
  have hfixed : translate firstQuery challenge first =
      translate firstQuery challenge second := by
    simpa only [hqueries] using htranslated
  exact Prod.ext (hinjective firstQuery challenge hfixed) rfl

/-- A response-adaptive tape translation is an equivalence whenever each
fixed-query translation is injective on the finite prover tape. -/
noncomputable def responseAdaptiveTapeTranslateEquiv
    [Fintype Tape] [Fintype VerifierCoins]
    (verifier : ResponseAdaptiveVerifier VerifierCoins Challenge Response Query)
    (responseFrom responseTo : Tape → Challenge → Response)
    (translate : Query → Challenge → Tape → Tape)
    (hresponse : ∀ query challenge tape,
      responseTo (translate query challenge tape) challenge =
        responseFrom tape challenge)
    (hinjective : ∀ query challenge, Function.Injective (translate query challenge)) :
    (Tape × VerifierCoins) ≃ (Tape × VerifierCoins) :=
  Equiv.ofBijective
    (responseAdaptiveTapeTranslate verifier responseFrom translate)
    (responseAdaptiveTapeTranslate_injective verifier responseFrom responseTo
      translate hresponse hinjective).bijective_of_finite

/-- Exact view preservation under an injective response-adaptive tape change
of variables implies equality of the two finite view distributions. -/
theorem sameDistribution_of_responseAdaptiveTapeTranslate
    [Fintype Tape] [Fintype VerifierCoins] [DecidableEq View]
    (verifier : ResponseAdaptiveVerifier VerifierCoins Challenge Response Query)
    (responseFrom responseTo : Tape → Challenge → Response)
    (translate : Query → Challenge → Tape → Tape)
    (hresponse : ∀ query challenge tape,
      responseTo (translate query challenge tape) challenge =
        responseFrom tape challenge)
    (hinjective : ∀ query challenge, Function.Injective (translate query challenge))
    (fromView toView : Tape × VerifierCoins → View)
    (hview : ∀ randomness,
      fromView randomness = toView
        (responseAdaptiveTapeTranslate verifier responseFrom translate randomness)) :
    SameDistribution fromView toView := by
  apply sameDistribution_of_equiv
    (responseAdaptiveTapeTranslateEquiv verifier responseFrom responseTo translate
      hresponse hinjective)
  exact hview

end AdaptiveTapeTranslation

end LigeroFamily.ZeroKnowledge
