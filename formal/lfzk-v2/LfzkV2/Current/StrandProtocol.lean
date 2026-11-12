import LfzkV2.Current.StrandDomains
import LfzkV2.Current.Soundness.StrandStoppedCosts
import Survival.Saturation

/-! Two composition methods on the same derived runtime stopped cost and
failure cover: unrestricted leading linear accounting, then optional W
saturation. Residual averaging and raw SHA realization follow these core
bounds; concrete profile arithmetic lives in the mdoc endpoint layer. -/
noncomputable section
namespace LfzkV2.Current.StrandProtocol
open Application ApplicationSetup CanonicalPrefix QueryRuntime RecursivePolygero
open Finset Bcs.FiniteProbability Merkle Merkle.Indexed Merkle.RandomOracle TranscriptV2
open scoped Classical
attribute [local instance] answerFintype valuesFintype idealLeafInhabited runtimeLeafInhabited

variable (c : CertifiedProfile)
variable {g : Geometry} {fields : Fields} {Advice B : Type}
variable [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable [∀ side, Fintype (fields side)] [Fintype Advice]
variable {shared maskBits adviceBits blocks : ℕ}
local notation "N" => ZMod Adapter.Mdoc.primeOrder
variable (binary : BinaryPublic B shared maskBits adviceBits) (prime : PrimePublic N shared)
variable (P : FieldBackend B c.k c.s c.n c.t) (R : FieldBackend N c.k c.s c.n c.t)
variable (countBinary countPrime binaryCapacity primeCapacity : ℕ)
variable (repr : ProofBodyCodec.Representations fields Advice)
variable (shape : WireBlocks.Shape g fields) (setup : FingerprintPrefix.Setup)
local notation "Answer" => IdealRuntime.Answer binary prime P R countBinary countPrime binaryCapacity primeCapacity
local notation "Point" => QueryRuntime.Runtime.Point repr shape setup binary.nPublic
local notation "Value" => QueryRuntime.Runtime.Value repr shape setup binary.nPublic
local notation "Output" => CanonicalRuntime.Output (Advice := Advice) binary shape
variable (binaryPlan : FrontendSchedule.Plan B binary.template)
variable (primePlan : FrontendSchedule.Plan N prime.circuit)
variable (binaryGeometry : binaryPlan.frontend = g.binary) (primeGeometry : primePlan.frontend = g.prime)
variable (binaryFits : binaryPlan.capacity ≤ binaryCapacity) (primeFits : primePlan.capacity ≤ primeCapacity)
variable (degreeFits : binary.degree ≤ binaryCapacity) (rowsFit : prime.circuit.layers+1 ≤ primeCapacity)
variable (cfg : RuntimeVerifier.Public (g := g) binary prime P R (fields := fields) (Advice := Advice)
  (Base := CanonicalRequest.Base repr shape setup binary.nPublic) (Key := FingerprintPrefix.Key binary.nPublic)
  (C := IdealRuntime.Answer binary prime P R countBinary countPrime binaryCapacity primeCapacity) (Salt := Fin c.n × MerkleNonce))
local notation "I" => IdealRuntime.challengePublic binary prime P R countBinary countPrime binaryCapacity primeCapacity cfg
local notation "W" => CanonicalRuntime.wirePublic binary prime P R repr shape setup (I)
variable (binaryCount : shape.binaryPublic = binary.nPublic)
variable (metadata : CanonicalRequest.Metadata (Advice := Advice)
  (C := IdealRuntime.Answer binary prime P R countBinary countPrime binaryCapacity primeCapacity) shape binary.nPublic)
local notation "Earlier" => CanonicalRuntime.earlier binary prime P R repr shape setup (I) binaryCount metadata
local notation "M" => RuntimeAdaptiveVerifier.chain binary prime P R (W) (Earlier)
local notation "bodyCodec" => ProofBodyCodec.codec repr g
variable (bodyFits : ProofBodyBounds.bodyBound repr g ≤ CanonicalPrefix.maxLength)
variable (fits : g.roles.length < 2^64)
variable (sample : (point : QueryRuntime.Runtime.Point repr shape setup binary.nPublic) →
  Tree Strand.Word Digest (Option (values c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup point)) blocks)
variable (fiber : QueryRuntime.Runtime.Point repr shape setup binary.nPublic → ℕ)
variable (uniform : ∀ point value,
  (Finset.univ.filter fun stream => ((sample point).run stream).1 = some value).card = fiber point)
local notation "physical" => sampler c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
  binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit cfg sample
variable (primeCount : shape.primePublic = prime.nPublic)
variable [Inhabited (Fin c.n × MerkleNonce)]
variable [leafDefault : Inhabited (Joint.Pair.family (P.indexed countBinary).participant (R.indexed countPrime).participant).Leaf]
local notation "First" => FieldBackend.participant (FieldBackend.indexed P countBinary)
local notation "Second" => FieldBackend.participant (FieldBackend.indexed R countPrime)
variable (columnsFit : c.n ≤ 2^64)
local notation "codec" => MerkleWireCodec.codec (First) (Second) repr
  cfg.binaryField cfg.primeField setup.jointContext columnsFit
variable {fuel : ℕ} (program : Tree Bytes Digest (CanonicalRuntime.Output (Advice := Advice) binary shape) fuel)
local notation "draw" => IdealRuntime.draw binary prime P R countBinary countPrime binaryCapacity primeCapacity cfg
local notation "names" => StrandRealization.queryCodec binary prime P R repr shape setup (I) binaryCount metadata
  fits physical codec id program
local notation "Other" => StrandRealization.other binary prime P R repr shape setup (I) binaryCount metadata fits
  physical codec id program
local notation "Node" => StrandWindow.Node (Other)
local notation "Name" => StrandSearch.Name Node Value
local notation "Tagged" => Point ⊕ Name
local notation "Row" => Strand.Word → Digest
local notation "Residual" => Fin (Fintype.card Row)
local notation "split" => coordinateSplit c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
  binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit cfg binaryCount metadata fits sample
  fiber uniform columnsFit program
local notation "namedH" => namedOracle c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
  binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit cfg binaryCount metadata fits sample
  fiber uniform columnsFit program
local notation "hashPublic" => CanonicalRequest.hashPublic binary.nPublic
local notation "primePublic" => CanonicalRuntime.decodePrimePublic binary prime P R repr shape setup (I) primeCount
local notation "actualVerify" => StrandVerifier.verify binary prime P R (W) (Earlier) bodyCodec physical
  hashPublic primePublic draw codec
local notation "search" => searchTree c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
  binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit cfg binaryCount metadata fits sample columnsFit program
local notation "analysis" => analysisTree c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
  binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit cfg binaryCount metadata fits sample
  fiber uniform columnsFit program
variable (layout : StatementCompiler.Addresses P R binary.cells prime.remaining prime.pads)
variable (bitsFit : shared+maskBits ≤ Adapter.Mdoc.quotientBound)
local notation "charges" => localProof c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
  binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit cfg binaryCount metadata fits sample
  fiber uniform primeCount columnsFit program layout bitsFit
local notation "View" => StrandExecution.View Output ((Output × Chain.State (M)) × Digest)
  (FingerprintPrefix.Key binary.nPublic)
local notation "decision" => StrandExecution.decision binary prime P R (W) (Earlier) bodyCodec physical codec id
  hashPublic primePublic draw
local notation "observe" => StrandRealization.observe binary prime P R repr shape setup (I) binaryCount metadata
  fits physical codec id program
local notation "sourceView" => fun K => observe (Prod.fst (Tree.run (search) K)) K
local notation "viewOf" => fun residual H => sourceView (namedH residual H)
local notation "failsView" => extractionFails c binary prime P R countBinary countPrime binaryCapacity primeCapacity
  repr shape setup binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit
  cfg binaryCount metadata sample primeCount columnsFit
variable (layoutCorrect : StatementCompiler.addresses P R binary.cells prime.remaining prime.pads = some layout)
local notation "marked" => (LfzkV2.Current.Soundness.RuntimeRoles.marked (Aux := Name) g.batchingIndex : Tagged → Bool)
local notation "hashBad" => StrandRecovery.hashException binary prime P R repr shape setup (I) binaryCount metadata
  columnsFit physical primeCount draw
local notation "costOf" => stoppedCost c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
  binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit cfg
  binaryCount metadata fits sample fiber uniform primeCount columnsFit program layout bitsFit
local notation "valueFinite" => Fintype.ofInjective
  (QueryRuntime.Runtime.toPoint repr shape setup binary.nPublic)
  (QueryRuntime.Runtime.toPoint_injective repr shape setup binary.nPublic fits)
local notation "ordinaryRate" => (2/((Adapter.Mdoc.binaryOrder-1:ℕ):ℚ))
variable {Q : ℕ} (queries : ∀ SHA : Bytes → Digest, (seen program SHA).card ≤ Q)
local notation "acceptedFailure" => fun (view : View) => decision view = true ∧ failsView view

/-- Uniform sampler coordinates preserve the law of events on the original
grouped oracle, including its query-counting events. -/
theorem named_event_average (event : (Name → Digest × Row) → Prop) :
    letI : Fintype Value := valueFinite
    letI : Fintype Name := inferInstance
    density event = (∑ residual : Tagged → Residual, density (fun H : Tagged → Digest × Answer =>
      event (namedH residual H))) / Fintype.card (Tagged → Residual) := by
  letI : Nonempty Answer := ⟨cfg.fallback⟩
  letI : Fintype Value := valueFinite
  letI : Fintype Name := inferInstance
  exact StrandComposition.event_average (names).tag (names).tag_injective split event
include bodyFits bitsFit layoutCorrect queries uniform in
/-- Leading shared-query bound on the same runtime cover and retained cost.
It does not assume `ordinaryRate * Q ≤ 1` or use the saturated potential. -/
theorem conditioned_linear_failure_le (residual : Tagged → Residual) (opaqueRate : ℚ)
    (nonnegative : 0 ≤ opaqueRate) (atMostRate : opaqueRate ≤ ordinaryRate)
    (parentBound : ParameterBounds.parentBudget c.n c.k c.s c.t c.activeCutoff c.activeList ≤ opaqueRate)
    (guessFits : (2*Q : ℚ)/2^256 ≤ opaqueRate) :
    letI : Fintype Value := valueFinite
    letI : Fintype Name := inferInstance
    density (fun H : Tagged → Digest × Answer => acceptedFailure (viewOf residual H)) ≤
      ordinaryRate*Q +
        density (fun H : Tagged → Digest × Answer => hashBad (viewOf residual H)) := by
  letI : Fintype Value := valueFinite
  letI : Fintype Name := inferInstance
  letI : Nonempty Answer := ⟨cfg.fallback⟩
  let cost := costOf residual
  have localBudget := single_budget_le c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
    binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit cfg
    binaryCount metadata fits sample fiber uniform primeCount columnsFit program layout bitsFit residual
  apply Survival.ChargeMonitor.linear_failure_le_support (charges residual) marked (default,cfg.fallback) (analysis residual)
    ordinaryRate opaqueRate (by norm_num [Adapter.Mdoc.binaryOrder]) atMostRate (fun point _ => localBudget point)
    (analysis_fresh c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
      binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit cfg
      binaryCount metadata fits sample fiber uniform columnsFit program residual)
    (analysis_queries c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
      binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit cfg
      binaryCount metadata fits sample fiber uniform columnsFit program queries residual)
    (fun H => acceptedFailure (viewOf residual H)) (fun H => hashBad (viewOf residual H)) cost
  · exact stoppedCost_nonneg c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
      binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit cfg
      binaryCount metadata fits sample fiber uniform primeCount columnsFit program layout bitsFit residual
  · exact stopped_failure_cover c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
      binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit cfg
      binaryCount metadata bodyFits fits sample fiber uniform primeCount columnsFit program layout bitsFit layoutCorrect residual
  · exact conditioned_cost_mean_le c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
      binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit cfg
      binaryCount metadata fits sample fiber uniform primeCount columnsFit program layout bitsFit queries residual
      opaqueRate nonnegative parentBound guessFits

include bodyFits bitsFit layoutCorrect queries uniform in
/-- Complete runtime failure coverage at a fixed sampler residual. The hash
exception stays symbolic here: its raw bound is applied only after averaging. -/
theorem conditioned_saturated_failure_le (residual : Tagged → Residual) (opaqueFraction : ℚ)
    (nonnegative : 0 ≤ opaqueFraction) (atMostOne : opaqueFraction ≤ 1) (budget : ordinaryRate*Q ≤ 1)
    (parentBound : ParameterBounds.parentBudget c.n c.k c.s c.t c.activeCutoff c.activeList ≤ opaqueFraction*ordinaryRate)
    (guessFits : (2*Q : ℚ)/2^256 ≤ opaqueFraction*ordinaryRate) :
    letI : Fintype Value := valueFinite
    letI : Fintype Name := inferInstance
    density (fun H : Tagged → Digest × Answer => acceptedFailure (viewOf residual H)) ≤
      Survival.Hybrid.envelope ordinaryRate opaqueFraction Q +
        density (fun H : Tagged → Digest × Answer => hashBad (viewOf residual H)) := by
  letI : Fintype Value := valueFinite
  letI : Fintype Name := inferInstance
  letI : Nonempty Answer := ⟨cfg.fallback⟩
  let cost := costOf residual
  have localBudget := single_budget_le c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
    binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit cfg
    binaryCount metadata fits sample fiber uniform primeCount columnsFit program layout bitsFit residual
  apply Survival.ChargeMonitor.failure_le_support (charges residual) marked (default,cfg.fallback) (analysis residual)
    ordinaryRate opaqueFraction (by norm_num [Adapter.Mdoc.binaryOrder]) (by norm_num [Adapter.Mdoc.binaryOrder])
    nonnegative atMostOne (fun point _ => localBudget point) budget
    (analysis_fresh c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
      binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit cfg
      binaryCount metadata fits sample fiber uniform columnsFit program residual)
    (analysis_queries c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
      binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit cfg
      binaryCount metadata fits sample fiber uniform columnsFit program queries residual)
    (fun H => acceptedFailure (viewOf residual H)) (fun H => hashBad (viewOf residual H)) cost
  · exact stoppedCost_nonneg c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
      binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit cfg
      binaryCount metadata fits sample fiber uniform primeCount columnsFit program layout bitsFit residual
  · exact stopped_failure_cover c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
      binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit cfg
      binaryCount metadata bodyFits fits sample fiber uniform primeCount columnsFit program layout bitsFit layoutCorrect residual
  · exact conditioned_cost_mean_le c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
      binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit cfg
      binaryCount metadata fits sample fiber uniform primeCount columnsFit program layout bitsFit queries residual
      (opaqueFraction*ordinaryRate) (mul_nonneg nonnegative (by norm_num [Adapter.Mdoc.binaryOrder])) parentBound guessFits

include bodyFits bitsFit layoutCorrect queries uniform in
/-- Average residuals before estimating the raw hash exception. Fixing a
residual is permitted for algebraic monitoring, but not for fresh seal bounds. -/
theorem named_linear_failure_le (opaqueRate : ℚ)
    (nonnegative : 0 ≤ opaqueRate) (atMostRate : opaqueRate ≤ ordinaryRate)
    (parentBound : ParameterBounds.parentBudget c.n c.k c.s c.t c.activeCutoff c.activeList ≤ opaqueRate)
    (guessFits : (2*Q : ℚ)/2^256 ≤ opaqueRate) :
    letI : Fintype Value := valueFinite
    letI : Fintype Name := inferInstance
    density (fun K : Name → Digest × Row => acceptedFailure (sourceView K)) ≤
      ordinaryRate*Q +
        density (fun K : Name → Digest × Row => hashBad (sourceView K)) := by
  letI : Fintype Value := valueFinite
  letI : Fintype Name := inferInstance
  letI : Nonempty Answer := ⟨cfg.fallback⟩
  letI : Nonempty (Tagged → Residual) := ⟨fun _ => ⟨0,Fintype.card_pos⟩⟩
  have each residual := conditioned_linear_failure_le c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
    binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit cfg
    binaryCount metadata bodyFits fits sample fiber uniform primeCount columnsFit program layout bitsFit layoutCorrect queries
    residual opaqueRate nonnegative atMostRate parentBound guessFits
  have averaged := ProtocolProbability.mean_add_mul_le
    (fun residual => density (fun H : Tagged → Digest × Answer => acceptedFailure (viewOf residual H)))
    (fun residual => density (fun H : Tagged → Digest × Answer => hashBad (viewOf residual H)))
    (-1) (ordinaryRate*Q) (fun residual => by have := each residual; linarith)
  have failureLaw := named_event_average c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
    binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit cfg
    binaryCount metadata fits sample fiber uniform columnsFit program (fun K => acceptedFailure (sourceView K))
  have hashLaw := named_event_average c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
    binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit cfg
    binaryCount metadata fits sample fiber uniform columnsFit program (fun K => hashBad (sourceView K))
  rw [← failureLaw, ← hashLaw] at averaged
  linarith
include bodyFits bitsFit layoutCorrect queries uniform in
/-- Average residuals before estimating the raw hash exception. Fixing a
residual is permitted for algebraic monitoring, but not for fresh seal bounds. -/
theorem named_saturated_failure_le (opaqueFraction : ℚ)
    (nonnegative : 0 ≤ opaqueFraction) (atMostOne : opaqueFraction ≤ 1) (budget : ordinaryRate*Q ≤ 1)
    (parentBound : ParameterBounds.parentBudget c.n c.k c.s c.t c.activeCutoff c.activeList ≤ opaqueFraction*ordinaryRate)
    (guessFits : (2*Q : ℚ)/2^256 ≤ opaqueFraction*ordinaryRate) :
    letI : Fintype Value := valueFinite
    letI : Fintype Name := inferInstance
    density (fun K : Name → Digest × Row => acceptedFailure (sourceView K)) ≤
      Survival.Hybrid.envelope ordinaryRate opaqueFraction Q +
        density (fun K : Name → Digest × Row => hashBad (sourceView K)) := by
  letI : Fintype Value := valueFinite
  letI : Fintype Name := inferInstance
  letI : Nonempty Answer := ⟨cfg.fallback⟩
  letI : Nonempty (Tagged → Residual) := ⟨fun _ => ⟨0,Fintype.card_pos⟩⟩
  have each residual := conditioned_saturated_failure_le c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
    binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit cfg
    binaryCount metadata bodyFits fits sample fiber uniform primeCount columnsFit program layout bitsFit layoutCorrect queries
    residual opaqueFraction nonnegative atMostOne budget parentBound guessFits
  have averaged := ProtocolProbability.mean_add_mul_le
    (fun residual => density (fun H : Tagged → Digest × Answer => acceptedFailure (viewOf residual H)))
    (fun residual => density (fun H : Tagged → Digest × Answer => hashBad (viewOf residual H)))
    (-1) (Survival.Hybrid.envelope ordinaryRate opaqueFraction Q) (fun residual => by have := each residual; linarith)
  have failureLaw := named_event_average c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
    binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit cfg
    binaryCount metadata fits sample fiber uniform columnsFit program (fun K => acceptedFailure (sourceView K))
  have hashLaw := named_event_average c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
    binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit cfg
    binaryCount metadata fits sample fiber uniform columnsFit program (fun K => hashBad (sourceView K))
  rw [← failureLaw, ← hashLaw] at averaged
  linarith
variable (fallbackPath : StrandMerkleMissingQueries.SelectedPath (n := c.n) (Salt := Fin c.n × MerkleNonce)
  («M» := (Joint.Pair.family (FieldBackend.indexed P countBinary).participant
    (FieldBackend.indexed R countPrime).participant).Leaf) (D := Digest) (Enc := Bytes))
variable (independent : CanonicalRequest.ChallengeIndependent shape binary.nPublic metadata)
variable (bindSalt : ∀ (key : FingerprintPrefix.Key binary.nPublic) (column : Fin c.n) (nonce : MerkleNonce), cfg.bindSalt key column nonce = (column,nonce))
local notation "rawView" => StrandRealization.rawView binary prime P R repr shape setup (I) binaryCount metadata
  fits physical codec id program
abbrev Raw := StrandWindow.Point (Other)

def failure (view : View) : Prop := acceptedFailure view

def verify (SHA : Bytes → Digest) (output : Output) : Bool := actualVerify SHA id output

def verifierReplay (output : Output) :=
  StrandAuthentication.replay binary prime P R (W) (Earlier) bodyCodec physical codec id output

omit [∀ side, Fintype (fields side)] [Fintype Advice] in
theorem failure_verified (view : View) (SHA : Bytes → Digest)
    (replayed : view.verifier =
      (verifierReplay c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
        binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit cfg binaryCount metadata
        sample columnsFit view.original.1).run SHA)
    (failed : failure c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
      binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit cfg binaryCount metadata
      sample primeCount columnsFit view) :
    verify c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
      binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit cfg binaryCount metadata
      sample primeCount columnsFit SHA view.original.1 = true := by
  have actual := StrandExecution.decision_of_trace binary prime P R (W) (Earlier) bodyCodec physical codec id
    hashPublic primePublic draw view SHA (congrArg Prod.snd replayed)
  exact actual.symm.trans failed.1

omit [∀ side, Fintype (fields side)] [Fintype Advice] in
theorem verifierReplay_domain (output : Output) :
    OracleDomain.UsesOnly StrandDomains.protocol
      (verifierReplay c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
        binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit cfg binaryCount metadata
        sample columnsFit output) :=
  StrandDomains.replay binary prime P R (W) (Earlier) bodyCodec physical codec id
    (fun value => StrandDomains.of_merkle (SHAOracle.leaf_in_domain First Second repr
      cfg.binaryField cfg.primeField setup.jointContext columnsFit value))
    (fun index value => StrandDomains.of_merkle (SHAOracle.node_in_domain First Second repr
      cfg.binaryField cfg.primeField setup.jointContext columnsFit value index)) output

def rawObservation (G : Raw c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
    binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit cfg binaryCount
    metadata fits sample columnsFit program → Digest) := rawView G

def rawOracle (G : Raw c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
    binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit cfg binaryCount
    metadata fits sample columnsFit program → Digest) : Bytes → Digest :=
  StrandRealization.rawSHA binary prime P R repr shape setup (I) binaryCount metadata
    fits physical codec id program G

theorem rawObservation_original (G : Raw c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
    binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit cfg binaryCount
    metadata fits sample columnsFit program → Digest) :
    (rawObservation c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
      binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit cfg binaryCount metadata
      fits sample columnsFit program G).original =
      program.run (rawOracle c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
        binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit cfg binaryCount metadata
        fits sample columnsFit program G) :=
  congrArg (fun view => view.original) (StrandRealization.rawView_actual binary prime P R repr shape setup (I)
    binaryCount metadata fits physical codec id program G)

theorem rawObservation_verifier (G : Raw c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
    binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit cfg binaryCount
    metadata fits sample columnsFit program → Digest) :
    (rawObservation c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
      binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit cfg binaryCount metadata
      fits sample columnsFit program G).verifier =
      (verifierReplay c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
        binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit cfg binaryCount metadata
        sample columnsFit (program.run
          (rawOracle c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
            binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit cfg binaryCount metadata
            fits sample columnsFit program G)).1).run
        (rawOracle c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
          binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit cfg binaryCount metadata
          fits sample columnsFit program G) :=
  congrArg (fun view => view.verifier) (StrandRealization.rawView_actual binary prime P R repr shape setup (I)
    binaryCount metadata fits physical codec id program G)

def rawFailure (G : Raw c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
    binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit cfg binaryCount
    metadata fits sample columnsFit program → Digest) : Prop := acceptedFailure (rawView G)

include bodyFits bitsFit layoutCorrect fallbackPath independent bindSalt queries uniform in
/-- Leading linear soundness of the actual numbered-strand runtime. All execution,
cache, recovery and stopped-charge facts are derived internally. The remaining
premises are explicit numerical budgets, discharged by the concrete profile.
No saturation or `ordinaryRate * Q ≤ 1` premise is used. -/
theorem soundness_linear (opaqueRate : ℚ)
    (nonnegative : 0 ≤ opaqueRate) (atMostRate : opaqueRate ≤ ordinaryRate)
    (parentBound : ParameterBounds.parentBudget c.n c.k c.s c.t c.activeCutoff c.activeList ≤ opaqueRate)
    (guessFits : (2*Q : ℚ)/2^256 ≤ opaqueRate) :
    density (rawFailure c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
      binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit cfg binaryCount metadata
      fits sample primeCount columnsFit program) ≤
        ordinaryRate*Q + StrandRecovery.hashCorrection Q g.roles.length c.n := by
  letI : Fintype Value := valueFinite
  letI : Fintype Name := inferInstance
  unfold rawFailure
  rw [StrandRealization.observation_law binary prime P R repr shape setup (I) binaryCount metadata fits
    physical codec id program (fun view => acceptedFailure view)]
  have algebra := named_linear_failure_le c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
    binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit cfg
    binaryCount metadata bodyFits fits sample fiber uniform primeCount columnsFit program layout bitsFit layoutCorrect queries
    opaqueRate nonnegative atMostRate parentBound guessFits
  apply algebra.trans
  apply add_le_add le_rfl
  have hash := StrandRecovery.hashException_ratio_le binary prime P R repr shape setup (I) binaryCount metadata fits
    columnsFit physical primeCount draw program fallbackPath independent bindSalt bodyFits queries
  apply hash.trans_eq
  unfold StrandRealizationBounds.delta StrandRecovery.hashCorrection
  ring

include bodyFits bitsFit layoutCorrect fallbackPath independent bindSalt queries uniform in
/-- Saturated soundness of the actual numbered-strand runtime. All execution,
cache, recovery and stopped-charge facts are derived internally. The remaining
premises are explicit numerical budgets, discharged by the concrete profile. -/
theorem soundness (opaqueFraction : ℚ)
    (nonnegative : 0 ≤ opaqueFraction) (atMostOne : opaqueFraction ≤ 1) (budget : ordinaryRate*Q ≤ 1)
    (parentBound : ParameterBounds.parentBudget c.n c.k c.s c.t c.activeCutoff c.activeList ≤ opaqueFraction*ordinaryRate)
    (guessFits : (2*Q : ℚ)/2^256 ≤ opaqueFraction*ordinaryRate) :
    density (rawFailure c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
      binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit cfg binaryCount metadata
      fits sample primeCount columnsFit program) ≤
        Survival.Hybrid.envelope ordinaryRate opaqueFraction Q + StrandRecovery.hashCorrection Q g.roles.length c.n := by
  letI : Fintype Value := valueFinite
  letI : Fintype Name := inferInstance
  unfold rawFailure
  rw [StrandRealization.observation_law binary prime P R repr shape setup (I) binaryCount metadata fits
    physical codec id program (fun view => acceptedFailure view)]
  have algebra := named_saturated_failure_le c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
    binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit cfg
    binaryCount metadata bodyFits fits sample fiber uniform primeCount columnsFit program layout bitsFit layoutCorrect queries
    opaqueFraction nonnegative atMostOne budget parentBound guessFits
  apply algebra.trans
  apply add_le_add le_rfl
  have hash := StrandRecovery.hashException_ratio_le binary prime P R repr shape setup (I) binaryCount metadata fits
    columnsFit physical primeCount draw program fallbackPath independent bindSalt bodyFits queries
  apply hash.trans_eq
  unfold StrandRealizationBounds.delta StrandRecovery.hashCorrection
  ring

end LfzkV2.Current.StrandProtocol
