import LfzkV2.Current.Soundness.StrandTransport
import LfzkV2.Current.Soundness.RuntimePath
import LfzkV2.Current.Soundness.HashTransport
import Survival.CausalCharges

/-! The actual runtime's chronological stopped costs and common failure cover.
Transport and recovered-path algebra come from `StrandTransport`. This module
constructs the one retained cost, its unconditional mean, and the central
pointwise failure indicator. It is independent of W and numeric parameters. -/
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
local notation "fitsRoles" => StrandRoleSampling.roleFits binaryCapacity primeCapacity g binaryPlan primePlan
  binaryGeometry primeGeometry binaryFits primeFits binary.degree (prime.circuit.layers+1) degreeFits rowsFit
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
local notation "merkleDec" => MerkleWireCodec.decoders (First) (Second) repr
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
local notation "SHAof" => shaOracle c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
  binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit cfg binaryCount metadata fits sample
  fiber uniform columnsFit program
local notation "hashPublic" => CanonicalRequest.hashPublic binary.nPublic
local notation "primePublic" => CanonicalRuntime.decodePrimePublic binary prime P R repr shape setup (I) primeCount
local notation "ordinary" => StrandVerifier.oracle binary prime P R (W) bodyCodec physical
local notation "actualVerify" => StrandVerifier.verify binary prime P R (W) (Earlier) bodyCodec physical
  hashPublic primePublic draw codec
local notation "search" => searchTree c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
  binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit cfg binaryCount metadata fits sample columnsFit program
local notation "analysis" => analysisTree c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
  binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit cfg binaryCount metadata fits sample
  fiber uniform columnsFit program
local notation "context" => QueryRuntime.Runtime.key repr shape setup binary.nPublic
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
local notation "recovered" => StrandRecovery.recovered binary prime P R repr shape setup (I) binaryCount metadata
  fits columnsFit physical primeCount draw program bodyFits
local notation "pathOf" => fun residual H index =>
  (Sum.inl (Chain.point (M) (Prod.fst (Tree.run program (SHAof residual H)))
    (ordinary (SHAof residual H)) index) : Tagged)
local notation "encodings" => RuntimeAdaptiveVerifier.encodings binary prime P R (W) (Earlier)
local notation "viewOf" => fun residual H => sourceView (namedH residual H)
local notation "failsView" => extractionFails c binary prime P R countBinary countPrime binaryCapacity primeCapacity
  repr shape setup binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit
  cfg binaryCount metadata sample primeCount columnsFit
variable (layoutCorrect : StatementCompiler.addresses P R binary.cells prime.remaining prime.pads = some layout)
local notation "marked" => (LfzkV2.Current.Soundness.RuntimeRoles.marked (Aux := Name) g.batchingIndex : Tagged → Bool)
local notation "causal" => causalProof c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
  binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit cfg
  binaryCount metadata fits sample primeCount columnsFit program layout bitsFit
local notation "auditSafe" => fun (_ : Tagged → Residual) => Survival.CausalCharges.safe (causal) marked
local notation "auditTree" => fun residual => Survival.History.audit (auditSafe residual) marked
  Survival.CausalCharges.advance [] (analysis residual)

/-- Original speculative and receiving hash charges, lifted to the common
protocol/auxiliary name space. Only the tree is stopped; names and targets
are the ones used by the existing runtime recovery theorem. -/
def hashCost [queryDecidable : DecidableEq Tagged] {X : Type} {steps : ℕ}
    (tree : Tree Tagged (Digest × Answer) X steps) (H : Tagged → Digest × Answer) : ℚ :=
  DigestProjection.charge (LfzkV2.Current.Soundness.HashTransport.liftClaims (names)
    (StrandSearch.claims (StrandWindow.Node.bytes (other := Other)))) tree H +
  DigestProjection.receivingCharge (LfzkV2.Current.Soundness.HashTransport.liftPredicate (names)
    (StrandMerkleRealization.receives codec (StrandWindow.Node.bytes (other := Other))))
    (LfzkV2.Current.Soundness.HashTransport.liftClaims (names)
      (StrandCommitment.claims MerkleWireCodec.nodeChildren context FingerprintPrefix.Key.root ∘
        StrandMerkleRealization.byteName (StrandWindow.Node.bytes (other := Other)))) tree H
local notation "hashOf" => hashCost c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
  binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit cfg
  binaryCount metadata fits sample columnsFit program

theorem hashCost_nonneg [queryDecidable : DecidableEq Tagged] {X : Type} {steps : ℕ}
    (tree : Tree Tagged (Digest × Answer) X steps) (H : Tagged → Digest × Answer) : 0 ≤ hashOf tree H :=
  add_nonneg (DigestProjection.charge_nonneg _ _ _) (DigestProjection.receivingCharge_nonneg _ _ _ _)

theorem stopped_hash_nonneg (residual : Tagged → Residual) (H : Tagged → Digest × Answer) :
    0 ≤ hashOf (auditTree residual) H :=
  hashCost_nonneg (queryDecidable := fun a b => Classical.propDecidable (a = b))
    c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
    binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit cfg
    binaryCount metadata fits sample columnsFit program (auditTree residual) H
local notation "hashBad" => StrandRecovery.hashException binary prime P R repr shape setup (I) binaryCount metadata
  columnsFit physical primeCount draw

/-- Lifting and changing sampling coordinates preserves the existing hash
charge exactly, including receiving inputs outside the eventual opening. -/
theorem hashCost_eq (residual : Tagged → Residual) (H : Tagged → Digest × Answer) :
    hashOf (analysis residual) H =
      StrandRecovery.hashCharge binary prime P R repr shape setup (I) binaryCount metadata fits
        columnsFit physical program (namedH residual H) := by
  unfold hashCost analysisTree
  erw [StrandComposition.coordinates_charge (names).tag (names).tag_injective split residual (search),
    LfzkV2.Current.Soundness.HashTransport.coordinates_receiving (names).tag (names).tag_injective split residual (search)]
  simp only [LfzkV2.Current.Soundness.HashTransport.liftClaims_tag, LfzkV2.Current.Soundness.HashTransport.liftPredicate_tag]
  rfl

/-- A surviving monitor retains the entire original digest trace, so its
hash cost is the same original recovery cost. -/
theorem stopped_hashCost_eq (residual : Tagged → Residual) (H : Tagged → Digest × Answer)
    (survived : ((auditTree residual).run H).1.1 = false) :
    hashOf (auditTree residual) H =
      StrandRecovery.hashCharge binary prime P R repr shape setup (I) binaryCount metadata fits
        columnsFit physical program (namedH residual H) := by
  have same := Survival.History.audit_trace (auditSafe residual) marked Survival.CausalCharges.advance []
    (analysis residual) H survived
  apply Eq.trans _ (hashCost_eq c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
    binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit cfg
    binaryCount metadata fits sample fiber uniform columnsFit program residual H)
  unfold hashCost
  rw [DigestProjection.charge_congr _ (auditTree residual) (analysis residual) H H
      (congrArg (List.map Prod.fst) same) (fun _ => rfl),
    LfzkV2.Current.Soundness.HashTransport.receiving_congr _ _ (auditTree residual) (analysis residual) H H
      (congrArg (List.map Prod.fst) same) (fun _ => rfl)]

include bodyFits in
theorem path_ancestors_before (residual : Tagged → Residual) (H : Tagged → Digest × Answer)
    (ready : recovered (namedH residual H)) (index : ℕ) (within : index ≤ g.roles.length)
    (j : Fin ((M).point (program.run (SHAof residual H)).1 (ordinary (SHAof residual H)) index).rank) :
    (Sum.inl (((M).point (program.run (SHAof residual H)).1 (ordinary (SHAof residual H)) index).priorPoints j) : Tagged) ∈
      before (analysis residual) H (pathOf residual H index) := by
  have path := analysis_path c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
    binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit cfg
    binaryCount metadata bodyFits fits sample fiber uniform primeCount columnsFit program residual H ready
  exact LfzkV2.Current.Soundness.RuntimePath.ancestors_before (queryDecidable := fun a b => Classical.propDecidable (a = b))
    (encodings) (W).initialLink (analysis residual) H
    (program.run (SHAof residual H)).1 (ordinary (SHAof residual H)) path index within j

include bodyFits in
theorem path_single_causal (residual : Tagged → Residual) (H : Tagged → Digest × Answer)
    (ready : recovered (namedH residual H)) (index : ℕ) (within : index ≤ g.roles.length)
    (past rest : List (Tagged × (Digest × Answer))) (answer : Digest × Answer)
    (trace : ((analysis residual).run H).2 = past ++ (pathOf residual H index,answer)::rest)
    (pastNames : past.map Prod.fst = before (analysis residual) H (pathOf residual H index)) :
    (causal).single (pathOf residual H index) ((causal).extract (pathOf residual H index) past) answer =
      (charges residual).single (pathOf residual H index) H answer := by
  let point : Point := (M).point (program.run (SHAof residual H)).1 (ordinary (SHAof residual H)) index
  have ancestors (j : Fin point.rank) : (Sum.inl (point.priorPoints j) : Tagged) ∈ past.map Prod.fst := by
    rw [pastNames]
    exact path_ancestors_before c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
      binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit cfg
      binaryCount metadata bodyFits fits sample fiber uniform primeCount columnsFit program residual H ready index within j
  exact StrandCharges.prefixCharge_eq_runtime c binary prime P R countBinary countPrime binaryCapacity primeCapacity (W)
    fitsRoles layout degreeFits rowsFit bitsFit hashPublic primePublic
    primePlan primeFits binaryPlan binaryFits
    (names) context codec merkleDec FingerprintPrefix.Key.root (StrandWindow.Node.bytes (other := Other))
    (analysis residual) H (default,cfg.fallback) point past rest answer trace ancestors

include bodyFits layoutCorrect in
/-- On a recovered accepting failure, surviving all transparent tests leaves
a backend rank/high-response charge on the stopped original-query trace. -/
theorem recovered_stopped_charge (residual : Tagged → Residual) (H : Tagged → Digest × Answer)
    (accepted : decision (viewOf residual H) = true) (ready : recovered (namedH residual H))
    (failed : failsView (viewOf residual H)) (survived : ((auditTree residual).run H).1.1 = false) :
    1 ≤ (Survival.StoppedCharges.restrict (charges residual) marked).charge (auditTree residual) H := by
  have path := analysis_path c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
    binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit cfg
    binaryCount metadata bodyFits fits sample fiber uniform primeCount columnsFit program residual H ready
  have cover := accepted_cover c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
    binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit cfg
    binaryCount metadata bodyFits fits sample fiber uniform primeCount columnsFit program layout bitsFit layoutCorrect
    residual H accepted ready failed
  apply Survival.CausalCharges.stopped_charge_of_causal_cover (causal) (charges residual) marked
    (analysis residual) H (pathOf residual H) path cover survived
  intro index within
  exact path_single_causal c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
    binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit cfg
    binaryCount metadata bodyFits fits sample fiber uniform primeCount columnsFit program layout bitsFit
    residual H ready index within.le

include bodyFits layoutCorrect in
/-- The charge uses the adversary's original query path and its original
commitment cut, after the exact change of sampler coordinates. -/
theorem recovered_failure_charge (residual : Tagged → Residual) (H : Tagged → Digest × Answer)
    (accepted : decision (viewOf residual H) = true) (ready : recovered (namedH residual H))
    (failed : failsView (viewOf residual H)) : 1 ≤ (charges residual).charge (analysis residual) H := by
  have path := analysis_path c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
    binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit cfg
    binaryCount metadata bodyFits fits sample fiber uniform primeCount columnsFit program residual H ready
  have cover := accepted_cover c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
    binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit cfg
    binaryCount metadata bodyFits fits sample fiber uniform primeCount columnsFit program layout bitsFit layoutCorrect
    residual H accepted ready failed
  exact SharedReduction.charges_of_cover (analysis residual) H (pathOf residual H)
    path.queried path.ordered (charges residual).single_nonneg (charges residual).pair_nonneg cover
/-- The single retained opaque cost used by both composition bounds.
It uses the original charge functions and cut; only the query tree is stopped. -/
def stoppedCost (residual : Tagged → Residual) (H : Tagged → Digest × Answer) : ℚ :=
  (Survival.StoppedCharges.restrict (charges residual) marked).charge (auditTree residual) H +
    hashOf (auditTree residual) H

local notation "costOf" => stoppedCost c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
  binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit cfg
  binaryCount metadata fits sample fiber uniform primeCount columnsFit program layout bitsFit

theorem stoppedCost_nonneg (residual : Tagged → Residual) (H : Tagged → Digest × Answer) :
    0 ≤ costOf residual H :=
  add_nonneg ((Survival.StoppedCharges.restrict (charges residual) marked).charge_nonneg _ _)
    (stopped_hash_nonneg c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
      binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit cfg
      binaryCount metadata fits sample fiber uniform primeCount columnsFit program layout bitsFit residual H)

local notation "valueFinite" => Fintype.ofInjective
  (QueryRuntime.Runtime.toPoint repr shape setup binary.nPublic)
  (QueryRuntime.Runtime.toPoint_injective repr shape setup binary.nPublic fits)
local notation "ordinaryRate" => (2/((Adapter.Mdoc.binaryOrder-1:ℕ):ℚ))


variable {Q : ℕ} (queries : ∀ SHA : Bytes → Digest, (seen program SHA).card ≤ Q)

include queries in
theorem analysis_queries (residual : Tagged → Residual) (H : Tagged → Digest × Answer) :
    (seen (analysis residual) H).card ≤ Q := by
  rw [analysis_seen, Finset.card_image_of_injective _ (names).tag_injective]
  exact StrandRecovery.grouped_budget binary prime P R repr shape setup (I)
    binaryCount metadata fits columnsFit physical program queries (namedH residual H)

include queries in
/-- Speculative strand inputs and Merkle receiving inputs remain disjoint
on the stopped tree. Their full mean is paid only by auxiliary query slots. -/
theorem stopped_hash_sum_le (residual : Tagged → Residual) :
    letI : Fintype Value := valueFinite
    letI : Fintype Name := inferInstance
    (∑ H : Tagged → Digest × Answer, hashOf (auditTree residual) H) ≤
      ∑ H : Tagged → Digest × Answer, ∑ p ∈ seen (auditTree residual) H,
        if LfzkV2.Current.Soundness.RuntimeRoles.auxiliary p then (2*Q : ℚ)/2^256 else 0 := by
  letI : Fintype Value := valueFinite
  letI : Fintype Name := inferInstance
  letI : Nonempty Answer := ⟨cfg.fallback⟩
  let bytes := StrandWindow.Node.bytes (other := Other)
  let strand := StrandSearch.claims (T := Value) bytes
  let merkle := StrandCommitment.claims MerkleWireCodec.nodeChildren context FingerprintPrefix.Key.root ∘
    StrandMerkleRealization.byteName bytes
  let receives : Name → Prop := StrandMerkleRealization.receives codec bytes
  have plantAuxiliary (p : Name) (planted : (strand p).Nonempty) : (names).decode p = none := by
    cases p with
    | inr _ => rfl
    | inl p =>
        rcases p with ⟨raw,value⟩
        cases value with
        | none => rfl
        | some _ => exact False.elim (Finset.not_nonempty_empty planted)
  have receiveAuxiliary (p : Name) (received : receives p) : (names).decode p = none := by
    apply StrandMerkleRealization.receives_auxiliary codec bytes (names) _ p received
    exact StrandMerkleRealization.wire_receives_disjoint First Second repr cfg.binaryField cfg.primeField
      setup.jointContext columnsFit shape setup binary.nPublic fits
      (StrandRealization.locate binary prime P R repr shape setup (I) binaryCount metadata fits physical codec id program)
      bytes (StrandRealization.locate_bytes binary prime P R repr shape setup (I) binaryCount metadata fits
        physical codec id program)
  have disjoint (p : Name) (received : receives p) : strand p = ∅ :=
    StrandMerkleRealization.receiving_claims_empty First Second repr cfg.binaryField cfg.primeField
      setup.jointContext columnsFit bytes p received
  have strandCard (p : Name) : (strand p).card ≤ 1 :=
    (StrandSearch.claims_card bytes p).trans (by split_ifs <;> decide)
  have merkleCard (p : Name) : (merkle p).card ≤ 2 :=
    StrandCommitment.claims_card MerkleWireCodec.nodeChildren context FingerprintPrefix.Key.root
      (StrandMerkleRealization.byteName bytes p)
  have stoppedQueries (H : Tagged → Digest × Answer) : (seen (auditTree residual) H).card ≤ Q := by
    apply (Finset.card_le_card (Survival.History.audit_seen_subset (auditSafe residual) marked
      Survival.CausalCharges.advance [] (analysis residual) H)).trans
    exact analysis_queries c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
      binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit cfg
      binaryCount metadata fits sample fiber uniform columnsFit program queries residual H
  have bound := LfzkV2.Current.Soundness.HashTransport.hash_sum_le
    (queryDecidable := fun a b => Classical.propDecidable (a = b))
    (names) strand merkle receives plantAuxiliary receiveAuxiliary disjoint strandCard merkleCard
    (auditTree residual) stoppedQueries
  rw [TranscriptV2.Strand.digest_card, Nat.cast_pow] at bound
  apply bound.trans_eq
  apply Finset.sum_congr rfl
  intro H _
  apply Finset.sum_congr rfl
  intro p _
  cases p <;> simp [LfzkV2.Current.Soundness.HashTransport.auxiliary, LfzkV2.Current.Soundness.RuntimeRoles.auxiliary]

theorem stopped_backend_budget_le (residual : Tagged → Residual) (opaqueRate : ℚ)
    (parentBound : ParameterBounds.parentBudget c.n c.k c.s c.t c.activeCutoff c.activeList ≤ opaqueRate)
    (point : Tagged) :
    (Survival.StoppedCharges.restrict (charges residual) marked).budget point ≤
      if marked point && !LfzkV2.Current.Soundness.RuntimeRoles.auxiliary point then opaqueRate else 0 := by
  exact StrandCharges.stopped_budget_le (budgetDecidable := fun a b => Classical.propDecidable (a = b)) c binary prime P R countBinary countPrime binaryCapacity primeCapacity (W)
    fitsRoles layout degreeFits rowsFit bitsFit hashPublic primePublic
    primePlan primeGeometry primeFits binaryPlan binaryGeometry binaryFits
    (names) context codec merkleDec FingerprintPrefix.Key.root (StrandWindow.Node.bytes (other := Other))
    (analysis residual) cfg.fallback opaqueRate parentBound point

include queries in
/-- The runtime backend and auxiliary hash mechanisms spend disjoint opaque
slots. Their combined stopped mean fits one opaqueRate per opaque query. -/
theorem conditioned_cost_mean_le (residual : Tagged → Residual) (opaqueRate : ℚ) (positive : 0 ≤ opaqueRate)
    (parentBound : ParameterBounds.parentBudget c.n c.k c.s c.t c.activeCutoff c.activeList ≤ opaqueRate)
    (guessFits : (2*Q : ℚ)/2^256 ≤ opaqueRate) :
    letI : Fintype Value := valueFinite
    letI : Fintype Name := inferInstance
    (∑ H : Tagged → Digest × Answer, costOf residual H) / Fintype.card (Tagged → Digest × Answer) ≤
      opaqueRate * ((∑ H : Tagged → Digest × Answer, (((auditTree residual).run H).1.2 : ℚ)) /
        Fintype.card (Tagged → Digest × Answer)) := by
  letI : Fintype Value := valueFinite
  letI : Fintype Name := inferInstance
  letI : Nonempty Answer := ⟨cfg.fallback⟩
  apply Survival.StoppedCharges.combined_mean_le (charges residual) (auditSafe residual) marked
    LfzkV2.Current.Soundness.RuntimeRoles.auxiliary Survival.CausalCharges.advance _ opaqueRate positive
  · exact stopped_backend_budget_le c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
      binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit cfg
      binaryCount metadata fits sample fiber uniform primeCount columnsFit program layout bitsFit residual opaqueRate parentBound
  · have hashMean := stopped_hash_sum_le c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
      binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit cfg
      binaryCount metadata fits sample fiber uniform primeCount columnsFit program layout bitsFit queries residual
    apply hashMean.trans
    apply Finset.sum_le_sum
    intro H _
    apply Finset.sum_le_sum
    intro p _
    split_ifs
    · exact guessFits
    · exact le_rfl
  · intro point auxiliary
    cases point with
    | inl point => cases auxiliary
    | inr _ => rfl
local notation "acceptedFailure" => fun (view : View) => decision view = true ∧ failsView view

include bodyFits layoutCorrect in
theorem stopped_failure_cover (residual : Tagged → Residual) (H : Tagged → Digest × Answer)
    (failed : decision (viewOf residual H) = true ∧ failsView (viewOf residual H))
    (noHash : ¬hashBad (viewOf residual H)) :
    ((auditTree residual).run H).1.1 = true ∨
      1 ≤ (Survival.StoppedCharges.restrict (charges residual) marked).charge (auditTree residual) H +
        hashOf (auditTree residual) H := by
  by_cases escapedNow : ((auditTree residual).run H).1.1 = true
  · exact Or.inl escapedNow
  · right
    have survived : ((auditTree residual).run H).1.1 = false := Bool.eq_false_iff.mpr escapedNow
    rcases StrandRecovery.accepted_recovery_or_hash binary prime P R repr shape setup (I) binaryCount metadata
      fits columnsFit physical primeCount draw program bodyFits (namedH residual H) failed.1 with ready | charged | exception
    · have paid := recovered_stopped_charge c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
        binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit cfg
        binaryCount metadata bodyFits fits sample fiber uniform primeCount columnsFit program layout bitsFit layoutCorrect
        residual H failed.1 ready failed.2 survived
      exact paid.trans (le_add_of_nonneg_right (stopped_hash_nonneg c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
          binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit cfg
          binaryCount metadata fits sample fiber uniform primeCount columnsFit program layout bitsFit residual H))
    · have same := stopped_hashCost_eq c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
        binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit cfg
        binaryCount metadata fits sample fiber uniform primeCount columnsFit program layout bitsFit residual H survived
      have paid : 1 ≤ hashOf (auditTree residual) H := by rw [same]; exact charged
      exact paid.trans (le_add_of_nonneg_left
        ((Survival.StoppedCharges.restrict (charges residual) marked).charge_nonneg (auditTree residual) H))
    · exact (noHash exception).elim

include bodyFits layoutCorrect in
/-- One actual runtime failure is covered by the raw exception, first
transparent escape, or the same stoppedCost used by both probability bounds. -/
theorem stopped_failure_indicator (residual : Tagged → Residual) (H : Tagged → Digest × Answer) :
    (if acceptedFailure (viewOf residual H) then (1 : ℚ) else 0) ≤
      (if hashBad (viewOf residual H) then 1 else 0) +
      (if ((auditTree residual).run H).1.1 = true then 1 else 0) + costOf residual H := by
  have bound := Survival.FiniteCover.indicator_cover
    (fun H => acceptedFailure (viewOf residual H)) (fun H => hashBad (viewOf residual H))
    (fun H => ((auditTree residual).run H).1.1 = true) (costOf residual)
    (stoppedCost_nonneg c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
      binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit cfg
      binaryCount metadata fits sample fiber uniform primeCount columnsFit program layout bitsFit residual)
    (stopped_failure_cover c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
      binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit cfg
      binaryCount metadata bodyFits fits sample fiber uniform primeCount columnsFit program layout bitsFit layoutCorrect residual) H
  convert bound using 1 <;> split_ifs <;> rfl

end LfzkV2.Current.StrandProtocol
