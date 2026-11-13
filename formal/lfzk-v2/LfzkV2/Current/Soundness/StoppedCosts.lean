import LfzkV2.Current.Protocol.Execution
import LfzkV2.Current.Soundness.Setup
import LfzkV2.Current.Soundness.Transport
import LfzkV2.Current.Soundness.AcceptedPath
import LfzkV2.Current.Soundness.HashTransport
import Survival.CausalCharges

/-! The actual runtime's chronological stopped costs and common failure cover.
Transport and recovered-path algebra come from `StrandTransport`. This module
constructs the one retained cost, its unconditional mean, and the central
pointwise failure indicator. It is independent of W and numeric parameters. -/
noncomputable section
namespace LfzkV2.Current.Soundness.Runtime
open Application ApplicationSetup CanonicalPrefix QueryRuntime RecursivePolygero
open Finset Bcs.FiniteProbability Merkle Merkle.Indexed Merkle.RandomOracle TranscriptV2
open Protocol.Sampling
open scoped Classical

attribute [local instance] answerFintype valuesFintype idealLeafInhabited runtimeLeafInhabited
variable {c : CertifiedProfile} {g : Geometry} {fields : Fields} {Advice B : Type}
variable [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable [∀ side, Fintype (fields side)] [Fintype Advice]
variable {shared maskBits adviceBits blocks fuel : ℕ}
variable (E : Protocol.Setup c g fields Advice B (shared := shared) (maskBits := maskBits) (adviceBits := adviceBits))
variable (fits : g.roles.length < 2^64)
variable (D : Protocol.SamplerData E blocks) (L : Protocol.SamplerLaws D)
variable (prog : Protocol.Execution.Program E.Output fuel)
variable (inputs : Soundness.Inputs E)
variable [Inhabited (Fin c.n × MerkleNonce)]
variable [leafDefault : Inhabited (Joint.Pair.family E.First E.Second).Leaf]

local notation "names" => Soundness.OracleTransport.queryCodec E.binary E.prime E.P E.R E.repr E.shape E.fingerprint (E.ideal) E.binaryCount E.metadata
  fits D.execution.sample E.merkleCodec id prog.tree
local notation "Other" => Soundness.OracleTransport.other E.binary E.prime E.P E.R E.repr E.shape E.fingerprint (E.ideal) E.binaryCount E.metadata fits
  D.execution.sample E.merkleCodec id prog.tree
local notation "Node" => StrandWindow.Node (Other)
local notation "Name" => StrandSearch.Name Node E.Value
local notation "Tagged" => E.Point ⊕ Name
local notation "Row" => Strand.Word → Digest
local notation "Residual" => Fin (Fintype.card Row)
local notation "split" => coordinateSplit E fits D L prog
local notation "namedH" => namedOracle E fits D L prog
local notation "SHAof" => shaOracle E fits D L prog
local notation "ordinary" => StrandVerifier.oracle E.binary E.prime E.P E.R (E.wire) E.bodyCodec D.execution.sample
local notation "actualVerify" => StrandVerifier.verify E.binary E.prime E.P E.R (E.wire) (E.earlier) E.bodyCodec D.execution.sample
  E.hashPublic E.primePublic E.draw E.merkleCodec
local notation "search" => searchTree E fits D prog
local notation "analysis" => analysisTree E fits D L prog
local notation "charges" => localProof E fits D L prog inputs
local notation "View" => Protocol.Execution.View E.Output ((E.Output × Chain.State (E.chain)) × Digest)
  (FingerprintPrefix.Key E.binary.nPublic)
local notation "decision" => Protocol.Observation.decision E.binary E.prime E.P E.R (E.wire) (E.earlier) E.bodyCodec D.execution.sample E.merkleCodec id
  E.hashPublic E.primePublic E.draw
local notation "observe" => Soundness.OracleTransport.observe E.binary E.prime E.P E.R E.repr E.shape E.fingerprint (E.ideal) E.binaryCount E.metadata
  fits D.execution.sample E.merkleCodec id prog.tree
local notation "sourceView" => fun K => observe (Prod.fst (Tree.run (search) K)) K
local notation "recovered" => Soundness.Recovery.recovered E.binary E.prime E.P E.R E.repr E.shape E.fingerprint (E.ideal) E.binaryCount E.metadata
  fits E.columnsFit D.execution.sample E.primeCount E.draw prog.tree inputs.bodyFits
local notation "pathOf" => fun residual H index =>
  (Sum.inl (Chain.point (E.chain) (Prod.fst (Tree.run prog.tree (SHAof residual H)))
    (ordinary (SHAof residual H)) index) : Tagged)
local notation "encodings" => RuntimeAdaptiveVerifier.encodings E.binary E.prime E.P E.R (E.wire) (E.earlier)
local notation "viewOf" => fun residual H => sourceView (namedH residual H)
local notation "failsView" => extractionFails E D
local notation "marked" => (LfzkV2.Current.Soundness.RuntimeRoles.marked (Aux := Name) g.batchingIndex : Tagged → Bool)
local notation "causal" => causalProof E fits D prog inputs
local notation "auditSafe" => fun (_ : Tagged → Residual) => Survival.CausalCharges.safe (causal) marked
local notation "auditTree" => fun residual => Survival.History.audit (auditSafe residual) marked
  Survival.CausalCharges.advance [] (analysis residual)

/-- Original speculative and receiving hash charges, lifted to the common
protocol/auxiliary name space. Only the tree is stopped; names and targets
are the ones used by the existing runtime recovery theorem. -/
def hashCost [queryDecidable : DecidableEq Tagged] {X : Type} {steps : ℕ}
    (tree : Tree Tagged (Digest × E.Answer) X steps) (H : Tagged → Digest × E.Answer) : ℚ :=
  DigestProjection.charge (LfzkV2.Current.Soundness.HashTransport.liftClaims (names)
    (StrandSearch.claims (StrandWindow.Node.bytes (other := Other)))) tree H +
  DigestProjection.receivingCharge (LfzkV2.Current.Soundness.HashTransport.liftPredicate (names)
    (StrandMerkleRealization.receives E.merkleCodec (StrandWindow.Node.bytes (other := Other))))
    (LfzkV2.Current.Soundness.HashTransport.liftClaims (names)
      (StrandCommitment.claims MerkleWireCodec.nodeChildren E.context FingerprintPrefix.Key.root ∘
        StrandMerkleRealization.byteName (StrandWindow.Node.bytes (other := Other)))) tree H
local notation "hashOf" => hashCost E fits D prog

theorem hashCost_nonneg [queryDecidable : DecidableEq Tagged] {X : Type} {steps : ℕ}
    (tree : Tree Tagged (Digest × E.Answer) X steps) (H : Tagged → Digest × E.Answer) : 0 ≤ hashOf tree H :=
  add_nonneg (DigestProjection.charge_nonneg _ _ _) (DigestProjection.receivingCharge_nonneg _ _ _ _)

theorem stopped_hash_nonneg (residual : Tagged → Residual) (H : Tagged → Digest × E.Answer) :
    0 ≤ hashOf (auditTree residual) H :=
  hashCost_nonneg (queryDecidable := fun a b => Classical.propDecidable (a = b)) E fits D prog (auditTree residual) H
local notation "hashBad" => Soundness.Recovery.hashException E.binary E.prime E.P E.R E.repr E.shape E.fingerprint (E.ideal) E.binaryCount E.metadata
  E.columnsFit D.execution.sample E.primeCount E.draw

/-- Lifting and changing sampling coordinates preserves the existing hash
charge exactly, including receiving inputs outside the eventual opening. -/
theorem hashCost_eq (residual : Tagged → Residual) (H : Tagged → Digest × E.Answer) :
    hashOf (analysis residual) H =
      Soundness.Recovery.hashCharge E.binary E.prime E.P E.R E.repr E.shape E.fingerprint (E.ideal) E.binaryCount E.metadata fits
        E.columnsFit D.execution.sample prog.tree (namedH residual H) := by
  unfold hashCost analysisTree
  erw [Soundness.Coordinates.coordinates_charge (names).tag (names).tag_injective split residual (search),
    LfzkV2.Current.Soundness.HashTransport.coordinates_receiving (names).tag (names).tag_injective split residual (search)]
  simp only [LfzkV2.Current.Soundness.HashTransport.liftClaims_tag, LfzkV2.Current.Soundness.HashTransport.liftPredicate_tag]
  rfl

/-- A surviving monitor retains the entire original digest trace, so its
hash cost is the same original recovery cost. -/
theorem stopped_hashCost_eq (residual : Tagged → Residual) (H : Tagged → Digest × E.Answer)
    (survived : ((auditTree residual).run H).1.1 = false) :
    hashOf (auditTree residual) H =
      Soundness.Recovery.hashCharge E.binary E.prime E.P E.R E.repr E.shape E.fingerprint (E.ideal) E.binaryCount E.metadata fits
        E.columnsFit D.execution.sample prog.tree (namedH residual H) := by
  have same := Survival.History.audit_trace (auditSafe residual) marked Survival.CausalCharges.advance []
    (analysis residual) H survived
  apply Eq.trans _ (hashCost_eq E fits D L prog residual H)
  unfold hashCost
  rw [DigestProjection.charge_congr _ (auditTree residual) (analysis residual) H H
      (congrArg (List.map Prod.fst) same) (fun _ => rfl),
    LfzkV2.Current.Soundness.HashTransport.receiving_congr _ _ (auditTree residual) (analysis residual) H H
      (congrArg (List.map Prod.fst) same) (fun _ => rfl)]

include inputs in
theorem path_ancestors_before (residual : Tagged → Residual) (H : Tagged → Digest × E.Answer)
    (ready : recovered (namedH residual H)) (index : ℕ) (within : index ≤ g.roles.length)
    (j : Fin ((E.chain).point (prog.tree.run (SHAof residual H)).1 (ordinary (SHAof residual H)) index).rank) :
    (Sum.inl (((E.chain).point (prog.tree.run (SHAof residual H)).1 (ordinary (SHAof residual H)) index).priorPoints j) : Tagged) ∈
      before (analysis residual) H (pathOf residual H index) := by
  have path := analysis_path E fits D L prog inputs residual H ready
  exact LfzkV2.Current.Soundness.AcceptedPath.ancestors_before (queryDecidable := fun a b => Classical.propDecidable (a = b))
    (encodings) (E.wire).initialLink (analysis residual) H
    (prog.tree.run (SHAof residual H)).1 (ordinary (SHAof residual H)) path index within j

include inputs in
theorem path_single_causal (residual : Tagged → Residual) (H : Tagged → Digest × E.Answer)
    (ready : recovered (namedH residual H)) (index : ℕ) (within : index ≤ g.roles.length)
    (past rest : List (Tagged × (Digest × E.Answer))) (answer : Digest × E.Answer)
    (trace : ((analysis residual).run H).2 = past ++ (pathOf residual H index,answer)::rest)
    (pastNames : past.map Prod.fst = before (analysis residual) H (pathOf residual H index)) :
    (causal).single (pathOf residual H index) ((causal).extract (pathOf residual H index) past) answer =
      (charges residual).single (pathOf residual H index) H answer := by
  let point : E.Point := (E.chain).point (prog.tree.run (SHAof residual H)).1 (ordinary (SHAof residual H)) index
  have ancestors (j : Fin point.rank) : (Sum.inl (point.priorPoints j) : Tagged) ∈ past.map Prod.fst := by
    rw [pastNames]
    exact path_ancestors_before E fits D L prog inputs residual H ready index within j
  exact Soundness.LocalCharges.prefixCharge_eq_runtime c E.binary E.prime E.P E.R E.countBinary E.countPrime E.binaryCapacity E.primeCapacity (E.wire)
    E.roleFits inputs.layout E.degreeFits E.rowsFit inputs.bitsFit E.hashPublic E.primePublic
    E.primePlan E.primeFits E.binaryPlan E.binaryFits
    (names) E.context E.merkleCodec E.merkleDecoders FingerprintPrefix.Key.root (StrandWindow.Node.bytes (other := Other))
    (analysis residual) H (default,E.cfg.fallback) point past rest answer trace ancestors

include inputs in
/-- On a recovered accepting failure, surviving all transparent tests leaves
a backend rank/high-response charge on the stopped original-query trace. -/
theorem recovered_stopped_charge (residual : Tagged → Residual) (H : Tagged → Digest × E.Answer)
    (accepted : decision (viewOf residual H) = true) (ready : recovered (namedH residual H))
    (failed : failsView (viewOf residual H)) (survived : ((auditTree residual).run H).1.1 = false) :
    1 ≤ (Survival.StoppedCharges.restrict (charges residual) marked).charge (auditTree residual) H := by
  have path := analysis_path E fits D L prog inputs residual H ready
  have cover := accepted_cover E fits D L prog inputs
    residual H accepted ready failed
  apply Survival.CausalCharges.stopped_charge_of_causal_cover (causal) (charges residual) marked
    (analysis residual) H (pathOf residual H) path cover survived
  intro index within
  exact path_single_causal E fits D L prog inputs
    residual H ready index within.le

include inputs in
/-- The charge uses the adversary's original query path and its original
commitment cut, after the exact change of sampler coordinates. -/
theorem recovered_failure_charge (residual : Tagged → Residual) (H : Tagged → Digest × E.Answer)
    (accepted : decision (viewOf residual H) = true) (ready : recovered (namedH residual H))
    (failed : failsView (viewOf residual H)) : 1 ≤ (charges residual).charge (analysis residual) H := by
  have path := analysis_path E fits D L prog inputs residual H ready
  have cover := accepted_cover E fits D L prog inputs
    residual H accepted ready failed
  exact PathCharges.charges_of_cover (analysis residual) H (pathOf residual H)
    path.queried path.ordered (charges residual).single_nonneg (charges residual).pair_nonneg cover
/-- The single retained opaque cost used by both composition bounds.
It uses the original charge functions and cut; only the query tree is stopped. -/
def stoppedCost (residual : Tagged → Residual) (H : Tagged → Digest × E.Answer) : ℚ :=
  (Survival.StoppedCharges.restrict (charges residual) marked).charge (auditTree residual) H +
    hashOf (auditTree residual) H

local notation "costOf" => stoppedCost E fits D L prog inputs

theorem stoppedCost_nonneg (residual : Tagged → Residual) (H : Tagged → Digest × E.Answer) :
    0 ≤ costOf residual H :=
  add_nonneg ((Survival.StoppedCharges.restrict (charges residual) marked).charge_nonneg _ _)
    (stopped_hash_nonneg E fits D L prog inputs residual H)

local notation "valueFinite" => Fintype.ofInjective
  (QueryRuntime.Runtime.toPoint E.repr E.shape E.fingerprint E.binary.nPublic)
  (QueryRuntime.Runtime.toPoint_injective E.repr E.shape E.fingerprint E.binary.nPublic fits)
local notation "ordinaryRate" => (2/((Adapter.Mdoc.binaryOrder-1:ℕ):ℚ))

variable {Q : ℕ} (queries : ∀ SHA : Bytes → Digest, (seen prog.tree SHA).card ≤ Q)

include queries in
theorem analysis_queries (residual : Tagged → Residual) (H : Tagged → Digest × E.Answer) :
    (seen (analysis residual) H).card ≤ Q := by
  rw [analysis_seen, Finset.card_image_of_injective _ (names).tag_injective]
  exact Soundness.Recovery.grouped_budget E.binary E.prime E.P E.R E.repr E.shape E.fingerprint (E.ideal)
    E.binaryCount E.metadata fits E.columnsFit D.execution.sample prog.tree queries (namedH residual H)

include queries in
/-- Speculative strand inputs and Merkle receiving inputs remain disjoint
on the stopped tree. Their full mean is paid only by auxiliary query slots. -/
theorem stopped_hash_sum_le (residual : Tagged → Residual) :
    letI : Fintype E.Value := valueFinite
    letI : Fintype Name := inferInstance
    (∑ H : Tagged → Digest × E.Answer, hashOf (auditTree residual) H) ≤
      ∑ H : Tagged → Digest × E.Answer, ∑ p ∈ seen (auditTree residual) H,
        if LfzkV2.Current.Soundness.RuntimeRoles.auxiliary p then (2*Q : ℚ)/2^256 else 0 := by
  letI : Fintype E.Value := valueFinite
  letI : Fintype Name := inferInstance
  letI : Nonempty E.Answer := ⟨E.cfg.fallback⟩
  let bytes := StrandWindow.Node.bytes (other := Other)
  let strand := StrandSearch.claims (T := E.Value) bytes
  let merkle := StrandCommitment.claims MerkleWireCodec.nodeChildren E.context FingerprintPrefix.Key.root ∘
    StrandMerkleRealization.byteName bytes
  let receives : Name → Prop := StrandMerkleRealization.receives E.merkleCodec bytes
  have plantAuxiliary (p : Name) (planted : (strand p).Nonempty) : (names).decode p = none := by
    cases p with
    | inr _ => rfl
    | inl p =>
        rcases p with ⟨raw,value⟩
        cases value with
        | none => rfl
        | some _ => exact False.elim (Finset.not_nonempty_empty planted)
  have receiveAuxiliary (p : Name) (received : receives p) : (names).decode p = none := by
    apply StrandMerkleRealization.receives_auxiliary E.merkleCodec bytes (names) _ p received
    exact StrandMerkleRealization.wire_receives_disjoint E.First E.Second E.repr E.cfg.binaryField E.cfg.primeField
      E.fingerprint.jointContext E.columnsFit E.shape E.fingerprint E.binary.nPublic fits
      (Soundness.OracleTransport.locate E.binary E.prime E.P E.R E.repr E.shape E.fingerprint (E.ideal) E.binaryCount E.metadata fits D.execution.sample E.merkleCodec id prog.tree)
      bytes (Soundness.OracleTransport.locate_bytes E.binary E.prime E.P E.R E.repr E.shape E.fingerprint (E.ideal) E.binaryCount E.metadata fits
        D.execution.sample E.merkleCodec id prog.tree)
  have disjoint (p : Name) (received : receives p) : strand p = ∅ :=
    StrandMerkleRealization.receiving_claims_empty E.First E.Second E.repr E.cfg.binaryField E.cfg.primeField
      E.fingerprint.jointContext E.columnsFit bytes p received
  have strandCard (p : Name) : (strand p).card ≤ 1 :=
    (StrandSearch.claims_card bytes p).trans (by split_ifs <;> decide)
  have merkleCard (p : Name) : (merkle p).card ≤ 2 :=
    StrandCommitment.claims_card MerkleWireCodec.nodeChildren E.context FingerprintPrefix.Key.root
      (StrandMerkleRealization.byteName bytes p)
  have stoppedQueries (H : Tagged → Digest × E.Answer) : (seen (auditTree residual) H).card ≤ Q := by
    apply (Finset.card_le_card (Survival.History.audit_seen_subset (auditSafe residual) marked
      Survival.CausalCharges.advance [] (analysis residual) H)).trans
    exact analysis_queries E fits D L prog queries residual H
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
  exact Soundness.LocalCharges.stopped_budget_le (budgetDecidable := fun a b => Classical.propDecidable (a = b)) c E.binary E.prime E.P E.R E.countBinary E.countPrime E.binaryCapacity E.primeCapacity (E.wire)
    E.roleFits inputs.layout E.degreeFits E.rowsFit inputs.bitsFit E.hashPublic E.primePublic
    E.primePlan E.primeGeometry E.primeFits E.binaryPlan E.binaryGeometry E.binaryFits
    (names) E.context E.merkleCodec E.merkleDecoders FingerprintPrefix.Key.root (StrandWindow.Node.bytes (other := Other))
    (analysis residual) E.cfg.fallback opaqueRate parentBound point

include queries in
/-- The runtime backend and auxiliary hash mechanisms spend disjoint opaque
slots. Their combined stopped mean fits one opaqueRate per opaque query. -/
theorem conditioned_cost_mean_le (residual : Tagged → Residual) (opaqueRate : ℚ) (positive : 0 ≤ opaqueRate)
    (parentBound : ParameterBounds.parentBudget c.n c.k c.s c.t c.activeCutoff c.activeList ≤ opaqueRate)
    (guessFits : (2*Q : ℚ)/2^256 ≤ opaqueRate) :
    letI : Fintype E.Value := valueFinite
    letI : Fintype Name := inferInstance
    (∑ H : Tagged → Digest × E.Answer, costOf residual H) / Fintype.card (Tagged → Digest × E.Answer) ≤
      opaqueRate * ((∑ H : Tagged → Digest × E.Answer, (((auditTree residual).run H).1.2 : ℚ)) /
        Fintype.card (Tagged → Digest × E.Answer)) := by
  letI : Fintype E.Value := valueFinite
  letI : Fintype Name := inferInstance
  letI : Nonempty E.Answer := ⟨E.cfg.fallback⟩
  apply Survival.StoppedCharges.combined_mean_le (charges residual) (auditSafe residual) marked
    LfzkV2.Current.Soundness.RuntimeRoles.auxiliary Survival.CausalCharges.advance _ opaqueRate positive
  · exact stopped_backend_budget_le E fits D L prog inputs residual opaqueRate parentBound
  · have hashMean := stopped_hash_sum_le E fits D L prog inputs queries residual
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

include inputs in
theorem stopped_failure_cover (residual : Tagged → Residual) (H : Tagged → Digest × E.Answer)
    (failed : decision (viewOf residual H) = true ∧ failsView (viewOf residual H))
    (noHash : ¬hashBad (viewOf residual H)) :
    ((auditTree residual).run H).1.1 = true ∨
      1 ≤ (Survival.StoppedCharges.restrict (charges residual) marked).charge (auditTree residual) H +
        hashOf (auditTree residual) H := by
  by_cases escapedNow : ((auditTree residual).run H).1.1 = true
  · exact Or.inl escapedNow
  · right
    have survived : ((auditTree residual).run H).1.1 = false := Bool.eq_false_iff.mpr escapedNow
    rcases Soundness.Recovery.accepted_recovery_or_hash E.binary E.prime E.P E.R E.repr E.shape E.fingerprint (E.ideal) E.binaryCount E.metadata
      fits E.columnsFit D.execution.sample E.primeCount E.draw prog.tree inputs.bodyFits (namedH residual H) failed.1 with ready | charged | exception
    · have paid := recovered_stopped_charge E fits D L prog inputs
        residual H failed.1 ready failed.2 survived
      exact paid.trans (le_add_of_nonneg_right (stopped_hash_nonneg E fits D L prog inputs residual H))
    · have same := stopped_hashCost_eq E fits D L prog inputs residual H survived
      have paid : 1 ≤ hashOf (auditTree residual) H := by rw [same]; exact charged
      exact paid.trans (le_add_of_nonneg_left
        ((Survival.StoppedCharges.restrict (charges residual) marked).charge_nonneg (auditTree residual) H))
    · exact (noHash exception).elim

include inputs in
/-- One actual runtime failure is covered by the raw exception, first
transparent escape, or the same stoppedCost used by both probability bounds. -/
theorem stopped_failure_indicator (residual : Tagged → Residual) (H : Tagged → Digest × E.Answer) :
    (if acceptedFailure (viewOf residual H) then (1 : ℚ) else 0) ≤
      (if hashBad (viewOf residual H) then 1 else 0) +
      (if ((auditTree residual).run H).1.1 = true then 1 else 0) + costOf residual H := by
  have bound := Survival.FiniteCover.indicator_cover
    (fun H => acceptedFailure (viewOf residual H)) (fun H => hashBad (viewOf residual H))
    (fun H => ((auditTree residual).run H).1.1 = true) (costOf residual)
    (stoppedCost_nonneg E fits D L prog inputs residual)
    (stopped_failure_cover E fits D L prog inputs residual) H
  convert bound using 1 <;> split_ifs <;> rfl

end LfzkV2.Current.Soundness.Runtime
