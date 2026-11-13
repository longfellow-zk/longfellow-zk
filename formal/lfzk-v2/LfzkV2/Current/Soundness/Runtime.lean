import LfzkV2.Current.Protocol.Execution
import LfzkV2.Current.Soundness.Setup
import LfzkV2.Current.StrandDomains
import LfzkV2.Current.Soundness.StoppedCosts
import Survival.HistoryBounds

/-! Two composition methods on the same derived runtime stopped cost and
failure cover: unrestricted leading linear accounting, then optional W
saturation. Residual averaging and raw SHA realization follow these core
bounds; concrete profile arithmetic lives in the mdoc endpoint layer. -/
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
local notation "viewOf" => fun residual H => sourceView (namedH residual H)
local notation "failsView" => extractionFails E D
local notation "marked" => (LfzkV2.Current.Soundness.RuntimeRoles.marked (Aux := Name) g.batchingIndex : Tagged → Bool)
local notation "causal" => causalProof E fits D prog inputs
local notation "hashBad" => Soundness.Recovery.hashException E.binary E.prime E.P E.R E.repr E.shape E.fingerprint (E.ideal) E.binaryCount E.metadata
  E.columnsFit D.execution.sample E.primeCount E.draw
local notation "costOf" => stoppedCost E fits D L prog inputs
local notation "valueFinite" => Fintype.ofInjective
  (QueryRuntime.Runtime.toPoint E.repr E.shape E.fingerprint E.binary.nPublic)
  (QueryRuntime.Runtime.toPoint_injective E.repr E.shape E.fingerprint E.binary.nPublic fits)
local notation "ordinaryRate" => (2/((Adapter.Mdoc.binaryOrder-1:ℕ):ℚ))
variable {Q : ℕ} (queries : ∀ SHA : Bytes → Digest, (seen prog.tree SHA).card ≤ Q)
local notation "acceptedFailure" => fun (view : View) => decision view = true ∧ failsView view

/-- Uniform sampler coordinates preserve the law of events on the original
grouped oracle, including its query-counting events. -/
theorem named_event_average (event : (Name → Digest × Row) → Prop) :
    letI : Fintype E.Value := valueFinite
    letI : Fintype Name := inferInstance
    density event = (∑ residual : Tagged → Residual, density (fun H : Tagged → Digest × E.Answer =>
      event (namedH residual H))) / Fintype.card (Tagged → Residual) := by
  letI : Nonempty E.Answer := ⟨E.cfg.fallback⟩
  letI : Fintype E.Value := valueFinite
  letI : Fintype Name := inferInstance
  exact Soundness.Coordinates.event_average (names).tag (names).tag_injective split event
include inputs queries L in
/-- Leading shared-query bound on the same runtime cover and retained cost.
It does not assume `ordinaryRate * Q ≤ 1` or use the saturated potential. -/
theorem conditioned_linear_failure_le (residual : Tagged → Residual) (opaqueRate : ℚ)
    (nonnegative : 0 ≤ opaqueRate) (atMostRate : opaqueRate ≤ ordinaryRate)
    (parentBound : ParameterBounds.parentBudget c.n c.k c.s c.t c.activeCutoff c.activeList ≤ opaqueRate)
    (guessFits : (2*Q : ℚ)/2^256 ≤ opaqueRate) :
    letI : Fintype E.Value := valueFinite
    letI : Fintype Name := inferInstance
    density (fun H : Tagged → Digest × E.Answer => acceptedFailure (viewOf residual H)) ≤
      ordinaryRate*Q +
        density (fun H : Tagged → Digest × E.Answer => hashBad (viewOf residual H)) := by
  letI : Fintype E.Value := valueFinite
  letI : Fintype Name := inferInstance
  letI : Nonempty E.Answer := ⟨E.cfg.fallback⟩
  let cost := costOf residual
  have localBudget := single_budget_le E fits D L prog inputs residual
  apply Survival.CausalCharges.linear_failure_le_support (causal) marked (analysis residual)
    ordinaryRate opaqueRate (by norm_num [Adapter.Mdoc.binaryOrder]) atMostRate (fun point _ => localBudget point)
    (analysis_fresh E fits D L prog residual)
    (analysis_queries E fits D L prog queries residual)
    (fun H => acceptedFailure (viewOf residual H)) (fun H => hashBad (viewOf residual H)) cost
  · exact stoppedCost_nonneg E fits D L prog inputs residual
  · exact stopped_failure_cover E fits D L prog inputs residual
  · exact conditioned_cost_mean_le E fits D L prog inputs queries residual
      opaqueRate nonnegative parentBound guessFits

include inputs queries L in
/-- Complete runtime failure coverage at a fixed sampler residual. The hash
exception stays symbolic here: its raw bound is applied only after averaging. -/
theorem conditioned_saturated_failure_le (residual : Tagged → Residual) (opaqueFraction : ℚ)
    (nonnegative : 0 ≤ opaqueFraction) (atMostOne : opaqueFraction ≤ 1) (budget : ordinaryRate*Q ≤ 1)
    (parentBound : ParameterBounds.parentBudget c.n c.k c.s c.t c.activeCutoff c.activeList ≤ opaqueFraction*ordinaryRate)
    (guessFits : (2*Q : ℚ)/2^256 ≤ opaqueFraction*ordinaryRate) :
    letI : Fintype E.Value := valueFinite
    letI : Fintype Name := inferInstance
    density (fun H : Tagged → Digest × E.Answer => acceptedFailure (viewOf residual H)) ≤
      Survival.Hybrid.envelope ordinaryRate opaqueFraction Q +
        density (fun H : Tagged → Digest × E.Answer => hashBad (viewOf residual H)) := by
  letI : Fintype E.Value := valueFinite
  letI : Fintype Name := inferInstance
  letI : Nonempty E.Answer := ⟨E.cfg.fallback⟩
  let cost := costOf residual
  have localBudget := single_budget_le E fits D L prog inputs residual
  apply Survival.CausalCharges.failure_le_support (causal) marked (analysis residual)
    ordinaryRate opaqueFraction (by norm_num [Adapter.Mdoc.binaryOrder]) (by norm_num [Adapter.Mdoc.binaryOrder])
    nonnegative atMostOne (fun point _ => localBudget point) budget
    (analysis_fresh E fits D L prog residual)
    (analysis_queries E fits D L prog queries residual)
    (fun H => acceptedFailure (viewOf residual H)) (fun H => hashBad (viewOf residual H)) cost
  · exact stoppedCost_nonneg E fits D L prog inputs residual
  · exact stopped_failure_cover E fits D L prog inputs residual
  · exact conditioned_cost_mean_le E fits D L prog inputs queries residual
      (opaqueFraction*ordinaryRate) (mul_nonneg nonnegative (by norm_num [Adapter.Mdoc.binaryOrder])) parentBound guessFits

include inputs queries L in
/-- Average residuals before estimating the raw hash exception. Fixing a
residual is permitted for algebraic monitoring, but not for fresh seal bounds. -/
theorem named_linear_failure_le (opaqueRate : ℚ)
    (nonnegative : 0 ≤ opaqueRate) (atMostRate : opaqueRate ≤ ordinaryRate)
    (parentBound : ParameterBounds.parentBudget c.n c.k c.s c.t c.activeCutoff c.activeList ≤ opaqueRate)
    (guessFits : (2*Q : ℚ)/2^256 ≤ opaqueRate) :
    letI : Fintype E.Value := valueFinite
    letI : Fintype Name := inferInstance
    density (fun K : Name → Digest × Row => acceptedFailure (sourceView K)) ≤
      ordinaryRate*Q +
        density (fun K : Name → Digest × Row => hashBad (sourceView K)) := by
  letI : Fintype E.Value := valueFinite
  letI : Fintype Name := inferInstance
  letI : Nonempty E.Answer := ⟨E.cfg.fallback⟩
  letI : Nonempty (Tagged → Residual) := ⟨fun _ => ⟨0,Fintype.card_pos⟩⟩
  have each residual := conditioned_linear_failure_le E fits D L prog inputs queries
    residual opaqueRate nonnegative atMostRate parentBound guessFits
  have averaged := Bcs.FiniteProbability.mean_add_mul_le
    (fun residual => density (fun H : Tagged → Digest × E.Answer => acceptedFailure (viewOf residual H)))
    (fun residual => density (fun H : Tagged → Digest × E.Answer => hashBad (viewOf residual H)))
    (-1) (ordinaryRate*Q) (fun residual => by have := each residual; linarith)
  have failureLaw := named_event_average E fits D L prog (fun K => acceptedFailure (sourceView K))
  have hashLaw := named_event_average E fits D L prog (fun K => hashBad (sourceView K))
  rw [← failureLaw, ← hashLaw] at averaged
  linarith
include inputs queries L in
/-- Average residuals before estimating the raw hash exception. Fixing a
residual is permitted for algebraic monitoring, but not for fresh seal bounds. -/
theorem named_saturated_failure_le (opaqueFraction : ℚ)
    (nonnegative : 0 ≤ opaqueFraction) (atMostOne : opaqueFraction ≤ 1) (budget : ordinaryRate*Q ≤ 1)
    (parentBound : ParameterBounds.parentBudget c.n c.k c.s c.t c.activeCutoff c.activeList ≤ opaqueFraction*ordinaryRate)
    (guessFits : (2*Q : ℚ)/2^256 ≤ opaqueFraction*ordinaryRate) :
    letI : Fintype E.Value := valueFinite
    letI : Fintype Name := inferInstance
    density (fun K : Name → Digest × Row => acceptedFailure (sourceView K)) ≤
      Survival.Hybrid.envelope ordinaryRate opaqueFraction Q +
        density (fun K : Name → Digest × Row => hashBad (sourceView K)) := by
  letI : Fintype E.Value := valueFinite
  letI : Fintype Name := inferInstance
  letI : Nonempty E.Answer := ⟨E.cfg.fallback⟩
  letI : Nonempty (Tagged → Residual) := ⟨fun _ => ⟨0,Fintype.card_pos⟩⟩
  have each residual := conditioned_saturated_failure_le E fits D L prog inputs queries
    residual opaqueFraction nonnegative atMostOne budget parentBound guessFits
  have averaged := Bcs.FiniteProbability.mean_add_mul_le
    (fun residual => density (fun H : Tagged → Digest × E.Answer => acceptedFailure (viewOf residual H)))
    (fun residual => density (fun H : Tagged → Digest × E.Answer => hashBad (viewOf residual H)))
    (-1) (Survival.Hybrid.envelope ordinaryRate opaqueFraction Q) (fun residual => by have := each residual; linarith)
  have failureLaw := named_event_average E fits D L prog (fun K => acceptedFailure (sourceView K))
  have hashLaw := named_event_average E fits D L prog (fun K => hashBad (sourceView K))
  rw [← failureLaw, ← hashLaw] at averaged
  linarith
local notation "rawView" => Soundness.OracleTransport.rawView E.binary E.prime E.P E.R E.repr E.shape E.fingerprint (E.ideal) E.binaryCount E.metadata
  fits D.execution.sample E.merkleCodec id prog.tree
abbrev Raw := StrandWindow.Point (Other)

def failure (view : View) : Prop := acceptedFailure view

def verify (SHA : Bytes → Digest) (output : E.Output) : Bool := actualVerify SHA id output

def verifierReplay (output : E.Output) :=
  StrandAuthentication.replay E.binary E.prime E.P E.R (E.wire) (E.earlier) E.bodyCodec D.execution.sample E.merkleCodec id output

omit [∀ side, Fintype (fields side)] [Fintype Advice] in
theorem failure_verified (view : View) (SHA : Bytes → Digest)
    (replayed : view.verifier =
      (verifierReplay E D view.original.1).run SHA)
    (failed : failure E D view) :
    verify E D SHA view.original.1 = true := by
  have actual := Protocol.Observation.decision_of_trace E.binary E.prime E.P E.R (E.wire) (E.earlier) E.bodyCodec D.execution.sample E.merkleCodec id
    E.hashPublic E.primePublic E.draw view SHA (congrArg Prod.snd replayed)
  exact actual.symm.trans failed.1

omit [∀ side, Fintype (fields side)] [Fintype Advice] in
theorem verifierReplay_domain (output : E.Output) :
    OracleDomain.UsesOnly StrandDomains.protocol
      (verifierReplay E D output) :=
  StrandDomains.replay E.binary E.prime E.P E.R (E.wire) (E.earlier) E.bodyCodec D.execution.sample E.merkleCodec id
    (fun value => StrandDomains.of_merkle (SHAOracle.leaf_in_domain E.First E.Second E.repr
      E.cfg.binaryField E.cfg.primeField E.fingerprint.jointContext E.columnsFit value))
    (fun index value => StrandDomains.of_merkle (SHAOracle.node_in_domain E.First E.Second E.repr
      E.cfg.binaryField E.cfg.primeField E.fingerprint.jointContext E.columnsFit value index)) output

def rawObservation (G : Raw E fits D prog → Digest) := rawView G

def rawOracle (G : Raw E fits D prog → Digest) : Bytes → Digest :=
  Soundness.OracleTransport.rawSHA E.binary E.prime E.P E.R E.repr E.shape E.fingerprint (E.ideal) E.binaryCount E.metadata
    fits D.execution.sample E.merkleCodec id prog.tree G

theorem rawObservation_original (G : Raw E fits D prog → Digest) :
    (rawObservation E fits D prog G).original =
      prog.tree.run (rawOracle E fits D prog G) :=
  congrArg (fun view => view.original) (Soundness.OracleTransport.rawView_actual E.binary E.prime E.P E.R E.repr E.shape E.fingerprint (E.ideal)
    E.binaryCount E.metadata fits D.execution.sample E.merkleCodec id prog.tree G)

theorem rawObservation_verifier (G : Raw E fits D prog → Digest) :
    (rawObservation E fits D prog G).verifier =
      (verifierReplay E D (prog.tree.run
          (rawOracle E fits D prog G)).1).run
        (rawOracle E fits D prog G) :=
  congrArg (fun view => view.verifier) (Soundness.OracleTransport.rawView_actual E.binary E.prime E.P E.R E.repr E.shape E.fingerprint (E.ideal)
    E.binaryCount E.metadata fits D.execution.sample E.merkleCodec id prog.tree G)

def rawFailure (G : Raw E fits D prog → Digest) : Prop := acceptedFailure (rawView G)

end LfzkV2.Current.Soundness.Runtime
