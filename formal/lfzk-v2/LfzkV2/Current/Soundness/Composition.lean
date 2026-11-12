import LfzkV2.Current.Soundness.Runtime

/-! The complete soundness composition takes public structural setup,
a balanced sampler and an original-query-bounded adversary. Failure coverage
and stopped hash/Polygero costs are proved internally. -/
noncomputable section
namespace LfzkV2.Current.Soundness.Composition
open Application ApplicationSetup RecursivePolygero Merkle Merkle.Indexed Merkle.RandomOracle TranscriptV2 Bcs.FiniteProbability
open Soundness.Runtime
open scoped Classical
attribute [local instance] Protocol.Sampling.answerFintype Protocol.Sampling.valuesFintype
  Soundness.Runtime.idealLeafInhabited Soundness.Runtime.runtimeLeafInhabited

variable {c : CertifiedProfile} {g : Geometry} {fields : Fields} {Advice B : Type}
variable [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable [∀ side, Fintype (fields side)] [Fintype Advice]
variable {shared maskBits adviceBits blocks fuel Q : ℕ}
variable (S : Soundness.Setup c g fields Advice B (shared := shared) (maskBits := maskBits) (adviceBits := adviceBits))
variable (M : Protocol.Sampler S.protocol blocks)
variable (A : Protocol.Execution.Adversary S.protocol.Output fuel Q)
variable [Inhabited (Fin c.n × MerkleNonce)]
variable [leafDefault : Inhabited (Joint.Pair.family S.protocol.First S.protocol.Second).Leaf]

local notation "Other" => Soundness.OracleTransport.other S.protocol.binary S.protocol.prime S.protocol.P S.protocol.R S.protocol.repr S.protocol.shape S.protocol.fingerprint (S.protocol.ideal) S.protocol.binaryCount S.protocol.metadata S.fits
  M.data.execution.sample S.protocol.merkleCodec id A.toProgram.tree
local notation "Node" => StrandWindow.Node (Other)
local notation "Name" => StrandSearch.Name Node S.protocol.Value
local notation "View" => Protocol.Execution.View S.protocol.Output ((S.protocol.Output × Chain.State (S.protocol.chain)) × Digest)
  (FingerprintPrefix.Key S.protocol.binary.nPublic)
local notation "decision" => Protocol.Observation.decision S.protocol.binary S.protocol.prime S.protocol.P S.protocol.R (S.protocol.wire) (S.protocol.earlier) S.protocol.bodyCodec M.data.execution.sample S.protocol.merkleCodec id
  S.protocol.hashPublic S.protocol.primePublic S.protocol.draw
local notation "failsView" => extractionFails S.protocol M.data
local notation "valueFinite" => Fintype.ofInjective
  (QueryRuntime.Runtime.toPoint S.protocol.repr S.protocol.shape S.protocol.fingerprint S.protocol.binary.nPublic)
  (QueryRuntime.Runtime.toPoint_injective S.protocol.repr S.protocol.shape S.protocol.fingerprint S.protocol.binary.nPublic S.fits)
local notation "ordinaryRate" => (2/((Adapter.Mdoc.binaryOrder-1:ℕ):ℚ))
local notation "acceptedFailure" => fun (view : View) => decision view = true ∧ failsView view

/-- Leading linear soundness of the actual numbered-strand runtime. All execution,
prefix-state, recovery and stopped-charge facts are derived internally. The remaining
premises are explicit numerical budgets, discharged by the concrete profile.
No saturation or `ordinaryRate * Q ≤ 1` premise is used. -/
theorem soundness_linear (opaqueRate : ℚ)
    (nonnegative : 0 ≤ opaqueRate) (atMostRate : opaqueRate ≤ ordinaryRate)
    (parentBound : ParameterBounds.parentBudget c.n c.k c.s c.t c.activeCutoff c.activeList ≤ opaqueRate)
    (guessFits : (2*Q : ℚ)/2^256 ≤ opaqueRate) :
    density (rawFailure S.protocol S.fits M.data A.toProgram) ≤
        ordinaryRate*Q + Soundness.Recovery.hashCorrection Q g.roles.length c.n := by
  letI : Fintype S.protocol.Value := valueFinite
  letI : Fintype Name := inferInstance
  unfold rawFailure
  rw [Soundness.OracleTransport.observation_law S.protocol.binary S.protocol.prime S.protocol.P S.protocol.R S.protocol.repr S.protocol.shape S.protocol.fingerprint (S.protocol.ideal) S.protocol.binaryCount S.protocol.metadata S.fits
    M.data.execution.sample S.protocol.merkleCodec id A.toProgram.tree (fun view => acceptedFailure view)]
  have algebra := named_linear_failure_le S.protocol S.fits M.data M.laws A.toProgram S.inputs A.queryBound
    opaqueRate nonnegative atMostRate parentBound guessFits
  apply algebra.trans
  apply add_le_add le_rfl
  have hash := Soundness.Recovery.hashException_ratio_le S.protocol.binary S.protocol.prime S.protocol.P S.protocol.R S.protocol.repr S.protocol.shape S.protocol.fingerprint (S.protocol.ideal) S.protocol.binaryCount S.protocol.metadata S.fits
    S.protocol.columnsFit M.data.execution.sample S.protocol.primeCount S.protocol.draw A.toProgram.tree S.fallbackPath S.independent S.bindSalt S.inputs.bodyFits A.queryBound
  apply hash.trans_eq
  unfold Soundness.OracleBounds.delta Soundness.Recovery.hashCorrection
  ring

/-- Saturated soundness of the actual numbered-strand runtime. All execution,
prefix-state, recovery and stopped-charge facts are derived internally. The remaining
premises are explicit numerical budgets, discharged by the concrete profile. -/
theorem soundness (opaqueFraction : ℚ)
    (nonnegative : 0 ≤ opaqueFraction) (atMostOne : opaqueFraction ≤ 1) (budget : ordinaryRate*Q ≤ 1)
    (parentBound : ParameterBounds.parentBudget c.n c.k c.s c.t c.activeCutoff c.activeList ≤ opaqueFraction*ordinaryRate)
    (guessFits : (2*Q : ℚ)/2^256 ≤ opaqueFraction*ordinaryRate) :
    density (rawFailure S.protocol S.fits M.data A.toProgram) ≤
        Survival.Hybrid.envelope ordinaryRate opaqueFraction Q + Soundness.Recovery.hashCorrection Q g.roles.length c.n := by
  letI : Fintype S.protocol.Value := valueFinite
  letI : Fintype Name := inferInstance
  unfold rawFailure
  rw [Soundness.OracleTransport.observation_law S.protocol.binary S.protocol.prime S.protocol.P S.protocol.R S.protocol.repr S.protocol.shape S.protocol.fingerprint (S.protocol.ideal) S.protocol.binaryCount S.protocol.metadata S.fits
    M.data.execution.sample S.protocol.merkleCodec id A.toProgram.tree (fun view => acceptedFailure view)]
  have algebra := named_saturated_failure_le S.protocol S.fits M.data M.laws A.toProgram S.inputs A.queryBound
    opaqueFraction nonnegative atMostOne budget parentBound guessFits
  apply algebra.trans
  apply add_le_add le_rfl
  have hash := Soundness.Recovery.hashException_ratio_le S.protocol.binary S.protocol.prime S.protocol.P S.protocol.R S.protocol.repr S.protocol.shape S.protocol.fingerprint (S.protocol.ideal) S.protocol.binaryCount S.protocol.metadata S.fits
    S.protocol.columnsFit M.data.execution.sample S.protocol.primeCount S.protocol.draw A.toProgram.tree S.fallbackPath S.independent S.bindSalt S.inputs.bodyFits A.queryBound
  apply hash.trans_eq
  unfold Soundness.OracleBounds.delta Soundness.Recovery.hashCorrection
  ring

end LfzkV2.Current.Soundness.Composition
