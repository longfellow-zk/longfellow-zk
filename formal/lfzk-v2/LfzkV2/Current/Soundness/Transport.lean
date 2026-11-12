import LfzkV2.Current.Protocol.Execution
import LfzkV2.Current.Soundness.Setup
import LfzkV2.Current.Protocol.Sampling
import LfzkV2.Current.Soundness.LocalCharges
import LfzkV2.Current.StrandDecoder
import LfzkV2.Current.Soundness.Recovery
import LfzkV2.Current.Soundness.RuntimeFresh

/-! Transport and recovered-path algebra for the numbered-strand runtime.
The shared definitions in this module retain the original SHA execution,
commitment cut and complete verifier decision. Stopped-cost assembly and the
exported soundness theorem live in `Current.Soundness.Runtime`. -/
noncomputable section
namespace LfzkV2.Current.Soundness.Runtime
open Application ApplicationSetup CanonicalPrefix QueryRuntime RecursivePolygero
open Finset Bcs.FiniteProbability Merkle Merkle.Indexed Merkle.RandomOracle TranscriptV2
open Protocol.Sampling
open scoped Classical
attribute [local instance] Protocol.Sampling.answerFintype Protocol.Sampling.valuesFintype

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

omit [∀ side, Fintype (fields side)] [Fintype Advice]
  [Inhabited (Fin c.n × MerkleNonce)] leafDefault in
theorem normalize_eq (fallback answer : E.Answer) (point : E.Point) :
    StrandSampling.normalize (E.factor point) fallback answer =
      Soundness.LocalCharges.normalize c E.binary E.prime E.P E.R E.countBinary E.countPrime E.binaryCapacity E.primeCapacity
        E.roleFits fallback answer point := by
  cases point with
  | round index history block => rfl
  | finalSeal history body => rfl

local instance idealLeafInhabited : Inhabited (Joint.Pair.family
    (E.P.indexed (E.ideal).countBinary).participant (E.R.indexed (E.ideal).countPrime).participant).Leaf := leafDefault
local instance runtimeLeafInhabited : Inhabited (RuntimeVerifier.Family E.binary E.prime E.P E.R (E.wire)).Leaf := by
  change Inhabited (Joint.Pair.family (E.P.indexed E.countBinary).participant (E.R.indexed E.countPrime).participant).Leaf
  infer_instance

local notation "names" => Soundness.OracleTransport.queryCodec E.binary E.prime E.P E.R E.repr E.shape E.fingerprint (E.ideal) E.binaryCount E.metadata
  fits D.execution.sample E.merkleCodec id prog.tree
local notation "Other" => Soundness.OracleTransport.other E.binary E.prime E.P E.R E.repr E.shape E.fingerprint (E.ideal) E.binaryCount E.metadata fits
  D.execution.sample E.merkleCodec id prog.tree
local notation "Node" => StrandWindow.Node (Other)
local notation "Name" => StrandSearch.Name Node E.Value
local notation "Tagged" => E.Point ⊕ Name
local notation "Row" => Strand.Word → Digest
local notation "Residual" => Fin (Fintype.card Row)

/-- This pointwise bijection retains the complete physical row, including
rejected and unused bytes. All participants' values within a role are one
joint factor. Auxiliary queries retain their full row as residual data. -/
def coordinateSplit (point : Tagged) : (Row × E.Answer) ≃ E.Answer × Residual := by
  letI : ∀ point : E.Point, Nonempty (E.RoleValue point) := fun point => ⟨(E.factor point E.cfg.fallback).1⟩
  exact StrandSampling.taggedEquiv (Aux := Name) E.factor (fun point row => ((D.sample point).run row).1)
    L.fiber L.uniform point

local notation "split" => coordinateSplit E fits D L prog

/-- Pull the inverse coordinate map back to the original named SHA
execution, discarding only the independent analysis padding. -/
def namedOracle (residual : Tagged → Residual) (H : Tagged → Digest × E.Answer) (name : Name) : Digest × Row :=
  let answer := ((StrandSampling.oracleEquiv split).symm (H,residual)) ((names).tag name)
  (answer.1,answer.2.1)

local notation "namedH" => namedOracle E fits D L prog

def shaOracle (residual : Tagged → Residual) (H : Tagged → Digest × E.Answer) : Strand.Oracle :=
  Soundness.OracleTransport.rawSHA E.binary E.prime E.P E.R E.repr E.shape E.fingerprint (E.ideal) E.binaryCount E.metadata fits D.execution.sample E.merkleCodec id prog.tree
    (Soundness.OracleTransport.completion E.binary E.prime E.P E.R E.repr E.shape E.fingerprint (E.ideal) E.binaryCount E.metadata fits D.execution.sample E.merkleCodec id prog.tree
      (namedH residual H))

local notation "SHAof" => shaOracle E fits D L prog
local notation "logical" => Soundness.LocalCharges.logicalOracle c E.binary E.prime E.P E.R E.countBinary E.countPrime E.binaryCapacity E.primeCapacity
  E.roleFits E.cfg.fallback
local notation "ordinary" => StrandVerifier.oracle E.binary E.prime E.P E.R (E.wire) E.bodyCodec D.execution.sample
local notation "actualVerify" => StrandVerifier.verify E.binary E.prime E.P E.R (E.wire) (E.earlier) E.bodyCodec D.execution.sample
  E.hashPublic E.primePublic E.draw E.merkleCodec

omit [∀ side, Fintype (fields side)] [Fintype Advice]
  [Inhabited (Fin c.n × MerkleNonce)] leafDefault in
theorem normalizedOracle_eq {Raw T : Type} (fallback : E.Answer)
    (H : (E.Point ⊕ StrandSearch.Name Raw T) → Digest × E.Answer) :
    StrandDecoder.normalizedOracle E.factor fallback (fun point => H (.inl point)) =
      Soundness.LocalCharges.logicalOracle c E.binary E.prime E.P E.R E.countBinary E.countPrime E.binaryCapacity E.primeCapacity
        E.roleFits fallback H := by
  funext point
  exact Prod.ext rfl (normalize_eq E fallback (H (.inl point)).2 point)

/-- The same named search used by the physical realization, before its
complete verifier replay. This is the extractor's query-counted prefix. -/
def searchTree :=
  StrandReplay.search (StrandRuntime.Runtime.schema E.repr E.shape E.fingerprint E.binary.nPublic)
    (StrandWindow.Node.bytes (other := Other))
    (mapQueries (StrandWindow.decode (Other)
      (Soundness.OracleTransport.fallback E.binary E.prime E.P E.R E.repr E.shape E.fingerprint (E.ideal) E.binaryCount E.metadata fits D.execution.sample E.merkleCodec id prog.tree)) prog.tree)

local notation "search" => searchTree E fits D prog

/-- At fixed residual randomness only the answer coordinates change; the
underlying adversarial branches and query count remain the original ones. -/
def analysisTree (residual : Tagged → Residual) :=
  StrandSampling.reindex split residual (mapQueries (names).tag (Soundness.Coordinates.pad (Extra := E.Answer) (search)))

local notation "analysis" => analysisTree E fits D L prog
/-- Coordinate padding and role sampling retain the original search's
fresh-query property; a recovered path is never independently resampled. -/
theorem analysis_fresh (residual : Tagged → Residual) :
    FreshOracle.FreshFrom (fun _ => False) (analysis residual) := by
  unfold analysisTree
  apply LfzkV2.Current.Soundness.RuntimeFresh.reindex_fresh
  apply LfzkV2.Current.Soundness.RuntimeFresh.mapQueries_fresh (names).tag (names).tag_injective
  apply LfzkV2.Current.Soundness.RuntimeFresh.pad_fresh
  exact LfzkV2.Current.Soundness.RuntimeFresh.replay_search_fresh
    (StrandRuntime.Runtime.schema E.repr E.shape E.fingerprint E.binary.nPublic)
    (StrandWindow.Node.bytes (other := Other)) _

/-- The extractor uses exactly the physical stopped cut, with its actual
node digests. Independent sampler padding cannot add commitment evidence. -/
theorem cut_eq (residual : Tagged → Residual) (H : Tagged → Digest × E.Answer)
    (target : FingerprintPrefix.Key E.binary.nPublic) :
    Soundness.LocalCharges.trace (names) Input.context E.context (analysis residual) H target =
      StrandCut.trace E.context (search) (namedH residual H) target := by
  exact Soundness.LocalCharges.trace_physical (names) Input.context E.context split residual (search) H target
    (Soundness.OracleTransport.queryCodec_label E.binary E.prime E.P E.R E.repr E.shape E.fingerprint (E.ideal) E.binaryCount E.metadata fits D.execution.sample E.merkleCodec id prog.tree)

/-- Causal one-answer tests use the original prefix directly. Their state
does not depend on a future query answer or on a completed prefix oracle. -/
def causalProof :=
  Soundness.LocalCharges.causalCharges c E.binary E.prime E.P E.R E.countBinary E.countPrime E.binaryCapacity E.primeCapacity (E.wire)
    E.roleFits inputs.layout E.degreeFits E.rowsFit inputs.bitsFit E.hashPublic E.primePublic
    E.primePlan E.primeGeometry E.primeFits E.binaryPlan E.binaryGeometry E.binaryFits
    (names) E.context E.merkleCodec E.merkleDecoders FingerprintPrefix.Key.root (StrandWindow.Node.bytes (other := Other))
    (default,E.cfg.fallback)

/-- The current runtime's local algebraic proof on the actual transformed
search. Both fields use the one tuple extracted from this search's cut. -/
def localProof (residual : Tagged → Residual) :=
  Soundness.LocalCharges.localProof c E.binary E.prime E.P E.R E.countBinary E.countPrime E.binaryCapacity E.primeCapacity (E.wire)
    E.roleFits inputs.layout E.degreeFits E.rowsFit inputs.bitsFit E.hashPublic E.primePublic
    E.primePlan E.primeGeometry E.primeFits E.binaryPlan E.binaryGeometry E.binaryFits
    (names) E.context E.merkleCodec E.merkleDecoders FingerprintPrefix.Key.root (StrandWindow.Node.bytes (other := Other))
    (analysis residual) E.cfg.fallback

local notation "charges" => localProof E fits D L prog inputs

/-- Shared role accounting uses the maximum local charge across the whole
protocol, including the adjacent joint-backend pair. -/
theorem budget_le (residual : Tagged → Residual) (point : Tagged) :
    (charges residual).budget point ≤
      Sum.elim (fun _ => 2/((Adapter.Mdoc.binaryOrder-1:ℕ):ℚ)) (fun _ => 0) point := by
  have bound := Soundness.LocalCharges.localProof_budget_le c E.binary E.prime E.P E.R E.countBinary E.countPrime E.binaryCapacity E.primeCapacity (E.wire)
    E.roleFits inputs.layout E.degreeFits E.rowsFit inputs.bitsFit E.hashPublic E.primePublic
    E.primePlan E.primeGeometry E.primeFits E.binaryPlan E.binaryGeometry E.binaryFits
    (names) E.context E.merkleCodec E.merkleDecoders FingerprintPrefix.Key.root (StrandWindow.Node.bytes (other := Other))
    (analysis residual) E.cfg.fallback point
  convert bound using 1
  unfold Composition.LocalCharges.budget localProof
  congr 1
  apply Finset.sum_congr rfl
  intro parent member
  split_ifs <;> rfl

theorem single_budget_le (residual : Tagged → Residual) (point : Tagged) :
    (charges residual).singleBudget point ≤ 2/((Adapter.Mdoc.binaryOrder-1:ℕ):ℚ) := by
  letI : Nonempty E.Answer := ⟨E.cfg.fallback⟩
  have bounded := budget_le E fits D L prog inputs residual point
  apply (Survival.StoppedCharges.singleBudget_le_budget (charges residual) point).trans
  cases point with
  | inl _ => exact bounded
  | inr _ => exact bounded.trans (by norm_num [Adapter.Mdoc.binaryOrder])

local notation "tupleAt" => Soundness.LocalCharges.cutOracle (names) Input.context E.context E.First E.Second E.merkleCodec E.merkleDecoders
  FingerprintPrefix.Key.root (StrandWindow.Node.bytes (other := Other))

/-- The concrete extractor retains the original byte-valued Merkle codec.
Its table consists exactly of the finite search's actual node inputs. -/
theorem cutOracle_eq (residual : Tagged → Residual) (H : Tagged → Digest × E.Answer)
    (target : FingerprintPrefix.Key E.binary.nPublic) :
    tupleAt (analysis residual) H target = Joint.Pair.oracleEquiv E.First E.Second
      ((Joint.Pair.family E.First E.Second).indexedOracle E.merkleDecoders target.root
        ((StrandCut.trace E.context (search) (namedH residual H) target).map fun entry => (entry.1.val.val,entry.2))) := by
  unfold Soundness.LocalCharges.cutOracle
  rw [cut_eq]

def authentication (residual : Tagged → Residual) (output : E.Output) (H : Tagged → Digest × E.Answer)
    (decoded : RuntimeVerifier.Decoded E.binary E.prime E.P E.R (E.wire)) :=
  Soundness.LocalCharges.authentication c E.binary E.prime E.P E.R E.countBinary E.countPrime E.binaryCapacity E.primeCapacity (E.wire)
    (names) E.context E.merkleCodec E.merkleDecoders FingerprintPrefix.Key.root (StrandWindow.Node.bytes (other := Other))
    (analysis residual) (E.earlier) output H decoded

local notation "auth" => authentication E fits D L prog

local notation "View" => Protocol.Execution.View E.Output ((E.Output × Chain.State (E.chain)) × Digest)
  (FingerprintPrefix.Key E.binary.nPublic)
local notation "decodeView" => Protocol.Observation.decoded E.binary E.prime E.P E.R (E.wire) (E.earlier) E.bodyCodec D.execution.sample
  E.hashPublic E.primePublic E.draw
local notation "decision" => Protocol.Observation.decision E.binary E.prime E.P E.R (E.wire) (E.earlier) E.bodyCodec D.execution.sample E.merkleCodec id
  E.hashPublic E.primePublic E.draw
local notation "observe" => Soundness.OracleTransport.observe E.binary E.prime E.P E.R E.repr E.shape E.fingerprint (E.ideal) E.binaryCount E.metadata
  fits D.execution.sample E.merkleCodec id prog.tree
local notation "sourceView" => fun K => observe (Prod.fst (Tree.run (search) K)) K
local notation "recovered" => Soundness.Recovery.recovered E.binary E.prime E.P E.R E.repr E.shape E.fingerprint (E.ideal) E.binaryCount E.metadata
  fits E.columnsFit D.execution.sample E.primeCount E.draw prog.tree inputs.bodyFits
local notation "sourcePath" => Soundness.OracleTransport.path E.binary E.prime E.P E.R E.repr E.shape E.fingerprint (E.ideal) E.binaryCount E.metadata
  inputs.bodyFits fits D.execution.sample E.merkleCodec id prog.tree
local notation "pathOf" => fun residual H index =>
  (Sum.inl (Chain.point (E.chain) (Prod.fst (Tree.run prog.tree (SHAof residual H)))
    (ordinary (SHAof residual H)) index) : Tagged)
local notation "encodings" => RuntimeAdaptiveVerifier.encodings E.binary E.prime E.P E.R (E.wire) (E.earlier)

local notation "viewOf" => fun residual H => sourceView (namedH residual H)

theorem observation_decoded (residual : Tagged → Residual) (H : Tagged → Digest × E.Answer) :
    decodeView (viewOf residual H) =
      RuntimeAdaptiveVerifier.decode E.binary E.prime E.P E.R (E.wire) (E.earlier) E.hashPublic E.primePublic E.draw
        (prog.tree.run (SHAof residual H)).1 (ordinary (SHAof residual H)) := by
  refine (congrArg (decodeView) (Soundness.OracleTransport.observe_actual E.binary E.prime E.P E.R E.repr E.shape E.fingerprint (E.ideal) E.binaryCount E.metadata
    fits D.execution.sample E.merkleCodec id prog.tree (namedH residual H))).trans ?_
  exact Protocol.Observation.decoded_actual E.binary E.prime E.P E.R (E.wire) (E.earlier) E.bodyCodec D.execution.sample E.merkleCodec id
    E.hashPublic E.primePublic E.draw _ _ _ _

theorem observation_decision (residual : Tagged → Residual) (H : Tagged → Digest × E.Answer) :
    decision (viewOf residual H) = actualVerify (SHAof residual H) id (prog.tree.run (SHAof residual H)).1 := by
  refine (congrArg (decision) (Soundness.OracleTransport.observe_actual E.binary E.prime E.P E.R E.repr E.shape E.fingerprint (E.ideal) E.binaryCount E.metadata
    fits D.execution.sample E.merkleCodec id prog.tree (namedH residual H))).trans ?_
  exact Protocol.Observation.decision_actual E.binary E.prime E.P E.R (E.wire) (E.earlier) E.bodyCodec D.execution.sample E.merkleCodec id
    E.hashPublic E.primePublic E.draw _ _ _ _

include inputs in
/-- On the recovered path, physical sampling and the normalized ideal
decoder use the same numbered rows. -/
theorem accepted_decoded (residual : Tagged → Residual) (H : Tagged → Digest × E.Answer)
    (accepted : decision (viewOf residual H) = true)
    (ready : recovered (namedH residual H)) :
    ∃ decoded,
      decodeView (viewOf residual H) = some decoded ∧
      RuntimeAdaptiveVerifier.decode E.binary E.prime E.P E.R (E.wire) (E.earlier) E.hashPublic E.primePublic E.draw
        (prog.tree.run (SHAof residual H)).1 (logical H) = some decoded ∧
      StrandVerifier.Checks E.binary E.prime E.P E.R (E.wire) (E.earlier) E.bodyCodec D.execution.sample E.merkleCodec (SHAof residual H) id
        (prog.tree.run (SHAof residual H)).1 decoded ∧
      ∀ i ≤ g.roles.length,
        (E.chain).point (prog.tree.run (SHAof residual H)).1 (ordinary (SHAof residual H)) i =
          (E.chain).point (prog.tree.run (SHAof residual H)).1 (logical H) i := by
  letI : ∀ point : E.Point, Nonempty (E.RoleValue point) := fun point => ⟨(E.factor point E.cfg.fallback).1⟩
  let SHA := SHAof residual H
  let output := (prog.tree.run SHA).1
  let original := namedH residual H
  rw [observation_decision] at accepted
  obtain ⟨decoded,found,checks⟩ := (StrandVerifier.verify_true_iff E.binary E.prime E.P E.R (E.wire) (E.earlier)
    E.bodyCodec D.execution.sample E.hashPublic E.primePublic E.draw E.merkleCodec SHA id output).mp accepted
  have rows i (within : i ≤ g.roles.length) := ready.2.1 i within
  have outputEq : (sourceView original).original.1 = output :=
    congrArg (fun view : View => view.original.1) (Soundness.OracleTransport.observe_actual E.binary E.prime E.P E.R
      E.repr E.shape E.fingerprint (E.ideal) E.binaryCount E.metadata fits D.execution.sample E.merkleCodec id prog.tree original)
  have tags i (within : i ≤ g.roles.length) :=
    Soundness.OracleTransport.tag_path E.binary E.prime E.P E.R E.repr E.shape E.fingerprint (E.ideal) E.binaryCount E.metadata inputs.bodyFits fits
      D.execution.sample E.merkleCodec id prog.tree ((search).run original).1 original i within
  have same := StrandDecoder.decode_and_path E.binary E.prime E.P E.R (E.wire) (E.earlier) E.bodyCodec E.factor D.sample L.fiber L.uniform
    E.hashPublic E.primePublic E.draw output SHA (fun point => H (.inl point)) (fun point => residual (.inl point))
    (by
      intro i
      have link := (rows i.val i.isLt.le).1
      change SHA (StrandRuntime.history E.bodyCodec
        ((E.chain).point (sourceView original).original.1 (ordinary SHA) i.val)).input.encode =
        (H ((names).tag (sourcePath ((search).run original).1 original i.val))).1 at link
      rw [outputEq,tags i.val i.isLt.le] at link
      exact link)
    (by
      intro i
      have row := (rows i.val i.isLt.le).2
      let point := (E.chain).point (sourceView original).original.1 (ordinary SHA) i.val
      change (fun counter => SHA (Strand.Input.prf (StrandRuntime.history E.bodyCodec point).id
        (SHA (StrandRuntime.history E.bodyCodec point).input.encode) counter).encode) =
        ((split ((names).tag (sourcePath ((search).run original).1 original i.val))).symm
          ((H ((names).tag (sourcePath ((search).run original).1 original i.val))).2,
            residual ((names).tag (sourcePath ((search).run original).1 original i.val)))).1 at row
      dsimp only [point] at row
      rw [outputEq,tags i.val i.isLt.le] at row
      exact row)
    checks.1
  rw [normalizedOracle_eq] at same
  rw [observation_decoded]
  exact ⟨decoded,found,same.1.symm.trans found,checks,same.2⟩

local notation "keyOf" => fun (output : E.Output) => Replay.Encoding.context
  (encodings (RuntimeAdaptive.Output.request output)) (RuntimeAdaptive.Output.proof output)

/-- Selection reads the original commitment cut of the observed proof. -/
def viewAuthentication (view : View) (decoded : RuntimeVerifier.Decoded E.binary E.prime E.P E.R (E.wire)) :=
  ZkJoint.authenticate decoded.statement
    (Protocol.Observation.extracted E.First E.Second E.merkleCodec E.merkleDecoders FingerprintPrefix.Key.root view (keyOf view.original.1))
    decoded.coin (RuntimeVerifier.responses E.binary E.prime E.P E.R (E.wire) view.original.1.proof) c.cutoff

local notation "viewAuth" => viewAuthentication E

/-- Failure concerns the witness selected from the original commitment cut. -/
def extractionFails (view : View) : Prop :=
  ∃ decoded, decodeView view = some decoded ∧
    ¬ ∃ witness, (viewAuth view decoded).context.extract = some witness ∧ decoded.application.True witness

local notation "failsView" => extractionFails E D

theorem viewAuthentication_eq (residual : Tagged → Residual) (H : Tagged → Digest × E.Answer)
    (decoded : RuntimeVerifier.Decoded E.binary E.prime E.P E.R (E.wire)) :
    viewAuth (viewOf residual H) decoded = auth residual (prog.tree.run (SHAof residual H)).1 H decoded := by
  refine (congrArg (fun view : View => viewAuth view decoded)
    (Soundness.OracleTransport.observe_actual E.binary E.prime E.P E.R E.repr E.shape E.fingerprint (E.ideal) E.binaryCount E.metadata
      fits D.execution.sample E.merkleCodec id prog.tree (namedH residual H))).trans ?_
  simp only [viewAuthentication,Protocol.Observation.extracted,authentication,Soundness.LocalCharges.authentication]
  rw [cutOracle_eq]
  rfl

include inputs in
/-- Agreement on the opened columns transfers the backend checks to the
tuple used by witness selection, even for an incomplete extracted tree. -/
theorem authenticated (residual : Tagged → Residual) (H : Tagged → Digest × E.Answer)
    (decoded : RuntimeVerifier.Decoded E.binary E.prime E.P E.R (E.wire))
    (found : decodeView (viewOf residual H) = some decoded)
    (checks : StrandVerifier.Checks E.binary E.prime E.P E.R (E.wire) (E.earlier) E.bodyCodec D.execution.sample E.merkleCodec (SHAof residual H) id
      (prog.tree.run (SHAof residual H)).1 decoded)
    (ready : recovered (namedH residual H)) :
    let a := auth residual (prog.tree.run (SHAof residual H)).1 H decoded
    JointResponse.Verify E.First E.Second a.statement a.oracle a.coin a.response decoded.query := by
  let output := (prog.tree.run (SHAof residual H)).1
  let key := keyOf output
  let cut := (StrandCut.trace E.context (search) (namedH residual H) key).map fun qa =>
    (StrandWindow.Node.bytes qa.1,qa.2)
  have agrees : ∀ column ∈ decoded.claim.I, messages E.merkleDecoders cut key.root c.n column = decoded.claim.a column := by
    intro column opened
    by_contra different
    apply ready.2.2
    refine ⟨decoded,found,column,opened,fun equal => different ?_⟩
    have same := congrArg (fun view : View => messages E.merkleDecoders (view.cuts (keyOf view.original.1))
      (keyOf view.original.1).root c.n column)
      (Soundness.OracleTransport.observe_actual E.binary E.prime E.P E.R E.repr E.shape E.fingerprint (E.ideal) E.binaryCount E.metadata
        fits D.execution.sample E.merkleCodec id prog.tree (namedH residual H))
    exact same.symm.trans equal
  have verified := (Joint.Pair.family E.First E.Second).verify_of_indexedAgreement E.merkleDecoders (E.wire).openingPositive
    ((E.merkleCodec).withOracle (SHAof residual H)) ((Joint.Pair.statementEquiv E.First E.Second).symm decoded.statement.statement)
    key.root cut ((Joint.Pair.coinEquiv E.First E.Second).symm decoded.coin)
    ((Joint.Pair.responseEquiv E.First E.Second).symm (RuntimeVerifier.responses E.binary E.prime E.P E.R (E.wire) output.proof))
    decoded.query decoded.claim agrees checks.2.2.2.1
  change JointResponse.Verify E.First E.Second decoded.statement.statement
    (tupleAt (analysis residual) H key) decoded.coin (RuntimeVerifier.responses E.binary E.prime E.P E.R (E.wire) output.proof) decoded.query
  rw [cutOracle_eq]
  exact (Joint.Pair.verify_iff E.First E.Second _ _ _ _ _).mp verified

include inputs in
/-- An accepting recovered execution whose selected witness fails the
application incurs a charge on the actual ordinary transcript path. -/
theorem accepted_cover (residual : Tagged → Residual) (H : Tagged → Digest × E.Answer)
    (accepted : decision (viewOf residual H) = true) (ready : recovered (namedH residual H))
    (failed : failsView (viewOf residual H)) :
    (charges residual).Covers (rounds := g.roles.length) (pathOf residual H) H := by
  obtain ⟨decoded,found,decodedCorrect,checks,path⟩ := accepted_decoded E fits D L prog inputs residual H accepted ready
  have verified := authenticated E fits D L prog inputs residual H decoded found checks ready
  obtain ⟨observed,read,failed⟩ := failed
  have same : observed = decoded := Option.some.inj (read.symm.trans found)
  subst observed
  rw [viewAuthentication_eq] at failed
  have covered := Soundness.LocalCharges.decoded_cover c E.binary E.prime E.P E.R E.countBinary E.countPrime E.binaryCapacity E.primeCapacity
    (E.wire) E.roleFits inputs.layout E.degreeFits E.rowsFit inputs.bitsFit E.hashPublic E.primePublic
    E.primePlan E.primeGeometry E.primeFits E.binaryPlan E.binaryGeometry E.binaryFits
    (names) E.context E.merkleCodec E.merkleDecoders FingerprintPrefix.Key.root (StrandWindow.Node.bytes (other := Other))
    (analysis residual) (E.earlier) inputs.layoutCorrect E.cfg.fallback (prog.tree.run (SHAof residual H)).1 H decoded
    decodedCorrect verified failed
  rcases covered with ⟨index,bounded,charged⟩ | ⟨index,bounded,parent,response,atParent,atChild,charged⟩
  · refine Or.inl ⟨index,bounded,?_⟩
    dsimp only
    rw [path index bounded.le]
    exact charged
  · refine Or.inr ⟨index,bounded,parent,response,?_,?_,charged⟩
    · dsimp only
      rw [path index bounded.le]
      exact atParent
    · dsimp only
      rw [path (index+1) (Nat.succ_le_of_lt bounded)]
      exact atChild

theorem analysis_seen (residual : Tagged → Residual) (H : Tagged → Digest × E.Answer) :
    seen (analysis residual) H = (seen (search) (namedH residual H)).image (names).tag :=
  Soundness.Coordinates.coordinates_seen (names).tag split residual (search) H

include inputs in
theorem analysis_path (residual : Tagged → Residual) (H : Tagged → Digest × E.Answer)
    (ready : recovered (namedH residual H)) :
    Composition.PathQueries (rounds := g.roles.length) (analysis residual) H (pathOf residual H) := by
  let original := namedH residual H
  let cut := ((search).run original).1
  have tags i (within : i ≤ g.roles.length) :
      (names).tag (sourcePath cut original i) = pathOf residual H i :=
    Soundness.OracleTransport.tag_path E.binary E.prime E.P E.R E.repr E.shape E.fingerprint (E.ideal) E.binaryCount E.metadata inputs.bodyFits fits
      D.execution.sample E.merkleCodec id prog.tree cut original i within
  constructor
  · intro i within
    rw [analysis_seen,← tags i within]
    exact Finset.mem_image.mpr ⟨_,ready.1.queried i within,rfl⟩
  · intro i within
    rw [← tags i within.le,← tags (i+1) (Nat.succ_le_of_lt within)]
    have same := StrandSampling.reindex_firstOfTwo split residual
      (mapQueries (names).tag (Soundness.Coordinates.pad (Extra := E.Answer) (search))) H
      ((names).tag (sourcePath cut original i)) ((names).tag (sourcePath cut original (i+1)))
    rw [Composition.firstOfTwo_mapQueries (names).tag (names).tag_injective,Soundness.Coordinates.pad_order] at same
    exact same.trans (ready.1.ordered i within)

end LfzkV2.Current.Soundness.Runtime
