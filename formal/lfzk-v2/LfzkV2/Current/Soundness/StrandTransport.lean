import LfzkV2.Current.StrandCharges
import LfzkV2.Current.StrandDecoder
import LfzkV2.Current.StrandRecovery
import LfzkV2.Current.Soundness.RuntimeFresh

/-! Transport and recovered-path algebra for the numbered-strand runtime.
The shared definitions in this module retain the original SHA execution,
commitment cut and complete verifier decision. Stopped-cost assembly and the
exported soundness theorem live in `Current.StrandProtocol`. -/
noncomputable section
namespace LfzkV2.Current.StrandProtocol
open Application ApplicationSetup CanonicalPrefix QueryRuntime RecursivePolygero
open Finset Bcs.FiniteProbability Merkle Merkle.Indexed Merkle.RandomOracle TranscriptV2
open scoped Classical

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
local notation "kind" => StrandRoleSampling.roleKind binary.degree (prime.circuit.layers+1)
local notation "RoleValue" => StrandRoleSampling.Value B N binary.Original prime.Original
  (IdealRuntime.RawBinary P countBinary) (IdealRuntime.RawPrime R countPrime) (Fin c.t ↪ Fin c.n)
local notation "RoleUnused" => StrandRoleSampling.Unused B N binary.Original prime.Original
  (IdealRuntime.RawBinary P countBinary) (IdealRuntime.RawPrime R countPrime) (Fin c.t ↪ Fin c.n)
  binaryCapacity primeCapacity

def values : Point → Type
  | .round index .. => RoleValue (kind (g.roles.get index))
  | .finalSeal .. => Answer

def unused : Point → Type
  | .round index .. => RoleUnused (kind (g.roles.get index))
  | .finalSeal .. => Unit

local instance answerFintype : Fintype Answer := by
  dsimp only [IdealRuntime.Answer,IdealSamples.Answer]
  infer_instance

local notation "Values" => values c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
local notation "Unused" => unused c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup

local instance valuesFintype (point : Point) : Fintype (Values point) := by
  cases point <;> dsimp only [values] <;> infer_instance

variable (binaryPlan : FrontendSchedule.Plan B binary.template)
variable (primePlan : FrontendSchedule.Plan N prime.circuit)
variable (binaryGeometry : binaryPlan.frontend = g.binary) (primeGeometry : primePlan.frontend = g.prime)
variable (binaryFits : binaryPlan.capacity ≤ binaryCapacity) (primeFits : primePlan.capacity ≤ primeCapacity)
variable (degreeFits : binary.degree ≤ binaryCapacity) (rowsFit : prime.circuit.layers+1 ≤ primeCapacity)
local notation "fitsRoles" => StrandRoleSampling.roleFits binaryCapacity primeCapacity g binaryPlan primePlan
  binaryGeometry primeGeometry binaryFits primeFits binary.degree (prime.circuit.layers+1) degreeFits rowsFit

/-- Only ordinary boundaries consume field samples. The final node's
identity factor is unused by the physical verifier; its seal is a raw PRF
answer, not an extra sampled field challenge. -/
def factor (point : Point) : Answer ≃ Values point × Unused point := by
  cases point with
  | round index history block =>
      exact StrandRoleSampling.factor B N binary.Original prime.Original
        (IdealRuntime.RawBinary P countBinary) (IdealRuntime.RawPrime R countPrime) (Fin c.t ↪ Fin c.n)
        binaryCapacity primeCapacity (kind (g.roles.get index)) (fitsRoles index)
  | finalSeal history body => exact (Equiv.prodUnique Answer Unit).symm

local notation "Factor" => factor c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
  binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit

omit [Fintype B] [DecidableEq B] [∀ side, Fintype (fields side)] [Fintype Advice] in
theorem normalize_eq (fallback answer : Answer) (point : Point) :
    StrandSampling.normalize (Factor point) fallback answer =
      StrandCharges.normalize c binary prime P R countBinary countPrime binaryCapacity primeCapacity
        fitsRoles fallback answer point := by
  cases point with
  | round index history block => rfl
  | finalSeal history body => rfl

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

def sampler (point : Point) : Tree Strand.Word Digest (Option Answer) blocks :=
  StrandSampling.read (Factor point) cfg.fallback (sample point)
local notation "physical" => sampler c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
  binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit cfg sample

variable (primeCount : shape.primePublic = prime.nPublic)
variable [Inhabited (Fin c.n × MerkleNonce)]
variable [leafDefault : Inhabited (Joint.Pair.family (P.indexed countBinary).participant (R.indexed countPrime).participant).Leaf]
local instance idealLeafInhabited : Inhabited (Joint.Pair.family
    (P.indexed (I).countBinary).participant (R.indexed (I).countPrime).participant).Leaf := leafDefault
local instance runtimeLeafInhabited : Inhabited (RuntimeVerifier.Family binary prime P R (W)).Leaf := by
  change Inhabited (Joint.Pair.family (P.indexed countBinary).participant (R.indexed countPrime).participant).Leaf
  infer_instance
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

/-- This pointwise bijection retains the complete physical row, including
rejected and unused bytes. All participants' values within a role are one
joint factor. Auxiliary queries retain their full row as residual data. -/
def coordinateSplit (point : Tagged) : (Row × Answer) ≃ Answer × Residual := by
  letI : ∀ point : Point, Nonempty (Values point) := fun point => ⟨(Factor point cfg.fallback).1⟩
  exact StrandSampling.taggedEquiv (Aux := Name) Factor (fun point row => ((sample point).run row).1)
    fiber uniform point

local notation "split" => coordinateSplit c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
  binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit cfg binaryCount metadata fits sample
  fiber uniform columnsFit program

/-- Pull the inverse coordinate map back to the original named SHA
execution, discarding only the independent analysis padding. -/
def namedOracle (residual : Tagged → Residual) (H : Tagged → Digest × Answer) (name : Name) : Digest × Row :=
  let answer := ((StrandSampling.oracleEquiv split).symm (H,residual)) ((names).tag name)
  (answer.1,answer.2.1)

local notation "namedH" => namedOracle c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
  binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit cfg binaryCount metadata fits sample
  fiber uniform columnsFit program

def shaOracle (residual : Tagged → Residual) (H : Tagged → Digest × Answer) : Strand.Oracle :=
  StrandRealization.rawSHA binary prime P R repr shape setup (I) binaryCount metadata fits physical codec id program
    (StrandRealization.completion binary prime P R repr shape setup (I) binaryCount metadata fits physical codec id program
      (namedH residual H))

local notation "SHAof" => shaOracle c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
  binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit cfg binaryCount metadata fits sample
  fiber uniform columnsFit program
local notation "logical" => StrandCharges.logicalOracle c binary prime P R countBinary countPrime binaryCapacity primeCapacity
  fitsRoles cfg.fallback
local notation "hashPublic" => CanonicalRequest.hashPublic binary.nPublic
local notation "primePublic" => CanonicalRuntime.decodePrimePublic binary prime P R repr shape setup (I) primeCount
local notation "ordinary" => StrandVerifier.oracle binary prime P R (W) bodyCodec physical
local notation "actualVerify" => StrandVerifier.verify binary prime P R (W) (Earlier) bodyCodec physical
  hashPublic primePublic draw codec

omit [Fintype B] [DecidableEq B] [∀ side, Fintype (fields side)] [Fintype Advice]
  [Inhabited (Fin c.n × MerkleNonce)] in
theorem normalizedOracle_eq {Raw T : Type} (fallback : Answer)
    (H : (Point ⊕ StrandSearch.Name Raw T) → Digest × Answer) :
    StrandDecoder.normalizedOracle Factor fallback (fun point => H (.inl point)) =
      StrandCharges.logicalOracle c binary prime P R countBinary countPrime binaryCapacity primeCapacity
        fitsRoles fallback H := by
  funext point
  exact Prod.ext rfl (normalize_eq c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
    binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit fallback (H (.inl point)).2 point)

/-- The same named search used by the physical realization, before its
complete verifier replay. This is the extractor's query-counted prefix. -/
def searchTree :=
  StrandReplay.search (StrandRuntime.Runtime.schema repr shape setup binary.nPublic)
    (StrandWindow.Node.bytes (other := Other))
    (mapQueries (StrandWindow.decode (Other)
      (StrandRealization.fallback binary prime P R repr shape setup (I) binaryCount metadata fits physical codec id program)) program)

local notation "search" => searchTree c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
  binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit cfg binaryCount metadata fits sample columnsFit program

/-- At fixed residual randomness only the answer coordinates change; the
underlying adversarial branches and query count remain the original ones. -/
def analysisTree (residual : Tagged → Residual) :=
  StrandSampling.reindex split residual (mapQueries (names).tag (StrandComposition.pad (Extra := Answer) (search)))

local notation "analysis" => analysisTree c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
  binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit cfg binaryCount metadata fits sample
  fiber uniform columnsFit program
/-- Coordinate padding and role sampling retain the original search's
fresh-query property; a recovered path is never independently resampled. -/
theorem analysis_fresh (residual : Tagged → Residual) :
    FreshOracle.FreshFrom (fun _ => False) (analysis residual) := by
  unfold analysisTree
  apply Survival.RuntimeFresh.reindex_fresh
  apply Survival.RuntimeFresh.mapQueries_fresh (names).tag (names).tag_injective
  apply Survival.RuntimeFresh.pad_fresh
  exact Survival.RuntimeFresh.replay_search_fresh
    (StrandRuntime.Runtime.schema repr shape setup binary.nPublic)
    (StrandWindow.Node.bytes (other := Other)) _

local notation "context" => QueryRuntime.Runtime.key repr shape setup binary.nPublic

/-- The extractor uses exactly the physical stopped cut, with its actual
node digests. Independent sampler padding cannot add commitment evidence. -/
theorem cut_eq (residual : Tagged → Residual) (H : Tagged → Digest × Answer)
    (target : FingerprintPrefix.Key binary.nPublic) :
    StrandCharges.trace (names) Input.context context (analysis residual) H target =
      StrandCut.trace context (search) (namedH residual H) target := by
  exact StrandCharges.trace_physical (names) Input.context context split residual (search) H target
    (StrandRealization.queryCodec_label binary prime P R repr shape setup (I) binaryCount metadata fits physical codec id program)

variable (layout : StatementCompiler.Addresses P R binary.cells prime.remaining prime.pads)
variable (bitsFit : shared+maskBits ≤ Adapter.Mdoc.quotientBound)

/-- The current runtime's local algebraic proof on the actual transformed
search. Both fields use the one tuple extracted from this search's cut. -/
def localProof (residual : Tagged → Residual) :=
  StrandCharges.localProof c binary prime P R countBinary countPrime binaryCapacity primeCapacity (W)
    fitsRoles layout degreeFits rowsFit bitsFit hashPublic primePublic
    primePlan primeGeometry primeFits binaryPlan binaryGeometry binaryFits
    (names) context codec merkleDec FingerprintPrefix.Key.root (StrandWindow.Node.bytes (other := Other))
    (analysis residual) cfg.fallback

local notation "charges" => localProof c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
  binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit cfg binaryCount metadata fits sample
  fiber uniform primeCount columnsFit program layout bitsFit

/-- Shared role accounting uses the maximum local charge across the whole
protocol, including the adjacent joint-backend pair. -/
theorem budget_le (residual : Tagged → Residual) (point : Tagged) :
    (charges residual).budget point ≤
      Sum.elim (fun _ => 2/((Adapter.Mdoc.binaryOrder-1:ℕ):ℚ)) (fun _ => 0) point := by
  have bound := StrandCharges.localProof_budget_le c binary prime P R countBinary countPrime binaryCapacity primeCapacity (W)
    fitsRoles layout degreeFits rowsFit bitsFit hashPublic primePublic
    primePlan primeGeometry primeFits binaryPlan binaryGeometry binaryFits
    (names) context codec merkleDec FingerprintPrefix.Key.root (StrandWindow.Node.bytes (other := Other))
    (analysis residual) cfg.fallback point
  convert bound using 1
  unfold Composition.LocalCharges.budget localProof
  congr 1
  apply Finset.sum_congr rfl
  intro parent member
  split_ifs <;> rfl

theorem single_budget_le (residual : Tagged → Residual) (point : Tagged) :
    (charges residual).singleBudget point ≤ 2/((Adapter.Mdoc.binaryOrder-1:ℕ):ℚ) := by
  letI : Nonempty Answer := ⟨cfg.fallback⟩
  have bounded := budget_le c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
    binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit cfg
    binaryCount metadata fits sample fiber uniform primeCount columnsFit program layout bitsFit residual point
  apply (Survival.StoppedCharges.singleBudget_le_budget (charges residual) point).trans
  cases point with
  | inl _ => exact bounded
  | inr _ => exact bounded.trans (by norm_num [Adapter.Mdoc.binaryOrder])

local notation "tupleAt" => StrandCharges.cutOracle (names) Input.context context First Second codec merkleDec
  FingerprintPrefix.Key.root (StrandWindow.Node.bytes (other := Other))

/-- The concrete extractor retains the original byte-valued Merkle codec.
Its table consists exactly of the finite search's actual node inputs. -/
theorem cutOracle_eq (residual : Tagged → Residual) (H : Tagged → Digest × Answer)
    (target : FingerprintPrefix.Key binary.nPublic) :
    tupleAt (analysis residual) H target = Joint.Pair.oracleEquiv First Second
      ((Joint.Pair.family First Second).indexedOracle merkleDec target.root
        ((StrandCut.trace context (search) (namedH residual H) target).map fun entry => (entry.1.val.val,entry.2))) := by
  unfold StrandCharges.cutOracle
  rw [cut_eq]

def authentication (residual : Tagged → Residual) (output : Output) (H : Tagged → Digest × Answer)
    (decoded : RuntimeVerifier.Decoded binary prime P R (W)) :=
  StrandCharges.authentication c binary prime P R countBinary countPrime binaryCapacity primeCapacity (W)
    (names) context codec merkleDec FingerprintPrefix.Key.root (StrandWindow.Node.bytes (other := Other))
    (analysis residual) (Earlier) output H decoded

local notation "auth" => authentication c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
  binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit cfg binaryCount metadata fits sample
  fiber uniform columnsFit program

local notation "View" => StrandExecution.View Output ((Output × Chain.State (M)) × Digest)
  (FingerprintPrefix.Key binary.nPublic)
local notation "decodeView" => StrandExecution.decoded binary prime P R (W) (Earlier) bodyCodec physical
  hashPublic primePublic draw
local notation "decision" => StrandExecution.decision binary prime P R (W) (Earlier) bodyCodec physical codec id
  hashPublic primePublic draw
local notation "observe" => StrandRealization.observe binary prime P R repr shape setup (I) binaryCount metadata
  fits physical codec id program
local notation "sourceView" => fun K => observe (Prod.fst (Tree.run (search) K)) K
local notation "recovered" => StrandRecovery.recovered binary prime P R repr shape setup (I) binaryCount metadata
  fits columnsFit physical primeCount draw program bodyFits
local notation "sourcePath" => StrandRealization.path binary prime P R repr shape setup (I) binaryCount metadata
  bodyFits fits physical codec id program
local notation "pathOf" => fun residual H index =>
  (Sum.inl (Chain.point (M) (Prod.fst (Tree.run program (SHAof residual H)))
    (ordinary (SHAof residual H)) index) : Tagged)
local notation "encodings" => RuntimeAdaptiveVerifier.encodings binary prime P R (W) (Earlier)

local notation "viewOf" => fun residual H => sourceView (namedH residual H)

theorem observation_decoded (residual : Tagged → Residual) (H : Tagged → Digest × Answer) :
    decodeView (viewOf residual H) =
      RuntimeAdaptiveVerifier.decode binary prime P R (W) (Earlier) hashPublic primePublic draw
        (program.run (SHAof residual H)).1 (ordinary (SHAof residual H)) := by
  refine (congrArg (decodeView) (StrandRealization.observe_actual binary prime P R repr shape setup (I) binaryCount metadata
    fits physical codec id program (namedH residual H))).trans ?_
  exact StrandExecution.decoded_actual binary prime P R (W) (Earlier) bodyCodec physical codec id
    hashPublic primePublic draw _ _ _ _

theorem observation_decision (residual : Tagged → Residual) (H : Tagged → Digest × Answer) :
    decision (viewOf residual H) = actualVerify (SHAof residual H) id (program.run (SHAof residual H)).1 := by
  refine (congrArg (decision) (StrandRealization.observe_actual binary prime P R repr shape setup (I) binaryCount metadata
    fits physical codec id program (namedH residual H))).trans ?_
  exact StrandExecution.decision_actual binary prime P R (W) (Earlier) bodyCodec physical codec id
    hashPublic primePublic draw _ _ _ _

include bodyFits in
/-- On the recovered path, physical sampling and the normalized ideal
decoder use the same numbered rows. -/
theorem accepted_decoded (residual : Tagged → Residual) (H : Tagged → Digest × Answer)
    (accepted : decision (viewOf residual H) = true)
    (ready : recovered (namedH residual H)) :
    ∃ decoded,
      decodeView (viewOf residual H) = some decoded ∧
      RuntimeAdaptiveVerifier.decode binary prime P R (W) (Earlier) hashPublic primePublic draw
        (program.run (SHAof residual H)).1 (logical H) = some decoded ∧
      StrandVerifier.Checks binary prime P R (W) (Earlier) bodyCodec physical codec (SHAof residual H) id
        (program.run (SHAof residual H)).1 decoded ∧
      ∀ i ≤ g.roles.length,
        (M).point (program.run (SHAof residual H)).1 (ordinary (SHAof residual H)) i =
          (M).point (program.run (SHAof residual H)).1 (logical H) i := by
  letI : ∀ point : Point, Nonempty (Values point) := fun point => ⟨(Factor point cfg.fallback).1⟩
  let SHA := SHAof residual H
  let output := (program.run SHA).1
  let original := namedH residual H
  rw [observation_decision] at accepted
  obtain ⟨decoded,found,checks⟩ := (StrandVerifier.verify_true_iff binary prime P R (W) (Earlier)
    bodyCodec physical hashPublic primePublic draw codec SHA id output).mp accepted
  have rows i (within : i ≤ g.roles.length) := ready.2.1 i within
  have outputEq : (sourceView original).original.1 = output :=
    congrArg (fun view : View => view.original.1) (StrandRealization.observe_actual binary prime P R
      repr shape setup (I) binaryCount metadata fits physical codec id program original)
  have tags i (within : i ≤ g.roles.length) :=
    StrandRealization.tag_path binary prime P R repr shape setup (I) binaryCount metadata bodyFits fits
      physical codec id program ((search).run original).1 original i within
  have same := StrandDecoder.decode_and_path binary prime P R (W) (Earlier) bodyCodec Factor sample fiber uniform
    hashPublic primePublic draw output SHA (fun point => H (.inl point)) (fun point => residual (.inl point))
    (by
      intro i
      have link := (rows i.val i.isLt.le).1
      change SHA (StrandRuntime.history bodyCodec
        ((M).point (sourceView original).original.1 (ordinary SHA) i.val)).input.encode =
        (H ((names).tag (sourcePath ((search).run original).1 original i.val))).1 at link
      rw [outputEq,tags i.val i.isLt.le] at link
      exact link)
    (by
      intro i
      have row := (rows i.val i.isLt.le).2
      let point := (M).point (sourceView original).original.1 (ordinary SHA) i.val
      change (fun counter => SHA (Strand.Input.prf (StrandRuntime.history bodyCodec point).id
        (SHA (StrandRuntime.history bodyCodec point).input.encode) counter).encode) =
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

local notation "keyOf" => fun (output : Output) => Replay.Encoding.context
  (encodings (RuntimeAdaptive.Output.request output)) (RuntimeAdaptive.Output.proof output)

/-- Selection reads the original commitment cut of the observed proof. -/
def viewAuthentication (view : View) (decoded : RuntimeVerifier.Decoded binary prime P R (W)) :=
  ZkJoint.authenticate decoded.statement
    (StrandExecution.extracted First Second codec merkleDec FingerprintPrefix.Key.root view (keyOf view.original.1))
    decoded.coin (RuntimeVerifier.responses binary prime P R (W) view.original.1.proof) c.cutoff

local notation "viewAuth" => viewAuthentication c binary prime P R countBinary countPrime binaryCapacity primeCapacity
  repr shape setup cfg binaryCount metadata columnsFit

/-- Failure concerns the witness selected from the original commitment cut. -/
def extractionFails (view : View) : Prop :=
  ∃ decoded, decodeView view = some decoded ∧
    ¬ ∃ witness, (viewAuth view decoded).context.extract = some witness ∧ decoded.application.True witness

local notation "failsView" => extractionFails c binary prime P R countBinary countPrime binaryCapacity primeCapacity
  repr shape setup binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit
  cfg binaryCount metadata sample primeCount columnsFit

theorem viewAuthentication_eq (residual : Tagged → Residual) (H : Tagged → Digest × Answer)
    (decoded : RuntimeVerifier.Decoded binary prime P R (W)) :
    viewAuth (viewOf residual H) decoded = auth residual (program.run (SHAof residual H)).1 H decoded := by
  refine (congrArg (fun view : View => viewAuth view decoded)
    (StrandRealization.observe_actual binary prime P R repr shape setup (I) binaryCount metadata
      fits physical codec id program (namedH residual H))).trans ?_
  simp only [viewAuthentication,StrandExecution.extracted,authentication,StrandCharges.authentication]
  rw [cutOracle_eq]
  rfl

include bodyFits in
/-- Agreement on the opened columns transfers the backend checks to the
tuple used by witness selection, even for an incomplete extracted tree. -/
theorem authenticated (residual : Tagged → Residual) (H : Tagged → Digest × Answer)
    (decoded : RuntimeVerifier.Decoded binary prime P R (W))
    (found : decodeView (viewOf residual H) = some decoded)
    (checks : StrandVerifier.Checks binary prime P R (W) (Earlier) bodyCodec physical codec (SHAof residual H) id
      (program.run (SHAof residual H)).1 decoded)
    (ready : recovered (namedH residual H)) :
    let a := auth residual (program.run (SHAof residual H)).1 H decoded
    JointResponse.Verify First Second a.statement a.oracle a.coin a.response decoded.query := by
  let output := (program.run (SHAof residual H)).1
  let key := keyOf output
  let cut := (StrandCut.trace context (search) (namedH residual H) key).map fun qa =>
    (StrandWindow.Node.bytes qa.1,qa.2)
  have agrees : ∀ column ∈ decoded.claim.I, messages merkleDec cut key.root c.n column = decoded.claim.a column := by
    intro column opened
    by_contra different
    apply ready.2.2
    refine ⟨decoded,found,column,opened,fun equal => different ?_⟩
    have same := congrArg (fun view : View => messages merkleDec (view.cuts (keyOf view.original.1))
      (keyOf view.original.1).root c.n column)
      (StrandRealization.observe_actual binary prime P R repr shape setup (I) binaryCount metadata
        fits physical codec id program (namedH residual H))
    exact same.symm.trans equal
  have verified := (Joint.Pair.family First Second).verify_of_indexedAgreement merkleDec (W).openingPositive
    ((codec).withOracle (SHAof residual H)) ((Joint.Pair.statementEquiv First Second).symm decoded.statement.statement)
    key.root cut ((Joint.Pair.coinEquiv First Second).symm decoded.coin)
    ((Joint.Pair.responseEquiv First Second).symm (RuntimeVerifier.responses binary prime P R (W) output.proof))
    decoded.query decoded.claim agrees checks.2.2.2.1
  change JointResponse.Verify First Second decoded.statement.statement
    (tupleAt (analysis residual) H key) decoded.coin (RuntimeVerifier.responses binary prime P R (W) output.proof) decoded.query
  rw [cutOracle_eq]
  exact (Joint.Pair.verify_iff First Second _ _ _ _ _).mp verified

variable (layoutCorrect : StatementCompiler.addresses P R binary.cells prime.remaining prime.pads = some layout)

include bodyFits layoutCorrect in
/-- An accepting recovered execution whose selected witness fails the
application incurs a charge on the actual ordinary transcript path. -/
theorem accepted_cover (residual : Tagged → Residual) (H : Tagged → Digest × Answer)
    (accepted : decision (viewOf residual H) = true) (ready : recovered (namedH residual H))
    (failed : failsView (viewOf residual H)) :
    (charges residual).Covers (rounds := g.roles.length) (pathOf residual H) H := by
  obtain ⟨decoded,found,decodedCorrect,checks,path⟩ := accepted_decoded c binary prime P R
    countBinary countPrime binaryCapacity primeCapacity repr shape setup
    binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit cfg
    binaryCount metadata bodyFits fits sample fiber uniform primeCount columnsFit program residual H accepted ready
  have verified := authenticated c binary prime P R countBinary countPrime binaryCapacity primeCapacity repr shape setup
    binaryPlan primePlan binaryGeometry primeGeometry binaryFits primeFits degreeFits rowsFit cfg
    binaryCount metadata bodyFits fits sample fiber uniform primeCount columnsFit program residual H decoded found checks ready
  obtain ⟨observed,read,failed⟩ := failed
  have same : observed = decoded := Option.some.inj (read.symm.trans found)
  subst observed
  rw [viewAuthentication_eq] at failed
  have covered := StrandCharges.decoded_cover c binary prime P R countBinary countPrime binaryCapacity primeCapacity
    (W) fitsRoles layout degreeFits rowsFit bitsFit hashPublic primePublic
    primePlan primeGeometry primeFits binaryPlan binaryGeometry binaryFits
    (names) context codec merkleDec FingerprintPrefix.Key.root (StrandWindow.Node.bytes (other := Other))
    (analysis residual) (Earlier) layoutCorrect cfg.fallback (program.run (SHAof residual H)).1 H decoded
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

theorem analysis_seen (residual : Tagged → Residual) (H : Tagged → Digest × Answer) :
    seen (analysis residual) H = (seen (search) (namedH residual H)).image (names).tag :=
  StrandComposition.coordinates_seen (names).tag split residual (search) H

include bodyFits in
theorem analysis_path (residual : Tagged → Residual) (H : Tagged → Digest × Answer)
    (ready : recovered (namedH residual H)) :
    Composition.PathQueries (rounds := g.roles.length) (analysis residual) H (pathOf residual H) := by
  let original := namedH residual H
  let cut := ((search).run original).1
  have tags i (within : i ≤ g.roles.length) :
      (names).tag (sourcePath cut original i) = pathOf residual H i :=
    StrandRealization.tag_path binary prime P R repr shape setup (I) binaryCount metadata bodyFits fits
      physical codec id program cut original i within
  constructor
  · intro i within
    rw [analysis_seen,← tags i within]
    exact Finset.mem_image.mpr ⟨_,ready.1.queried i within,rfl⟩
  · intro i within
    rw [← tags i within.le,← tags (i+1) (Nat.succ_le_of_lt within)]
    have same := StrandSampling.reindex_firstOfTwo split residual
      (mapQueries (names).tag (StrandComposition.pad (Extra := Answer) (search))) H
      ((names).tag (sourcePath cut original i)) ((names).tag (sourcePath cut original (i+1)))
    rw [Composition.firstOfTwo_mapQueries (names).tag (names).tag_injective,StrandComposition.pad_order] at same
    exact same.trans (ready.1.ordered i within)

end LfzkV2.Current.StrandProtocol
