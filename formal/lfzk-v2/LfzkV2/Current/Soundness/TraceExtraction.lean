import LfzkV2.Current.Soundness.Transport
import LfzkV2.Current.StrandRowTrace

/-! Extraction from the adversary's own row trace, with no oracle. The
extractor reads the submitted output and the row trace: the commitment cut
of the submitted context comes from the trace's query log
(`StrandCutObservation.logCut`), and every challenge it needs, the sumcheck
challenges that rebuild the statement and the backend challenge that
identifies the good columns, comes from the rows of the queried nodes
(`StrandRowTrace.oracle`). On an accepted proof outside the hash exception,
every node on the accepted path was queried, so this replay equals the
verifier's replay with the oracle (`traceRecover_eq`). -/
noncomputable section
namespace LfzkV2.Current.Soundness.Runtime
open Application ApplicationSetup CanonicalPrefix QueryRuntime RecursivePolygero
open Merkle Merkle.Indexed Merkle.RandomOracle TranscriptV2
open scoped Classical
attribute [local instance] idealLeafInhabited runtimeLeafInhabited

variable {c : CertifiedProfile} {g : Geometry} {fields : Fields} {Advice B : Type}
variable [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable [∀ side, Fintype (fields side)] [Fintype Advice]
variable {shared maskBits adviceBits blocks : ℕ}
variable (E : Protocol.Setup c g fields Advice B (shared := shared) (maskBits := maskBits) (adviceBits := adviceBits))
variable (D : Protocol.SamplerData E blocks)
variable [Inhabited (Fin c.n × MerkleNonce)]
variable [leafDefault : Inhabited (Joint.Pair.family E.First E.Second).Leaf]

local notation "View" => Protocol.Execution.View E.Output ((E.Output × Chain.State (E.chain)) × Digest)
  (E.fmt.Key)
local notation "decodeView" => Protocol.Observation.decoded E.binary E.prime E.P E.R (E.wire) (E.earlier) E.fmt.wire E.bodyCodec D.execution.sample
  E.hashPublic E.primePublic E.draw
local notation "decision" => Protocol.Observation.decision E.binary E.prime E.P E.R (E.wire) (E.earlier) E.fmt.wire E.bodyCodec D.execution.sample E.merkleCodec id
  E.hashPublic E.primePublic E.draw
local notation "hashBad" => Soundness.Recovery.hashException E.binary E.prime E.P E.R E.fmt (E.ideal) E.binaryCount E.metadata
  E.columnsFit D.execution.sample E.primeCount E.draw
local notation "ordinary" => StrandVerifier.oracle E.binary E.prime E.P E.R (E.wire) E.fmt.wire E.bodyCodec D.execution.sample
local notation "decodeAt" => RuntimeAdaptiveVerifier.decode E.binary E.prime E.P E.R (E.wire) (E.earlier) E.hashPublic E.primePublic E.draw
local notation "encodings" => RuntimeAdaptiveVerifier.encodings E.binary E.prime E.P E.R (E.wire) (E.earlier)
local notation "keyOf" => fun (output : E.Output) => Replay.Encoding.context
  (encodings (RuntimeAdaptive.Output.request output)) (RuntimeAdaptive.Output.proof output)
local notation "history" => StrandRuntime.history E.fmt.wire E.bodyCodec
local notation "M" => RuntimeAdaptiveVerifier.chain E.binary E.prime E.P E.R (E.wire) (E.earlier)

/-- The tuple committed at `key`, read from the cut of a raw query log. -/
def logTuple (key : E.fmt.Key) (log : List (Bytes × Digest)) : JointResponse.Oracle E.First E.Second :=
  Joint.Pair.oracleEquiv E.First E.Second
    ((Joint.Pair.family E.First E.Second).indexedOracle E.merkleDecoders (E.fmt.root key)
      (StrandCutObservation.logCut E.fmt.schema E.fmt.key key log))

/-- Transcript-assisted extraction from a submitted output and the
adversary's row trace: decode the statement, coin and query from the
challenges the trace's rows determine, then uniquely decode the tuple
committed at the trace's cut (`Application.StatementData.recover`). It takes
no oracle. -/
def traceRecover (output : E.Output) (trace : List StrandRowTrace.Entry) :
    Option (Selection.Pair B (ZMod Adapter.Mdoc.primeOrder) E.binary.Original E.prime.Original) :=
  (decodeAt output (ordinary (StrandRowTrace.oracle trace))).bind fun decoded =>
    decoded.statement.recover (logTuple E (keyOf output) (trace.map fun entry => (entry.1,entry.2.1)))
      decoded.coin (RuntimeVerifier.responses E.binary E.prime E.P E.R (E.wire) output.proof)

omit [∀ side, Fintype (fields side)] [Fintype Advice] in
/-- On an accepted proof outside the hash exception, extraction from the
row trace of the adversary's log equals extraction from the verifier's
replay with the oracle. The row trace is the wide-oracle trace of the log:
each queried input with its digest and its row of PRF words. -/
theorem traceRecover_eq (view : View) (SHA : Bytes → Digest)
    (replayed : view.verifier = (StrandAuthentication.replay E.binary E.prime E.P E.R (E.wire) (E.earlier) E.fmt.wire
      E.bodyCodec D.execution.sample E.merkleCodec id view.original.1).run SHA)
    (sound : ∀ qa ∈ view.original.2, qa.2 = SHA qa.1)
    (cuts : ∀ key, view.cuts key = StrandCutObservation.logCut E.fmt.schema E.fmt.key key view.original.2)
    (accepted : decision view = true) (noHash : ¬hashBad view) :
    ∃ decoded, decodeView view = some decoded ∧
      traceRecover E D view.original.1 (StrandRowTrace.ofLog SHA view.original.2) = viewRecover E view decoded := by
  have trace := congrArg Prod.snd replayed
  have decodedEq := Protocol.Observation.decoded_of_trace E.binary E.prime E.P E.R (E.wire) (E.earlier) E.fmt.wire
    E.bodyCodec D.execution.sample E.merkleCodec id E.hashPublic E.primePublic E.draw view SHA trace
  have decisionEq := Protocol.Observation.decision_of_trace E.binary E.prime E.P E.R (E.wire) (E.earlier) E.fmt.wire
    E.bodyCodec D.execution.sample E.merkleCodec id E.hashPublic E.primePublic E.draw view SHA trace
  obtain ⟨decoded,found,checks⟩ := (StrandVerifier.verify_true_iff E.binary E.prime E.P E.R (E.wire) (E.earlier)
    E.fmt.wire E.bodyCodec D.execution.sample E.hashPublic E.primePublic E.draw E.merkleCodec SHA id
    view.original.1).mp (decisionEq.symm.trans accepted)
  refine ⟨decoded,decodedEq.trans found,?_⟩
  have result := StrandAuthentication.replay_result E.binary E.prime E.P E.R (E.wire) (E.earlier) E.fmt.wire
    E.bodyCodec D.execution.sample E.merkleCodec id view.original.1 SHA
  rw [← replayed] at result
  -- Outside the observed exception, every ancestor of the accepted path is in the log.
  have known : ∀ raw ∈ (history ((M).input ((M).replay view.original.1 (ordinary SHA) g.roles.length))).ancestors,
      Merkle.QueryTable.Known view.original.2 raw := by
    by_contra missing
    apply noHash
    refine Or.inl ⟨?_,Or.inr ?_⟩
    · rw [result]
      exact checks.2.2.2.1
    · rw [result]
      exact missing
  have path : ∀ i ≤ g.roles.length,
      Merkle.QueryTable.Known view.original.2 (history ((M).point view.original.1 (ordinary SHA) i)).input.encode :=
    fun i within => known _ (StrandRuntime.replay_node_mem E.fmt.wire E.bodyCodec (M) (E.wire).initialLink
      (fun _ => rfl) _ _ g.roles.length i le_rfl within)
  have same := StrandAuthentication.decode_congr E.binary E.prime E.P E.R (E.wire) (E.earlier) E.hashPublic
    E.primePublic E.draw view.original.1 (ordinary SHA) (ordinary (StrandRowTrace.oracle (StrandRowTrace.ofLog SHA view.original.2)))
    (fun i within => (StrandRowTrace.strand_oracle SHA view.original.2 history D.execution.sample (E.wire).fallback
      sound _ (path i within.le)).symm)
  unfold traceRecover viewRecover
  rw [← same,found,Option.bind_some,StrandRowTrace.log_ofLog]
  unfold Protocol.Observation.extracted logTuple
  rw [cuts]

end LfzkV2.Current.Soundness.Runtime
