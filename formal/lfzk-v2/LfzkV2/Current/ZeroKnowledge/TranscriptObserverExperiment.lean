import LfzkV2.Current.ZeroKnowledge.TranscriptObserverTrace
import LfzkV1.FromLigeroZKV1

/-! Full raw observer views are postprocessing of the concrete typed
observer experiment. The prior observer still returns the original public
request, and both phases retain all raw malformed/repeated calls. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.TranscriptObserverExperiment
open Merkle.RandomOracle LigeroFamily
open scoped Classical
variable {QM AM Point Raw AT Request Proof Out : Type} {valid : Point → Prop}
variable (codec : ByteOracleTransport.Codec Point Raw valid)
variable (outside : Raw → AT) (defaultM : AM) (defaultT : AT)
variable {preM preT postM postT : ℕ}
variable (prior : TwoOracleTree QM AM Raw AT Request preM preT)
variable (after : Request → Proof → TwoOracleTree QM AM Raw AT Out postM postT)

/-- A raw implementation can fill auxiliary invalid typed coordinates
arbitrarily. They never change its raw oracle, including malformed inputs. -/
theorem normalize_oracle (HT : Point → AT) (fallback : Point → AT) :
    codec.oracle outside (codec.restrict (codec.oracle outside HT) fallback) = codec.oracle outside HT := by
  funext raw
  cases decoded : codec.decode raw with
  | none => simp only [ByteOracleTransport.Codec.oracle,decoded]
  | some point =>
      simp only [ByteOracleTransport.Codec.oracle,decoded,ByteOracleTransport.Codec.restrict,dif_pos point.property,
        codec.decode_encode]

/-- The returned byte oracle is a change to one input of the original
raw ideal oracle, rather than a freshly sampled or reset complementary
table. Canonicality is a property of the actual programmed point. -/
theorem program_raw [DecidableEq Point] [DecidableEq Raw]
    (rawOracle : Raw → AT) (fallback : Point → AT) (point : {point // valid point}) (answer : AT) :
    codec.oracle rawOracle (Function.update (codec.restrict rawOracle fallback) point.val answer) =
      Function.update rawOracle (codec.encode point) answer := by
  rw [TranscriptObserver.oracle_update,ByteOracleTransport.Codec.oracle_restrict]

def restoreView (view : Observer.View QM AM Point AT Request Proof Out) :
    Observer.View QM AM Raw AT Request Proof Out where
  request := view.request
  proof := view.proof
  before := (TranscriptObserverTrace.restore codec outside defaultM defaultT prior view.before).2
  output := view.output
  after := (TranscriptObserverTrace.restore codec outside defaultM defaultT (after view.request view.proof) view.after).2

/-- The honest or simulated prover uses its typed oracle and returns the
typed oracle used by the later observer. Its raw view exposes only the
canonical extension of that returned table, with the same complement. -/
def rawExperiment
    (prove : Request → (QM → AM) → (Point → AT) → Proof × ((QM → AM) × (Point → AT)))
    (HM : QM → AM) (HT : Point → AT) : Observer.View QM AM Raw AT Request Proof Out :=
  let before := Observer.run HM (codec.oracle outside HT) prior
  let result := prove before.1 HM HT
  let later := Observer.run result.2.1 (codec.oracle outside result.2.2) (after before.1 result.1)
  ⟨before.1,result.1,before.2,later.1,later.2⟩

theorem experiment_view
    (prove : Request → (QM → AM) → (Point → AT) → Proof × ((QM → AM) × (Point → AT)))
    (HM : QM → AM) (HT : Point → AT) :
    restoreView codec outside defaultM defaultT prior after
      (Observer.experiment (codec.program outside prior) prove (fun request proof => codec.program outside (after request proof)) HM HT) =
      rawExperiment codec outside prior after prove HM HT := by
  simp only [restoreView,Observer.experiment,rawExperiment,TranscriptObserver.program_output,
    TranscriptObserverTrace.restore_run]

include defaultM defaultT in
theorem statClose {R S : Type} [Fintype R] [Fintype S] [Fintype Point] [Fintype AT]
    {epsilon : ℚ} (realHM : R → QM → AM) (simulateHM : S → QM → AM)
    (real : R → Request → (QM → AM) → (Point → AT) → Proof × ((QM → AM) × (Point → AT)))
    (simulate : S → Request → (QM → AM) → (Point → AT) → Proof × ((QM → AM) × (Point → AT)))
    (typed : StatClose epsilon
      (fun coin : R × (Point → AT) => Observer.experiment (codec.program outside prior) (real coin.1)
        (fun request proof => codec.program outside (after request proof)) (realHM coin.1) coin.2)
      (fun coin : S × (Point → AT) => Observer.experiment (codec.program outside prior) (simulate coin.1)
        (fun request proof => codec.program outside (after request proof)) (simulateHM coin.1) coin.2)) :
    StatClose epsilon
      (fun coin : R × (Point → AT) => rawExperiment codec outside prior after (real coin.1) (realHM coin.1) coin.2)
      (fun coin : S × (Point → AT) => rawExperiment codec outside prior after (simulate coin.1) (simulateHM coin.1) coin.2) := by
  have mapped := statClose_map (restoreView codec outside defaultM defaultT prior after) typed
  simpa only [experiment_view] using mapped

end LfzkV2.Current.ZeroKnowledge.TranscriptObserverExperiment
