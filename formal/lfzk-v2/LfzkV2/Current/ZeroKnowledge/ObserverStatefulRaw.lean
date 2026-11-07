import LfzkV2.Current.ZeroKnowledge.ObserverStateful
import LfzkV2.Current.ZeroKnowledge.OracleRawExecution
import LfzkV2.Current.ZeroKnowledge.TranscriptObserverExperiment

/-! Raw transcript-oracle transport preserves the observer's private
context unchanged. The codec translates queries and restores their full
traces; it neither projects away state nor adds post-phase replay queries.
Only the public request projection enters the protocol callback. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.ObserverStatefulRaw
open Merkle.RandomOracle LigeroFamily
open scoped Classical
variable {QM AM Point Raw AT Context Request Proof Out : Type} {valid : Point → Prop}
variable (codec : ByteOracleTransport.Codec Point Raw valid)
variable {preM preT postM postT : ℕ}
variable (requestOf : Context → Request)
variable (prior : TwoOracleTree QM AM Raw AT Context preM preT)
variable (prove : Request → (QM → AM) → (Point → AT) → Proof × ((QM → AM) × (Point → AT)))
variable (after : Context → Proof → TwoOracleTree QM AM Raw AT Out postM postT)

def rawProver (fallback : Point → AT) (request : Request) (HM : QM → AM) (HT : Raw → AT) :
    Proof × ((QM → AM) × (Raw → AT)) :=
  let result := prove request HM (codec.restrict HT fallback)
  (result.1,(result.2.1,codec.oracle HT result.2.2))

def rawRun (fallback : Point → AT) (HM : QM → AM) (HT : Raw → AT) :=
  ObserverStateful.experiment requestOf prior (rawProver codec prove fallback) after HM HT

def rawExperiment (outside : Raw → AT) (HM : QM → AM) (HT : Point → AT) :=
  TranscriptObserverExperiment.rawExperiment codec outside prior after
    (ObserverStateful.callback requestOf prove) HM HT

theorem rawRun_eq_execution (fallback : Point → AT) (HM : QM → AM) (HT : Raw → AT) :
    rawRun codec requestOf prior prove after fallback HM HT =
      OracleRawExecution.run codec prior after (ObserverStateful.callback requestOf prove) fallback HM HT := by
  unfold rawRun rawProver ObserverStateful.experiment ObserverStateful.callback Observer.experiment
    OracleRawExecution.run TranscriptObserverExperiment.rawExperiment
  simp only [ByteOracleTransport.Codec.oracle_restrict]

theorem normalized_agree (outside : Raw → AT) (H fallback : Point → AT) :
    Set.EqOn H (codec.restrict (codec.oracle outside H) fallback) {point | valid point} := by
  intro point member
  change valid point at member
  simp only [ByteOracleTransport.Codec.restrict,dif_pos member,ByteOracleTransport.Codec.oracle,
    codec.decode_encode ⟨point,member⟩]

/-- The protocol-specific normalization fact is needed at exactly the
private context actually returned by the earlier observer. -/
theorem projection (outside : Raw → AT) (fallback : Point → AT) (HM : QM → AM) (H : Point → AT)
    (same : OracleResults.Same {point | valid point}
      (prove (requestOf (Observer.run HM (codec.oracle outside H) prior).1) HM H)
      (prove (requestOf (Observer.run HM (codec.oracle outside H) prior).1) HM
        (codec.restrict (codec.oracle outside H) fallback))) :
    rawRun codec requestOf prior prove after fallback HM (codec.oracle outside H) =
      rawExperiment codec requestOf prior prove after outside HM H := by
  rw [rawRun_eq_execution,OracleRawExecution.run_overlay]
  exact (OracleRawNormalization.experiment_eq_at_result codec outside prior after
    (ObserverStateful.callback requestOf prove) HM H (codec.restrict (codec.oracle outside H) fallback)
    (normalized_agree codec outside H fallback) same).symm

theorem experiment_view (outside : Raw → AT) (defaultM : AM) (defaultT : AT)
    (HM : QM → AM) (HT : Point → AT) :
    TranscriptObserverExperiment.restoreView codec outside defaultM defaultT prior after
      (ObserverStateful.experiment requestOf (codec.program outside prior) prove
        (fun context proof => codec.program outside (after context proof)) HM HT) =
      rawExperiment codec requestOf prior prove after outside HM HT :=
  TranscriptObserverExperiment.experiment_view codec outside defaultM defaultT prior after
    (ObserverStateful.callback requestOf prove) HM HT

theorem statClose {R S : Type} [Fintype R] [Fintype S] [Fintype Point] [Fintype AT]
    (outside : Raw → AT) (defaultM : AM) (defaultT : AT) {epsilon : ℚ}
    (realHM : R → QM → AM) (simulateHM : S → QM → AM)
    (real : R → Request → (QM → AM) → (Point → AT) → Proof × ((QM → AM) × (Point → AT)))
    (simulate : S → Request → (QM → AM) → (Point → AT) → Proof × ((QM → AM) × (Point → AT)))
    (typed : StatClose epsilon
      (fun coin : R × (Point → AT) => ObserverStateful.experiment requestOf (codec.program outside prior) (real coin.1)
        (fun context proof => codec.program outside (after context proof)) (realHM coin.1) coin.2)
      (fun coin : S × (Point → AT) => ObserverStateful.experiment requestOf (codec.program outside prior) (simulate coin.1)
        (fun context proof => codec.program outside (after context proof)) (simulateHM coin.1) coin.2)) :
    StatClose epsilon
      (fun coin : R × (Point → AT) => rawExperiment codec requestOf prior (real coin.1) after outside (realHM coin.1) coin.2)
      (fun coin : S × (Point → AT) => rawExperiment codec requestOf prior (simulate coin.1) after outside (simulateHM coin.1) coin.2) :=
  TranscriptObserverExperiment.statClose codec outside defaultM defaultT prior after realHM simulateHM
    (fun coin => ObserverStateful.callback requestOf (real coin))
    (fun coin => ObserverStateful.callback requestOf (simulate coin)) typed

section Support
variable [Fintype AM] [Fintype AT]

theorem supported_rawRun (fallback : Point → AT) (HM : QM → AM) (HT : Raw → AT) :
    ObserverStateful.mapContext Subtype.val
      (rawRun codec (requestOf ∘ Subtype.val) (ObserverSupport.restrict prior) prove
        (fun context => after context.val) fallback HM HT) =
      rawRun codec requestOf prior prove after fallback HM HT :=
  ObserverStateful.supported_experiment requestOf prior (rawProver codec prove fallback) after HM HT

end Support
end LfzkV2.Current.ZeroKnowledge.ObserverStatefulRaw
