import LfzkV2.Current.ZeroKnowledge.OracleRawNormalization

/-! Execute a typed prover against one raw oracle. Canonical transcript
queries use their byte encodings; auxiliary typed coordinates are ignored.
The same raw oracle supplies all malformed-input answers before and after
completion, including an abort. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.OracleRawExecution
open Merkle.RandomOracle
open scoped Classical
variable {QM AM Point Raw AT Request Proof Out : Type} {valid : Point → Prop}
variable (codec : ByteOracleTransport.Codec Point Raw valid)
variable {preM preT postM postT : ℕ}
variable (prior : TwoOracleTree QM AM Raw AT Request preM preT)
variable (after : Request → Proof → TwoOracleTree QM AM Raw AT Out postM postT)
variable (prove : Request → (QM → AM) → (Point → AT) → Proof × ((QM → AM) × (Point → AT)))

def run (fallback : Point → AT) (HM : QM → AM) (H : Raw → AT) :=
  TranscriptObserverExperiment.rawExperiment codec H prior after prove HM (codec.restrict H fallback)

/-- Overwriting canonical coordinates never alters the complementary raw
answers. Thus the continuation uses one oracle, even after programming. -/
theorem oracle_overlay (outside : Raw → AT) (base returned : Point → AT) :
    codec.oracle (codec.oracle outside base) returned = codec.oracle outside returned := by
  funext raw
  cases decoded : codec.decode raw with
  | none => simp only [ByteOracleTransport.Codec.oracle,decoded]
  | some point => simp only [ByteOracleTransport.Codec.oracle,decoded]

theorem experiment_overlay (outside : Raw → AT) (base H : Point → AT) (HM : QM → AM) :
    TranscriptObserverExperiment.rawExperiment codec (codec.oracle outside base) prior after prove HM H =
      TranscriptObserverExperiment.rawExperiment codec outside prior after prove HM H := by
  unfold TranscriptObserverExperiment.rawExperiment
  simp only [oracle_overlay]

theorem run_overlay (outside : Raw → AT) (fallback base : Point → AT) (HM : QM → AM) :
    run codec prior after prove fallback HM (codec.oracle outside base) =
      TranscriptObserverExperiment.rawExperiment codec outside prior after prove HM
        (codec.restrict (codec.oracle outside base) fallback) :=
  experiment_overlay codec prior after prove outside base _ HM

end LfzkV2.Current.ZeroKnowledge.OracleRawExecution
