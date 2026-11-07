import LfzkV2.Current.ZeroKnowledge.OracleResults
import LfzkV2.Current.ZeroKnowledge.TranscriptObserverExperiment

/-! Equality of the full raw observer view under typed-coordinate
normalization. Malformed raw inputs, repetitions and their answers remain
in the trace. The returned raw oracle, rather than auxiliary typed entries,
determines all subsequent observation. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.OracleRawNormalization
open Merkle.RandomOracle
open scoped Classical
variable {QM AM Point Raw AT Request Proof Out : Type} {valid : Point → Prop}
variable (codec : ByteOracleTransport.Codec Point Raw valid) (outside : Raw → AT)

theorem oracle_eq (H H' : Point → AT) (agree : ∀ point, valid point → H point = H' point) :
    codec.oracle outside H = codec.oracle outside H' := by
  funext raw
  cases decoded : codec.decode raw with
  | none => simp only [ByteOracleTransport.Codec.oracle,decoded]
  | some point => simpa only [ByteOracleTransport.Codec.oracle,decoded] using agree point.val point.property

variable {preM preT postM postT : ℕ}
variable (prior : TwoOracleTree QM AM Raw AT Request preM preT)
variable (after : Request → Proof → TwoOracleTree QM AM Raw AT Out postM postT)
variable (prove : Request → (QM → AM) → (Point → AT) → Proof × ((QM → AM) × (Point → AT)))

theorem experiment_eq (HM : QM → AM) (H H' : Point → AT)
    (before : codec.oracle outside H = codec.oracle outside H')
    (complete : ∀ request,
      (prove request HM H).1 = (prove request HM H').1 ∧
      (prove request HM H).2.1 = (prove request HM H').2.1 ∧
      codec.oracle outside (prove request HM H).2.2 = codec.oracle outside (prove request HM H').2.2) :
    TranscriptObserverExperiment.rawExperiment codec outside prior after prove HM H =
      TranscriptObserverExperiment.rawExperiment codec outside prior after prove HM H' := by
  unfold TranscriptObserverExperiment.rawExperiment
  rw [before]
  let request := (Observer.run HM (codec.oracle outside H') prior).1
  obtain ⟨proofs,merkle,transcript⟩ := complete request
  simp only
  rw [proofs,merkle,transcript]

/-- Public result equivalence is sufficient for the complete raw observer
view. Malformed raw queries use the same complement oracle, and canonical
queries use the equal answers recorded in the semantic result boundary. -/
theorem experiment_eq_of_results (HM : QM → AM) (H H' : Point → AT)
    (before : Set.EqOn H H' {point | valid point})
    (complete : ∀ request, OracleResults.Same {point | valid point}
      (prove request HM H) (prove request HM H')) :
    TranscriptObserverExperiment.rawExperiment codec outside prior after prove HM H =
      TranscriptObserverExperiment.rawExperiment codec outside prior after prove HM H' := by
  apply experiment_eq codec outside prior after prove HM H H'
    (oracle_eq codec outside H H' (fun point member => before member))
  intro request
  have same := complete request
  exact ⟨same.public_eq,same.merkle_eq,
    oracle_eq codec outside _ _ (fun _ member => same.transcript_eq member)⟩

/-- Only the request actually returned by this observer prefix matters.
No claim about an unreachable public request is needed for normalization. -/
theorem experiment_eq_at_result (HM : QM → AM) (H H' : Point → AT)
    (before : Set.EqOn H H' {point | valid point})
    (complete : OracleResults.Same {point | valid point}
      (prove (Observer.run HM (codec.oracle outside H) prior).1 HM H)
      (prove (Observer.run HM (codec.oracle outside H) prior).1 HM H')) :
    TranscriptObserverExperiment.rawExperiment codec outside prior after prove HM H =
      TranscriptObserverExperiment.rawExperiment codec outside prior after prove HM H' := by
  have beforeOracle := oracle_eq codec outside H H' (fun _ member => before member)
  have earlierEq := congrArg (fun oracle => Observer.run HM oracle prior) beforeOracle
  unfold TranscriptObserverExperiment.rawExperiment
  rw [← earlierEq]
  have afterOracle := oracle_eq codec outside _ _ (fun _ member => complete.transcript_eq member)
  simp only
  rw [complete.public_eq,complete.merkle_eq,afterOracle]

end LfzkV2.Current.ZeroKnowledge.OracleRawNormalization
