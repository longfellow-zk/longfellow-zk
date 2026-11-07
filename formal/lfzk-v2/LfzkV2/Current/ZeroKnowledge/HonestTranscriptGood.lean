import LfzkV2.Current.ZeroKnowledge.HonestTranscriptMdoc
import LfzkV2.Current.ZeroKnowledge.FrontendSimulationHistory

/-! The honest frontend retains its actual past answers and link feedback.
This invariant is independent of circuit satisfaction or witness privacy:
every state update is one of the already checked complete-reader actions. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.HonestTranscript.Mdoc
open Merkle.RandomOracle SumcheckV2 ApplicationSetup ConcreteSetup Frontend
open scoped Classical
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
variable {B Key Base C : Type} [Field B] [Fintype B] [Algebra (ZMod 2) B]
local notation "P" => Adapter.Mdoc.P
variable (binary : BinaryCircuit B) (prime : PrimePublic P 768)
variable (primePlan : FrontendSchedule.Plan P prime.circuit)
variable (samples : ConcreteMetadata.Samples B C)
variable (base : CompleteSimulation.BaseWriter binary prime primePlan (Base := Base) (C := C))
local notation "Point" => CompleteSimulation.Point binary prime primePlan (Key := Key) (Base := Base)

theorem run_good (coefficients : C → WitnessSelection.Coins B binary.description.Original × WitnessSelection.Coins P prime.Original)
    (context : Key) (original : Fin binary.nPrivate → Bool) (remaining : Fin prime.remaining → P)
    (tape : CompleteHonest.Tape binary prime) (masks : CompleteHonest.Masks (B := B)) (H : Point → Digest × C) :
    History.Good base H context
      (CompleteHonest.run binary prime primePlan samples base H coefficients context original remaining tape masks).state := by
  unfold CompleteHonest.run CompleteHonest.runSelected
  apply History.bind_good
  apply History.step_good
  apply History.bind_good
  apply SimulationHistory.binary_good
  apply SimulationHistory.conversion_good
  apply SimulationHistory.prime_good
  apply History.bind_good
  apply History.step_good
  exact History.initial_good base H context samples.fallback

theorem program_good (coefficients : C → WitnessSelection.Coins B binary.description.Original × WitnessSelection.Coins P prime.Original)
    (context : Key) (original : Fin binary.nPrivate → Bool) (remaining : Fin prime.remaining → P)
    (tape : CompleteHonest.Tape binary prime) (masks : CompleteHonest.Masks (B := B)) (H : Point → Digest × C) :
    History.Good base H context
      ((program binary prime primePlan samples base coefficients context original remaining tape masks).run H).1.state := by
  rw [program_output]
  exact run_good binary prime primePlan samples base coefficients context original remaining tape masks H

end LfzkV2.Current.ZeroKnowledge.HonestTranscript.Mdoc
