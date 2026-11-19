import LfzkV2.Current.MdocWitness
import LfzkV2.Current.ZeroKnowledge.FrontendHonestAdapter

noncomputable section
namespace LfzkV2.Current.MdocWitness
open Application ApplicationSetup ConcreteSetup ZeroKnowledge.Frontend
open scoped Classical
variable {B : Type} [Field B] [Algebra (ZMod 2) B]

section Frontend
variable [Fintype B] [DecidableEq B]
variable {Key Base C : Type}
variable (binary : BinaryCircuit B) (prime : PrimePublic Adapter.Mdoc.P 768)
variable (primePlan : FrontendSchedule.Plan Adapter.Mdoc.P prime.circuit)
variable (samples : ConcreteMetadata.Samples B C)
variable (base : CompleteSimulation.BaseWriter binary prime primePlan (Base := Base) (C := C))
variable (H : CompleteSimulation.Point binary prime primePlan (Key := Key) (Base := Base) → Digest × C)

omit [Fintype B] [DecidableEq B] in
theorem coupling_hash (context : Key) (original : Fin binary.nPrivate → Bool) (valid : UniformHashValid binary original)
    (responses : CompleteHonest.Masks (B := B)) (coin : CircuitTape prime.circuit)
    (converted : (Adapter.Mdoc.P × MdocAdvice.Value) × AdapterBits.Unused) :
    FullCoupling.hashChecks binary prime primePlan samples base H context original responses coin converted := by
  unfold FullCoupling.hashChecks FullCoupling.recoveredInputs CompleteHonest.arrayOf FullCoupling.recoveredPrivate
    CompleteInputs.recoveredPrivate
  exact valid _ _ _

omit [Fintype B] [DecidableEq B] in
theorem honest_hash (native : CompleteSimulation.PrimePrefix binary prime primePlan Key Base C)
    (original : Fin binary.nPrivate → Bool) (valid : UniformHashValid binary original)
    (tape : CompleteHonest.Tape binary prime) :
    HonestAdapter.hashChecks binary prime primePlan samples base H native original tape := by
  unfold HonestAdapter.hashChecks CompleteHonest.binaryInputs CompleteHonest.arrayOf CompleteHonest.privateBits
  exact valid _ _ _

end Frontend


end LfzkV2.Current.MdocWitness
