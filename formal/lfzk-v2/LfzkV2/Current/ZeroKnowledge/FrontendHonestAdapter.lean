import LfzkV2.Current.ZeroKnowledge.FrontendHonestBinaryRows

/-! Honest generated-adapter correctness for the actual independently
sampled scalar and three-byte OTP. Only twenty OTP bits are consumed by
the circuit; the remaining four are an independent inert coordinate.
The trusted ordinary hash checks are kept separate below. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
namespace LfzkV2.Current.ZeroKnowledge.Frontend.HonestAdapter
open SumcheckV2 ApplicationSetup ConcreteSetup
open scoped Classical
variable {B Key Base C : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
local notation "P" => Adapter.Mdoc.P
variable (binary : BinaryCircuit B)

omit [Fintype B] [DecidableEq B] in
theorem private_recovered (original : Fin binary.nPrivate → Bool)
    (weights : Fin 768 → P) (eta : P) (alpha : Adapter.Mdoc.Alphas) (mask : P) (otp : Fin (2^24)) :
    let mu := Adapter.Mdoc.offset weights (WitnessInputs.shared binary original) eta+mask
    let advice := AdapterBits.xorEquiv (Adapter.Mdoc.advice weights (WitnessInputs.shared binary original) eta alpha mu)
      (AdapterBits.rawOtpEquiv otp).1
    CompleteInputs.recoveredPrivate binary original weights eta alpha mu advice =
      WitnessInputs.privateValues binary original (Adapter.canonicalMask Adapter.Mdoc.maskCapacity mask)
        (fun tree i => otp.val.testBit (10*tree.val+i.val)) := by
  dsimp only [CompleteInputs.recoveredPrivate]
  rw [Adapter.Mdoc.recoverMask_mu,Equiv.symm_apply_apply]
  apply congrArg (WitnessInputs.privateValues binary original _)
  funext tree i
  exact AdapterBits.rawOtp_bits otp tree i

omit [Fintype B] [DecidableEq B] in
theorem adapter_satisfies (original : Fin binary.nPrivate → Bool) (generator : Bˣ)
    (weights : Fin 768 → P) (eta : P) (alpha : Adapter.Mdoc.Alphas) (mask : P) (otp : Fin (2^24)) :
    let mu := Adapter.Mdoc.offset weights (WitnessInputs.shared binary original) eta+mask
    let advice := AdapterBits.xorEquiv (Adapter.Mdoc.advice weights (WitnessInputs.shared binary original) eta alpha mu)
      (AdapterBits.rawOtpEquiv otp).1
    Current.Adapter.Circuit.Satisfies binary.description.shape binary.description.sources binary.description.advice
      (fun tree i => generator^((alpha mu tree).val*Adapter.Mdoc.weights weights eta i).val)
      (generator^(-(Current.Adapter.Mdoc.primeOrder : ℤ))) (MdocAdvice.bits advice)
      (fun tree => generator^((alpha mu tree).val*mu).val)
      (Current.Adapter.Circuit.bitValue ∘ WitnessInputs.bits binary
        (WitnessInputs.privateValues binary original (Adapter.canonicalMask Adapter.Mdoc.maskCapacity mask)
          (fun tree i => otp.val.testBit (10*tree.val+i.val)))) := by
  letI : CharP B 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) B).injective 2
  dsimp only
  have recovered := CompleteInputs.recovered_adapter_satisfies binary original generator weights eta alpha
    (Adapter.Mdoc.offset weights (WitnessInputs.shared binary original) eta+mask)
    (AdapterBits.xorEquiv (Adapter.Mdoc.advice weights (WitnessInputs.shared binary original) eta alpha
      (Adapter.Mdoc.offset weights (WitnessInputs.shared binary original) eta+mask)) (AdapterBits.rawOtpEquiv otp).1)
  exact Eq.mp (congrArg (fun privateBits =>
    Current.Adapter.Circuit.Satisfies binary.description.shape binary.description.sources binary.description.advice
      (fun tree i => generator^((alpha (Adapter.Mdoc.offset weights (WitnessInputs.shared binary original) eta+mask) tree).val*
        Adapter.Mdoc.weights weights eta i).val)
      (generator^(-(Current.Adapter.Mdoc.primeOrder : ℤ)))
      (MdocAdvice.bits (AdapterBits.xorEquiv (Adapter.Mdoc.advice weights (WitnessInputs.shared binary original) eta alpha
        (Adapter.Mdoc.offset weights (WitnessInputs.shared binary original) eta+mask)) (AdapterBits.rawOtpEquiv otp).1))
      (fun tree => generator^((alpha (Adapter.Mdoc.offset weights (WitnessInputs.shared binary original) eta+mask) tree).val*
        (Adapter.Mdoc.offset weights (WitnessInputs.shared binary original) eta+mask)).val)
      (Current.Adapter.Circuit.bitValue ∘ WitnessInputs.bits binary privateBits))
    (private_recovered binary original weights eta alpha mask otp)) recovered

variable (prime : PrimePublic P 768) (primePlan : FrontendSchedule.Plan P prime.circuit)
variable (samples : ConcreteMetadata.Samples B C)
variable (base : CompleteSimulation.BaseWriter binary prime primePlan (Base := Base) (C := C))
variable (H : CompleteSimulation.Point binary prime primePlan (Key := Key) (Base := Base) → Digest × C)

def advice (native : CompleteSimulation.PrimePrefix binary prime primePlan Key Base C)
    (original : Fin binary.nPrivate → Bool) (tape : CompleteHonest.Tape binary prime) : MdocAdvice.Value :=
  let mu := Adapter.Mdoc.offset native.claim.sharedWeights (WitnessInputs.shared binary original) native.eta.val+tape.mask
  AdapterBits.xorEquiv (Adapter.Mdoc.advice native.claim.sharedWeights (WitnessInputs.shared binary original) native.eta.val
    (CompleteCoupling.alphas binary prime primePlan samples base H native) mu) (AdapterBits.rawOtpEquiv tape.otp).1

/-- This premise contains only the ordinary application checks. The two
generated adapter assertions are established by `adapter_satisfies`. -/
def hashChecks (native : CompleteSimulation.PrimePrefix binary prime primePlan Key Base C)
    (original : Fin binary.nPrivate → Bool) (tape : CompleteHonest.Tape binary prime) : Prop :=
  let mu := Adapter.Mdoc.offset native.claim.sharedWeights (WitnessInputs.shared binary original) native.eta.val+tape.mask
  let converted := CompleteSimulation.conversionPrefix binary prime primePlan samples base H native mu
  HashCircuit.Checks binary.description.layout binary.description.output binary.description.shape binary.description.others
    binary.description.carry binary.description.above binary.description.sources binary.description.advice
    (CompleteSimulation.powers binary prime primePlan native converted) (CompleteSimulation.generatorBase binary)
    (MdocAdvice.bits (advice binary prime primePlan samples base H native original tape))
    (CompleteSimulation.targets binary prime primePlan converted)
    (Current.Adapter.Circuit.bitValue ∘ WitnessInputs.bits binary (CompleteHonest.privateBits binary prime original tape))

omit [Fintype B] [DecidableEq B] in
theorem generated_satisfies (native : CompleteSimulation.PrimePrefix binary prime primePlan Key Base C)
    (original : Fin binary.nPrivate → Bool) (tape : CompleteHonest.Tape binary prime)
    (hash : hashChecks binary prime primePlan samples base H native original tape) :
    let mu := Adapter.Mdoc.offset native.claim.sharedWeights (WitnessInputs.shared binary original) native.eta.val+tape.mask
    let converted := CompleteSimulation.conversionPrefix binary prime primePlan samples base H native mu
    (CompleteSimulation.generatedCircuit binary prime primePlan native converted
      (advice binary prime primePlan samples base H native original tape)).Satisfies
        (Current.Adapter.Circuit.bitValue ∘ WitnessInputs.bits binary (CompleteHonest.privateBits binary prime original tape)) := by
  dsimp only
  apply (HashCircuit.build_satisfies_iff _ _ _ _ _ _ _ _ _ _ _ _ _).mpr
  exact ⟨hash,adapter_satisfies binary original (MdocRuntime.generator binary.basis) native.claim.sharedWeights native.eta.val
    (CompleteCoupling.alphas binary prime primePlan samples base H native) tape.mask tape.otp⟩

end LfzkV2.Current.ZeroKnowledge.Frontend.HonestAdapter
