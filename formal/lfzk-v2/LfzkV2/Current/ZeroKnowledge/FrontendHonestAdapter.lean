import LfzkV2.Current.ZeroKnowledge.FrontendHonestBinaryRows

/-! Honest generated-adapter correctness for the actual independently
sampled scalar and two two-byte OTPs. Only ten bits of each pad are consumed by
the circuit; the six high bits of each are an independent inert coordinate.
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
    (weights : Fin 768 → P) (eta : P) (alpha : Adapter.Mdoc.Alphas) (mask : P) (otp : (Fin 2 → AdapterBits.RawWord)) :
    let mu := Adapter.Mdoc.offset weights (WitnessInputs.shared binary original) eta+mask
    let advice := AdapterBits.xorValue (Adapter.Mdoc.advice weights (WitnessInputs.shared binary original) eta alpha mu)
      (AdapterBits.rawOtpEquiv otp).1
    CompleteInputs.recoveredPrivate binary original weights eta alpha mu advice =
      WitnessInputs.privateValues binary original (Adapter.canonicalMask Adapter.Mdoc.maskCapacity mask)
        (fun tree i => (otp tree).val.testBit i.val) := by
  dsimp only [CompleteInputs.recoveredPrivate]
  rw [Adapter.Mdoc.recoverMask_mu,Equiv.symm_apply_apply]
  apply congrArg (WitnessInputs.privateValues binary original _)
  funext tree i
  exact AdapterBits.rawOtp_bits otp tree i

omit [Fintype B] [DecidableEq B] in
/-- On the honest committed bits, every tree's virtual leaves multiply to one. -/
theorem adapter_satisfies (original : Fin binary.nPrivate → Bool) (generator : Bˣ)
    (weights : Fin 768 → P) (eta : P) (alpha : Adapter.Mdoc.Alphas) (mask : P) (otp : (Fin 2 → AdapterBits.RawWord))
    (tree : Fin 2) :
    let mu := Adapter.Mdoc.offset weights (WitnessInputs.shared binary original) eta+mask
    let advice := AdapterBits.xorValue (Adapter.Mdoc.advice weights (WitnessInputs.shared binary original) eta alpha mu)
      (AdapterBits.rawOtpEquiv otp).1
    ∏ i, (Current.Adapter.Leaves.tree binary.description.sources
      (fun j => generator^((alpha mu tree).val*Adapter.Mdoc.weights weights eta j).val)
      (binary.advicePrivate tree) (generator^(-(Current.Adapter.Mdoc.primeOrder : ℤ)))
      (MdocAdvice.bits advice tree) (generator^((alpha mu tree).val*mu).val) i).value
        (Current.Adapter.Circuit.bitValue ∘ WitnessInputs.privateValues binary original
          (Adapter.canonicalMask Adapter.Mdoc.maskCapacity mask) (fun tree i => (otp tree).val.testBit i.val)) = 1 := by
  letI : CharP B 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) B).injective 2
  dsimp only
  rw [← private_recovered binary original weights eta alpha mask otp]
  exact CompleteInputs.recovered_adapter_satisfies binary original generator weights eta alpha _ _ tree

variable (prime : PrimePublic P 768) (primePlan : FrontendSchedule.Plan P prime.circuit)
variable (samples : ConcreteMetadata.Samples B C)
variable (base : CompleteSimulation.BaseWriter binary prime primePlan (Base := Base) (C := C))
variable (H : CompleteSimulation.Point binary prime primePlan (Key := Key) (Base := Base) → Digest × C)

def advice (native : CompleteSimulation.PrimePrefix binary prime primePlan Key Base C)
    (original : Fin binary.nPrivate → Bool) (tape : CompleteHonest.Tape binary prime) : MdocAdvice.Value :=
  let mu := Adapter.Mdoc.offset native.claim.sharedWeights (WitnessInputs.shared binary original) native.eta.val+tape.mask
  AdapterBits.xorValue (Adapter.Mdoc.advice native.claim.sharedWeights (WitnessInputs.shared binary original) native.eta.val
    (CompleteCoupling.alphas binary prime primePlan samples base H native) mu) (AdapterBits.rawOtpEquiv tape.otp).1

/-- The honest virtual definitions for this tape. -/
def entries (native : CompleteSimulation.PrimePrefix binary prime primePlan Key Base C)
    (original : Fin binary.nPrivate → Bool) (tape : CompleteHonest.Tape binary prime) :
    Fin (2*(768+256+10)) → VirtualInput (Fin binary.nPrivate) B :=
  let mu := Adapter.Mdoc.offset native.claim.sharedWeights (WitnessInputs.shared binary original) native.eta.val+tape.mask
  let converted := CompleteSimulation.conversionPrefix binary prime primePlan samples base H native mu
  CompleteSimulation.entries binary prime primePlan native converted
    (advice binary prime primePlan samples base H native original tape)

/-- This premise contains only the ordinary hash checks. The two adapter
assertions are established by `adapter_satisfies`. -/
def hashChecks (native : CompleteSimulation.PrimePrefix binary prime primePlan Key Base C)
    (original : Fin binary.nPrivate → Bool) (tape : CompleteHonest.Tape binary prime) : Prop :=
  MdocWitness.HashChecks binary (CompleteHonest.binaryInputs binary prime original tape
    (entries binary prime primePlan samples base H native original tape))

omit [Fintype B] [DecidableEq B] in
theorem generated_satisfies (native : CompleteSimulation.PrimePrefix binary prime primePlan Key Base C)
    (original : Fin binary.nPrivate → Bool) (tape : CompleteHonest.Tape binary prime)
    (hash : hashChecks binary prime primePlan samples base H native original tape) :
    binary.description.circuit.Satisfies (CompleteHonest.binaryInputs binary prime original tape
      (entries binary prime primePlan samples base H native original tape)) := by
  letI : CharP B 2 := charP_of_injective_algebraMap (algebraMap (ZMod 2) B).injective 2
  apply MdocWitness.satisfies_of binary _ _ hash
  intro tree
  have h := adapter_satisfies binary original (MdocRuntime.generator binary.basis) native.claim.sharedWeights
    native.eta.val (CompleteCoupling.alphas binary prime primePlan samples base H native) tape.mask tape.otp tree
  simp only [entries,CompleteSimulation.entries,BinaryPublic.entries,Equiv.symm_apply_apply]
  exact h

end LfzkV2.Current.ZeroKnowledge.Frontend.HonestAdapter
