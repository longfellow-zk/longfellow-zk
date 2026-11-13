import LfzkV2.Current.ZeroKnowledge.FrontendCompleteSimulation

/-! Store the public frontend simulator's actual messages in the complete
runtime body. Backend arrays and authentication are placeholders until the
public affine statement and shared opening sample have been read. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.CompleteFrontendBody

open Frontend ApplicationSetup ConcreteSetup SumcheckV2
open scoped Classical

variable {B Key Base C : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable (binary : BinaryCircuit B) (prime : PrimePublic Adapter.Mdoc.P 768)
variable (primePlan : FrontendSchedule.Plan Adapter.Mdoc.P prime.circuit)

def rawBody (commitment : Digest)
    (result : CompleteSimulation.RawResult binary prime primePlan Key Base C) :
    Body (MdocRuntime.geometry binary.description prime binary.plan primePlan) (MdocRuntime.fields B)
      MdocAdvice.Value (OpeningBody.Authentication (MdocRuntime.geometry binary.description prime binary.plan primePlan)) where
  commitment := commitment
  fingerprints := result.fingerprints
  mu := result.mu
  advice := result.advice
  binary := CompleteShape.bodyEquiv binary.plan result.binaryPayload
  prime := CompleteShape.bodyEquiv primePlan result.primePayload
  packing := result.packing
  binaryBackend := ⟨⟨fun _ => (0:B),fun _ => (0:B)⟩,fun _ _ => (0:B)⟩
  primeBackend := ⟨⟨fun _ => (0:Adapter.Mdoc.P),fun _ => (0:Adapter.Mdoc.P)⟩,
    fun _ _ => (0:Adapter.Mdoc.P)⟩
  authentication := {
    context := fun _ => 0
    nonce := fun _ _ => 0
    frontierLength := ⟨0,Nat.succ_pos _⟩
    frontier := Fin.elim0 }

def body (commitment : Digest)
    (result : CompleteSimulation.Result binary prime primePlan Key Base C) :
    Body (MdocRuntime.geometry binary.description prime binary.plan primePlan) (MdocRuntime.fields B)
      MdocAdvice.Value (OpeningBody.Authentication (MdocRuntime.geometry binary.description prime binary.plan primePlan)) :=
  rawBody binary prime primePlan commitment result.raw

omit [Fintype B] [DecidableEq B] in
theorem prime_decode (commitment : Digest)
    (result : CompleteSimulation.Result binary prime primePlan Key Base C) :
    FrontendBody.decode id prime.circuit primePlan.frontend
      (body binary prime primePlan commitment result).prime = some result.primePayload :=
  CompleteShape.decode_bodyEquiv primePlan result.primePayload

omit [Fintype B] [DecidableEq B] in
theorem binary_decode (commitment : Digest)
    (result : CompleteSimulation.Result binary prime primePlan Key Base C) :
    FrontendBody.decode id binary.description.circuit binary.plan.frontend
      (body binary prime primePlan commitment result).binary = some result.binaryPayload :=
  CompleteShape.decode_bodyEquiv binary.plan result.binaryPayload

end LfzkV2.Current.ZeroKnowledge.CompleteFrontendBody
