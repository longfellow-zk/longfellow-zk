import LfzkV2.Current.MdocRuntime
import LfzkV2.Current.Protocol.Sampling
import LfzkV2.Current.ConcreteSetup
import LfzkV2.Current.Parameters.Rate7

/-! The concrete circuit and codec data shared by mdoc soundness, privacy
and honest execution. No witness, sampling law or execution certificate is
stored in this setup. Public identifiers and causal metadata may vary with
the public oracle slice. -/
noncomputable section
namespace LfzkV2.Current.Mdoc
open Application ApplicationSetup ConcreteSetup
open scoped Classical

structure Runtime (B : Type) [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B] where
  binary : BinaryCircuit B
  prime : PrimePublic (ZMod Adapter.Mdoc.primeOrder) 768
  primePlan : FrontendSchedule.Plan (ZMod Adapter.Mdoc.primeOrder) prime.circuit
  binaryNodes : Fin 2792 ↪ B
  scalars : MdocRuntime.Scalars B
  inputFits : 768+prime.remaining+prime.pads < 2^64
  privateFits : binary.nPrivate < 2^64
  fingerprint : FingerprintPrefix.Setup
  metadata : CanonicalRequest.Metadata (Advice := MdocAdvice.Value)
    (C := MdocRuntime.Answer binary.description prime binary.plan primePlan binaryNodes)
    (MdocRuntime.shape binary.description prime binary.plan primePlan inputFits privateFits
      (by change 128 < 2^64; decide)) binary.nPublic

namespace Runtime
variable {B : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable (S : Runtime B)
local notation "g" => MdocRuntime.geometry S.binary.description S.prime S.binary.plan S.primePlan

abbrev protocol : Protocol.Setup FixedRate.Rate7.certificate g (MdocRuntime.fields B) MdocAdvice.Value B
    (shared := 768) (maskBits := 256) (adviceBits := 10) where
  binary := S.binary.description
  prime := S.prime
  P := MdocRuntime.binaryBackend S.binary.description S.binaryNodes
  R := MdocRuntime.primeBackend S.prime
  countBinary := Geometry.affineRows g Side.binary
  countPrime := Geometry.affineRows g Side.prime
  binaryCapacity := MdocRuntime.binaryCapacity S.binary.description S.binary.plan
  primeCapacity := MdocRuntime.primeCapacity S.prime S.primePlan
  repr := MdocRuntime.representations S.scalars
  shape := MdocRuntime.shape S.binary.description S.prime S.binary.plan S.primePlan
    S.inputFits S.privateFits (by change 128 < 2^64; decide)
  fingerprint := S.fingerprint
  binaryPlan := S.binary.plan
  primePlan := S.primePlan
  binaryGeometry := rfl
  primeGeometry := rfl
  binaryFits := Nat.le_max_right _ _
  primeFits := Nat.le_max_right _ _
  degreeFits := Nat.le_max_left _ _
  rowsFit := Nat.le_max_left _ _
  cfg := MdocRuntime.configuration S.binary.description S.prime S.binary.plan S.primePlan S.binaryNodes S.scalars
    S.inputFits S.privateFits (by change 128 < 2^64; decide) S.fingerprint
    (MdocRuntime.field_card S.binary.basis) (MdocRuntime.polynomialX S.binary.basis)
  binaryCount := rfl
  primeCount := rfl
  metadata := S.metadata
  columnsFit := by decide

end Runtime
end LfzkV2.Current.Mdoc
