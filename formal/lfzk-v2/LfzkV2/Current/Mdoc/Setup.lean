import LfzkV2.Current.Mdoc.Runtime
import LfzkV2.Current.MdocIdentifiers
import LfzkV2.Current.ConcreteMetadata
import LfzkV2.Current.Parameters.Rate7

/-! One concrete public protocol setup shared by mdoc soundness, privacy
and honest execution. Sampling and witness policies are separate inputs. -/
noncomputable section
namespace LfzkV2.Current.Mdoc.Setup
open Application ApplicationSetup
open scoped Classical
set_option maxRecDepth 4096

variable {B : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable (binary : ConcreteSetup.BinaryCircuit B) (prime : ConcreteSetup.PrimeCircuit)
variable (cantor : Module.Basis (Fin 128) (ZMod 2) B) (scalars : MdocRuntime.Scalars B)
variable (ids : MdocIdentifiers.Identifiers) (bounds : MdocIdentifiers.Bounds binary prime)

/-- Concrete public data; the SHA function is supplied through the identifiers. -/
abbrev runtime : Mdoc.Runtime B where
  binary := binary
  prime := prime.description
  primePlan := prime.plan
  binaryNodes := ConcreteSetup.binaryNodes cantor
  scalars := scalars
  inputFits := bounds.inputFits
  privateFits := bounds.privateFits
  fingerprint := MdocIdentifiers.setup binary prime cantor scalars ids bounds
  metadata := ConcreteMetadata.metadata
    (Advice := MdocAdvice.Value)
    (C := MdocRuntime.Answer binary.description prime.description binary.plan prime.plan (ConcreteSetup.binaryNodes cantor))
    binary.description prime.description
    (MdocRuntime.shape binary.description prime.description binary.plan prime.plan bounds.inputFits bounds.privateFits
      (by change 128 < 2^64; decide))
    (MdocIdentifiers.parameters binary prime cantor scalars ids bounds)
    (MdocIdentifiers.setup binary prime cantor scalars ids bounds)

abbrev protocol := (runtime binary prime cantor scalars ids bounds).protocol

end LfzkV2.Current.Mdoc.Setup
