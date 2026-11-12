import LfzkV2.Current.Protocol.Setup
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
local notation "c" => FixedRate.Rate7.certificate
local notation "bp" => binary.description
local notation "pp" => prime.description
local notation "nodes" => ConcreteSetup.binaryNodes cantor
local notation "P" => MdocRuntime.binaryBackend bp nodes
local notation "R" => MdocRuntime.primeBackend pp
local notation "g" => MdocRuntime.geometry bp pp binary.plan prime.plan
local notation "repr" => MdocRuntime.representations scalars
local notation "shape" => MdocRuntime.shape bp pp binary.plan prime.plan bounds.inputFits bounds.privateFits (by change 128 < 2^64; decide)
local notation "setup" => MdocIdentifiers.setup binary prime cantor scalars ids bounds
local notation "cfg" => MdocRuntime.configuration bp pp binary.plan prime.plan nodes scalars
  bounds.inputFits bounds.privateFits (by change 128 < 2^64; decide) setup (MdocRuntime.field_card binary.basis)
  (MdocRuntime.polynomialX binary.basis)
local notation "Answer" => MdocRuntime.Answer bp pp binary.plan prime.plan nodes
local notation "cb" => Geometry.affineRows g Side.binary
local notation "cp" => Geometry.affineRows g Side.prime
local notation "bc" => MdocRuntime.binaryCapacity bp binary.plan
local notation "pc" => MdocRuntime.primeCapacity pp prime.plan
local notation "params" => MdocIdentifiers.parameters binary prime cantor scalars ids bounds
local notation "metadata" => ConcreteMetadata.metadata (Advice := MdocAdvice.Value) (C := Answer)
  bp pp shape params setup
local notation "bf" => Nat.le_max_right (BinaryPublic.degree bp) binary.plan.capacity
local notation "primeFits" => Nat.le_max_right ((Layered.Circuit.layers (PrimePublic.circuit pp))+1) prime.plan.capacity
local notation "df" => Nat.le_max_left (BinaryPublic.degree bp) binary.plan.capacity
local notation "rf" => Nat.le_max_left ((Layered.Circuit.layers (PrimePublic.circuit pp))+1) prime.plan.capacity

abbrev protocol : Protocol.Setup c g (MdocRuntime.fields B) MdocAdvice.Value B
    (shared := 768) (maskBits := 256) (adviceBits := 10) where
  «binary» := bp
  «prime» := pp
  «P» := P
  «R» := R
  «countBinary» := cb
  «countPrime» := cp
  «binaryCapacity» := bc
  «primeCapacity» := pc
  «repr» := repr
  «shape» := shape
  «fingerprint» := setup
  «binaryPlan» := binary.plan
  «primePlan» := prime.plan
  «binaryGeometry» := rfl
  «primeGeometry» := rfl
  «binaryFits» := bf
  «primeFits» := primeFits
  «degreeFits» := df
  «rowsFit» := rf
  «cfg» := cfg
  «binaryCount» := rfl
  «primeCount» := rfl
  «metadata» := metadata
  «columnsFit» := by decide

end LfzkV2.Current.Mdoc.Setup
