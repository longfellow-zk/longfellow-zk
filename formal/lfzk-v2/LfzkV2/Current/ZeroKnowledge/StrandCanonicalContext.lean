import LfzkV2.Current.ZeroKnowledge.StrandCanonicalBackend
import LfzkV2.Current.ZeroKnowledge.FrontendRuntimeStatement

/-! Public runtime configuration and actual numbered challenge oracle, shared by execution, completeness and privacy. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.StrandCanonicalContext
open Application ApplicationSetup ConcreteSetup Frontend SumcheckV2 TranscriptV2
open scoped Classical
variable {B : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
local notation "N" => Adapter.Mdoc.P
variable (binary : BinaryCircuit B) (prime : PrimePublic N 768)
variable (primePlan : FrontendSchedule.Plan N prime.circuit) (binaryNodes : Fin 2792 ↪ B)
variable (scalars : MdocRuntime.Scalars B)
variable (inputFits : 768+prime.remaining+prime.pads < 2^64) (privateFits : binary.nPrivate < 2^64)
variable (setup : FingerprintPrefix.Setup)
local notation "G" => MdocRuntime.geometry binary.description prime binary.plan primePlan
local notation "Sh" => MdocRuntime.shape binary.description prime binary.plan primePlan inputFits privateFits
  (RuntimeStatement.degreeFits binary)
local notation "Repr" => MdocRuntime.representations scalars
local notation "Cfg" => RuntimeStatement.configuration binary prime primePlan binaryNodes scalars inputFits privateFits setup
local notation "Request" => CanonicalRequest.Request Sh binary.nPublic
local notation "Point" => QueryRuntime.Runtime.Point Repr Sh setup binary.nPublic
local notation "Answer" => MdocRuntime.Answer binary.description prime binary.plan primePlan binaryNodes
/-- Expose the already fixed runtime geometry once, so composition never
needs to infer it by unfolding the complete application configuration. -/
def configuration : RuntimeVerifier.Public
    (g := G)
    binary.description prime (backend binaryNodes binary.description.cells)
    (backend ConcreteSetup.primeNodes (CellLayout.Prime.cells prime.remaining prime.pads))
    (fields := MdocRuntime.fields B) (Advice := MdocAdvice.Value)
    (Base := CanonicalRequest.Base Repr Sh setup binary.nPublic)
    (Key := FingerprintPrefix.Key binary.nPublic) (C := Answer) (Salt := Fin 2443 × MerkleNonce) :=
  Cfg

local notation "Public" => configuration binary prime primePlan binaryNodes scalars inputFits privateFits setup
variable {blocks : ℕ}
variable (roundSampler : QueryRuntime.Runtime.Point (MdocRuntime.representations scalars)
  (MdocRuntime.shape binary.description prime binary.plan primePlan inputFits privateFits
    (RuntimeStatement.degreeFits binary)) setup binary.nPublic →
    Merkle.RandomOracle.Tree Strand.Word Strand.Digest
      (Option (MdocRuntime.Answer binary.description prime binary.plan primePlan binaryNodes)) blocks)
variable (SHA : Strand.Oracle)
def actualOracle : Point → Digest × Answer :=
  StrandCanonicalBackend.logicalOracle (g := G) (fields := MdocRuntime.fields B)
    (Advice := MdocAdvice.Value) (C := Answer) binary.description Repr Sh setup roundSampler (Public).fallback SHA


end LfzkV2.Current.ZeroKnowledge.StrandCanonicalContext

-- Existing entry points remain aliases of the declarations at their logical home.
namespace LfzkV2.Current.ZeroKnowledge.StrandCanonicalFullCoupling
export LfzkV2.Current.ZeroKnowledge.StrandCanonicalContext (configuration actualOracle)
end LfzkV2.Current.ZeroKnowledge.StrandCanonicalFullCoupling
