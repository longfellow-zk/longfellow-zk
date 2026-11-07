import LfzkV2.Current.ZeroKnowledge.MdocSetupFamily
import LfzkV2.Current.ZeroKnowledge.ObserverFamilySupport
import LfzkV2.Current.ZeroKnowledge.TranscriptGlobalWindow
import LfzkV2.Current.ZeroKnowledge.MdocRawSHAWindow
import LfzkV2.Current.ZeroKnowledge.BackendRuntimeContext

/-! Fixed raw-oracle marginals for the actual mdoc setup. The finite public
setup family covers every digest-selected observer program. Its derived
private-state support is shared across the family; the original private-state
type need not be finite. Neither window depends on the sampled oracle. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.MdocOracleWindows
open Application ApplicationSetup ConcreteSetup Merkle Merkle.MH
open scoped Classical
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

variable {B : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable (binary : BinaryCircuit B) (prime : PrimeCircuit)
variable (cantor : Module.Basis (Fin 128) (ZMod 2) B) (scalars : MdocRuntime.Scalars B)
variable (ids : MdocIdentifiers.Identifiers) (bounds : MdocIdentifiers.Bounds binary prime)

abbrev Answer := MdocRuntime.Answer binary.description prime.description binary.plan prime.plan (ConcreteSetup.binaryNodes cantor)
abbrev Output := CanonicalRuntime.Output (Advice := MdocAdvice.Value) binary.description
  (MdocRuntime.shape binary.description prime.description binary.plan prime.plan bounds.inputFits bounds.privateFits
    (by change 128 < 2^64; decide))

attribute [local instance] BackendRuntime.requestFintype BackendRuntime.leafFintype

local instance answerFintype : Fintype (Answer binary prime cantor) := inferInstance
local instance outputFintype : Fintype (Output binary prime bounds) := inferInstance
local instance familyPointFintype (visible : MdocSetupFamily.Values) :
    Fintype (MdocSetupFamily.Point binary prime cantor scalars ids bounds visible) :=
  MdocSetupFamily.pointFintype binary prime cantor scalars ids bounds visible

local instance pairLeafFintype : Fintype (MdocSHAWindow.Leaf binary prime) :=
  @instFintypeProd _ _
    (MerkleRuntime.leafFintype B (rows binary.description.cells))
    (MerkleRuntime.leafFintype (ZMod Current.Adapter.Mdoc.primeOrder)
      (rows (CellLayout.Prime.cells prime.description.remaining prime.description.pads)))

variable {Context Observed : Type} {preM preT postM postT : ℕ}
variable (priorFamily : MdocSetupFamily.Values → RandomOracle.TwoOracleTree Bytes Digest Bytes
  (Digest × Answer binary prime cantor) Context preM preT)
variable (afterFamily : MdocSetupFamily.Values → Context → Option (Output binary prime bounds) →
  RandomOracle.TwoOracleTree Bytes Digest Bytes (Digest × Answer binary prime cantor) Observed postM postT)

abbrev Support := ObserverFamilySupport.Support priorFamily

def supportedPrior (visible : MdocSetupFamily.Values) := ObserverFamilySupport.restrict priorFamily visible

def supportedAfter (visible : MdocSetupFamily.Values) (context : Support binary prime cantor priorFamily)
    (proof : Option (Output binary prime bounds)) := afterFamily visible context.val proof

@[irreducible] def merkleWindow : Finset Bytes :=
  MdocRawSHAWindow.familyWindow binary prime cantor scalars
    (supportedPrior binary prime cantor priorFamily)
    (supportedAfter binary prime cantor bounds priorFamily afterFamily)

variable (fits : (MdocRuntime.geometry binary.description prime.description binary.plan prime.plan).roles.length < 2^64)

@[irreducible] def transcriptWindow : Finset Bytes :=
  TranscriptGlobalWindow.window
    (MdocSetupFamily.Point binary prime cantor scalars ids bounds)
    (MdocSetupFamily.Canonical binary prime cantor scalars ids bounds)
    (MdocSetupFamily.codec binary prime cantor scalars ids bounds fits)
    priorFamily afterFamily

local notation "Shape" => MdocRuntime.shape binary.description prime.description binary.plan prime.plan
  bounds.inputFits bounds.privateFits (by change 128 < 2^64; decide)
local notation "Repr" => MdocRuntime.representations scalars
local notation "ActualSetup" SHA => MdocPublicSetup.setup binary prime cantor scalars ids bounds SHA
local notation "ActualCfg" SHA => MdocPublicSetup.configuration binary prime cantor scalars ids bounds SHA

def byteCodec (SHA : Bytes → Digest) :
    ByteOracleTransport.Codec (QueryRuntime.Runtime.Point Repr Shape (ActualSetup SHA) binary.nPublic) Bytes
      (QueryRuntime.Runtime.Canonical Repr Shape (ActualSetup SHA) binary.nPublic) :=
  QueryRuntime.Runtime.codec Repr Shape (ActualSetup SHA) binary.nPublic fits

theorem transcript_covers (SHA : Bytes → Digest) :
    ∀ point : {point : QueryRuntime.Runtime.Point Repr Shape (ActualSetup SHA) binary.nPublic //
      QueryRuntime.Runtime.Canonical Repr Shape (ActualSetup SHA) binary.nPublic point},
      (byteCodec binary prime cantor scalars ids bounds fits SHA).encode point ∈
        transcriptWindow binary prime cantor scalars ids bounds priorFamily afterFamily fits := by
  unfold byteCodec transcriptWindow
  rw [MdocSetupFamily.setup_values binary prime cantor scalars ids bounds SHA]
  intro point
  exact TranscriptGlobalWindow.canonical_mem
    (MdocSetupFamily.Point binary prime cantor scalars ids bounds)
    (MdocSetupFamily.Canonical binary prime cantor scalars ids bounds)
    (MdocSetupFamily.codec binary prime cantor scalars ids bounds fits)
    priorFamily afterFamily (MdocSetupFamily.values binary prime cantor scalars ids bounds SHA) point

theorem transcript_observer_subset (visible : MdocSetupFamily.Values) :
    TranscriptGlobalWindow.observerQueries (priorFamily visible) (afterFamily visible) ⊆
      transcriptWindow binary prime cantor scalars ids bounds priorFamily afterFamily fits := by
  unfold transcriptWindow
  exact TranscriptGlobalWindow.observer_subset
    (MdocSetupFamily.Point binary prime cantor scalars ids bounds)
    (MdocSetupFamily.Canonical binary prime cantor scalars ids bounds)
    (MdocSetupFamily.codec binary prime cantor scalars ids bounds fits) priorFamily afterFamily visible

theorem merkle_contains_actual (SHA : Bytes → Digest) (complement : Bytes → Digest × Answer binary prime cantor)
    (outside : Bytes → Digest) :
    SHAObserverWindow.window SHAOracle.merkleDomain outside
      (MdocSHAWindow.runtimeCodec binary prime cantor scalars ids bounds SHA)
      ((byteCodec binary prime cantor scalars ids bounds fits SHA).program complement
        (supportedPrior binary prime cantor priorFamily (MdocSetupFamily.values binary prime cantor scalars ids bounds SHA)))
      (fun context proof => (byteCodec binary prime cantor scalars ids bounds fits SHA).program complement
        (supportedAfter binary prime cantor bounds priorFamily afterFamily
          (MdocSetupFamily.values binary prime cantor scalars ids bounds SHA) context proof)) ⊆
      merkleWindow binary prime cantor scalars bounds priorFamily afterFamily := by
  unfold merkleWindow
  apply (MdocRawSHAWindow.contains_actual binary prime cantor scalars ids bounds
    (supportedPrior binary prime cantor priorFamily (MdocSetupFamily.values binary prime cantor scalars ids bounds SHA))
    (supportedAfter binary prime cantor bounds priorFamily afterFamily (MdocSetupFamily.values binary prime cantor scalars ids bounds SHA))
    (byteCodec binary prime cantor scalars ids bounds fits SHA) complement outside SHA).trans
  exact MdocRawSHAWindow.window_subset_family binary prime cantor scalars
    (supportedPrior binary prime cantor priorFamily) (supportedAfter binary prime cantor bounds priorFamily afterFamily)
    (MdocSetupFamily.values binary prime cantor scalars ids bounds SHA)

theorem backend_window_contains (SHA : Bytes → Digest) (complement : Bytes → Digest × Answer binary prime cantor)
    (outside : Bytes → Digest) :
    BackendRuntimeContext.window binary prime.description prime.plan (ConcreteSetup.binaryNodes cantor)
      Repr Shape (ActualSetup SHA) (ActualCfg SHA)
      ((byteCodec binary prime cantor scalars ids bounds fits SHA).program complement
        (supportedPrior binary prime cantor priorFamily (MdocSetupFamily.values binary prime cantor scalars ids bounds SHA)))
      (fun context proof => (byteCodec binary prime cantor scalars ids bounds fits SHA).program complement
        (supportedAfter binary prime cantor bounds priorFamily afterFamily
          (MdocSetupFamily.values binary prime cantor scalars ids bounds SHA) context proof)) outside ⊆
      merkleWindow binary prime cantor scalars bounds priorFamily afterFamily := by
  have same : BackendRuntime.codec binary prime.description prime.plan (ConcreteSetup.binaryNodes cantor)
      Repr Shape (ActualSetup SHA) (ActualCfg SHA) =
      MdocSHAWindow.runtimeCodec binary prime cantor scalars ids bounds SHA := rfl
  change SHAObserverWindow.window SHAOracle.merkleDomain outside
    (BackendRuntime.codec binary prime.description prime.plan (ConcreteSetup.binaryNodes cantor)
      Repr Shape (ActualSetup SHA) (ActualCfg SHA)) _ _ ⊆ _
  rw [same]
  exact merkle_contains_actual binary prime cantor scalars ids bounds priorFamily afterFamily fits SHA complement outside

theorem merkle_domain (raw : Bytes)
    (member : raw ∈ merkleWindow binary prime cantor scalars bounds priorFamily afterFamily) :
    SHAOracle.merkleDomain raw := by
  unfold merkleWindow at member
  exact MdocRawSHAWindow.family_domain binary prime cantor scalars
    (supportedPrior binary prime cantor priorFamily)
    (supportedAfter binary prime cantor bounds priorFamily afterFamily) raw member

theorem merkle_merge_extend (outside : Bytes → Digest)
    (HM : {raw // raw ∈ merkleWindow binary prime cantor scalars bounds priorFamily afterFamily} → Digest) :
    SHAOracle.merge SHAOracle.merkleDomain outside
      (OracleWindow.extend (merkleWindow binary prime cantor scalars bounds priorFamily afterFamily) HM outside) =
      OracleWindow.extend (merkleWindow binary prime cantor scalars bounds priorFamily afterFamily) HM outside := by
  unfold merkleWindow at HM ⊢
  exact MdocRawSHAWindow.family_merge_extend binary prime cantor scalars outside
    (supportedPrior binary prime cantor priorFamily)
    (supportedAfter binary prime cantor bounds priorFamily afterFamily) HM

theorem values_extend (outside : Bytes → Digest)
    (HM : {raw // raw ∈ merkleWindow binary prime cantor scalars bounds priorFamily afterFamily} → Digest) :
    MdocSetupFamily.values binary prime cantor scalars ids bounds
      (OracleWindow.extend (merkleWindow binary prime cantor scalars bounds priorFamily afterFamily) HM outside) =
      MdocSetupFamily.values binary prime cantor scalars ids bounds outside := by
  have same := MdocSetupFamily.values_merge binary prime cantor scalars ids bounds outside
    (OracleWindow.extend (merkleWindow binary prime cantor scalars bounds priorFamily afterFamily) HM outside)
  rw [merkle_merge_extend binary prime cantor scalars bounds priorFamily afterFamily outside HM] at same
  exact same

end LfzkV2.Current.ZeroKnowledge.MdocOracleWindows
