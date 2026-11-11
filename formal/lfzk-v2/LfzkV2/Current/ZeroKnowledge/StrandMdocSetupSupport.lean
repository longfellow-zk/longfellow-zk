import LfzkV2.Current.ZeroKnowledge.StrandMdocSetup

/-! The four actual public-setup hash evaluations form a finite oracle
program. Its all-branch support includes the joint-context input selected
by the two component-context answers; no setup input is supplied as advice. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.StrandMdocSetupSupport
open Application ApplicationSetup ConcreteSetup Frontend TranscriptV2 Merkle.RandomOracle
open scoped Classical
attribute [local irreducible] OracleWindow.queries
variable {B : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable (binary : BinaryCircuit B) (prime : PrimeCircuit)
variable (cantor : Module.Basis (Fin 128) (ZMod 2) B) (scalars : MdocRuntime.Scalars B)
variable (ids : MdocIdentifiers.Identifiers) (bounds : MdocIdentifiers.Bounds binary prime)

private def templateBytes : Bytes :=
  MetadataIdentifiers.adapterBytes scalars.binary.encode binary.description.shape
    (binary.nPublic+binary.nPrivate) binary.nPublic
    (ConcreteMetadata.adapterSources binary.description) (ConcreteMetadata.adapterPads binary.description)
    (fun _ _ => 1) (MdocRuntime.polynomialX binary.basis) (fun _ _ => false) (fun _ => 1)

def program : Tree Bytes Digest MdocSetupFamily.Values 4 :=
  .query (templateBytes binary scalars) fun template =>
  .query (MdocIdentifiers.contextBytes (MdocIdentifiers.binaryDomain cantor scalars) (binary.description.cells+2)) fun bc =>
  .query (MdocIdentifiers.contextBytes (MdocIdentifiers.primeDomain scalars)
    (CellLayout.Prime.cells prime.description.remaining prime.description.pads+2)) fun pc =>
  .query (MdocIdentifiers.jointContextBytes bc pc) fun joint =>
  .done ⟨template,bc,pc,joint⟩

omit [Fintype B] [DecidableEq B] in
theorem program_result (SHA : Strand.Oracle) :
    ((program binary prime cantor scalars).run SHA).1 =
      MdocSetupFamily.values binary prime cantor scalars ids bounds SHA := rfl

def window : Finset Bytes := OracleWindow.queries (program binary prime cantor scalars)

omit [Fintype B] [DecidableEq B] in
theorem values_congr (first second : Strand.Oracle)
    (same : ∀ raw ∈ window binary prime cantor scalars, first raw = second raw) :
    MdocSetupFamily.values binary prime cantor scalars ids bounds first =
      MdocSetupFamily.values binary prime cantor scalars ids bounds second := by
  have run : (program binary prime cantor scalars).run first = (program binary prime cantor scalars).run second := by
    apply Tree.run_congr_on_trace
    intro qa member
    exact (same qa.1 (OracleWindow.trace_mem_queries _ second qa member)).trans (Tree.trace_sound _ second qa member).symm
  exact (program_result binary prime cantor scalars ids bounds first).symm.trans
    ((congrArg Prod.fst run).trans (program_result binary prime cantor scalars ids bounds second))

def metadata (visible : MdocSetupFamily.Values) : CanonicalRequest.Metadata (Advice := MdocAdvice.Value)
    (C := MdocRuntime.Answer binary.description prime.description binary.plan prime.plan (ConcreteSetup.binaryNodes cantor))
    (MdocRuntime.shape binary.description prime.description binary.plan prime.plan bounds.inputFits bounds.privateFits (RuntimeStatement.degreeFits binary)) binary.nPublic :=
  let fixed := MdocIdentifiers.parameters binary prime cantor scalars
    (MdocPublicSetup.identifiers ids (fun _ => 0)) bounds
  let params := { fixed with binaryContext := visible.binaryContext, primeContext := visible.primeContext }
  ConcreteMetadata.metadata binary.description prime.description (MdocRuntime.shape binary.description prime.description binary.plan prime.plan bounds.inputFits bounds.privateFits (RuntimeStatement.degreeFits binary)) params
    (MdocSetupFamily.setup binary prime cantor scalars ids bounds visible)

omit [Fintype B] [DecidableEq B] in
/-- The observer reconstructs exactly the metadata used by the prover;
no independent identifier or verifier configuration is assumed. -/
theorem metadata_actual (SHA : Strand.Oracle) :
    metadata binary prime cantor scalars ids bounds
      (MdocSetupFamily.values binary prime cantor scalars ids bounds SHA) =
    MdocPublicSetup.metadata binary prime cantor scalars ids bounds SHA := rfl

omit [Fintype B] [DecidableEq B] in
theorem metadata_congr (first second : Strand.Oracle)
    (same : MdocSetupFamily.values binary prime cantor scalars ids bounds first =
      MdocSetupFamily.values binary prime cantor scalars ids bounds second) :
    MdocPublicSetup.metadata binary prime cantor scalars ids bounds first =
      MdocPublicSetup.metadata binary prime cantor scalars ids bounds second := by
  exact (metadata_actual binary prime cantor scalars ids bounds first).symm.trans
    ((congrArg (metadata binary prime cantor scalars ids bounds) same).trans
      (metadata_actual binary prime cantor scalars ids bounds second))

end LfzkV2.Current.ZeroKnowledge.StrandMdocSetupSupport
