import LfzkV2.Current.Mdoc.OracleWindow

/-! The four actual public-setup hash evaluations form a finite oracle
program. Its all-branch support includes the joint-context input selected
by the two component-context answers; no setup input is supplied as advice. -/
noncomputable section
namespace LfzkV2.Current.Mdoc.SetupSupport
open LfzkV2.Current.ZeroKnowledge
open Application ApplicationSetup ConcreteSetup Frontend TranscriptV2 Merkle.RandomOracle
open scoped Classical
attribute [local irreducible] OracleWindow.queries
variable {B : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable (binary : BinaryCircuit B) (prime : PrimeCircuit)
variable (cantor : Module.Basis (Fin 128) (ZMod 2) B) (scalars : MdocRuntime.Scalars B)
variable (ids : MdocIdentifiers.Identifiers) (bounds : MdocIdentifiers.Bounds binary prime)

private def fragmentBytes : Bytes :=
  MetadataIdentifiers.fragmentBytes scalars.binary.encode binary.description.shape
    (binary.nPublic+binary.nPrivate+2*(768+256+10)) binary.nPublic (binary.nPublic+binary.nPrivate)

def program : Tree Bytes Digest Mdoc.SetupFamily.Values 4 :=
  .query (fragmentBytes binary scalars) fun fragment =>
  .query (MdocIdentifiers.contextBytes (MdocIdentifiers.binaryDomain cantor scalars) (binary.description.cells+2)) fun bc =>
  .query (MdocIdentifiers.contextBytes (MdocIdentifiers.primeDomain scalars)
    (CellLayout.Prime.cells prime.description.remaining prime.description.pads+2)) fun pc =>
  .query (MdocIdentifiers.jointContextBytes bc pc) fun joint =>
  .done ⟨fragment,bc,pc,joint⟩

omit [Fintype B] [DecidableEq B] in
theorem program_result (SHA : Strand.Oracle) :
    ((program binary prime cantor scalars).run SHA).1 =
      Mdoc.SetupFamily.values binary prime cantor scalars ids bounds SHA := rfl

def window : Finset Bytes := OracleWindow.queries (program binary prime cantor scalars)

omit [Fintype B] [DecidableEq B] in
theorem values_congr (first second : Strand.Oracle)
    (same : ∀ raw ∈ window binary prime cantor scalars, first raw = second raw) :
    Mdoc.SetupFamily.values binary prime cantor scalars ids bounds first =
      Mdoc.SetupFamily.values binary prime cantor scalars ids bounds second := by
  have run : (program binary prime cantor scalars).run first = (program binary prime cantor scalars).run second := by
    apply Tree.run_congr_on_trace
    intro qa member
    exact (same qa.1 (OracleWindow.trace_mem_queries _ second qa member)).trans (Tree.trace_sound _ second qa member).symm
  exact (program_result binary prime cantor scalars ids bounds first).symm.trans
    ((congrArg Prod.fst run).trans (program_result binary prime cantor scalars ids bounds second))

/-- A digest-selected member of the same concrete runtime family used by
soundness and honest execution. Only the public setup values vary. -/
abbrev runtime (visible : Mdoc.SetupFamily.Values) : Mdoc.Runtime B :=
  { Mdoc.PublicSetup.runtime binary prime cantor scalars ids bounds (fun _ => 0) with
    fingerprint := Mdoc.SetupFamily.setup binary prime cantor scalars ids bounds visible }

abbrev protocol (visible : Mdoc.SetupFamily.Values) :=
  (runtime binary prime cantor scalars ids bounds visible).protocol

/-- The finite family selects exactly the setup built from the actual SHA
oracle; it is not an independently assumed public configuration. -/
theorem runtime_actual (SHA : Strand.Oracle) :
    runtime binary prime cantor scalars ids bounds
        (Mdoc.SetupFamily.values binary prime cantor scalars ids bounds SHA) =
      Mdoc.PublicSetup.runtime binary prime cantor scalars ids bounds SHA := rfl

end LfzkV2.Current.Mdoc.SetupSupport
