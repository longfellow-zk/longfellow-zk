import LfzkV2.Current.ZeroKnowledge.MdocSHAWindow
import LfzkV2.Current.ZeroKnowledge.SHAGlobalWindow

/-! One fixed finite SHA marginal for the actual mdoc layout and an arbitrary
raw-byte observer. Public identifiers may depend on complementary SHA answers;
the Merkle codec then selects just one digest-indexed member of this family.
Decoding transcript inputs and routing complementary SHA inputs only remove
queries, so neither operation changes the window selected here. Observer
syntax is fixed here; an observer selected by public setup must first be
covered by the corresponding finite family of programs. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.MdocRawSHAWindow
open Application ApplicationSetup ConcreteSetup Merkle Merkle.MH RecursivePolygero
open scoped Classical
-- These sets describe entire oracle tables. Their membership lemmas are
-- the interface; expanding their finite enumerations is unnecessary.
attribute [local irreducible] SHAGlobalWindow.window SHAGlobalWindow.observerQueries
attribute [local irreducible] SHAObserverWindow.window MdocSHAWindow.codec

variable {B : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable (binary : BinaryCircuit B) (prime : PrimeCircuit)
variable (cantor : Module.Basis (Fin 128) (ZMod 2) B) (scalars : MdocRuntime.Scalars B)
variable (ids : MdocIdentifiers.Identifiers) (bounds : MdocIdentifiers.Bounds binary prime)

local notation "Codecs" => MdocSHAWindow.codec binary prime cantor scalars

local instance pairLeafFintype : Fintype (MdocSHAWindow.Leaf binary prime) :=
  @instFintypeProd _ _
    (MerkleRuntime.leafFintype B (rows binary.description.cells))
    (MerkleRuntime.leafFintype (ZMod Current.Adapter.Mdoc.primeOrder)
      (rows (CellLayout.Prime.cells prime.description.remaining prime.description.pads)))

variable {Request Proof Answer Observed : Type} [Fintype Request] [Fintype Proof] [Fintype Answer]
variable {preM preT postM postT : ℕ}
variable (prior : RandomOracle.TwoOracleTree Bytes Digest Bytes Answer Request preM preT)
variable (after : Request → Proof → RandomOracle.TwoOracleTree Bytes Digest Bytes Answer Observed postM postT)

@[irreducible] def window : Finset Bytes :=
  (SHAGlobalWindow.window Codecs (SHAGlobalWindow.observerQueries prior after)).filter SHAOracle.merkleDomain

theorem mem_window (raw : Bytes) :
    raw ∈ window binary prime cantor scalars prior after ↔
      raw ∈ SHAGlobalWindow.window Codecs (SHAGlobalWindow.observerQueries prior after) ∧
      SHAOracle.merkleDomain raw := by
  rw [window,Finset.mem_filter]

variable {Point : Type} {valid : Point → Prop}
variable (transcript : ByteOracleTransport.Codec Point Bytes valid)
variable (complement : Bytes → Answer) (outside : Bytes → Digest)

theorem contains (context : Digest) :
    SHAObserverWindow.window SHAOracle.merkleDomain outside (Codecs context)
        (transcript.program complement prior)
        (fun request proof => transcript.program complement (after request proof)) ⊆
      window binary prime cantor scalars prior after :=
  by
    intro raw member
    exact (mem_window binary prime cantor scalars prior after raw).mpr ⟨
      SHAGlobalWindow.translated_window_subset Codecs transcript complement prior after
        SHAOracle.merkleDomain outside context member,
      SHAObserverWindow.window_domain SHAOracle.merkleDomain outside (Codecs context)
        (transcript.program complement prior)
        (fun request proof => transcript.program complement (after request proof))
        (MdocSHAWindow.leaf_domain binary prime cantor scalars context)
        (MdocSHAWindow.node_domain binary prime cantor scalars context) raw member⟩

/-- The concrete setup chooses its context using the same SHA oracle.
It contributes no additional family or marginal-independence assumption. -/
theorem contains_actual (SHA : Bytes → Digest) :
    SHAObserverWindow.window SHAOracle.merkleDomain outside
        (MdocSHAWindow.runtimeCodec binary prime cantor scalars ids bounds SHA)
        (transcript.program complement prior)
        (fun request proof => transcript.program complement (after request proof)) ⊆
      window binary prime cantor scalars prior after := by
  rw [MdocSHAWindow.runtime_codec]
  exact contains binary prime cantor scalars prior after transcript complement outside _

omit transcript complement in
theorem extend_outside
    (HM : {raw // raw ∈ window binary prime cantor scalars prior after} → Digest)
    (raw : Bytes) (notDomain : ¬SHAOracle.merkleDomain raw) :
    OracleWindow.extend (window binary prime cantor scalars prior after) HM outside raw = outside raw := by
  apply dif_neg
  intro member
  exact notDomain ((mem_window binary prime cantor scalars prior after raw).mp member).2

omit transcript complement in
theorem merge_extend
    (HM : {raw // raw ∈ window binary prime cantor scalars prior after} → Digest) :
    SHAOracle.merge SHAOracle.merkleDomain outside
        (OracleWindow.extend (window binary prime cantor scalars prior after) HM outside) =
      OracleWindow.extend (window binary prime cantor scalars prior after) HM outside := by
  funext raw
  by_cases member : SHAOracle.merkleDomain raw
  · exact SHAOracle.merge_inside SHAOracle.merkleDomain outside _ raw member
  · rw [SHAOracle.merge_outside SHAOracle.merkleDomain outside _ raw member,
      extend_outside binary prime cantor scalars prior after outside HM raw member]

omit transcript complement in
/-- Sampling the Merkle slice leaves the literal setup hashes on the same
oracle's complementary slice. This is derived from their byte domains. -/
theorem setup_extend
    (HM : {raw // raw ∈ window binary prime cantor scalars prior after} → Digest) :
    MdocPublicSetup.setup binary prime cantor scalars ids bounds
        (OracleWindow.extend (window binary prime cantor scalars prior after) HM outside) =
      MdocPublicSetup.setup binary prime cantor scalars ids bounds outside := by
  have same := MdocPublicSetup.setup_merge binary prime cantor scalars ids bounds outside
    (OracleWindow.extend (window binary prime cantor scalars prior after) HM outside)
  rw [merge_extend binary prime cantor scalars prior after outside HM] at same
  exact same

omit transcript complement in
theorem metadata_extend
    (HM : {raw // raw ∈ window binary prime cantor scalars prior after} → Digest) :
    MdocPublicSetup.metadata binary prime cantor scalars ids bounds
        (OracleWindow.extend (window binary prime cantor scalars prior after) HM outside) =
      MdocPublicSetup.metadata binary prime cantor scalars ids bounds outside := by
  have same := MdocPublicSetup.metadata_merge binary prime cantor scalars ids bounds outside
    (OracleWindow.extend (window binary prime cantor scalars prior after) HM outside)
  rw [merge_extend binary prime cantor scalars prior after outside HM] at same
  exact same

section PublicFamily
variable {Public : Type} [Fintype Public]
variable (priorFamily : Public → RandomOracle.TwoOracleTree Bytes Digest Bytes Answer Request preM preT)
variable (afterFamily : Public → Request → Proof →
  RandomOracle.TwoOracleTree Bytes Digest Bytes Answer Observed postM postT)

/-- Public setup may choose an observer program. Cover every possible
public choice before either oracle marginal is sampled. -/
@[irreducible] def familyWindow : Finset Bytes :=
  Finset.univ.biUnion fun visible => window binary prime cantor scalars (priorFamily visible) (afterFamily visible)

theorem window_subset_family (visible : Public) :
    window binary prime cantor scalars (priorFamily visible) (afterFamily visible) ⊆
      familyWindow binary prime cantor scalars priorFamily afterFamily := by
  intro raw member
  rw [familyWindow]
  exact Finset.mem_biUnion.mpr ⟨visible,Finset.mem_univ _,member⟩

theorem family_domain (raw : Bytes)
    (member : raw ∈ familyWindow binary prime cantor scalars priorFamily afterFamily) :
    SHAOracle.merkleDomain raw := by
  rw [familyWindow] at member
  obtain ⟨visible,_,member⟩ := Finset.mem_biUnion.mp member
  exact ((mem_window binary prime cantor scalars (priorFamily visible) (afterFamily visible) raw).mp member).2

omit transcript complement in
theorem family_merge_extend
    (HM : {raw // raw ∈ familyWindow binary prime cantor scalars priorFamily afterFamily} → Digest) :
    SHAOracle.merge SHAOracle.merkleDomain outside
        (OracleWindow.extend (familyWindow binary prime cantor scalars priorFamily afterFamily) HM outside) =
      OracleWindow.extend (familyWindow binary prime cantor scalars priorFamily afterFamily) HM outside := by
  funext raw
  by_cases member : SHAOracle.merkleDomain raw
  · exact SHAOracle.merge_inside SHAOracle.merkleDomain outside _ raw member
  · rw [SHAOracle.merge_outside SHAOracle.merkleDomain outside _ raw member]
    symm
    apply dif_neg
    exact fun inside => member (family_domain binary prime cantor scalars priorFamily afterFamily raw inside)

end PublicFamily

end LfzkV2.Current.ZeroKnowledge.MdocRawSHAWindow
