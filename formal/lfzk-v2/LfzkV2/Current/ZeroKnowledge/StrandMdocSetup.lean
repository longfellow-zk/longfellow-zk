import LfzkV2.Current.ZeroKnowledge.StrandCanonicalByteOracle
import LfzkV2.Current.ZeroKnowledge.MdocSetupFamily

/-! Public setup is a function of complementary SHA coordinates. A single
finite union of leaf domains covers every possible public setup, before any
oracle is sampled. Overwriting this union preserves all public identifiers
and metadata, including when the observer has queried their preimages. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.StrandMdocSetup
open Application ApplicationSetup ConcreteSetup Frontend TranscriptV2
open scoped Classical
local instance : DecidableEq (Fin 2443) := fun a b => Classical.propDecidable (a = b)
attribute [local instance] StrandCanonicalHiding.columnFintype
attribute [local irreducible] StrandCanonicalHiding.leafWindow

variable {B : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
variable (binary : BinaryCircuit B) (prime : PrimeCircuit)
variable (cantor : Module.Basis (Fin 128) (ZMod 2) B) (scalars : MdocRuntime.Scalars B)
variable (ids : MdocIdentifiers.Identifiers) (bounds : MdocIdentifiers.Bounds binary prime)

local notation "Nodes" => ConcreteSetup.binaryNodes cantor
local notation "Setup" visible => MdocSetupFamily.setup binary prime cantor scalars ids bounds visible
local notation "Leaves" visible => StrandCanonicalHiding.leafWindow binary prime.description prime.plan Nodes scalars
  bounds.inputFits bounds.privateFits (Setup visible)

def leafWindow : Finset Bytes := Finset.univ.biUnion fun visible => Leaves visible

theorem leaves_subset (visible : MdocSetupFamily.Values) :
    (Leaves visible) ⊆ leafWindow binary prime cantor scalars ids bounds := by
  intro raw member
  change raw ∈ Finset.univ.biUnion (fun visible : MdocSetupFamily.Values => Leaves visible)
  simp only [Finset.mem_biUnion,Finset.mem_univ,true_and]
  exact ⟨visible,member⟩

theorem leafWindow_domain :
    ∀ raw ∈ leafWindow binary prime cantor scalars ids bounds, SHAOracle.merkleDomain raw := by
  intro raw member
  obtain ⟨visible,_,member⟩ := Finset.mem_biUnion.mp member
  simp only [StrandCanonicalHiding.leafWindow,StrandLeafWindow.window,
    Finset.mem_image,Finset.mem_univ,true_and] at member
  obtain ⟨leaf,rfl⟩ := member
  exact SHAOracle.leaf_in_domain _ _ _ _ _ _ (by decide) leaf

/-- No query outside the varying domain is changed. This is an equality of
the complete oracle functions, not a statement conditioned on a trace. -/
theorem merge_extend (window : Finset Bytes)
    (domain : ∀ raw ∈ window, SHAOracle.merkleDomain raw)
    (table : {raw // raw ∈ window} → Digest) (outside : Strand.Oracle) :
    SHAOracle.merge SHAOracle.merkleDomain outside (OracleWindow.extend window table outside) =
      OracleWindow.extend window table outside := by
  funext raw
  by_cases member : SHAOracle.merkleDomain raw
  · exact SHAOracle.merge_inside _ _ _ _ member
  · rw [SHAOracle.merge_outside _ _ _ _ member]
    unfold OracleWindow.extend
    rw [dif_neg (fun inside => member (domain raw inside))]

omit [Fintype B] [DecidableEq B] in
theorem values_extend (window : Finset Bytes)
    (domain : ∀ raw ∈ window, SHAOracle.merkleDomain raw)
    (table : {raw // raw ∈ window} → Digest) (outside : Strand.Oracle) :
    MdocSetupFamily.values binary prime cantor scalars ids bounds (OracleWindow.extend window table outside) =
      MdocSetupFamily.values binary prime cantor scalars ids bounds outside := by
  have law := MdocSetupFamily.values_merge binary prime cantor scalars ids bounds outside
    (OracleWindow.extend window table outside)
  rw [merge_extend window domain table outside] at law
  exact law

omit [Fintype B] [DecidableEq B] in
/-- Programming only leaf addresses cannot alter the setup. This version
avoids enumerating the leaf embedding when reasoning about one actual oracle. -/
theorem values_leafOracle {Leaf : Type} (encode : Leaf ↪ Bytes)
    (domain : ∀ leaf, SHAOracle.merkleDomain (encode leaf))
    (table : Leaf → Digest) (outside : Strand.Oracle) :
    MdocSetupFamily.values binary prime cantor scalars ids bounds
        (StrandGhostMerkle.Swap.Slice.oracle encode outside table) =
      MdocSetupFamily.values binary prime cantor scalars ids bounds outside := by
  have unchanged : SHAOracle.merge SHAOracle.merkleDomain outside
      (StrandGhostMerkle.Swap.Slice.oracle encode outside table) =
        StrandGhostMerkle.Swap.Slice.oracle encode outside table := by
    funext raw
    by_cases member : SHAOracle.merkleDomain raw
    · exact SHAOracle.merge_inside _ _ _ _ member
    · rw [SHAOracle.merge_outside _ _ _ _ member]
      symm
      apply StrandGhostMerkle.Swap.replace_off
      intro leaf same
      exact member (same ▸ domain leaf)
  have law := MdocSetupFamily.values_merge binary prime cantor scalars ids bounds outside
    (StrandGhostMerkle.Swap.Slice.oracle encode outside table)
  rw [unchanged] at law
  exact law

omit [Fintype B] [DecidableEq B] in
theorem metadata_extend (window : Finset Bytes)
    (domain : ∀ raw ∈ window, SHAOracle.merkleDomain raw)
    (table : {raw // raw ∈ window} → Digest) (outside : Strand.Oracle) :
    MdocPublicSetup.metadata binary prime cantor scalars ids bounds (OracleWindow.extend window table outside) =
      MdocPublicSetup.metadata binary prime cantor scalars ids bounds outside := by
  have law := MdocPublicSetup.metadata_merge binary prime cantor scalars ids bounds outside
    (OracleWindow.extend window table outside)
  rw [merge_extend window domain table outside] at law
  exact law

end LfzkV2.Current.ZeroKnowledge.StrandMdocSetup
