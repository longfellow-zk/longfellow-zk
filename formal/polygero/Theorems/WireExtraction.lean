import polygero.Theorems.Extraction
import polygero.Recursion.Wire

/-! Witness extraction for the transmitted verifier, by exact expansion. -/

namespace RecursivePolygero.Protocol.ProfileProof
open Finset Counting ProfileAnalysis
attribute [local instance] Classical.propDecidable
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {I : Instance F} {protocol : Protocol I} {p : ProfileCertificate I}

noncomputable def wireExtract (r : protocol.ProfileProof p) (masks : Bool)
    (σ : I.layer.Statement) (W : I.WireOracle masks)
    (messages : protocol.WireStrategy) (coins : protocol.chain.Coins) : Option I.layer.Witness :=
  r.extractWitness σ (I.expandWireOracle masks W) (protocol.expandWireStrategy messages) coins

theorem wireExtract_valid (r : protocol.ProfileProof p) (masks : Bool)
    (σ : I.layer.Statement) (W : I.WireOracle masks)
    (messages : protocol.WireStrategy) (coins : protocol.chain.Coins)
    (witness : I.layer.Witness) (h : r.wireExtract masks σ W messages coins = some witness) :
    I.layer.satisfies σ witness :=
  r.extractWitness_valid σ _ _ coins witness h

theorem wire_extraction_failure (r : protocol.ProfileProof p) (masks : Bool)
    (σ : I.layer.Statement) (W : I.WireOracle masks) (messages : protocol.WireStrategy) :
    ((univ.filter fun coins : protocol.chain.Coins =>
      protocol.wireVerify masks σ W messages coins = true ∧
      r.wireExtract masks σ W messages coins = none).card : ℚ) /
      Fintype.card protocol.chain.Coins ≤ 1-(r.localErrors.map (1-·)).prod :=
  r.extractWitness_failure σ _ _

end RecursivePolygero.Protocol.ProfileProof

namespace RecursivePolygero.Protocol.HahnProfileProof
open Finset Counting ProfileAnalysis
attribute [local instance] Classical.propDecidable
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {I : Instance F} {protocol : Protocol I} {p : HahnSystemCertificate I}

noncomputable def wireExtract (r : protocol.HahnProfileProof p) (masks : Bool)
    (σ : I.layer.Statement) (W : I.WireOracle masks)
    (messages : protocol.WireStrategy) (coins : protocol.chain.Coins) : Option I.layer.Witness :=
  r.extractWitness σ (I.expandWireOracle masks W) (protocol.expandWireStrategy messages) coins

theorem wireExtract_valid (r : protocol.HahnProfileProof p) (masks : Bool)
    (σ : I.layer.Statement) (W : I.WireOracle masks)
    (messages : protocol.WireStrategy) (coins : protocol.chain.Coins)
    (witness : I.layer.Witness) (h : r.wireExtract masks σ W messages coins = some witness) :
    I.layer.satisfies σ witness :=
  r.extractWitness_valid σ _ _ coins witness h

theorem wire_extraction_failure (r : protocol.HahnProfileProof p) (masks : Bool)
    (σ : I.layer.Statement) (W : I.WireOracle masks) (messages : protocol.WireStrategy) :
    ((univ.filter fun coins : protocol.chain.Coins =>
      protocol.wireVerify masks σ W messages coins = true ∧
      r.wireExtract masks σ W messages coins = none).card : ℚ) /
      Fintype.card protocol.chain.Coins ≤ 1 - (r.localErrors.map (1 - ·)).prod :=
  r.extractWitness_failure σ _ _

end RecursivePolygero.Protocol.HahnProfileProof

namespace RecursivePolygero.Protocol.ProfileProof
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {I : Instance F} {protocol : Protocol I} {p : ProfileCertificate I}

/-- Certificate conversion preserves extraction from the physical wire oracle. -/
theorem toHahnProfileProof_wireExtract (r : protocol.ProfileProof p) (masks : Bool)
    (σ : I.layer.Statement) (W : I.WireOracle masks)
    (messages : protocol.WireStrategy) (coins : protocol.chain.Coins) :
    r.toHahnProfileProof.wireExtract masks σ W messages coins =
      r.wireExtract masks σ W messages coins :=
  r.toHahnProfileProof_extractWitness σ _ _ coins

end RecursivePolygero.Protocol.ProfileProof
