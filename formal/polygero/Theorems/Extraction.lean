import polygero.Theorems.IndexExtraction

/-! Public witness-valued extraction: validity and the product failure bound. -/

namespace RecursivePolygero.Protocol.ProfileProof
open Finset Counting ProfileAnalysis
attribute [local instance] Classical.propDecidable
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {I : Instance F} {protocol : Protocol I} {p : ProfileCertificate I}

theorem extract_valid (r : protocol.ProfileProof p)
    (σ : I.layer.Statement) (W : I.layer.Oracle)
    (messages : Strategy protocol.chain) (coins : protocol.chain.Coins) (g)
    (h : r.extract σ W messages coins = some g) :
    I.layer.satisfies σ ((r.family W).witness g) :=
  r.extractTranscript_valid σ W _ g h

noncomputable def extractWitness (r : protocol.ProfileProof p)
    (σ : I.layer.Statement) (W : I.layer.Oracle)
    (messages : Strategy protocol.chain) (coins : protocol.chain.Coins) :
    Option I.layer.Witness :=
  (r.extract σ W messages coins).map (r.family W).witness

theorem extractWitness_valid (r : protocol.ProfileProof p)
    (σ : I.layer.Statement) (W : I.layer.Oracle)
    (messages : Strategy protocol.chain) (coins : protocol.chain.Coins)
    (witness : I.layer.Witness) (h : r.extractWitness σ W messages coins = some witness) :
    I.layer.satisfies σ witness := by
  cases he : r.extract σ W messages coins with
  | none => simp [extractWitness, he] at h
  | some g =>
    have hw : (r.family W).witness g = witness := by simpa [extractWitness, he] using h
    exact hw ▸ r.extract_valid σ W messages coins g he

theorem extractWitness_eq_none_iff (r : protocol.ProfileProof p)
    (σ : I.layer.Statement) (W : I.layer.Oracle)
    (messages : Strategy protocol.chain) (coins : protocol.chain.Coins) :
    r.extractWitness σ W messages coins = none ↔ r.extract σ W messages coins = none := by
  cases he : r.extract σ W messages coins <;> simp [extractWitness, he]

theorem extractWitness_failure (r : protocol.ProfileProof p)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (messages : Strategy protocol.chain) :
    ((univ.filter fun coins : protocol.chain.Coins =>
      executionVerify protocol.chain σ W messages coins = true ∧
      r.extractWitness σ W messages coins = none).card : ℚ) /
      Fintype.card protocol.chain.Coins ≤ 1-(r.localErrors.map (1-·)).prod := by
  rw [← r.error_eq_product]
  simpa only [r.extractWitness_eq_none_iff] using r.extraction_failure σ W messages

end RecursivePolygero.Protocol.ProfileProof
