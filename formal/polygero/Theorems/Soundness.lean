import polygero.Theorems.WireExtraction

/-! False-statement soundness as a corollary of recursive witness extraction. -/

namespace RecursivePolygero.Protocol.ProfileProof
open Finset Counting ProfileAnalysis
attribute [local instance] Classical.propDecidable
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {I : Instance F} {protocol : Protocol I} {p : ProfileCertificate I}

/-- False-statement soundness is a corollary of witness extraction. -/
theorem soundness_of_extraction (r : protocol.ProfileProof p) (masks : Bool)
    (σ : I.layer.Statement) (hfalse : ∀ witness, ¬ I.layer.satisfies σ witness)
    (W : I.WireOracle masks) (messages : protocol.WireStrategy) :
    ((univ.filter fun coins : protocol.chain.Coins =>
      protocol.wireVerify masks σ W messages coins = true).card : ℚ) /
      Fintype.card protocol.chain.Coins ≤ 1-(r.localErrors.map (1-·)).prod := by
  have hnone (coins : protocol.chain.Coins) : r.wireExtract masks σ W messages coins = none := by
    cases he : r.wireExtract masks σ W messages coins with
    | none => rfl
    | some witness => exact (hfalse witness (r.wireExtract_valid masks σ W messages coins witness he)).elim
  simpa only [hnone, and_true] using r.wire_extraction_failure masks σ W messages


/-- Unconditional soundness of the concrete verifier, with the product-error
recurrence. The only statement premise is that no satisfying witness exists. -/
theorem false_statement (r : protocol.ProfileProof p)
    (σ : I.layer.Statement) (hfalse : ∀ witness, ¬ I.layer.satisfies σ witness)
    (W : I.layer.Oracle) (messages : Strategy protocol.chain) :
    ((univ.filter fun coins : protocol.chain.Coins =>
      executionVerify protocol.chain σ W messages coins = true).card : ℚ)/
      Fintype.card protocol.chain.Coins ≤ r.error := by
  have hnone (coins : protocol.chain.Coins) : r.run σ W messages coins = none := by
    cases he : r.run σ W messages coins with
    | none => rfl
    | some g => exact (hfalse _ (r.run_valid σ W messages coins g he)).elim
  have h := r.extraction_failure_le σ W messages
  simp only [familyProbability,hnone,outputHit,and_true,mean_indicator] at h
  convert! h using 1; congr 1
  apply congrArg (fun s : Finset protocol.chain.Coins => (s.card : ℚ))
  ext coins
  simp only [mem_filter,mem_univ,true_and]


/-- The product bound applies to arbitrary transmitted oracles and adaptive
wire strategies. Omitted masks are expanded exactly as in the verifier. -/
theorem wire_false_statement (r : protocol.ProfileProof p) (masks : Bool)
    (σ : I.layer.Statement) (hfalse : ∀ witness, ¬ I.layer.satisfies σ witness)
    (W : I.WireOracle masks) (messages : protocol.WireStrategy) :
    ((univ.filter fun coins : protocol.chain.Coins =>
      protocol.wireVerify masks σ W messages coins = true).card : ℚ)/
      Fintype.card protocol.chain.Coins ≤ 1-(r.localErrors.map (1-·)).prod :=
  r.soundness_of_extraction masks σ hfalse W messages

end RecursivePolygero.Protocol.ProfileProof
