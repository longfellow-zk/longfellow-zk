import polygero.Recursion.Probability

/-! Joint acceptance and index-extraction failure for the concrete recursive verifier. -/

namespace RecursivePolygero.Protocol.HahnProfileProof
open Finset Counting ProfileAnalysis
attribute [local instance] Classical.propDecidable
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {I : Instance F} {protocol : Protocol I} {p : HahnSystemCertificate I}

theorem extraction_failure (r : protocol.HahnProfileProof p)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (messages : Strategy protocol.chain) :
    ((univ.filter fun coins : protocol.chain.Coins =>
      executionVerify protocol.chain σ W messages coins = true ∧ r.extract σ W messages coins = none).card : ℚ) /
      Fintype.card protocol.chain.Coins ≤ r.error := by
  have h := r.extraction_failure_le σ W messages
  have hout (coins : protocol.chain.Coins) :
      outputHit (fun _ => False) (r.run σ W messages coins) ↔ r.run σ W messages coins = none := by
    cases r.run σ W messages coins <;> simp [outputHit]
  simp only [familyProbability, hout, mean_indicator] at h
  convert! h using 1; congr 1
  apply congrArg (fun s : Finset protocol.chain.Coins => (s.card : ℚ))
  ext coins
  simp only [mem_filter, mem_univ, true_and]
  by_cases hacc : executionVerify protocol.chain σ W messages coins = true
  · rw [r.extract_eq_run_of_accept σ W messages coins hacc]
  · simp [hacc]

end RecursivePolygero.Protocol.HahnProfileProof

namespace RecursivePolygero.Protocol.ProfileProof
open Finset Counting ProfileAnalysis
attribute [local instance] Classical.propDecidable
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {I : Instance F} {protocol : Protocol I} {p : ProfileCertificate I}

theorem extraction_failure (r : protocol.ProfileProof p)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (messages : Strategy protocol.chain) :
    ((univ.filter fun coins : protocol.chain.Coins =>
      executionVerify protocol.chain σ W messages coins = true ∧ r.extract σ W messages coins = none).card : ℚ)/
      Fintype.card protocol.chain.Coins ≤ r.error := by
  have h := r.toHahnProfileProof.extraction_failure σ W messages
  simp_rw [r.toHahnProfileProof_extract, r.toHahnProfileProof_error] at h
  convert h using 1
  congr 1
  apply congrArg (fun s : Finset protocol.chain.Coins => (s.card : ℚ))
  ext coin
  simp only [mem_filter, mem_univ, true_and]
  tauto

end RecursivePolygero.Protocol.ProfileProof
