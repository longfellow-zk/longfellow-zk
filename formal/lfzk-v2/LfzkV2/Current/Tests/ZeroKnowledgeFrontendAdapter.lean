import LfzkV2.Current.ZeroKnowledge.FrontendAdapterCorrectness

/-! Adapter simulator regression and axiom audits, including the exact
current advice width and the source RNG bits which are not serialized. -/
noncomputable section
namespace LfzkV2.Current.Tests.ZeroKnowledgeFrontendAdapter
open ZeroKnowledge.Frontend
open scoped Classical

instance : Fact (Nat.Prime 7) := ⟨by decide⟩

/-- The honest quotient can reach the last allowed integer, with no
negative subtraction or nonzero-remainder rejection. -/
example : (Adapter.honestQuotient (fun _ : Fin 4 => (6 : ZMod 7)) (fun _ => true)
    1 (show 4 ≤ 4 from le_rfl) (by decide)).val = 3 := by decide

example : AdapterBits.packedQuotients (fun _ => ⟨1023,by decide⟩) =
    (⟨2^20-1,by decide⟩ : MdocAdvice.Value) := by decide

example : (AdapterBits.rawOtpEquiv ⟨2^24-1,by decide⟩).1 =
    (⟨2^20-1,by decide⟩ : MdocAdvice.Value) := by decide

example (sharedWeights : Fin 768 → Adapter.Mdoc.P) (shared : Fin 768 → Bool)
    (eta : Adapter.Mdoc.P) (alpha : Adapter.Mdoc.Alphas) (mu : Adapter.Mdoc.P)
    (tree : Fin 2) :
    (Adapter.Mdoc.quotients sharedWeights shared eta alpha mu tree).val < 1024 :=
  (Adapter.Mdoc.quotients sharedWeights shared eta alpha mu tree).isLt

#print axioms AdapterBits.wordEquiv_decode
#print axioms AdapterBits.binaryValue_word
#print axioms AdapterBits.rawOtp_bits
#print axioms Adapter.honestQuotient_runtime
#print axioms Adapter.canonicalMask_value
#print axioms Adapter.muAdvice_sameDistribution
#print axioms Adapter.rawMuAdvice_sameDistribution
#print axioms Adapter.Mdoc.sameDistribution
#print axioms Adapter.Mdoc.quotients_runtime
#print axioms Adapter.recovered_advice
#print axioms Adapter.product_check_satisfies
#print axioms Adapter.Mdoc.recoveredInputs_satisfy
end LfzkV2.Current.Tests.ZeroKnowledgeFrontendAdapter
