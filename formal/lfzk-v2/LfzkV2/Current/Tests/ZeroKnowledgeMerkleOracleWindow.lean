import LfzkV2.Current.ZeroKnowledge.MerkleOracleWindow

/-! The raw query type here is Nat, with no finite-type instance. The
Merkle window includes both codec images and every mixed observer branch. -/
namespace LfzkV2.Current.Tests.ZeroKnowledgeMerkleOracleWindow
open Merkle Merkle.MH Merkle.RandomOracle
open ZeroKnowledge.MerkleOracleWindow Current.ObserverWindow

private def exampleCodec : Codec Bool Bool Bool Nat where
  leafEnc value := 10+(if value.1 then 2 else 0)+(if value.2 then 1 else 0)
  nodeEnc value := 20+(if value.1 then 2 else 0)+(if value.2 then 1 else 0)

private def observer : TwoOracleTree Nat Bool Nat Bool Nat 1 1 :=
  .queryLeft 1000 fun first => .queryRight 2000 fun second =>
    .done (if first = second then 1 else 0)

private def budgets (_ : Unit) : Nat × Nat := (1,1)
private def trees (_ : Unit) := observer

example : 1000 ∈ window exampleCodec budgets trees :=
  queries_subset exampleCodec budgets trees () (Finset.mem_insert_self _ _)

#print axioms restrictMixed_run
#print axioms queries_fixTranscript_subset
#print axioms finiteResidual_output
#print axioms commitPass_run

end LfzkV2.Current.Tests.ZeroKnowledgeMerkleOracleWindow
