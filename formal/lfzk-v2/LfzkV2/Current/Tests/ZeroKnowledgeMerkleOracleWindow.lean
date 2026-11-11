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

example : exampleCodec.leafEnc (false,true) ∈ window exampleCodec budgets trees :=
  leaf_mem exampleCodec budgets trees _

example : exampleCodec.nodeEnc (true,false) ∈ window exampleCodec budgets trees :=
  node_mem exampleCodec budgets trees _

#print axioms restrictMixed_run
#print axioms finiteTree_run
#print axioms finiteCodec_inj
#print axioms queries_fixTranscript_subset
#print axioms finiteResidual_output
#print axioms commitLabels_eq
#print axioms root_eq
#print axioms commitPass_run
#print axioms openCore_eq

end LfzkV2.Current.Tests.ZeroKnowledgeMerkleOracleWindow
