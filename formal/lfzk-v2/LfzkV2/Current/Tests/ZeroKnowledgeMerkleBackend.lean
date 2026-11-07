import LfzkV2.Current.ZeroKnowledge.MerkleBackend

/-! The concrete composition exposes complete tuple columns and both
responses. In particular the proximity mask is not lost when passing from
the Polygero oracle to Merkle leaves. -/
namespace LfzkV2.Current.Tests.ZeroKnowledgeMerkleBackend

open ZeroKnowledge.MerkleBackend RecursivePolygero.Local

example {F : Type} {n rows : ℕ} (oracle : Polygero.Oracle F rows 0 n) (i : Fin n) :
    (column oracle i).2 = oracle.proximityMask i := rfl

example {F : Type} {n rows : ℕ} (oracle : Polygero.Oracle F rows 0 n) (i : Fin n) :
    (column oracle i).1.checkedMask .vCoefficient =
      oracle.ordinary.checkedMask .vCoefficient i ∧
    (column oracle i).1.checkedMask .zRCoefficient =
      oracle.ordinary.checkedMask .zRCoefficient i := ⟨rfl,rfl⟩

example {F : Type} {n rows : ℕ} (oracle : Polygero.Oracle F rows 0 n)
    (i : Fin n) (row : Fin rows) :
    (column oracle i).1.core .linear row = oracle.ordinary.core .linear row i := rfl

#print axioms columns_coupling
#print axioms responses_coupling
#print axioms joint_hiding

end LfzkV2.Current.Tests.ZeroKnowledgeMerkleBackend
