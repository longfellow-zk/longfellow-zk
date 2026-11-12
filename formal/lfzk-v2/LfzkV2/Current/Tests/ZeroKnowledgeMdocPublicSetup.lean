import LfzkV2.Current.ZeroKnowledge.MdocPublicSetup

/-! The concrete mdoc runtime shares one SHA oracle across public setup,
generated adapter identifiers and Merkle authentication. -/
namespace LfzkV2.Current.Tests.ZeroKnowledgeMdocPublicSetup

#check ZeroKnowledge.MdocPublicSetup.protocol
#print axioms ZeroKnowledge.MdocPublicSetup.setup_merge
#print axioms ZeroKnowledge.MdocPublicSetup.metadata_merge

end LfzkV2.Current.Tests.ZeroKnowledgeMdocPublicSetup
