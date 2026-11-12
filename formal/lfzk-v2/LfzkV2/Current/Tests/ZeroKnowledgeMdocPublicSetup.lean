import LfzkV2.Current.Mdoc.PublicSetup

/-! The concrete mdoc runtime shares one SHA oracle across public setup,
generated adapter identifiers and Merkle authentication. -/
namespace LfzkV2.Current.Tests.ZeroKnowledgeMdocPublicSetup

#check Mdoc.PublicSetup.protocol
#print axioms Mdoc.PublicSetup.setup_merge
#print axioms Mdoc.PublicSetup.metadata_merge

end LfzkV2.Current.Tests.ZeroKnowledgeMdocPublicSetup
