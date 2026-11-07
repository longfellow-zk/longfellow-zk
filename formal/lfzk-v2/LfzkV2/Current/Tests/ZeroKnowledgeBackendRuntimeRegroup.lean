import LfzkV2.Current.ZeroKnowledge.BackendRuntimeRegroup

/-! The finite Merkle table can be sampled independently last without
altering either complete experiment or its statistical bound. -/
namespace LfzkV2.Current.Tests.ZeroKnowledgeBackendRuntimeRegroup
open ZeroKnowledge

#check @BackendRuntimeRegroup.transcriptLast
#print axioms BackendRuntimeRegroup.transcriptLast
#check @BackendRuntimeRegroup.PrivateOuter
#check @BackendRuntimeRegroup.PublicOuter
#check @BackendRuntimeRegroup.privateEquiv
#check @BackendRuntimeRegroup.publicEquiv
#check @BackendRuntimeRegroup.real_literal
#check @BackendRuntimeRegroup.simulate_literal
#print axioms BackendRuntimeRegroup.real_literal
#print axioms BackendRuntimeRegroup.simulate_literal
#print axioms BackendRuntimeRegroup.statClose

end LfzkV2.Current.Tests.ZeroKnowledgeBackendRuntimeRegroup
