import LfzkV2.Current.ZeroKnowledge.BackendRuntimeEncoding

/-! The compiled backend and literal runtime use the same heap, opening,
original observer view and dummy commitment root. -/
namespace LfzkV2.Current.Tests.ZeroKnowledgeBackendRuntimeEncoding

#print axioms ZeroKnowledge.BackendViewTransport.runView_of_opening
#print axioms ZeroKnowledge.BackendViewTransport.actualLabels_last
#print axioms ZeroKnowledge.BackendRuntimeEncoding.heap_value
#print axioms ZeroKnowledge.BackendRuntimeEncoding.committed_root
#print axioms ZeroKnowledge.BackendRuntimeEncoding.runView_output
#print axioms ZeroKnowledge.BackendRuntimeEncoding.dummy_root

end LfzkV2.Current.Tests.ZeroKnowledgeBackendRuntimeEncoding
