import LfzkV2.Current.ZeroKnowledge.MdocWitness

/-! Kernel assumption audit for ordinary application witnesses supplying
the concrete runtime's protocol truth. No per-round/backend/Execution
certificate appears among the trusted witness premises. -/
namespace LfzkV2.Current.Tests.ZeroKnowledgeMdocWitness

#print axioms ZeroKnowledge.MdocWitness.private_prefix
#print axioms ZeroKnowledge.MdocWitness.coupling_hash
#print axioms ZeroKnowledge.MdocWitness.honest_hash
#print axioms ZeroKnowledge.MdocWitness.configuration_runtime
#print axioms ZeroKnowledge.MdocWitness.backend_hash
#print axioms ZeroKnowledge.MdocWitness.runtime_hash
#print axioms ZeroKnowledge.MdocWitness.satisfied

end LfzkV2.Current.Tests.ZeroKnowledgeMdocWitness
