import LfzkV2.Current.ZeroKnowledge.MdocZeroKnowledge

/-! The public endpoint has no execution, layout, oracle-correspondence,
or statistical certificate premise. Its simulator has no witness input.
The full raw view retains private observer context and both query traces. -/
namespace LfzkV2.Current.Tests.ZeroKnowledgeMdocZeroKnowledge

#check @ZeroKnowledge.MdocZeroKnowledge.simulate
#check @ZeroKnowledge.MdocZeroKnowledge.statClose
#print axioms ZeroKnowledge.MdocZeroKnowledge.fixedComplement
#print axioms ZeroKnowledge.MdocZeroKnowledge.statClose

end LfzkV2.Current.Tests.ZeroKnowledgeMdocZeroKnowledge
