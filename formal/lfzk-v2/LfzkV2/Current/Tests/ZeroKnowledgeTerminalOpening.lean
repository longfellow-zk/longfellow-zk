import LfzkV2.Current.ZeroKnowledge.CompleteTerminalOpening

/-! Authentication changes the final seal but not the opening query when
the two transmitted response arrays are held fixed. -/
namespace LfzkV2.Current.Tests.ZeroKnowledgeTerminalOpening
open ZeroKnowledge

#print axioms CompleteTerminalOpening.fresh_eq
#print axioms CompleteTerminalOpening.block_eq
#print axioms CompleteTerminalOpening.opening_point
#print axioms CompleteTerminalOpening.opening_point_zero
#print axioms CompleteTerminalOpening.programAndFinalize_update

end LfzkV2.Current.Tests.ZeroKnowledgeTerminalOpening
