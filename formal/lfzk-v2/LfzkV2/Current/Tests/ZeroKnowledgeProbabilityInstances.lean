import LfzkV2.Current.ZeroKnowledge.ProbabilityInstances

/-! Instance transport has no nonemptiness or finite-view premise. In
particular it changes only the enumeration of coins, never the experiment. -/
namespace LfzkV2.Current.Tests.ZeroKnowledgeProbabilityInstances
open ZeroKnowledge

#check @Probability.changeFintype
#print axioms Probability.changeFintype

/-- The conclusion must use the explicitly requested enumeration, rather
than silently retaining the source enumeration through instance search. -/
example {R S T : Type} (sourceR targetR : Fintype R) (sourceS targetS : Fintype S)
    {epsilon : ℚ} {first : R → T} {second : S → T}
    (known : @StatClose R S T sourceR sourceS epsilon first second) :
    @StatClose R S T targetR targetS epsilon first second :=
  @Probability.changeFintype R S T targetR targetS sourceR sourceS epsilon first second known

end LfzkV2.Current.Tests.ZeroKnowledgeProbabilityInstances
