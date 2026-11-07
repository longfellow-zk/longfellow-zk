import LfzkV1.ZkHiding

/-! A finite uniform distribution depends on its set of coins, rather than
the particular complete enumeration chosen by typeclass synthesis. Explicit
instance transport keeps this fact separate from large protocol definitions:
the kernel need not normalize an enumeration of all oracle tables to compare
two presentations of the same probability space. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.Probability

theorem changeFintype {R S T : Type} [newR : Fintype R] [newS : Fintype S]
    {oldR : Fintype R} {oldS : Fintype S} {epsilon : ℚ} {first : R → T} {second : S → T}
    (known : @StatClose R S T oldR oldS epsilon first second) :
    @StatClose R S T newR newS epsilon first second := by
  cases Subsingleton.elim oldR newR
  cases Subsingleton.elim oldS newS
  exact known

end LfzkV2.Current.ZeroKnowledge.Probability
