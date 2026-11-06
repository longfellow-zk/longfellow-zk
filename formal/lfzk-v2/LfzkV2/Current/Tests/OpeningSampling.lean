import LfzkV2.Current.OpeningFisherYates

namespace LfzkV2.Current.Tests.OpeningSampling
open OpeningFisherYates

private def picks : Choices 3 2 := ((2 : Fin 3),((1 : Fin 2),()))

/-- Swapping column two to the front leaves [1,0] as the actual tail.
Selecting tail offset one therefore emits column zero, rather than one. -/
example : ordered 3 2 picks (0 : Fin 2) = (2 : Fin 3) := rfl

example : ordered 3 2 picks (1 : Fin 2) = (0 : Fin 3) := by
  change Equiv.swap (0 : Fin 3) (2 : Fin 3) ((1 : Fin 2).succ) = 0
  norm_num [Equiv.swap_apply_def]

example (query : LigeroFamily.QuerySet 3 2) :
    (Finset.univ.filter fun indices : Fin 2 ↪ Fin 3 => OrderedOpening.query indices = query).card = 2 := by
  rw [LfzkV2.Current.OpeningSampling.query_fiber_card]
  rfl

end LfzkV2.Current.Tests.OpeningSampling
