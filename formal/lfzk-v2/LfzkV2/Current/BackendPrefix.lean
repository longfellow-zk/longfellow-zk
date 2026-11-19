import LfzkV2.Joint.Participant

/-! The runtime's extra deterministic check on the logical mask prefix.
The paper-facing Polygero verifier remains unchanged. -/
noncomputable section
namespace LfzkV2.Current.BackendPrefix
open Polynomial LigeroFamily RecursivePolygero

def Zero {k s n t : ℕ} (P : Joint.Participant k s n t) (response : P.Response) : Prop :=
  ∀ i : Fin P.backend.r,
    (response.arithmetic : P.Carrier[X]).eval (P.backend.domain.point (randomPosition i)) = 0


end LfzkV2.Current.BackendPrefix
