import LfzkV2.Joint.Participant
import LfzkV2.PolygeroZk

/-! The runtime's extra deterministic check on the logical mask prefix.
The paper-facing Polygero verifier remains unchanged. -/
noncomputable section
namespace LfzkV2.Current.BackendPrefix
open Polynomial LigeroFamily RecursivePolygero

def Zero {k s n t : ℕ} (P : Joint.Participant k s n t) (response : P.Response) : Prop :=
  ∀ i : Fin P.backend.r,
    (response.arithmetic : P.Carrier[X]).eval (P.backend.domain.point (randomPosition i)) = 0

variable {F : Type} [Field F] {r w p n nw nq s : ℕ}
variable (G : PolygeroZk.Geometry F r w p n)
variable {Equations : Type} [Fintype Equations]

theorem payload_random (hk : 0 < r+w)
    (statement : ConstraintSystem F nw nq w Equations)
    (coin : Local.Polygero.Coin F Equations nw nq s)
    (messages : PolygeroCoreMasking.Messages F w p nw nq)
    (tape : PolygeroZk.Tape G nw nq s) (i : Fin r) :
    ((PolygeroZk.payload G hk statement coin messages tape).arithmetic : F[X]).eval
      (G.domain.point (randomPosition i)) = 0 := by
  simp only [PolygeroZk.payload]
  rw [PolynomialDirect.responsePolynomial_eval]
  change DirectVerifier.linearCore G.code (ConstraintLayout.identity w) statement coin.1
    (PolygeroZk.core G messages tape.1) (randomPosition i) +
      PolygeroMasking.response G.code G.basis (PolygeroZk.sumFunctional F w) tape.2.1
        (randomPosition i) = 0
  rw [PolygeroMasking.linearCore_random]
  simpa only [zero_add, PolygeroMasking.response] using
    (linearMaskMap G.code G.basis ∅ (PolygeroZk.sumFunctional F w) tape.2.1).2.2.1 i

end LfzkV2.Current.BackendPrefix
