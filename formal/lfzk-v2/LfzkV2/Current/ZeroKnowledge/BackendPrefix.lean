import LfzkV2.Current.BackendPrefix
import LfzkV2.PolygeroZk

/-! Honest arithmetic responses satisfy the runtime's deterministic prefix check. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.BackendPrefix
open Polynomial LigeroFamily RecursivePolygero

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

end LfzkV2.Current.ZeroKnowledge.BackendPrefix
