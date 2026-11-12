import LfzkV2.Joint.Backend

/-! The basic two-field family and its coordinate equivalences.
Compiled-side replay adapters live in the `Joint.Pair` facade. -/
namespace LfzkV2.Joint.Pair
open RecursivePolygero LigeroFamily
variable {k s n t : ℕ} (P₁ P₂ : Joint.Participant k s n t)

def family : Family k s n t where
  count := 2
  nonempty := by decide
  participant := Fin.cons P₁ (Fin.cons P₂ Fin.elim0)

def statementEquiv : (family P₁ P₂).Statement ≃ P₁.Statement × P₂.Statement :=
  piFinTwoEquiv _

def oracleEquiv : (family P₁ P₂).Oracle ≃ P₁.Oracle × P₂.Oracle := piFinTwoEquiv _
def coinEquiv : (family P₁ P₂).Coin ≃ P₁.Coin × P₂.Coin := piFinTwoEquiv _
def responseEquiv : (family P₁ P₂).Response ≃ P₁.Response × P₂.Response := piFinTwoEquiv _

theorem verify_iff (σ : P₁.Statement × P₂.Statement) (W : (family P₁ P₂).Oracle)
    (coins : P₁.Coin × P₂.Coin) (responses : P₁.Response × P₂.Response) (Q : QuerySet n t) :
    (family P₁ P₂).Verify ((statementEquiv P₁ P₂).symm σ) W
      ((coinEquiv P₁ P₂).symm coins) ((responseEquiv P₁ P₂).symm responses) Q ↔
    P₁.backend.layer.verify σ.1 (oracleEquiv P₁ P₂ W).1 coins.1 responses.1 (P₁.localQuery Q) ∧
    P₂.backend.layer.verify σ.2 (oracleEquiv P₁ P₂ W).2 coins.2 responses.2 (P₂.localQuery Q) := by
  change (∀ i : Fin 2, _) ↔ _
  rw [Fin.forall_fin_two]
  rfl


end LfzkV2.Joint.Pair
