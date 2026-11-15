import Bcs.FirstPairQuery

/-! Append a verifier's final oracle lookup to an adaptive prover. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bcs.TotalOracle

open Merkle.RandomOracle

/-- The final verifier point can depend on the prover's complete output. -/
def appendFinalQuery {Q C Out : Type} {N : ℕ}
    (tree : Tree Q C Out N) (point : Out → Q) : Tree Q C Out (1 + N) :=
  tree.bind fun out => Tree.query (point out) (fun _ => Tree.done out)

/-- The verifier's terminal point is among the extended execution's queries. -/
theorem appendFinalQuery_mem {Q C Out : Type} {N : ℕ}
    (tree : Tree Q C Out N) (point : Out → Q) (H : Q → C) :
    point (tree.run H).1 ∈ queried (appendFinalQuery tree point) H := by
  simp [queried, appendFinalQuery, Tree.run_bind]

end Bcs.TotalOracle
