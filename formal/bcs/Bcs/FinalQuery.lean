import Bcs.FirstPairQuery
import Merkle.TreeCompose

/-! Append a verifier's final oracle lookup to an adaptive prover. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bcs.TotalOracle

open Merkle.RandomOracle

/-- The final verifier point can depend on the prover's complete output. -/
def appendFinalQuery {Q C Out : Type} {N : ℕ}
    (tree : Tree Q C Out N) (point : Out → Q) : Tree Q C Out (1 + N) :=
  tree.bind fun out => Tree.query (point out) (fun _ => Tree.done out)

/-- The extra lookup does not change the prover's output. -/
theorem appendFinalQuery_output {Q C Out : Type} {N : ℕ}
    (tree : Tree Q C Out N) (point : Out → Q) (H : Q → C) :
    ((appendFinalQuery tree point).run H).1 = (tree.run H).1 := by
  simp [appendFinalQuery, Tree.run_bind]

/-- The verifier's terminal point is among the extended execution's queries. -/
theorem appendFinalQuery_mem {Q C Out : Type} {N : ℕ}
    (tree : Tree Q C Out N) (point : Out → Q) (H : Q → C) :
    point (tree.run H).1 ∈ queried (appendFinalQuery tree point) H := by
  simp [queried, appendFinalQuery, Tree.run_bind]

/-- Its first-hit pair classification exists even if the parent was never queried. -/
theorem appendFinalQuery_first_ne_neither {Q C Out : Type} {N : ℕ}
    [DecidableEq Q]
    (tree : Tree Q C Out N) (point : Out → Q) (H : Q → C) (x : Q) :
    firstOfTwo (appendFinalQuery tree point) H x (point (tree.run H).1) ≠
      .neither :=
  firstOfTwo_ne_neither_of_right_mem _ _ _ _
    (appendFinalQuery_mem tree point H)

end Bcs.TotalOracle
