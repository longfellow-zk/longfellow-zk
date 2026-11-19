import Bcs.FirstPairQuery
import Bcs.TwoCoordinatePotential

/-! The first-hit decision between two paired queries, computed from the
off-pair oracle. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace Bcs.TotalOracle

open Finset Merkle.RandomOracle
open scoped Classical

variable {Q C Out Parent Response : Type}
  [Fintype Q] [DecidableEq Q] [Fintype C] [Nonempty C]
  [Fintype Parent] [Fintype Response]
  {N : ℕ}

/-- The full first-hit result computed from the off-pair oracle. -/
noncomputable def firstOfTwoOffResult (tree : Tree Q C Out N)
    (x y : Q) (hxy : x ≠ y)
    (off : AwayFromTwo x y → C) : FirstOfTwo :=
  let e := splitTwo (C := C) x y hxy
  firstOfTwo tree (e.symm (off, (Classical.choice inferInstance,
    Classical.choice inferInstance))) x y

/-- The first-hit decision computed from the off-pair oracle is the actual
first-hit decision.  It is independent of both paired answers. -/
theorem firstOfTwoOff_eq (tree : Tree Q C Out N)
    (x y : Q) (hxy : x ≠ y) (H : Q → C) :
    firstOfTwoOffResult tree x y hxy (fun z => H z.1) =
      firstOfTwo tree H x y := by
  let e := splitTwo (C := C) x y hxy
  let H' := e.symm ((fun z : AwayFromTwo x y => H z.1),
    (Classical.choice inferInstance, Classical.choice inferInstance))
  have hoff : ∀ q, q ≠ x → q ≠ y → H' q = H q := by
    intro q hx hy
    have hproj := congrArg Prod.fst (e.right_inv
      ((fun z : AwayFromTwo x y => H z.1),
        (Classical.choice inferInstance, Classical.choice inferInstance)))
    exact congrFun hproj ⟨q, hx, hy⟩
  exact firstOfTwo_congr_off tree H' H x y hoff

end Bcs.TotalOracle
