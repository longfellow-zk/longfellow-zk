import LfzkV2.Current.AdapterLeaves

/-! The fixed adapter fragment and its virtual leaves. Leaf values match the
runtime's `Leaf::data` and `Leaf::quotient` on every committed bit, and the
leaf algebra lemma relates the fragment's unit products to the conversion
proof's product equation. -/
noncomputable section
namespace LfzkV2.Current.Tests.AdapterFragment
open Adapter

-- The runtime's tree-major layout: leaf `i` of tree `t` is at `t*n+i`.
example : (ProductTree.wireIndex 1034 (1,5)).val = 1039 := by
  rw [ProductTree.wireIndex_val]; rfl

-- Halving with an odd carry: 1034 leaves reduce to two wires in ten layers.
example : (List.range 10).foldl (fun n _ => Circuit.half n) 1034 = 2 := by decide
example : Circuit.half 3 = 2 := rfl

-- A quotient leaf is affine in the pad bit, with coefficients chosen by
-- the public masked bit; it selects the power exactly when `o xor m`.
example {F : Type} [Field F] [CharP F 2] (power : F) (m o : Bool) :
    (Leaves.quotient () power m).value (Circuit.bitValue ∘ fun _ => o) =
      if Bool.xor o m then power else 1 :=
  Leaves.quotient_value () power m _

#print axioms ProductTree.satisfies_iff
#print axioms Leaves.tree_product
#print axioms Leaves.tree_product_check

end LfzkV2.Current.Tests.AdapterFragment
