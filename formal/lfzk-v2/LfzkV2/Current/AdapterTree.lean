import LfzkV2.Current.Adapter

/-! Quotient algebra of the product-tree adapter. Quotient bits are
recovered by XOR with their committed pads, so arbitrary canonical masked
words still give a bounded integer. The quotient leaf powers are the base
squared at each next bit, exactly as in the runtime. No honest-prover
assumption is needed for the masked words. -/
namespace LfzkV2.Current.Adapter.Tree

variable {G : Type}

def binaryValue : List Bool → ℕ
  | [] => 0
  | bit :: rest => (if bit then 1 else 0) + 2 * binaryValue rest

theorem binaryValue_lt (bits : List Bool) : binaryValue bits < 2^bits.length := by
  induction bits with
  | nil => decide
  | cons bit rest ih =>
      simp only [binaryValue, List.length_cons, pow_succ]
      cases bit <;> simp only [Bool.false_eq_true, if_false, if_true] <;> omega

/-- This recursion lists the quotient leaf powers in little-endian order:
the base is squared at each next bit, exactly as in the runtime. -/
def quotientLeaves [Monoid G] (base : G) : List Bool → List G
  | [] => []
  | bit :: rest => (if bit then base else 1) :: quotientLeaves (base*base) rest

theorem quotientLeaves_prod [CommMonoid G] (base : G) (bits : List Bool) :
    (quotientLeaves base bits).prod = base ^ binaryValue bits := by
  induction bits generalizing base with
  | nil => simp [quotientLeaves, binaryValue]
  | cons bit rest ih =>
      rw [quotientLeaves, List.prod_cons, ih]
      rw [← pow_two, ← pow_mul]
      cases bit <;> simp [binaryValue, pow_add]

end LfzkV2.Current.Adapter.Tree
