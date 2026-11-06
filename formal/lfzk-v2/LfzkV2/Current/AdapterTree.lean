import LfzkV2.Current.Adapter
import Mathlib.Algebra.CharP.Two

/-! Algebra of the runtime product tree. A layer multiplies adjacent pairs
and carries an odd final wire unchanged. Quotient bits are recovered by XOR
with their selected private pads, so arbitrary canonical masked advice still
gives a bounded integer. No honest-prover assumption is needed for the advice. -/
namespace LfzkV2.Current.Adapter.Tree

variable {G B : Type}

def pairs [Mul G] : List G → List G
  | [] => []
  | [a] => [a]
  | a :: b :: rest => (a*b) :: pairs rest

theorem pairs_prod [CommMonoid G] (xs : List G) : (pairs xs).prod = xs.prod := by
  match xs with
  | [] => rfl
  | [a] => rfl
  | a :: b :: rest => simp only [pairs, List.prod_cons, pairs_prod rest, mul_assoc]

def reduce [Mul G] : ℕ → List G → List G
  | 0, xs => xs
  | steps+1, xs => reduce steps (pairs xs)

theorem reduce_prod [CommMonoid G] (steps : ℕ) (xs : List G) :
    (reduce steps xs).prod = xs.prod := by
  induction steps generalizing xs with
  | zero => rfl
  | succ steps ih => exact (ih (pairs xs)).trans (pairs_prod xs)

/-- The two nonzero linear coefficients used by the compiler evaluate to
the usual Boolean mux, including the case where the public power is one. -/
theorem leaf [Field B] (power : B) (bit : Bool) :
    1 + power * (if bit then 1 else 0) - (if bit then 1 else 0) =
      if bit then power else 1 := by
  cases bit <;> simp

theorem masked_leaf [Field B] [CharP B 2] (power : B) (pad masked : Bool) :
    (if masked then power else 1) + power * (if pad then 1 else 0) + (if pad then 1 else 0) =
      if Bool.xor pad masked then power else 1 := by
  cases pad <;> cases masked <;>
    simp [CharTwo.add_self_eq_zero, add_left_comm, add_comm]

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

/-- If the final product layer vanishes, its two reduced roots satisfy the
group equation used by the conversion proof. Equality of field elements is
enough because coercion from units is injective. -/
theorem final_equation [Field B] [CharP B 2]
    (data advice : List Bˣ) (target : Bˣ) (steps : ℕ)
    (h : ((reduce steps data).prod : B) * ((reduce steps advice).prod : B) + (target : B) = 0) :
    data.prod * advice.prod = target := by
  apply Units.ext
  have h' := congrArg (fun x : B => x + (target : B)) h
  simpa [reduce_prod, add_assoc, CharTwo.add_self_eq_zero] using h'

/-- The tree's final assertion yields the precise bounded-quotient equation
used by the conversion theorem. Masked advice may be chosen after both
conversion challenges; XOR decoding still bounds its represented quotient. -/
theorem product_check [Field B] [CharP B 2] {p bits adviceBits : ℕ} [Fact p.Prime]
    (generator : Bˣ) (weights : Fin bits → ZMod p) (values : Fin bits → Bool)
    (target alpha : ZMod p) (pad masked : Fin adviceBits → Bool) (steps : ℕ) :
    let advice := List.ofFn (fun i => Bool.xor (pad i) (masked i))
    let data := List.ofFn (fun i => if values i then generator^(alpha * weights i).val else 1)
    let quotient := quotientLeaves (generator^(-(p : ℤ))) advice
    ((reduce steps data).prod : B) * ((reduce steps quotient).prod : B) +
      ((generator^(alpha*target).val : Bˣ) : B) = 0 →
    binaryValue advice < 2^adviceBits ∧
      Adapter.ProductCheck generator weights values target alpha (binaryValue advice) := by
  intro advice data quotient h
  refine ⟨by simpa [advice] using binaryValue_lt advice, ?_⟩
  have heq := final_equation data quotient (generator^(alpha*target).val) steps h
  simpa only [data, quotient, List.prod_ofFn, quotientLeaves_prod, Adapter.ProductCheck] using heq

end LfzkV2.Current.Adapter.Tree
