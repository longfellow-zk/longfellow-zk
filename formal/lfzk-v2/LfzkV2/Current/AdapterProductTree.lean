import LfzkV2.Current.AdapterCircuit

/-! The archived adapter fragment of `runtime::v2::foreign::adapter`. It is
one fixed product tree per conversion tree over virtual leaves: adjacent
products with odd carries until two wires remain in each tree, then one output
`l*r + 1`, which must vanish. In characteristic two this says that the tree's
product is one. The fragment has no challenge-dependent coefficient: every
per-proof value is a virtual input, and each tree's target is folded into its
first leaf. Its semantics is derived from its sparse terms. -/
noncomputable section
namespace LfzkV2.Current.Adapter.ProductTree
open Layered SumcheckV2 Finset Adapter.Circuit
open scoped Classical

variable {F W : Type} [Field F]

/-- Runtime tree-major layout: wire `i` of tree `t` is array position
`t*n+i`, both for the virtual leaves and for every reduction layer. -/
abbrev Wire (n : ℕ) := Fin 2 × Fin n

def wireIndex (n : ℕ) : Wire n ≃ Fin (2*n) := finProdFinEquiv

@[simp] theorem wireIndex_val {n : ℕ} (tree : Fin 2) (i : Fin n) :
    (wireIndex n (tree,i)).val = tree.val*n+i.val := by
  simp [wireIndex,finProdFinEquiv,Nat.add_comm,Nat.mul_comm]

/-- Each reduction layer pairs within each tree separately. -/
def pairRows (n : ℕ) : Fin (2*half n) → Row (Wire n) F :=
  fun output => match (wireIndex (half n)).symm output with
    | (tree,i) => pairRow (fun j => (tree,j)) i

def step {n : ℕ} (w : Wire n → F) : Wire (half n) → F := fun output =>
  (Layered.sparseLayer (stream (pairRows n))
    (Fin.elim0 : Fin 0 → LfzkV2.Native.AssertionTerm (Wire n))).outputs w (wireIndex (half n) output)

@[simp] theorem step_apply {n : ℕ} (w : Wire n → F) (tree : Fin 2) (i : Fin (half n)) :
    step w (tree,i) = pairValue (fun j => w (tree,j)) i := by
  simp [step,stream_outputs,pairRows,pairRow_eval,Function.comp_def]

/-- The runtime loop pairs while more than two wires remain in a tree. -/
inductive Shape : ℕ → Type where
  | root : Shape 2
  | pair {n : ℕ} : Shape (half n) → Shape n

private theorem half_two_le {n : ℕ} (h : 2 < n) : 2 ≤ half n := by dsimp [half]; omega
private theorem half_lt {n : ℕ} (h : 1 < n) : half n < n := by dsimp [half]; omega

/-- The same stopping rule as the runtime `while count > 2` loop. -/
def plan (n : ℕ) (h : 2 ≤ n) : Shape n :=
  if h2 : n = 2 then h2 ▸ .root
  else .pair (plan (half n) (half_two_le (by omega)))
termination_by n
decreasing_by exact half_lt (by omega)

/-- Number of reduction layers below the final product layer. -/
def depth : {n : ℕ} → Shape n → ℕ
  | _, .root => 0
  | _, .pair next => 1+depth next

def roots : {n : ℕ} → Shape n → (Wire n → F) → Wire 2 → F
  | _, .root, w => w
  | _, .pair rest, w => roots rest (step w)

theorem roots_prod {n : ℕ} (shape : Shape n) (w : Wire n → F) (tree : Fin 2) :
    roots shape w (tree,0) * roots shape w (tree,1) = ∏ i, w (tree,i) := by
  induction shape with
  | root => simp [roots,Fin.prod_univ_two]
  | pair rest ih =>
      rw [roots,ih]
      simp only [step_apply]
      exact pairValue_prod _

/-- Output `t` is `l*r + 1` on the last two wires of tree `t`. -/
def finalRows (tree : Fin 2) : Row (Wire 2) F :=
  [.quadratic () (tree,0) (tree,1) 1, .constant () 1]

def eval {n : ℕ} (shape : Shape n) (w : Wire n → F) : Fin 2 → F :=
  (Layered.sparseLayer (stream finalRows)
    (Fin.elim0 : Fin 0 → LfzkV2.Native.AssertionTerm (Wire 2))).outputs (roots shape w)

theorem eval_product {n : ℕ} (shape : Shape n) (w : Wire n → F) (tree : Fin 2) :
    eval shape w tree = (∏ i, w (tree,i)) + 1 := by
  rw [← roots_prod shape w tree]
  simp only [eval,stream_outputs,finalRows,rowEval,List.map_cons,Layered.Term.value,
    List.map_nil,List.sum_cons,List.sum_nil,one_mul,add_zero]

def Satisfies {n : ℕ} (shape : Shape n) (w : Wire n → F) : Prop :=
  ∀ tree, eval shape w tree = 0

/-- Satisfaction is exactly a unit product in each tree. -/
theorem satisfies_iff [CharP F 2] {n : ℕ} (shape : Shape n) (w : Wire n → F) :
    Satisfies shape w ↔ ∀ tree, ∏ i, w (tree,i) = 1 := by
  simp only [Satisfies,eval_product,add_eq_zero_iff_eq_neg,CharTwo.neg_eq]

end LfzkV2.Current.Adapter.ProductTree
