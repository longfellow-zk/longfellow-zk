import LfzkV2.Current.AdapterProductTree
import LfzkV2.InputBinding

/-! Per-proof virtual leaves of the fixed adapter fragment, as defined by
`Leaf::data`, `Leaf::quotient` and `adapter::virtual_inputs` in the runtime.
Each leaf is `constant + coefficient * x[source]` of one committed bit:

- a data leaf `1 + b*(g^A - 1)`;
- a quotient leaf `power^(m xor o)`, affine in the committed pad bit `o` with
  coefficients chosen by the public masked bit `m`.

Each tree's target is folded into its first leaf, scaled by `target⁻¹`, so
the fixed fragment checks only that each tree's product is one. These
definitions are substituted into the final input claim and never absorbed. -/
noncomputable section
namespace LfzkV2.Current.Adapter.Leaves
open Finset Adapter.Circuit
open scoped Classical

variable {Source F : Type} [Field F]

/-- One leaf is one virtual input `constant + coefficient * x[source]`. -/
abbrev Leaf (Source F : Type) := VirtualInput Source F

/-- Scale both affine coefficients of a leaf. -/
def scale (c : F) (leaf : Leaf Source F) : Leaf Source F :=
  ⟨leaf.source,c*leaf.constant,c*leaf.coefficient⟩

theorem scale_value (c : F) (leaf : Leaf Source F) (x : Source → F) :
    (scale c leaf).value x = c * leaf.value x := by
  simp only [VirtualInput.value,scale]
  ring

/-- A data leaf `1 + b*(power - 1)`. -/
def data (source : Source) (power : F) : Leaf Source F := ⟨source,1,power-1⟩

/-- A quotient leaf `power^(m xor o)` for public bit `m` and pad bit `o`. -/
def quotient (source : Source) (power : F) (m : Bool) : Leaf Source F :=
  ⟨source,if m then power else 1,power-1⟩

theorem data_value (source : Source) (power : F) (bits : Source → Bool) :
    (data source power).value (bitValue ∘ bits) = if bits source then power else 1 := by
  simp only [VirtualInput.value,data,Function.comp_apply,bitValue]
  cases bits source <;> simp

theorem quotient_value [CharP F 2] (source : Source) (power : F) (m : Bool) (bits : Source → Bool) :
    (quotient source power m).value (bitValue ∘ bits) =
      if Bool.xor (bits source) m then power else 1 := by
  simp only [VirtualInput.value,quotient,Function.comp_apply,bitValue]
  cases bits source <;> cases m
  · simp
  · simp
  · simp
  · simp only [Bool.xor_self,if_true,mul_one,Bool.false_eq_true,if_false]
    rw [sub_eq_add_neg,CharTwo.neg_eq,← add_assoc,CharTwo.add_self_eq_zero,zero_add]

/-- One tree in runtime order: data leaves, then quotient leaves, with the
target folded into leaf zero. -/
def tree {d q : ℕ} (sources : Fin d → Source) (powers : Fin d → Fˣ)
    (pads : Fin q → Source) (base : Fˣ) (masked : Fin q → Bool) (target : Fˣ) :
    Fin (d+q) → Leaf Source F := fun i =>
  let leaf : Leaf Source F := Fin.addCases (fun j => data (sources j) (powers j : F))
    (fun j => quotient (pads j) (quotientPower base j.val : F) (masked j)) i
  if i.val = 0 then scale ((target⁻¹ : Fˣ) : F) leaf else leaf

/-- On committed bits, a tree's leaf product is the target's inverse times
the data product and the selected quotient powers. -/
theorem tree_product [CharP F 2] {d q : ℕ} (hd : 0 < d) (sources : Fin d → Source)
    (powers : Fin d → Fˣ) (pads : Fin q → Source) (base : Fˣ) (masked : Fin q → Bool)
    (target : Fˣ) (bits : Source → Bool) :
    (∏ i, (tree sources powers pads base masked target i).value (bitValue ∘ bits)) =
      ((target⁻¹ : Fˣ) : F) * ((∏ j, if bits (sources j) then (powers j : F) else 1) *
        ∏ j, if Bool.xor (bits (pads j)) (masked j) then (quotientPower base j.val : F) else 1) := by
  obtain ⟨d,rfl⟩ : ∃ e, d = e+1 := ⟨d-1,by omega⟩
  unfold tree
  rw [Fin.prod_univ_add,Fin.prod_univ_succ,Fin.prod_univ_succ (n := d)]
  simp only [Fin.val_castAdd,Fin.val_zero,Fin.val_succ,Fin.val_natAdd,Fin.addCases_left,
    Fin.addCases_right,if_true,Nat.add_one_ne_zero,if_false,Nat.add_eq_zero_iff,
    false_and,scale_value,data_value,quotient_value]
  ring

/-- The leaf algebra lemma: on committed bits, the fixed fragment's unit
product for one tree is exactly the conversion proof's product equation,
with the quotient decoded from the pads and the public masked bits. -/
theorem tree_product_check [CharP F 2] {p d q : ℕ} [Fact p.Prime] (hd : 0 < d)
    (generator : Fˣ) (weights : Fin d → ZMod p) (target alpha : ZMod p)
    (sources : Fin d → Source) (pads : Fin q → Source) (masked : Fin q → Bool)
    (bits : Source → Bool) :
    (∏ i, (tree sources (fun j => generator^(alpha*weights j).val) pads
        (generator^(-(p : ℤ))) masked (generator^(alpha*target).val) i).value (bitValue ∘ bits) = 1) ↔
      Adapter.ProductCheck generator weights (bits ∘ sources) target alpha
        (Tree.binaryValue (List.ofFn fun j => Bool.xor (bits (pads j)) (masked j))) := by
  have hq := Tree.quotientLeaves_prod (generator^(-(p : ℤ)))
    (List.ofFn fun j => Bool.xor (bits (pads j)) (masked j))
  rw [quotientLeaves_ofFn,List.prod_ofFn] at hq
  rw [tree_product hd]
  unfold Adapter.ProductCheck
  rw [← hq]
  constructor
  · intro h
    apply Units.ext
    have h' := congrArg (fun x : F => ((generator^(alpha*target).val : Fˣ) : F) * x) h
    simp only [← mul_assoc,← Units.val_mul,mul_inv_cancel,Units.val_one,one_mul,mul_one] at h'
    simpa only [Units.val_mul,Units.coe_prod,apply_ite,Units.val_one,Function.comp_apply] using h'
  · intro h
    have h' := congrArg (fun x : Fˣ => ((x : Fˣ) : F)) h
    simp only [Units.val_mul,Units.coe_prod,apply_ite,Units.val_one,Function.comp_apply] at h'
    rw [h',← Units.val_mul,inv_mul_cancel,Units.val_one]

end LfzkV2.Current.Adapter.Leaves
