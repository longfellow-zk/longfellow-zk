import LfzkV2.Current.AdapterTree
import LfzkV2.Layered.SparseLayer

/-! Sparse rows shared by the fixed adapter fragment: one output's terms,
adjacent products with odd carries, and their placement in a global sparse
layer. The fragment itself is `Adapter.ProductTree`; its virtual leaves are
`Adapter.Leaves`. These rows have no challenge-dependent coefficient. -/
noncomputable section
namespace LfzkV2.Current.Adapter.Circuit
open Layered SumcheckV2 Finset
open scoped Classical

variable {F W : Type} [Field F]

abbrev Row (W F : Type) := List (Layered.Term Unit W F)

def rowEval (row : Row W F) (w : W → F) : F := (row.map (Layered.Term.value w)).sum

/-- One output's terms are appended together. Splitting the three term kinds
into Rust's three streams changes their traversal order, not their sum. -/
def stream {n : ℕ} (rows : Fin n → Row W F) : List (Layered.Term (Fin n) W F) :=
  (List.ofFn fun i : Fin n => i).flatMap fun i =>
    (rows i).map (Layered.Term.map (fun _ => i) id)

private theorem lifted_value {n : ℕ} (term : Layered.Term Unit W F)
    (w : W → F) (i g : Fin n) :
    (term.map (fun _ => i) id).evaluated w g =
      if i = g then term.value w else 0 := by
  cases term <;> simp [Layered.Term.evaluated, Layered.Term.map,
    Layered.Term.output, Layered.Term.value]

private theorem stream_list {n : ℕ} (rows : Fin n → Row W F)
    (w : W → F) (g : Fin n) (indices : List (Fin n)) :
    ((indices.flatMap fun i => (rows i).map
      (Layered.Term.map (fun _ => i) id)).map (Layered.Term.evaluated w g)).sum =
      (indices.map fun i => if i = g then rowEval (rows i) w else 0).sum := by
  induction indices with
  | nil => rfl
  | cons i rest ih =>
      simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_cons,
        List.sum_cons, List.map_map, Function.comp_def, lifted_value, ih]
      congr 1
      by_cases h : i = g <;> simp [h, rowEval]

/-- The sparse tensor interpretation evaluates the generated row exactly. -/
theorem stream_outputs {n : ℕ} [Fintype W] (rows : Fin n → Row W F)
    (w : W → F) (g : Fin n) :
    (Layered.sparseLayer (stream rows) (Fin.elim0 : Fin 0 → LfzkV2.Native.AssertionTerm W)).outputs w g =
      rowEval (rows g) w := by
  rw [Layered.sparseLayer_outputs, stream, stream_list]
  simp [List.map_ofFn, List.sum_ofFn]

/-- Runtime tree-major layout: data first, then quotient factors, in each of
its two challenge trees. -/
def half (n : ℕ) : ℕ := (n+1)/2

private theorem pair_left_lt {n : ℕ} (i : Fin (half n)) : 2*i.val < n := by
  have := i.isLt
  dsimp [half] at this
  omega

/-- Exactly one product, or one linear odd carry, for each destination. -/
def pairRow {n : ℕ} (wire : Fin n → W) (i : Fin (half n)) : Row W F :=
  if h : 2*i.val+1 < n then
    [.quadratic () (wire ⟨2*i.val,pair_left_lt i⟩) (wire ⟨2*i.val+1,h⟩) 1]
  else [.linear () (wire ⟨2*i.val,pair_left_lt i⟩) 1]

def pairValue {n : ℕ} (w : Fin n → F) (i : Fin (half n)) : F :=
  if h : 2*i.val+1 < n then w ⟨2*i.val,pair_left_lt i⟩ * w ⟨2*i.val+1,h⟩
  else w ⟨2*i.val,pair_left_lt i⟩

@[simp] theorem pairRow_eval {n : ℕ} (wire : Fin n → W)
    (w : W → F) (i : Fin (half n)) :
    rowEval (pairRow wire i) w = pairValue (w ∘ wire) i := by
  unfold pairRow pairValue
  split_ifs <;> simp [rowEval, Layered.Term.value]

private def pairNat (n : ℕ) (w : ℕ → F) (i : ℕ) : F :=
  if 2*i+1 < n then w (2*i)*w (2*i+1) else w (2*i)

private theorem pairNat_prod (n : ℕ) (w : ℕ → F) :
    (∏ i ∈ range (half n), pairNat n w i) = ∏ i ∈ range n, w i := by
  induction n using Nat.twoStepInduction generalizing w with
  | zero => simp [half]
  | one => simp [half, pairNat]
  | more n ih _ =>
      have hh : half (n+2) = half n+1 := by dsimp [half]; omega
      have hs (i : ℕ) : pairNat (n+2) w (i+1) =
          pairNat n (fun j => w (j+2)) i := by
        simp only [pairNat]
        have he : 2*(i+1)+1 < n+2 ↔ 2*i+1 < n := by omega
        simp only [he]
        split_ifs <;> simp [Nat.mul_add, Nat.add_left_comm, Nat.add_comm]
      rw [hh, Finset.prod_range_succ', Finset.prod_range_succ', Finset.prod_range_succ']
      simp_rw [hs]
      rw [ih]
      have hz : pairNat (n+2) w 0 = w 0*w 1 := by simp [pairNat]
      rw [hz]
      simp [mul_assoc, mul_comm, Nat.add_assoc]

/-- Pairing never loses an odd tail and preserves each group's product. -/
theorem pairValue_prod {n : ℕ} (w : Fin n → F) :
    (∏ i, pairValue w i) = ∏ i, w i := by
  let extended : ℕ → F := fun j => if h : j < n then w ⟨j,h⟩ else 1
  have hp := pairNat_prod n extended
  calc
    (∏ i, pairValue w i) = ∏ i : Fin (half n), pairNat n extended i.val := by
      apply Finset.prod_congr rfl
      intro i _
      have hl := pair_left_lt i
      dsimp [pairValue, pairNat, extended]
      split_ifs <;> simp_all
    _ = ∏ i ∈ range (half n), pairNat n extended i := Fin.prod_univ_eq_prod_range _ _
    _ = ∏ i ∈ range n, extended i := hp
    _ = ∏ i : Fin n, extended i.val := (Fin.prod_univ_eq_prod_range _ _).symm
    _ = ∏ i, w i := by apply Finset.prod_congr rfl; intro i _; simp [extended]

/-- Repeated squaring produces the little-endian quotient powers. -/
def quotientPower (base : Fˣ) (i : ℕ) : Fˣ := base^(2^i)

theorem quotientLeaves_ofFn {a : ℕ} (base : Fˣ) (bits : Fin a → Bool) :
    Tree.quotientLeaves base (List.ofFn bits) =
      List.ofFn (fun i => if bits i then quotientPower base i.val else 1) := by
  induction a generalizing base with
  | zero => simp [Tree.quotientLeaves]
  | succ a ih =>
      rw [List.ofFn_succ, Tree.quotientLeaves, ih, List.ofFn_succ]
      congr 1
      · simp [quotientPower]
      · apply List.ofFn_inj.mpr
        funext i
        simp [quotientPower, pow_succ, pow_mul, mul_pow]

/-- A committed bit as a field element. -/
def bitValue (b : Bool) : F := if b then 1 else 0

section Layered

/-- Place a generated exact-width sparse layer in the global padded arrays.
Only public address maps change; unmentioned padded outputs receive no terms. -/
def mappedLayer {n out mid : ℕ} (rows : Fin n → Row W F)
    (input : W → Cube mid) (output : Fin n ↪ Cube out) :
    LfzkV2.Native.CircuitLayer (Cube out) (Cube mid) (Fin 0) F :=
  Layered.sparseLayer ((stream rows).map (Layered.Term.map output input)) Fin.elim0

private theorem evaluated_map {n out mid : ℕ} (input : W → Cube mid)
    (output : Fin n ↪ Cube out) (w : Cube mid → F) (g : Fin n)
    (term : Layered.Term (Fin n) W F) :
    (term.map output input).evaluated w (output g) = term.evaluated (w ∘ input) g := by
  cases term <;> simp [Layered.Term.evaluated, Layered.Term.map,
    Layered.Term.output, Layered.Term.value, output.injective.eq_iff]

/-- Padding and embedding are proved at the sparse tensor layer. -/
theorem mappedLayer_outputs {n out mid : ℕ} [Fintype W] (rows : Fin n → Row W F)
    (input : W → Cube mid) (output : Fin n ↪ Cube out) (w : Cube mid → F) (g : Fin n) :
    (mappedLayer rows input output).outputs w (output g) = rowEval (rows g) (w ∘ input) := by
  rw [mappedLayer, Layered.sparseLayer_outputs]
  simp only [List.map_map, Function.comp_def, evaluated_map]
  have h := stream_outputs rows (w ∘ input) g
  rw [Layered.sparseLayer_outputs] at h
  exact h
end Layered
end LfzkV2.Current.Adapter.Circuit
