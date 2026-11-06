import LfzkV2.Current.AdapterTree
import LfzkV2.Layered.SparseLayer
import Mathlib.Data.Nat.Log

/-! The generated adapter is an ordinary sparse circuit: Boolean mux leaves,
adjacent products with odd carries, and two zero-output product assertions.
The mathematical generator below follows those three loops. Its semantics
is derived from its sparse terms, not supplied as a root-equation premise. -/
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
abbrev Wire (data quotient : ℕ) := Fin 2 × (Fin data ⊕ Fin quotient)

def wireIndex (data quotient : ℕ) : Wire data quotient ≃ Fin (2*(data+quotient)) :=
  (Equiv.prodCongr (Equiv.refl (Fin 2)) finSumFinEquiv).trans finProdFinEquiv

@[simp] theorem wireIndex_data {d q : ℕ} (tree : Fin 2) (i : Fin d) :
    (wireIndex d q (tree,Sum.inl i)).val = tree.val*(d+q)+i.val := by
  simp [wireIndex, finProdFinEquiv, finSumFinEquiv, Nat.mul_comm, Nat.add_comm]

@[simp] theorem wireIndex_quotient {d q : ℕ} (tree : Fin 2) (i : Fin q) :
    (wireIndex d q (tree,Sum.inr i)).val = tree.val*(d+q)+d+i.val := by
  simp [wireIndex, finProdFinEquiv, finSumFinEquiv, Nat.mul_comm, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

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

/-- Each reduction layer preserves the two contiguous groups separately. -/
def pairRows (d q : ℕ) : Fin (2*(half d+half q)) → Row (Wire d q) F :=
  fun output => match (wireIndex (half d) (half q)).symm output with
    | (tree, .inl i) => pairRow (fun j => (tree, Sum.inl j)) i
    | (tree, .inr i) => pairRow (fun j => (tree, Sum.inr j)) i

def step {d q : ℕ} (w : Wire d q → F) : Wire (half d) (half q) → F := fun output =>
  (Layered.sparseLayer (stream (pairRows d q))
    (Fin.elim0 : Fin 0 → LfzkV2.Native.AssertionTerm (Wire d q))).outputs w
      (wireIndex (half d) (half q) output)

@[simp] theorem step_data {d q : ℕ} (w : Wire d q → F) (tree : Fin 2) (i : Fin (half d)) :
    step w (tree,Sum.inl i) = pairValue (fun j => w (tree,Sum.inl j)) i := by
  simp [step, stream_outputs, pairRows, pairRow_eval, Function.comp_def]

@[simp] theorem step_quotient {d q : ℕ} (w : Wire d q → F) (tree : Fin 2) (i : Fin (half q)) :
    step w (tree,Sum.inr i) = pairValue (fun j => w (tree,Sum.inr j)) i := by
  simp [step, stream_outputs, pairRows, pairRow_eval, Function.comp_def]

/-- A generated reduction ends with one data and one quotient factor in each
challenge tree. Extra intermediate wires or asserted root equations are absent. -/
inductive Shape : ℕ → ℕ → Type where
  | root : Shape 1 1
  | pair {d q : ℕ} : Shape (half d) (half q) → Shape d q

private theorem half_pos {n : ℕ} (h : 0 < n) : 0 < half n := by dsimp [half]; omega
private theorem half_le {n : ℕ} (h : 0 < n) : half n ≤ n := by dsimp [half]; omega
private theorem half_lt {n : ℕ} (h : 1 < n) : half n < n := by dsimp [half]; omega

/-- The same stopping rule as the runtime while loop. -/
def plan (d q : ℕ) (hd : 0 < d) (hq : 0 < q) : Shape d q :=
  if h : d = 1 ∧ q = 1 then by rcases h with ⟨rfl,rfl⟩; exact .root
  else .pair (plan (half d) (half q) (half_pos hd) (half_pos hq))
termination_by d+q
decreasing_by
  have hdle := half_le hd
  have hqle := half_le hq
  have hs : half d < d ∨ half q < q := by
    by_cases hdone : d = 1
    · right; apply half_lt; omega
    · left; apply half_lt; omega
  omega

def roots {d q : ℕ} : Shape d q → (Wire d q → F) → Wire 1 1 → F
  | .root, w => w
  | .pair rest, w => roots rest (step w)

theorem roots_data {d q : ℕ} (shape : Shape d q) (w : Wire d q → F) (tree : Fin 2) :
    roots shape w (tree,Sum.inl 0) = ∏ i, w (tree,Sum.inl i) := by
  induction shape with
  | root => simp [roots]
  | pair rest ih =>
      rw [roots, ih]
      simp only [step_data]
      exact pairValue_prod _

theorem roots_quotient {d q : ℕ} (shape : Shape d q) (w : Wire d q → F) (tree : Fin 2) :
    roots shape w (tree,Sum.inr 0) = ∏ i, w (tree,Sum.inr i) := by
  induction shape with
  | root => simp [roots]
  | pair rest ih =>
      rw [roots, ih]
      simp only [step_quotient]
      exact pairValue_prod _

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

/-- The two linear coefficients stay separate, exactly as in LFC3, even
when their sum is zero. Thus the topology does not depend on the challenges. -/
def leafRows {d q : ℕ} (sources : Fin d → W) (pads : Fin 2 → Fin q → W)
    (powers : Fin 2 → Fin d → Fˣ) (base : Fˣ) (masked : Fin 2 → Fin q → Bool) :
    Fin (2*(d+q)) → Row W F := fun output =>
  match (wireIndex d q).symm output with
  | (tree,.inl i) => [.linear () (sources i) (powers tree i), .linear () (sources i) 1,
      .constant () 1]
  | (tree,.inr i) => [.linear () (pads tree i) (quotientPower base i.val),
      .linear () (pads tree i) 1,
      .constant () (if masked tree i then (quotientPower base i.val : F) else 1)]

def leafState {d q : ℕ} [Fintype W]
    (sources : Fin d → W) (pads : Fin 2 → Fin q → W)
    (powers : Fin 2 → Fin d → Fˣ) (base : Fˣ) (masked : Fin 2 → Fin q → Bool)
    (w : W → F) : Wire d q → F := fun output =>
  (Layered.sparseLayer (stream (leafRows sources pads powers base masked))
    (Fin.elim0 : Fin 0 → LfzkV2.Native.AssertionTerm W)).outputs w (wireIndex d q output)

def bitValue (b : Bool) : F := if b then 1 else 0

variable [CharP F 2]

@[simp] theorem leafState_data {d q : ℕ} [Fintype W]
    (sources : Fin d → W) (pads : Fin 2 → Fin q → W)
    (powers : Fin 2 → Fin d → Fˣ) (base : Fˣ) (masked : Fin 2 → Fin q → Bool)
    (bits : W → Bool) (tree : Fin 2) (i : Fin d) :
    leafState sources pads powers base masked (bitValue ∘ bits) (tree,.inl i) =
      if bits (sources i) then (powers tree i : F) else 1 := by
  simp only [leafState, stream_outputs, leafRows, Equiv.symm_apply_apply, rowEval,
    List.map_cons, Layered.Term.value, List.map_nil, List.sum_cons, List.sum_nil,
    one_mul, Function.comp_apply, bitValue]
  cases bits (sources i) <;> simp [CharTwo.add_self_eq_zero]

@[simp] theorem leafState_quotient {d q : ℕ} [Fintype W]
    (sources : Fin d → W) (pads : Fin 2 → Fin q → W)
    (powers : Fin 2 → Fin d → Fˣ) (base : Fˣ) (masked : Fin 2 → Fin q → Bool)
    (bits : W → Bool) (tree : Fin 2) (i : Fin q) :
    leafState sources pads powers base masked (bitValue ∘ bits) (tree,.inr i) =
      if Bool.xor (bits (pads tree i)) (masked tree i) then
        (quotientPower base i.val : F) else 1 := by
  simp only [leafState, stream_outputs, leafRows, Equiv.symm_apply_apply, rowEval,
    List.map_cons, Layered.Term.value, List.map_nil, List.sum_cons, List.sum_nil,
    one_mul, Function.comp_apply, bitValue]
  cases bits (pads tree i) <;> cases masked tree i <;>
    simp [CharTwo.add_self_eq_zero, add_left_comm]

/-- The final layer multiplies the two roots and adds its public target. -/
def finalRows (targets : Fin 2 → Fˣ) (tree : Fin 2) : Row (Wire 1 1) F :=
  [.quadratic () (tree,.inl 0) (tree,.inr 0) 1, .constant () (targets tree)]

def eval {d q : ℕ} [Fintype W] (shape : Shape d q)
    (sources : Fin d → W) (pads : Fin 2 → Fin q → W)
    (powers : Fin 2 → Fin d → Fˣ) (base : Fˣ) (masked : Fin 2 → Fin q → Bool)
    (targets : Fin 2 → Fˣ) (w : W → F) : Fin 2 → F :=
  (Layered.sparseLayer (stream (finalRows targets))
    (Fin.elim0 : Fin 0 → LfzkV2.Native.AssertionTerm (Wire 1 1))).outputs
      (roots shape (leafState sources pads powers base masked w))

def Satisfies {d q : ℕ} [Fintype W] (shape : Shape d q)
    (sources : Fin d → W) (pads : Fin 2 → Fin q → W)
    (powers : Fin 2 → Fin d → Fˣ) (base : Fˣ) (masked : Fin 2 → Fin q → Bool)
    (targets : Fin 2 → Fˣ) (w : W → F) : Prop :=
  ∀ tree, eval shape sources pads powers base masked targets w tree = 0

theorem eval_products {d q : ℕ} [Fintype W] (shape : Shape d q)
    (sources : Fin d → W) (pads : Fin 2 → Fin q → W)
    (powers : Fin 2 → Fin d → Fˣ) (base : Fˣ) (masked : Fin 2 → Fin q → Bool)
    (targets : Fin 2 → Fˣ) (bits : W → Bool) (tree : Fin 2) :
    eval shape sources pads powers base masked targets (bitValue ∘ bits) tree =
      (∏ i, if bits (sources i) then (powers tree i : F) else 1) *
      (∏ i, if Bool.xor (bits (pads tree i)) (masked tree i) then
        (quotientPower base i.val : F) else 1) + targets tree := by
  simp only [eval, stream_outputs, finalRows, rowEval, List.map_cons, Layered.Term.value,
    List.map_nil, List.sum_cons, List.sum_nil, one_mul, add_zero,
    roots_data, roots_quotient, leafState_data, leafState_quotient]

/-- Satisfaction of the generated sparse circuit supplies the conversion
proof's product equation and its bounded quotient, for each challenge. -/
theorem satisfies_product_check {p d q : ℕ} [Fact p.Prime] [Fintype W]
    (shape : Shape d q) (sources : Fin d → W) (pads : Fin 2 → Fin q → W)
    (generator : Fˣ) (weights : Fin d → ZMod p) (target : ZMod p)
    (alpha : Fin 2 → ZMod p) (masked : Fin 2 → Fin q → Bool) (bits : W → Bool)
    (h : Satisfies shape sources pads
      (fun tree i => generator^(alpha tree*weights i).val) (generator^(-(p : ℤ))) masked
      (fun tree => generator^(alpha tree*target).val) (bitValue ∘ bits)) :
    let quotient := fun tree => Tree.binaryValue
      (List.ofFn fun i => Bool.xor (bits (pads tree i)) (masked tree i))
    (∀ tree, quotient tree < 2^q) ∧ ∀ tree,
      Adapter.ProductCheck generator weights (bits ∘ sources) target (alpha tree) (quotient tree) := by
  intro quotient
  have hproduct (tree : Fin 2) := h tree
  simp only [eval_products] at hproduct
  constructor
  · intro tree
    simpa only [quotient, List.length_ofFn] using
      (Tree.binaryValue_lt (List.ofFn fun i => Bool.xor (bits (pads tree i)) (masked tree i)))
  intro tree
  have hq := Tree.quotientLeaves_prod (generator^(-(p : ℤ)))
    (List.ofFn fun i => Bool.xor (bits (pads tree i)) (masked tree i))
  rw [quotientLeaves_ofFn, List.prod_ofFn] at hq
  have heq :
      (∏ i, if bits (sources i) then generator^(alpha tree*weights i).val else 1) *
        (generator^(-(p : ℤ)))^(quotient tree) = generator^(alpha tree*target).val := by
    apply Units.ext
    have hp := congrArg (fun x : F => x + (generator^(alpha tree*target).val : Fˣ)) (hproduct tree)
    rw [← hq]
    simpa only [Units.val_mul, Units.coe_prod, apply_ite, Units.val_one,
      add_assoc, CharTwo.add_self_eq_zero, add_zero, zero_add] using hp
  change _ = _ at heq ⊢
  exact heq

section Layered

/-- Place a generated exact-width sparse layer in the global padded arrays.
Only public address maps change; unmentioned padded outputs receive no terms. -/
def mappedLayer {n out mid : ℕ} (rows : Fin n → Row W F)
    (input : W → Cube mid) (output : Fin n ↪ Cube out) :
    LfzkV2.Native.CircuitLayer (Cube out) (Cube mid) (Fin 0) F :=
  Layered.sparseLayer ((stream rows).map (Layered.Term.map output input)) Fin.elim0

omit [CharP F 2] in
private theorem evaluated_map {n out mid : ℕ} (input : W → Cube mid)
    (output : Fin n ↪ Cube out) (w : Cube mid → F) (g : Fin n)
    (term : Layered.Term (Fin n) W F) :
    (term.map output input).evaluated w (output g) = term.evaluated (w ∘ input) g := by
  cases term <;> simp [Layered.Term.evaluated, Layered.Term.map,
    Layered.Term.output, Layered.Term.value, output.injective.eq_iff]

omit [CharP F 2] in
/-- Padding and embedding are proved at the sparse tensor layer. -/
theorem mappedLayer_outputs {n out mid : ℕ} [Fintype W] (rows : Fin n → Row W F)
    (input : W → Cube mid) (output : Fin n ↪ Cube out) (w : Cube mid → F) (g : Fin n) :
    (mappedLayer rows input output).outputs w (output g) = rowEval (rows g) (w ∘ input) := by
  rw [mappedLayer, Layered.sparseLayer_outputs]
  simp only [List.map_map, Function.comp_def, evaluated_map]
  have h := stream_outputs rows (w ∘ input) g
  rw [Layered.sparseLayer_outputs] at h
  exact h

/-- Every intermediate layer has its own dense wire array. These public
injections specify its ordinary padding and indexing; no semantic equality is
stored in the layout. -/
structure Layout where
  log : ℕ → ℕ → ℕ
  index : ∀ d q, Wire d q ↪ Cube (log d q)

def Layout.flat (layout : Layout) (d q : ℕ) : Fin (2*(d+q)) ↪ Cube (layout.log d q) :=
  (wireIndex d q).symm.toEmbedding.trans (layout.index d q)

/-- Canonical low-bit-first dense-array indexing into the Boolean cube. -/
def cube (n : ℕ) : Fin (2^n) → Cube n :=
  match n with
  | 0 => fun _ => ()
  | n+1 => fun i => (decide (i.val%2 = 1), cube n ⟨i.val/2,by
      exact Nat.div_lt_of_lt_mul (by simpa only [pow_succ, Nat.mul_comm] using i.isLt)⟩)

omit [CharP F 2] in
private theorem cube_injective (n : ℕ) : Function.Injective (cube n) := by
  induction n with
  | zero => intro i j _; apply Fin.ext; have := i.isLt; have := j.isLt; simp_all
  | succ n ih =>
      intro i j h
      have ht := congrArg Prod.snd h
      have hp := congrArg Prod.fst h
      change cube n _ = cube n _ at ht
      have hd := congrArg Fin.val (ih ht)
      change decide (i.val%2 = 1) = decide (j.val%2 = 1) at hp
      have hi := Nat.mod_lt i.val (by decide : 0 < 2)
      have hj := Nat.mod_lt j.val (by decide : 0 < 2)
      have hm : i.val%2 = j.val%2 := by
        by_cases ha : i.val%2 = 1 <;> by_cases hb : j.val%2 = 1 <;> simp_all
      apply Fin.ext
      dsimp at hd
      omega

/-- Construct padding maps from the public numeric width bounds. -/
def Layout.ofBounds (log : ℕ → ℕ → ℕ)
    (bound : ∀ d q, 2*(d+q) ≤ 2^(log d q)) : Layout where
  log := log
  index d q := (wireIndex d q).toEmbedding.trans
    ((Fin.castLEEmb (bound d q)).trans ⟨cube (log d q),cube_injective _⟩)

/-- The ordinary next-power-of-two padding used for the generated arrays. -/
def Layout.standard : Layout :=
  Layout.ofBounds (fun d q => Nat.clog 2 (2*(d+q))) (fun _ _ => Nat.le_pow_clog (by decide) _)

end Layered
end LfzkV2.Current.Adapter.Circuit
