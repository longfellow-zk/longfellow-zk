import Lfzk.ZkArithBoundary
import Lfzk.NizkZk

/-!
# The arithmetization at the deployed width profile

`Lfzk.ZkArithBoundary.zkFieldDataOf` builds the field half of the zero-knowledge chain
(`RbrZkSplit.ZkFieldData`) for a circuit with **one** width `logw` at every layer, the output layer
included, and binds the two hands one after the other.  The deployed circuits have a width per layer
(`v7-circuit-profiles.json`: the signature circuit's hand widths run `9, 10, 11, …, 12`, the hash
circuits' `13, 13, 14, …`), an output width `logv` of its own, and the verifier binds the two hands
**interleaved** (`verifier_layers.h` `layer_h`, `zk_common.h:L91-L96`: `for round < logw, for hand <
2`, challenge `hb[hand][round]`).  This file builds a whole `ZkFieldData` for that profile.

## The profile

A circuit `c` (`Lfzk.Arith.QuadCircuit`), an output width `logv`, and hand widths `lw ly` for its
layers `ly < nl`: layer `ly` reads layer `ly + 1`'s wires on the cube `{0,1}^{lw ly}`, and writes its
own wires on `{0,1}^{ow ly}`, `ow 0 = logv`, `ow (ly + 1) = lw ly`; the last layer reads the input
wires, so `ninp ≤ 2^{lw (nl - 1)}`.  `WellFormedP` says so (decidable).  The sumcheck of layer `ly`
runs `2 · lw ly` rounds — the row's `CostV1.Params.rounds` at `lw := logw` — and nothing below the
input layer is ever run.

## Points

Every point lives in one container `Vector F L`, `L` at least every width, padded with zeros
(`evenPt`, `oddPt`, `padG`): a cube vector supported on `[0, 2^n)` has the same multilinear
extension at a padded point as at the unpadded one, so nothing in the container is visible.  A bound
list `bnd = [L₀, R₀, L₁, R₁, …]` gives the left point `evenPt L (ptOf bnd)` and the right point
`oddPt L (ptOf bnd)`.

## What is proved

* `cube_sum_layer` — **the layer relation, interleaved**: the hypercube sum of
  `bind_gh_all · W(L) · W(R)` over the `2n` interleaved hand variables is the `alpha`-combination of
  the layer's gate evaluation at its two points;
* `zkHonestP` — the honest values (`ZkHonest`), the partial hypercube sums of that polynomial at
  layer `ly < nl`, and the zero-variable constant `V_ly(g0) + alpha · V_ly(g1)` below the circuit;
* `zkBoundaryP` — **the whole `ZkBoundary`** at `w ly = 2 · lw ly`, under `DeadEnd`, for a code that
  agrees with the construction (`CodeAgreesP`: interleaved points, `bind_gh_all` at the layer's own
  `beta` for `ly < nl`, the input row) and candidates whose committed columns are their witnesses;
* `zk_hinitP` — the layer-0 count at the output point `G : Fin logv → F`, at `(logv + 2)·|F|^(logv+1)`;
* `zkFieldDataP` and `zkFieldDataP_exactAt` — **a `ZkFieldData` at `Sat := Satisfied`, exactly at
  the row's numerals**: the only further inputs are the decoders' balances.

So at the deployed v7 rows the field half of the zero-knowledge chain is constructed from a circuit
in the deployed format (`Lfzk.CompiledZkProfileRows`), not assumed.  What remains about the
arithmetization is what `ZkArithBoundary` lists: `WellFormedP`, `Isolated`, `DeadEnd` (decidable
facts about the circuit, checked on the registered v7 circuits by `inspect_v7_assertions.py`), the
code's agreement with the construction, and that `QuadCircuit` is the artifact's bytes.  No
`OneWire` is needed: nothing below the input layer is run.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.ZkArithProfile

open Finset Lfzk.Arith Lfzk.RbrZkLongfellow Lfzk.RbrZkSplit Lfzk.ZkMultilinear Lfzk.ZkArithInit

variable {F : Type} [Field F]

/-! ## 1. Interleaved points -/

section Points

/-- **The left hand's point** of a coordinate function: its even coordinates. -/
def evenPt (L : ℕ) (y : ℕ → F) : Vector F L := Vector.ofFn fun k : Fin L => y (2 * k.val)

/-- **The right hand's point** of a coordinate function: its odd coordinates. -/
def oddPt (L : ℕ) (y : ℕ → F) : Vector F L := Vector.ofFn fun k : Fin L => y (2 * k.val + 1)

/-- A vector as a coordinate function, zero past its length. -/
def vf {m : ℕ} (x : Vector F m) : ℕ → F := fun i => if h : i < m then x[i] else 0

/-- A coordinate function cut at `m` coordinates. -/
def cut (m : ℕ) (y : ℕ → F) : ℕ → F := fun i => if i < m then y i else 0

/-- The output point `G`, padded into the container. -/
def padG {logv : ℕ} (L : ℕ) (G : Fin logv → F) : Vector F L :=
  Vector.ofFn fun k : Fin L => if h : k.val < logv then G ⟨k.val, h⟩ else 0

/-- The challenges of a full bound, as a vector, are the list's coordinates. -/
theorem vf_chalVec (bnd : List F) {m : ℕ} (hm : bnd.length = m) :
    vf (chalVec bnd m) = ptOf bnd := by
  funext i
  unfold vf ptOf
  split_ifs with h
  · simp [chalVec]
  · rw [List.getD_eq_default _ _ (by omega)]

/-- At the full bound a completion is cut away. -/
theorem cut_append_full (bnd ext : List F) {m : ℕ} (hm : bnd.length = m) :
    cut m (ptOf (bnd ++ ext)) = ptOf bnd := by
  funext i
  unfold cut
  split_ifs with h
  · exact ptOf_append_lt bnd ext (by omega)
  · unfold ptOf
    rw [List.getD_eq_default _ _ (by omega)]

/-- A cube vector with bits `s`. -/
def bitsF (m : ℕ) (s : Fin m → Fin 2) : ℕ → F :=
  fun i => if h : i < m then ((s ⟨i, h⟩ : ℕ) : F) else 0

omit [Field F] in
/-- The bits of the `finFunctionFinEquiv` index are its digits. -/
theorem bit_value_ffe {n : ℕ} (s : Fin n → Fin 2) (k : ℕ) :
    bit_value (finFunctionFinEquiv s : ℕ) k = if h : k < n then (s ⟨k, h⟩ : ℕ) else 0 := by
  split_ifs with h
  · have := finFunctionFinEquiv_symm_apply_val (m := 2) (finFunctionFinEquiv s) ⟨k, h⟩
    rw [Equiv.symm_apply_apply] at this
    rw [this]
    rfl
  · unfold bit_value
    have hlt : (finFunctionFinEquiv s : ℕ) < 2 ^ k :=
      lt_of_lt_of_le (finFunctionFinEquiv s).isLt (Nat.pow_le_pow_right (by norm_num) (by omega))
    rw [Nat.div_eq_of_lt hlt]

/-- A boolean vector, as a coordinate function, is the bit function of its index. -/
theorem vf_bv (m j : ℕ) (hj : j < 2 ^ m) :
    vf (boolean_vector j : Vector F m)
      = bitsF m (finFunctionFinEquiv.symm (⟨j, hj⟩ : Fin (2 ^ m))) := by
  funext i
  unfold vf bitsF
  split_ifs with h
  · rw [finFunctionFinEquiv_symm_apply_val]
    simp only [boolean_vector, Vector.getElem_ofFn]
    show (if bit_value j i = 1 then (1 : F) else 0) = ((j / 2 ^ i % 2 : ℕ) : F)
    have hb : j / 2 ^ i % 2 < 2 := Nat.mod_lt _ (by norm_num)
    unfold bit_value
    rcases (by omega : j / 2 ^ i % 2 = 0 ∨ j / 2 ^ i % 2 = 1) with h0 | h1
    · rw [h0]; simp
    · rw [h1]; simp
  · rfl

/-- **The hypercube sum, over bit functions.** -/
theorem cube_sum_bits (m : ℕ) (φ : (ℕ → F) → F) :
    ∑ j ∈ range (2 ^ m), φ (vf (boolean_vector j : Vector F m))
      = ∑ s : Fin m → Fin 2, φ (bitsF m s) := by
  rw [← Fin.sum_univ_eq_sum_range (fun j => φ (vf (boolean_vector j : Vector F m))) (2 ^ m)]
  refine Fintype.sum_equiv finFunctionFinEquiv.symm _ _ fun j => ?_
  rw [vf_bv m j.val j.isLt]

/-- **Splitting `2n` bits into the even (left) and odd (right) ones.** -/
def splitEquiv (n : ℕ) : (Fin (2 * n) → Fin 2) ≃ (Fin n → Fin 2) × (Fin n → Fin 2) where
  toFun s := (fun k => s ⟨2 * k.val, by omega⟩, fun k => s ⟨2 * k.val + 1, by omega⟩)
  invFun p := fun i => if i.val % 2 = 0 then p.1 ⟨i.val / 2, by omega⟩ else p.2 ⟨i.val / 2, by omega⟩
  left_inv s := by
    funext i
    by_cases h : i.val % 2 = 0
    · simp only [if_pos h]
      congr 1
      ext
      simp only
      omega
    · simp only [if_neg h]
      congr 1
      ext
      simp only
      omega
  right_inv p := by
    obtain ⟨p1, p2⟩ := p
    refine Prod.ext ?_ ?_
    · funext k
      dsimp only
      rw [if_pos (show (2 * k.val) % 2 = 0 by omega)]
      congr 1
      ext
      simp only
      omega
    · funext k
      dsimp only
      rw [if_neg (show ¬ ((2 * k.val + 1) % 2 = 0) by omega)]
      congr 1
      ext
      simp only
      omega

/-- The even coordinates of an interleaved bit function are the left bits, as a cube point. -/
theorem evenPt_split {n L : ℕ} (p : (Fin n → Fin 2) × (Fin n → Fin 2)) :
    evenPt L (bitsF (2 * n) ((splitEquiv n).symm p))
      = (boolean_vector (finFunctionFinEquiv p.1 : ℕ) : Vector F L) := by
  ext k hk
  simp only [evenPt, boolean_vector, Vector.getElem_ofFn, bitsF]
  rw [bit_value_ffe]
  by_cases h : k < n
  · rw [dif_pos (by omega), dif_pos h]
    simp only [splitEquiv, Equiv.coe_fn_symm_mk, show (2 * k) % 2 = 0 by omega, if_true]
    have hk2 : (⟨2 * k / 2, by omega⟩ : Fin n) = ⟨k, h⟩ := Fin.ext (by simp)
    rw [hk2]
    rcases Fin.exists_fin_two.mp ⟨p.1 ⟨k, h⟩, rfl⟩ with h0 | h1
    · rw [h0]; simp
    · rw [h1]; simp
  · rw [dif_neg (by omega), dif_neg h]
    simp

/-- The odd coordinates of an interleaved bit function are the right bits, as a cube point. -/
theorem oddPt_split {n L : ℕ} (p : (Fin n → Fin 2) × (Fin n → Fin 2)) :
    oddPt L (bitsF (2 * n) ((splitEquiv n).symm p))
      = (boolean_vector (finFunctionFinEquiv p.2 : ℕ) : Vector F L) := by
  ext k hk
  simp only [oddPt, boolean_vector, Vector.getElem_ofFn, bitsF]
  rw [bit_value_ffe]
  by_cases h : k < n
  · rw [dif_pos (by omega), dif_pos h]
    simp only [splitEquiv, Equiv.coe_fn_symm_mk, show ¬ ((2 * k + 1) % 2 = 0) by omega, if_false]
    have hk2 : (⟨(2 * k + 1) / 2, by omega⟩ : Fin n) = ⟨k, h⟩ := Fin.ext (by simp; omega)
    rw [hk2]
    rcases Fin.exists_fin_two.mp ⟨p.2 ⟨k, h⟩, rfl⟩ with h0 | h1
    · rw [h0]; simp
    · rw [h1]; simp
  · rw [dif_neg (by omega), dif_neg h]
    simp

/-- **The interleaved hypercube sum is the double sum over the two hands' cubes.** -/
theorem cube_sum_hands {n L : ℕ} (Φ : Vector F L → Vector F L → F) :
    ∑ j ∈ range (2 ^ (2 * n)),
        Φ (evenPt L (vf (boolean_vector j : Vector F (2 * n))))
          (oddPt L (vf (boolean_vector j : Vector F (2 * n))))
      = ∑ l ∈ range (2 ^ n), ∑ r ∈ range (2 ^ n),
          Φ (boolean_vector l : Vector F L) (boolean_vector r : Vector F L) := by
  rw [cube_sum_bits (2 * n) (fun y => Φ (evenPt L y) (oddPt L y))]
  rw [Fintype.sum_equiv (splitEquiv n) _
    (fun p => Φ (evenPt L (bitsF (2 * n) ((splitEquiv n).symm p)))
      (oddPt L (bitsF (2 * n) ((splitEquiv n).symm p)))) (fun s => by simp)]
  rw [Fintype.sum_prod_type]
  simp only [evenPt_split, oddPt_split]
  rw [← Fin.sum_univ_eq_sum_range (fun l => ∑ r ∈ range (2 ^ n),
    Φ (boolean_vector l : Vector F L) (boolean_vector r : Vector F L)) (2 ^ n)]
  refine Fintype.sum_equiv finFunctionFinEquiv _ _ fun s1 => ?_
  rw [← Fin.sum_univ_eq_sum_range (fun r =>
    Φ (boolean_vector (finFunctionFinEquiv s1 : ℕ) : Vector F L) (boolean_vector r : Vector F L)) (2 ^ n)]
  exact Fintype.sum_equiv finFunctionFinEquiv _ _ fun s2 => rfl


/-- `cube_sum_hands` at any dimension equal to `2n`. -/
theorem cube_sum_hands' {m n L : ℕ} (hm : m = 2 * n) (Φ : Vector F L → Vector F L → F) :
    ∑ j ∈ range (2 ^ m),
        Φ (evenPt L (vf (boolean_vector j : Vector F m))) (oddPt L (vf (boolean_vector j : Vector F m)))
      = ∑ l ∈ range (2 ^ n), ∑ r ∈ range (2 ^ n),
          Φ (boolean_vector l : Vector F L) (boolean_vector r : Vector F L) := by
  subst hm
  exact cube_sum_hands Φ

/-- A zero-variable hypercube sum is the value at the empty point. -/
theorem cube_sum_zero {m : ℕ} (hm : m = 0) (f : Vector F m → F) :
    ∑ j ∈ range (2 ^ m), f (boolean_vector j) = f (boolean_vector 0) := by
  subst hm
  simp

/-- `vf` of a vector with one coordinate set. -/
theorem vf_set {m : ℕ} (v : Vector F m) (j : ℕ) (hj : j < m) (X : F) :
    vf (v.set j X hj) = Function.update (vf v) j X := by
  funext i
  unfold vf
  by_cases hij : i = j
  · subst hij
    simp [hj]
  · rw [Function.update_of_ne hij]
    split_ifs with hi
    · rw [Vector.getElem_set, if_neg (Ne.symm hij)]
    · rfl

omit [Field F] in
/-- Setting an even coordinate moves the left point along its coordinate. -/
theorem evenPt_update_even {L : ℕ} (y : ℕ → F) {k : ℕ} (hk : k < L) (X : F) :
    evenPt L (Function.update y (2 * k) X) = (evenPt L y).set k X hk := by
  ext i hi
  simp only [evenPt, Vector.getElem_ofFn, Vector.getElem_set]
  by_cases h : k = i
  · subst h; simp
  · rw [if_neg h, Function.update_of_ne (by omega)]

omit [Field F] in
/-- Setting an even coordinate does not move the right point. -/
theorem oddPt_update_even {L : ℕ} (y : ℕ → F) (k : ℕ) (X : F) :
    oddPt L (Function.update y (2 * k) X) = oddPt L y := by
  ext i hi
  simp only [oddPt, Vector.getElem_ofFn]
  rw [Function.update_of_ne (by omega)]

omit [Field F] in
/-- Setting an odd coordinate moves the right point along its coordinate. -/
theorem oddPt_update_odd {L : ℕ} (y : ℕ → F) {k : ℕ} (hk : k < L) (X : F) :
    oddPt L (Function.update y (2 * k + 1) X) = (oddPt L y).set k X hk := by
  ext i hi
  simp only [oddPt, Vector.getElem_ofFn, Vector.getElem_set]
  by_cases h : k = i
  · subst h; simp
  · rw [if_neg h, Function.update_of_ne (by omega)]

omit [Field F] in
/-- Setting an odd coordinate does not move the left point. -/
theorem evenPt_update_odd {L : ℕ} (y : ℕ → F) (k : ℕ) (X : F) :
    evenPt L (Function.update y (2 * k + 1) X) = evenPt L y := by
  ext i hi
  simp only [evenPt, Vector.getElem_ofFn]
  rw [Function.update_of_ne (by omega)]

end Points

/-! ## 2. The width profile -/

section Profile

variable [DecidableEq F]

/-- **Layer `ly`'s own wire width**: `logv` at the output layer, and the hand width of the layer above
below it. -/
def ow (logv : ℕ) (lw : ℕ → ℕ) : ℕ → ℕ
  | 0 => logv
  | ly + 1 => lw ly

/--
**The circuit fits the width profile**, in a container of dimension `L`: it has a layer; the output
width and every hand width fit the container; the inputs fit the last layer's hand cube; and every
stored term of layer `ly` has its output corner in layer `ly`'s own cube and its hand corners in the
hand cube.  Decidable (`instDecidableWellFormedP`).
-/
def WellFormedP (c : QuadCircuit F) (logv : ℕ) (lw : ℕ → ℕ) (L : ℕ) : Prop :=
  0 < c.nl ∧ logv ≤ L ∧ (∀ ly < c.nl, lw ly ≤ L) ∧ c.ninp ≤ 2 ^ lw (c.nl - 1) ∧
    ∀ ly < c.nl, ∀ t ∈ c.gates ly, t.g < 2 ^ ow logv lw ly ∧ t.h0 < 2 ^ lw ly ∧ t.h1 < 2 ^ lw ly

instance instDecidableWellFormedP (c : QuadCircuit F) (logv : ℕ) (lw : ℕ → ℕ) (L : ℕ) :
    Decidable (WellFormedP c logv lw L) := by
  unfold WellFormedP; infer_instance

variable {c : QuadCircuit F} {logv L : ℕ} {lw : ℕ → ℕ}

omit [Field F] [DecidableEq F] in
theorem WellFormedP.ow_le (hwf : WellFormedP c logv lw L) {ly : ℕ} (hly : ly ≤ c.nl) :
    ow logv lw ly ≤ L := by
  cases ly with
  | zero => exact hwf.2.1
  | succ k => exact hwf.2.2.1 k (by omega)

omit [Field F] [DecidableEq F] in
theorem WellFormedP.pow_ow_le (hwf : WellFormedP c logv lw L) {ly : ℕ} (hly : ly ≤ c.nl) :
    2 ^ ow logv lw ly ≤ 2 ^ L :=
  Nat.pow_le_pow_right (by norm_num) (hwf.ow_le hly)

omit [Field F] [DecidableEq F] in
theorem WellFormedP.pow_lw_le (hwf : WellFormedP c logv lw L) {ly : ℕ} (hly : ly < c.nl) :
    2 ^ lw ly ≤ 2 ^ L :=
  Nat.pow_le_pow_right (by norm_num) (hwf.2.2.1 ly hly)

omit [Field F] [DecidableEq F] in
/-- The input layer's width is the last layer's hand width. -/
theorem WellFormedP.ow_nl (hwf : WellFormedP c logv lw L) : ow logv lw c.nl = lw (c.nl - 1) := by
  obtain ⟨k, hk⟩ : ∃ k, c.nl = k + 1 := ⟨c.nl - 1, by have := hwf.1; omega⟩
  rw [hk]
  rfl

omit [Field F] [DecidableEq F] in
/-- The terms of layer `ly` read the cube of layer `ly + 1`'s width. -/
theorem WellFormedP.lw_eq_ow (ly : ℕ) : lw ly = ow logv lw (ly + 1) := rfl

/-- **Every layer's wires, the inputs included, live on its own cube.** -/
theorem wires_suppP (hwf : WellFormedP c logv lw L) (pub priv : Fin c.ninp → F) (betas : ℕ → F)
    {ly : ℕ} (hly : ly ≤ c.nl) {j : ℕ} (hj : 2 ^ ow logv lw ly ≤ j) :
    c.wires pub priv betas ly j = 0 := by
  rcases Nat.lt_or_ge ly c.nl with hlt | hge
  · rw [QuadCircuit.wires_lt hlt]
    exact QuadCircuit.evalGates_supp _ (fun t ht => (hwf.2.2.2.2 ly hlt t ht).1) _ _ hj
  · have hle : ly = c.nl := le_antisymm hly hge
    subst hle
    rw [QuadCircuit.wires_ge le_rfl]
    rw [hwf.ow_nl] at hj
    exact QuadCircuit.inputVec_supp pub priv j (le_trans hwf.2.2.2.1 hj)

/-- **Every layer's assertion vector lives on its own cube.** -/
theorem assertVec_suppP (hwf : WellFormedP c logv lw L) (pub priv : Fin c.ninp → F)
    {ly : ℕ} (hly : ly < c.nl) {j : ℕ} (hj : 2 ^ ow logv lw ly ≤ j) :
    c.assertVec pub priv ly j = 0 := by
  unfold QuadCircuit.assertVec QuadCircuit.assertSum
  refine Finset.sum_eq_zero (fun i _ => ?_)
  rw [if_neg]
  have := (hwf.2.2.2.2 ly hly _ (List.get_mem _ i)).1
  omega

/-! ### The layer polynomial, interleaved -/

/-- The number of sumcheck variables of layer `ly`: `2 · lw ly` on the circuit, none below it. -/
def dimP (c : QuadCircuit F) (lw : ℕ → ℕ) (ly : ℕ) : ℕ := if ly < c.nl then 2 * lw ly else 0

/-- **Layer `ly`'s values**: the MLE of its wires at a schedule, at a container point. -/
noncomputable def VP (c : QuadCircuit F) (pub priv : Fin c.ninp → F) (L ly : ℕ) (X : ℕ → F)
    (g : Vector F L) : F :=
  mle L (c.wires pub priv X ly) g

/-- **Layer `ly`'s sumcheck polynomial, at a coordinate function.**  On the circuit: the verifier's
`bind_gh_all` at the layer's `beta = X ly` and fold `a`, at the two hand points, times the next
layer's values there.  Below the circuit: the constant `alpha`-combination of the layer's values. -/
noncomputable def lpolyFn (c : QuadCircuit F) (pub priv : Fin c.ninp → F) (L ly : ℕ)
    (st : LayerState L 0 F) (X : ℕ → F) (a : F) (y : ℕ → F) : F :=
  if ly < c.nl then
    bindGhAll (c.gates ly) (X ly) a st.g0 st.g1 (evenPt L y) (oddPt L y)
      * VP c pub priv L (ly + 1) X (evenPt L y) * VP c pub priv L (ly + 1) X (oddPt L y)
  else VP c pub priv L ly X st.g0 + a * VP c pub priv L ly X st.g1

/-- **Layer `ly`'s sumcheck polynomial** in its `dimP` variables. -/
noncomputable def lpoly (c : QuadCircuit F) (pub priv : Fin c.ninp → F) (L : ℕ) (lw : ℕ → ℕ)
    (ly : ℕ) (st : LayerState L 0 F) (X : ℕ → F) (a : F) : Vector F (dimP c lw ly) → F :=
  fun x => lpolyFn c pub priv L ly st X a (vf x)

/--
**The layer's gate sum over the two hand cubes.**  For a layer's terms with output corners in the
container's cube and hand corners in the `n`-cube, the double sum of `bind_gh_all · W(l) · W(r)` over
the hand cubes is the `alpha`-combination of the MLE of the layer's gate evaluation at its two points.
-/
theorem layer_sum_gates {n : ℕ} (hn : 2 ^ n ≤ 2 ^ L) (gates : List (GateTerm F)) (b a : F)
    (g0 g1 : Vector F L) (W : ℕ → F)
    (hg : ∀ t ∈ gates, t.g < 2 ^ L ∧ t.h0 < 2 ^ n ∧ t.h1 < 2 ^ n) :
    ∑ l ∈ range (2 ^ n), ∑ r ∈ range (2 ^ n),
        bindGhAll gates b a g0 g1 (boolean_vector l : Vector F L) (boolean_vector r : Vector F L)
          * mle L W (boolean_vector l) * mle L W (boolean_vector r)
      = mle L (evalGates gates b W) g0 + a * mle L (evalGates gates b W) g1 := by
  set T : Fin gates.length → F := fun k => prepV (gates.get k).v b
    * (eq_mle_basis (gates.get k).g g0 + a * eq_mle_basis (gates.get k).g g1) with hT
  have key : ∀ l ∈ range (2 ^ n), ∀ r ∈ range (2 ^ n),
      bindGhAll gates b a g0 g1 (boolean_vector l : Vector F L) (boolean_vector r : Vector F L)
          * mle L W (boolean_vector l) * mle L W (boolean_vector r)
        = ∑ k : Fin gates.length, if (gates.get k).h0 = l then
            (if (gates.get k).h1 = r then T k * W l * W r else 0) else 0 := by
    intro l hl r hr
    have hl' : l < 2 ^ L := lt_of_lt_of_le (mem_range.mp hl) hn
    have hr' : r < 2 ^ L := lt_of_lt_of_le (mem_range.mp hr) hn
    rw [mle_bv W hl', mle_bv W hr']
    unfold bindGhAll
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hk := hg _ (List.get_mem gates k)
    rw [eq_bv_of_lt (lt_of_lt_of_le hk.2.1 hn) hl', eq_bv_of_lt (lt_of_lt_of_le hk.2.2 hn) hr']
    simp only [hT]
    split_ifs <;> ring
  rw [Finset.sum_congr rfl fun l hl => Finset.sum_congr rfl fun r hr => key l hl r hr]
  have hinner : ∀ l ∈ range (2 ^ n),
      ∑ r ∈ range (2 ^ n), ∑ k : Fin gates.length, (if (gates.get k).h0 = l then
          (if (gates.get k).h1 = r then T k * W l * W r else 0) else 0)
        = ∑ k : Fin gates.length, if (gates.get k).h0 = l then T k * W l * W (gates.get k).h1
            else 0 := by
    intro l _
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    have hk := hg _ (List.get_mem gates k)
    by_cases h0 : (gates.get k).h0 = l
    · simp only [if_pos h0]
      rw [Finset.sum_ite_eq (range (2 ^ n)) (gates.get k).h1, if_pos (mem_range.mpr hk.2.2)]
    · simp only [if_neg h0, Finset.sum_const_zero]
  rw [Finset.sum_congr rfl hinner, Finset.sum_comm]
  have houter : ∀ k : Fin gates.length,
      ∑ l ∈ range (2 ^ n), (if (gates.get k).h0 = l then T k * W l * W (gates.get k).h1 else 0)
        = T k * W (gates.get k).h0 * W (gates.get k).h1 := by
    intro k
    have hk := hg _ (List.get_mem gates k)
    rw [Finset.sum_ite_eq (range (2 ^ n)) (gates.get k).h0, if_pos (mem_range.mpr hk.2.1)]
  rw [Finset.sum_congr rfl fun k _ => houter k]
  have hgL : ∀ t ∈ gates, t.g < 2 ^ L := fun t ht => (hg t ht).1
  rw [mle_evalGates gates b W hgL, mle_evalGates gates b W hgL, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [hT]
  ring

/-- **The layer relation at the profile**: the hypercube sum of layer `ly`'s polynomial is the
`alpha`-combination of the layer's values at its two points (on the circuit: `cube_sum_hands'` and
`layer_sum_gates`; below it: the zero-variable constant). -/
theorem lpoly_rel (hwf : WellFormedP c logv lw L) (pub priv : Fin c.ninp → F) (ly : ℕ)
    (st : LayerState L 0 F) (X : ℕ → F) (a : F) :
    ∑ j ∈ range (2 ^ dimP c lw ly), lpoly c pub priv L lw ly st X a (boolean_vector j)
      = VP c pub priv L ly X st.g0 + a * VP c pub priv L ly X st.g1 := by
  by_cases hly : ly < c.nl
  · have hd : dimP c lw ly = 2 * lw ly := if_pos hly
    have hfn : ∀ y, lpolyFn c pub priv L ly st X a y
        = bindGhAll (c.gates ly) (X ly) a st.g0 st.g1 (evenPt L y) (oddPt L y)
          * VP c pub priv L (ly + 1) X (evenPt L y) * VP c pub priv L (ly + 1) X (oddPt L y) :=
      fun y => if_pos hly
    unfold lpoly
    simp only [hfn]
    have h := cube_sum_hands' (F := F) (L := L) hd (fun H0 H1 =>
      bindGhAll (c.gates ly) (X ly) a st.g0 st.g1 H0 H1
        * VP c pub priv L (ly + 1) X H0 * VP c pub priv L (ly + 1) X H1)
    rw [h]
    unfold VP
    rw [layer_sum_gates (hwf.pow_lw_le hly) (c.gates ly) (X ly) a st.g0 st.g1
      (c.wires pub priv X (ly + 1)) (fun t ht => ⟨lt_of_lt_of_le (hwf.2.2.2.2 ly hly t ht).1
        (hwf.pow_ow_le hly.le), (hwf.2.2.2.2 ly hly t ht).2⟩),
      QuadCircuit.wires_lt hly]
  · have hd0 : dimP c lw ly = 0 := if_neg hly
    rw [cube_sum_zero hd0]
    show lpolyFn c pub priv L ly st X a _ = _
    rw [lpolyFn, if_neg hly]

omit [DecidableEq F] in
/-- At the full bound the partial sum is the polynomial at the challenges. -/
theorem partialSum_full {n : ℕ} (f : Vector F n → F) (bnd : List F) (h : bnd.length = n) :
    partialSum f bnd = f (chalVec bnd n) := by
  rw [partialSum_ge f bnd (by omega), h, Finset.Ico_self, Finset.prod_empty, mul_one]

/-- **The layer identity at the full bound**: at `2 · lw ly` bound challenges the honest claim is
`bind_gh_all` at the two hand points the bound determines, times the next layer's values there. -/
theorem lpoly_final (pub priv : Fin c.ninp → F) {ly : ℕ} (hly : ly < c.nl)
    (st : LayerState L 0 F) (X : ℕ → F) (a : F) (bnd : List F) (hlen : bnd.length = 2 * lw ly) :
    partialSum (lpoly c pub priv L lw ly st X a) bnd
      = bindGhAll (c.gates ly) (X ly) a st.g0 st.g1 (evenPt L (ptOf bnd)) (oddPt L (ptOf bnd))
        * VP c pub priv L (ly + 1) X (evenPt L (ptOf bnd))
        * VP c pub priv L (ly + 1) X (oddPt L (ptOf bnd)) := by
  have hd : bnd.length = dimP c lw ly := by rw [hlen]; exact (if_pos hly).symm
  rw [partialSum_full _ bnd hd]
  show lpolyFn c pub priv L ly st X a (vf (chalVec bnd (dimP c lw ly))) = _
  rw [vf_chalVec bnd hd, lpolyFn, if_pos hly]

/-- `bind_gh_all` is multilinear in the left hand's point. -/
theorem bindGhAll_ml_l (gates : List (GateTerm F)) (b a : F) (g0 g1 H1 : Vector F L) :
    IsMultilinear (fun H0 => bindGhAll gates b a g0 g1 H0 H1) := by
  have h : (fun H0 => bindGhAll gates b a g0 g1 H0 H1)
      = fun H0 => ∑ k : Fin gates.length, eq_mle_basis (gates.get k).h0 H0
          * (prepV (gates.get k).v b
            * (eq_mle_basis (gates.get k).g g0 + a * eq_mle_basis (gates.get k).g g1)
            * eq_mle_basis (gates.get k).h1 H1) := by
    funext H0
    unfold bindGhAll
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [h]
  exact IsMultilinear.sum _ _ fun k => (eq_mle_basis_multilinear _).mul_const _

/-- `bind_gh_all` is multilinear in the right hand's point. -/
theorem bindGhAll_ml_r (gates : List (GateTerm F)) (b a : F) (g0 g1 H0 : Vector F L) :
    IsMultilinear (fun H1 => bindGhAll gates b a g0 g1 H0 H1) := by
  have h : (fun H1 => bindGhAll gates b a g0 g1 H0 H1)
      = fun H1 => ∑ k : Fin gates.length, eq_mle_basis (gates.get k).h1 H1
          * (prepV (gates.get k).v b
            * (eq_mle_basis (gates.get k).g g0 + a * eq_mle_basis (gates.get k).g g1)
            * eq_mle_basis (gates.get k).h0 H0) := by
    funext H1
    unfold bindGhAll
    exact Finset.sum_congr rfl fun k _ => by ring
  rw [h]
  exact IsMultilinear.sum _ _ fun k => (eq_mle_basis_multilinear _).mul_const _

/-- **Every round of the layer polynomial is quadratic**: a round binds one coordinate of one hand,
which enters `bind_gh_all` and one of the two values, each affinely. -/
theorem lpoly_quadratic (hwf : WellFormedP c logv lw L) (pub priv : Fin c.ninp → F) (ly : ℕ)
    (st : LayerState L 0 F) (X : ℕ → F) (a : F) :
    IsQuadratic (lpoly c pub priv L lw ly st X a) := by
  intro j hj v
  by_cases hly : ly < c.nl
  · have hd : dimP c lw ly = 2 * lw ly := if_pos hly
    have hjw : j < 2 * lw ly := hd ▸ hj
    have hlwL := hwf.2.2.1 ly hly
    set y := vf v with hy
    have hset : ∀ Y : F, lpoly c pub priv L lw ly st X a (v.set j Y hj)
        = bindGhAll (c.gates ly) (X ly) a st.g0 st.g1 (evenPt L (Function.update y j Y))
            (oddPt L (Function.update y j Y))
          * VP c pub priv L (ly + 1) X (evenPt L (Function.update y j Y))
          * VP c pub priv L (ly + 1) X (oddPt L (Function.update y j Y)) := by
      intro Y
      show lpolyFn c pub priv L ly st X a (vf (v.set j Y hj)) = _
      rw [vf_set, lpolyFn, if_pos hly]
    rcases Nat.even_or_odd' j with ⟨k, rfl | rfl⟩
    · have hk : k < L := by omega
      obtain ⟨a1, b1, e1⟩ := bindGhAll_ml_l (c.gates ly) (X ly) a st.g0 st.g1 (oddPt L y)
        (evenPt L y) k hk
      obtain ⟨a2, b2, e2⟩ := QuadCircuit.mle_ml (n := L) (c.wires pub priv X (ly + 1)) (evenPt L y) k hk
      set K := VP c pub priv L (ly + 1) X (oddPt L y)
      refine ⟨a1 * a2 * K, (a1 * b2 + b1 * a2) * K, b1 * b2 * K, fun Y => ?_⟩
      rw [hset, evenPt_update_even y hk, oddPt_update_even]
      have e1' := e1 Y
      have e2' : VP c pub priv L (ly + 1) X ((evenPt L y).set k Y hk) = a2 + b2 * Y := e2 Y
      simp only at e1'
      rw [e1', e2']
      ring
    · have hk : k < L := by omega
      obtain ⟨a1, b1, e1⟩ := bindGhAll_ml_r (c.gates ly) (X ly) a st.g0 st.g1 (evenPt L y)
        (oddPt L y) k hk
      obtain ⟨a2, b2, e2⟩ := QuadCircuit.mle_ml (n := L) (c.wires pub priv X (ly + 1)) (oddPt L y) k hk
      set K := VP c pub priv L (ly + 1) X (evenPt L y)
      refine ⟨a1 * a2 * K, (a1 * b2 + b1 * a2) * K, b1 * b2 * K, fun Y => ?_⟩
      rw [hset, oddPt_update_odd y hk, evenPt_update_odd]
      have e1' := e1 Y
      have e2' : VP c pub priv L (ly + 1) X ((oddPt L y).set k Y hk) = a2 + b2 * Y := e2 Y
      simp only at e1'
      rw [e1', e2']
      ring
  · exfalso
    have : dimP c lw ly = 0 := if_neg hly
    omega

/-- **A layer's values are affine in its own `beta`.** -/
theorem VP_affine (pub priv : Fin c.ninp → F) (ly : ℕ) (b : F) (g : Vector F L) :
    VP c pub priv L ly (sched ly b) g = VP c pub priv L ly (sched ly 0) g
      + b * (VP c pub priv L ly (sched ly 1) g - VP c pub priv L ly (sched ly 0) g) := by
  unfold VP mle
  rw [← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [sched]
  rw [QuadCircuit.wires_affine_beta pub priv (fun _ => 0) ly b j]
  ring

/-- The next layer read at the current layer's schedule is the next layer at `beta = 0`. -/
theorem VP_next_sched (pub priv : Fin c.ninp → F) (ly : ℕ) (b : F) (g : Vector F L) :
    VP c pub priv L (ly + 1) (sched ly b) g = VP c pub priv L (ly + 1) (sched (ly + 1) 0) g := by
  unfold VP
  rw [QuadCircuit.wires_local pub priv _ (ly + 1) rfl (sched ly b) (sched (ly + 1) 0) fun i hi => by
    simp only [sched]
    rw [Function.update_of_ne (by omega)]
    by_cases h : i = ly + 1
    · subst h; simp
    · rw [Function.update_of_ne h]]

/-- **Under `DeadEnd`, a gate layer's values at its own `beta = b`** are its `beta`-free values plus
`b` times the MLE of its assertion vector. -/
theorem VP_decomp (hde : c.DeadEnd) (pub priv : Fin c.ninp → F) {ly : ℕ} (hly : ly < c.nl) (b : F)
    (g : Vector F L) :
    VP c pub priv L ly (sched ly b) g
      = VP c pub priv L ly (fun _ => 0) g + b * mle L (c.assertVec pub priv ly) g := by
  unfold VP mle
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [QuadCircuit.wires_decomp hde pub priv _ hly j, QuadCircuit.wires_decomp hde pub priv _ hly j]
  simp only [sched, Function.update_self]
  ring

omit [DecidableEq F] in
/-- **The input row's linear form, split as the verifier folds it**, is the `alpha`-combination of
the input layer's values at the two points (`input_constraint`, `zk_common.h:L406-L418`). -/
theorem input_row_split (hle : c.ninp ≤ 2 ^ L) (pub priv : Fin c.ninp → F) (E O : Vector F L)
    (a : F) :
    (∑ i ∈ univ \ privIdx c.ninp c.npub, (eq_mle_basis i.val E + a * eq_mle_basis i.val O) * pub i)
      + ∑ i ∈ privIdx c.ninp c.npub, (eq_mle_basis i.val E + a * eq_mle_basis i.val O) * priv i
      = mle L (c.inputVec pub priv) E + a * mle L (c.inputVec pub priv) O := by
  rw [QuadCircuit.mle_inputVec hle, QuadCircuit.mle_inputVec hle, Finset.mul_sum,
    ← Finset.sum_add_distrib, ← Finset.sum_sdiff (Finset.subset_univ (privIdx c.ninp c.npub))]
  congr 1
  · refine Finset.sum_congr rfl (fun i hi => ?_)
    simp only [privIdx, Finset.mem_sdiff, Finset.mem_univ, Finset.mem_filter, true_and] at hi
    rw [wCol, if_pos (show i.val < c.npub by omega)]
    ring
  · refine Finset.sum_congr rfl (fun i hi => ?_)
    simp only [privIdx, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    rw [wCol, if_neg (show ¬ i.val < c.npub by omega)]
    ring

end Profile

/-! ## 3. The code, the pending predicate and the boundary -/

section Boundary

variable [DecidableEq F] [Fintype F]
variable {c : QuadCircuit F} {logv L : ℕ} {lw : ℕ → ℕ}

/--
**The verifier's code agrees with the construction at the profile.**  The next state's points are
the bound list's even and odd coordinates (the deployed interleaving), padded; a layer's coefficient
`EQQ` is `bind_gh_all` of the layer's terms at its own `beta` and those points (on the circuit's
layers only); the input row is the `alpha_in`-combination of the two points' `EQ` vectors, the
public part folded into the constant.
-/
structure CodeAgreesP {C X Q Msg Gpt : Type} {M : ℕ} (c : QuadCircuit F) (pub : Fin c.ninp → F)
    (L : ℕ) (V : ZkCode C F X Q Msg Gpt M c.ninp L 0) : Prop where
  hst : ∀ bnd wc0 wc1, (V.stNext bnd wc0 wc1).g0 = evenPt L (ptOf bnd)
    ∧ (V.stNext bnd wc0 wc1).g1 = oddPt L (ptOf bnd)
  heqq : ∀ ly < c.nl, ∀ st b a bnd, V.eqqOf ly st b a bnd
    = bindGhAll (c.gates ly) b a st.g0 st.g1 (evenPt L (ptOf bnd)) (oddPt L (ptOf bnd))
  hnpub : V.npub = c.npub
  hinC : ∀ bnd a (i : Fin c.ninp), V.inCoeffs bnd a i
    = eq_mle_basis i.val (evenPt L (ptOf bnd)) + a * eq_mle_basis i.val (oddPt L (ptOf bnd))
  hpubB : ∀ bnd a, V.pubBinding bnd a
    = ∑ i ∈ univ \ privIdx c.ninp c.npub,
        (eq_mle_basis i.val (evenPt L (ptOf bnd)) + a * eq_mle_basis i.val (oddPt L (ptOf bnd)))
          * pub i

/-- **The construction's honest values at the profile**, as a `ZkHonest`: the partial hypercube sums
of `lpoly` at the schedule `sched ly b`; the pending predicate is a parameter. -/
noncomputable def zkHonestP [SumcheckInterp F] (hwf : WellFormedP c logv lw L)
    (pub : Fin c.ninp → F) {Lift : Type} (wOf : Lift → Fin c.ninp → F)
    (Pend : Lift → ℕ → List F → Prop) : ZkHonest F Lift L 0 where
  sum ℓ ly st b a bnd := partialSum (lpoly c pub (wOf ℓ) L lw ly st (sched ly b) a) bnd
  poly ℓ ly st b a bnd := partialPoly (lpoly c pub (wOf ℓ) L lw ly st (sched ly b) a) bnd
  deg_le ℓ ly st _ a bnd := partialPoly_deg _ (lpoly_quadratic hwf pub (wOf ℓ) ly st _ a) bnd
  sum_eq _ _ _ _ _ bnd := partialPoly_sum _ bnd
  next_eq _ _ _ _ _ bnd r := partialPoly_next _ bnd r
  Pend := Pend

/-- **The construction's honest pair** at a layer's two points, at the layer's `beta = b`. -/
noncomputable def zkWP (pub : Fin c.ninp → F) {Lift : Type} (wOf : Lift → Fin c.ninp → F)
    (ℓ : Lift) (ly : ℕ) (st : LayerState L 0 F) (b : F) : F × F :=
  (VP c pub (wOf ℓ) L ly (sched ly b) st.g0, VP c pub (wOf ℓ) L ly (sched ly b) st.g1)

/-- Layer `j`'s assertion MLE is non-zero at the left or the right point of `y`, cut at the full
bound of the layer above (`2 · n` coordinates). -/
def AssertsAtP (c : QuadCircuit F) (pub priv : Fin c.ninp → F) (L n j : ℕ) (y : ℕ → F) : Prop :=
  mle L (c.assertVec pub priv j) (evenPt L (cut (2 * n) y)) ≠ 0
    ∨ mle L (c.assertVec pub priv j) (oddPt L (cut (2 * n) y)) ≠ 0

/-- **The construction's pending predicate at the profile**: layer `ly + 1` is a gate layer and
some completion of layer `ly`'s bound prefix has a non-zero assertion MLE of layer `ly + 1` at one of
its two (interleaved) hand points. -/
def cPendP (c : QuadCircuit F) (pub : Fin c.ninp → F) (L : ℕ) (lw : ℕ → ℕ) {Lift : Type}
    (wOf : Lift → Fin c.ninp → F) : Lift → ℕ → List F → Prop :=
  fun ℓ ly bnd => ly + 1 < c.nl ∧
    ∃ ext : List F, AssertsAtP c pub (wOf ℓ) L (lw ly) (ly + 1) (ptOf (bnd ++ ext))

omit [DecidableEq F] [Fintype F] in
theorem cut_update_lt (y : ℕ → F) {m i : ℕ} (hi : i < m) (r : F) :
    cut m (Function.update y i r) = Function.update (cut m y) i r := by
  funext k
  unfold cut
  by_cases hk : k = i
  · subst hk; simp [hi]
  · rw [Function.update_of_ne hk, Function.update_of_ne hk]

omit [DecidableEq F] [Fintype F] in
theorem cut_update_ge (y : ℕ → F) {m i : ℕ} (hi : m ≤ i) (r : F) :
    cut m (Function.update y i r) = cut m y := by
  funext k
  unfold cut
  split_ifs with hk
  · rw [Function.update_of_ne (by omega)]
  · rfl

omit [Field F] [DecidableEq F] [Fintype F] in
/-- A container point read as a multilinear function of its coordinates. -/
theorem evenPt_ofFn (L : ℕ) (y : ℕ → F) :
    evenPt L y = Vector.ofFn (fun k : Fin L => y (2 * k.val)) := rfl

omit [Fintype F] in
/-- **`cPendP` sees the assertion vectors** with nothing bound: a non-zero entry `i` of layer
`j + 1`'s assertion vector is that vector's MLE at the cube point `i`, which a completion reaches
through the left hand. -/
theorem cPendP_sees (hwf : WellFormedP c logv lw L) (pub : Fin c.ninp → F) {Lift : Type}
    (wOf : Lift → Fin c.ninp → F) : SeesAsserts pub wOf (cPendP c pub L lw wOf) := by
  intro ℓ j hj ⟨i, hi⟩
  have hlt : i < 2 ^ lw j := by
    by_contra hge
    exact hi (assertVec_suppP hwf pub (wOf ℓ) hj (by rw [← WellFormedP.lw_eq_ow]; omega))
  have hjL : lw j ≤ L := hwf.2.2.1 j (by omega)
  refine ⟨hj, List.ofFn (fun m : Fin (2 * lw j) =>
    if m.val % 2 = 0 ∧ bit_value i (m.val / 2) = 1 then (1 : F) else 0), Or.inl ?_⟩
  have hE : evenPt L (cut (2 * lw j) (ptOf ([] ++ List.ofFn (fun m : Fin (2 * lw j) =>
      if m.val % 2 = 0 ∧ bit_value i (m.val / 2) = 1 then (1 : F) else 0))))
      = (boolean_vector i : Vector F L) := by
    ext k hk
    simp only [evenPt, boolean_vector, Vector.getElem_ofFn, cut, List.nil_append, ptOf]
    by_cases hkw : k < lw j
    · rw [if_pos (by omega), List.getD_eq_getElem _ _ (by simp; omega)]
      simp only [List.getElem_ofFn]
      have h2 : 2 * k / 2 = k := by omega
      simp [h2]
    · rw [if_neg (by omega)]
      have hb : bit_value i k = 0 := by
        unfold bit_value
        rw [Nat.div_eq_of_lt (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num) (by omega)))]
      simp [hb]
  rw [hE, mle_bv _ (lt_of_lt_of_le hlt (Nat.pow_le_pow_right (by norm_num) hjL))]
  exact hi

open scoped Classical in
/-- **Binding a coordinate keeps `cPendP` but for one value** (`ZkBoundary.pend_round`): the bound
coordinate is a coordinate of one hand point, along which the assertion MLE is affine. -/
theorem cPendP_round (hwf : WellFormedP c logv lw L) (pub : Fin c.ninp → F) {Lift : Type}
    (wOf : Lift → Fin c.ninp → F) (ℓ : Lift) (ly : ℕ) (bnd : List F)
    (hp : cPendP c pub L lw wOf ℓ ly bnd) :
    (univ.filter fun r : F => ¬ cPendP c pub L lw wOf ℓ ly (bnd ++ [r])).card ≤ 1 := by
  obtain ⟨hly, ext, hb⟩ := hp
  refine Finset.card_le_one.mpr fun r1 h1 r2 h2 => ?_
  simp only [mem_filter, mem_univ, true_and, cPendP, not_and, not_exists] at h1 h2
  have h1' := h1 hly ext.tail
  have h2' := h2 hly ext.tail
  by_contra hne
  rw [ptOf_bind] at h1' h2'
  set y := ptOf (bnd ++ ext)
  set S := c.assertVec pub (wOf ℓ) (ly + 1)
  set n := lw ly
  have hnL : n ≤ L := hwf.2.2.1 ly (by omega)
  unfold AssertsAtP at h1' h2' hb
  push Not at h1' h2'
  by_cases hk : bnd.length < 2 * n
  · rw [cut_update_lt y hk] at h1' h2'
    set z := cut (2 * n) y
    rcases Nat.even_or_odd' bnd.length with ⟨k, hkk | hkk⟩
    · have hkL : k < L := by omega
      rw [hkk, evenPt_update_even z hkL, oddPt_update_even] at h1' h2'
      rw [evenPt_ofFn] at h1' h2'
      have hv : ∀ r, mle L S ((Vector.ofFn fun k' : Fin L => z (2 * k'.val)).set k r hkL)
          = mle L S (Vector.ofFn (Function.update (fun k' : Fin L => z (2 * k'.val)) ⟨k, hkL⟩ r)) :=
        fun r => by rw [ofFn_update]
      have hz := mlin_line_zero (fun v => mle L S (Vector.ofFn v)) (mle_mlin S)
        (fun k' : Fin L => z (2 * k'.val)) ⟨k, hkL⟩ hne ((hv r1).symm.trans h1'.1)
        ((hv r2).symm.trans h2'.1) (z (2 * k))
      have hfix : Function.update (fun k' : Fin L => z (2 * k'.val)) ⟨k, hkL⟩ (z (2 * k))
          = fun k' : Fin L => z (2 * k'.val) := by
        funext k'
        by_cases hk' : k' = ⟨k, hkL⟩
        · subst hk'; simp
        · rw [Function.update_of_ne hk']
      rw [hfix] at hz
      rcases hb with hb | hb
      · exact hb hz
      · exact hb h1'.2
    · have hkL : k < L := by omega
      rw [hkk, oddPt_update_odd z hkL, evenPt_update_odd] at h1' h2'
      have hodd : oddPt L z = Vector.ofFn (fun k' : Fin L => z (2 * k'.val + 1)) := rfl
      rw [hodd] at h1' h2'
      have hv : ∀ r, mle L S ((Vector.ofFn fun k' : Fin L => z (2 * k'.val + 1)).set k r hkL)
          = mle L S (Vector.ofFn
            (Function.update (fun k' : Fin L => z (2 * k'.val + 1)) ⟨k, hkL⟩ r)) :=
        fun r => by rw [ofFn_update]
      have hz := mlin_line_zero (fun v => mle L S (Vector.ofFn v)) (mle_mlin S)
        (fun k' : Fin L => z (2 * k'.val + 1)) ⟨k, hkL⟩ hne ((hv r1).symm.trans h1'.2)
        ((hv r2).symm.trans h2'.2) (z (2 * k + 1))
      have hfix : Function.update (fun k' : Fin L => z (2 * k'.val + 1)) ⟨k, hkL⟩ (z (2 * k + 1))
          = fun k' : Fin L => z (2 * k'.val + 1) := by
        funext k'
        by_cases hk' : k' = ⟨k, hkL⟩
        · subst hk'; simp
        · rw [Function.update_of_ne hk']
      rw [hfix] at hz
      rcases hb with hb | hb
      · exact hb h1'.1
      · exact hb (by rw [hodd]; exact hz)
  · rw [cut_update_ge y (by omega)] at h1'
    rcases hb with hb | hb
    · exact hb h1'.1
    · exact hb h1'.2

omit [Fintype F] in
/-- **`cPendP` at the full bound is the slope of the next layer's pair in its `beta`**
(`ZkBoundary.pend_close`), under `DeadEnd` (`VP_decomp`). -/
theorem cPendP_close {C X Q Msg Gpt : Type} {M : ℕ} (pub : Fin c.ninp → F) (hde : c.DeadEnd)
    {V : ZkCode C F X Q Msg Gpt M c.ninp L 0} (hV : CodeAgreesP c pub L V) {Lift : Type}
    (wOf : Lift → Fin c.ninp → F) (ℓ : Lift) (ly : ℕ) (bnd : List F) (wc0 wc1 : F)
    (hlen : bnd.length = 2 * lw ly) (hp : cPendP c pub L lw wOf ℓ ly bnd) :
    zkWP pub wOf ℓ (ly + 1) (V.stNext bnd wc0 wc1) 1
      ≠ zkWP pub wOf ℓ (ly + 1) (V.stNext bnd wc0 wc1) 0 := by
  obtain ⟨hly, ext, hb⟩ := hp
  unfold AssertsAtP at hb
  rw [cut_append_full bnd ext hlen] at hb
  intro heq
  have h1 := congrArg Prod.fst heq
  have h2 := congrArg Prod.snd heq
  simp only [zkWP, VP_decomp hde pub (wOf ℓ) hly, one_mul, zero_mul, add_zero,
    add_eq_left] at h1 h2
  rw [(hV.hst bnd wc0 wc1).1] at h1
  rw [(hV.hst bnd wc0 wc1).2] at h2
  rcases hb with hb | hb
  · exact hb h1
  · exact hb h2

/--
**The construction's `ZkBoundary` at the profile**, under `DeadEnd`, for a code that agrees with the
construction (`CodeAgreesP`) and candidates whose committed columns are their witnesses
(`AsgAgrees`).  The round count is `2 · lw ly` per layer — the row's `rounds` at `lw := logw`.
-/
noncomputable def zkBoundaryP [SumcheckInterp F] {C X Q Msg Gpt : Type} {M : ℕ}
    (hwf : WellFormedP c logv lw L) (pub : Fin c.ninp → F) (hde : c.DeadEnd)
    (V : ZkCode C F X Q Msg Gpt M c.ninp L 0) (hV : CodeAgreesP c pub L V) {Lift : Type}
    (wOf : Lift → Fin c.ninp → F) (asg : Lift → LigeroAssignment c.ninp M F)
    (hasg : AsgAgrees asg wOf) {nl : ℕ} (hnl : c.nl = nl) :
    ZkBoundary V (zkHonestP hwf pub wOf (cPendP c pub L lw wOf)) asg nl (fun ly => 2 * lw ly) where
  W := zkWP pub wOf
  rel ℓ ly st b a := by
    show partialSum _ [] = _
    rw [partialSum_nil, lpoly_rel hwf]
    rfl
  final ℓ ly st b a bnd wc0 wc1 hlen hly := by
    replace hly : ly < c.nl := by omega
    show partialSum _ bnd = _
    rw [lpoly_final pub (wOf ℓ) hly st _ a bnd hlen, hV.heqq ly hly]
    simp only [zkWP, (hV.hst bnd wc0 wc1).1, (hV.hst bnd wc0 wc1).2, sched, Function.update_self]
    rw [← VP_next_sched pub (wOf ℓ) ly b, ← VP_next_sched pub (wOf ℓ) ly b]
  W_affine ℓ ly st b :=
    ⟨VP_affine pub (wOf ℓ) ly b st.g0, VP_affine pub (wOf ℓ) ly b st.g1⟩
  pend_round ℓ ly bnd hp := by
    convert cPendP_round hwf pub wOf ℓ ly bnd hp
    rfl
  pend_close ℓ ly bnd wc0 wc1 hlen hp := cPendP_close pub hde hV wOf ℓ ly bnd wc0 wc1 hlen hp
  pend_last ℓ j bnd hj hp := by
    have := hp.1
    omega
  hin ℓ ly bnd wc0 wc1 a hlen hlast := by
    have hle : c.ninp ≤ 2 ^ L := le_trans hwf.2.2.2.1 (hwf.pow_lw_le (by have := hwf.1; omega))
    rw [hV.hpubB, hV.hnpub]
    simp only [hV.hinC]
    have hpriv : ∀ i ∈ privIdx c.ninp c.npub,
        (eq_mle_basis i.val (evenPt L (ptOf bnd)) + a * eq_mle_basis i.val (oddPt L (ptOf bnd)))
          * (asg ℓ).1 i
        = (eq_mle_basis i.val (evenPt L (ptOf bnd)) + a * eq_mle_basis i.val (oddPt L (ptOf bnd)))
          * wOf ℓ i := fun i hi => by rw [hasg ℓ i hi]
    rw [Finset.sum_congr rfl hpriv, input_row_split hle]
    simp only [zkWP, (hV.hst bnd wc0 wc1).1, (hV.hst bnd wc0 wc1).2, VP]
    rw [hlast, QuadCircuit.wires_ge (by omega)]

end Boundary

/-! ## 4. Layer 0: the output point -/

section Init

variable [DecidableEq F] [Fintype F]
variable {c : QuadCircuit F} {logv L : ℕ} {lw : ℕ → ℕ}

omit [DecidableEq F] [Fintype F] in
/-- Moving one coordinate of the output point moves the padded point along that coordinate. -/
theorem padG_update (hle : logv ≤ L) (G : Fin logv → F) (j : Fin logv) (X : F) :
    padG L (Function.update G j X) = (padG L G).set j.val X (by omega) := by
  ext k hk
  simp only [padG, Vector.getElem_ofFn, Vector.getElem_set]
  by_cases h : j.val = k
  · subst h
    simp
  · rw [if_neg h]
    split_ifs with hk'
    · rw [Function.update_of_ne]
      intro h'
      exact h (by rw [← h'])
    · rfl

omit [DecidableEq F] [Fintype F] in
/-- The output cube point `j < 2^logv`, padded, is the container's cube point `j`. -/
theorem padG_bits {j : ℕ} (hj : j < 2 ^ logv) :
    padG L (fun k : Fin logv => if bit_value j k.val = 1 then (1 : F) else 0)
      = (boolean_vector j : Vector F L) := by
  ext k hk
  simp only [padG, boolean_vector, Vector.getElem_ofFn]
  by_cases h : k < logv
  · rw [dif_pos h]
  · rw [dif_neg h]
    have hb : bit_value j k = 0 := by
      unfold bit_value
      rw [Nat.div_eq_of_lt (lt_of_lt_of_le hj (Nat.pow_le_pow_right (by norm_num) (by omega)))]
    simp [hb]

omit [Fintype F] in
/-- **The output extension is multilinear in the output point.** -/
theorem outExtP_mlin (hle : logv ≤ L) (pub priv : Fin c.ninp → F) (b : F) :
    MLin (fun G : Fin logv → F => VP c pub priv L 0 (sched 0 b) (padG L G)) := by
  intro v j
  obtain ⟨a', b', h⟩ := QuadCircuit.mle_ml (n := L) (c.wires pub priv (sched 0 b) 0) (padG L v)
    j.val (by omega)
  exact ⟨a', b', fun X => by
    show mle L _ (padG L (Function.update v j X)) = _
    rw [padG_update hle]
    exact h X⟩

omit [Fintype F] in
/--
**`hinit_of_output`'s `harith` at `Satisfied`, at the profile.**  An unsatisfied witness all of whose
intermediate assertion vectors vanish has a non-zero output or layer-0 assertion wire `j`
(`satisfied_iff_top`, under `Isolated`); `j` is in the output cube (`wires_suppP`,
`assertVec_suppP`), and the output extension at `G = j` is that wire at `beta₀ ∈ {0, 1}`
(`wires_decomp`, under `DeadEnd`).
-/
theorem outExtP_ne (hwf : WellFormedP c logv lw L) (pub : Fin c.ninp → F) (hiso : c.Isolated)
    (hde : c.DeadEnd) (priv : Fin c.ninp → F) (hns : ¬ c.Satisfied pub priv)
    (hint : ∀ ly, 0 < ly → ly < c.nl → ∀ j, c.assertVec pub priv ly j = 0) :
    ∃ (b : F) (G : Fin logv → F), VP c pub priv L 0 (sched 0 b) (padG L G) ≠ 0 := by
  have hnl := hwf.1
  have htop : ¬ c.TopSat pub priv := fun ht =>
    hns ((QuadCircuit.satisfied_iff_top hiso hnl pub priv).mpr ⟨ht, hint⟩)
  unfold QuadCircuit.TopSat at htop
  push Not at htop
  have hcube : ∀ (b : F) (j : ℕ), c.wires pub priv (sched 0 b) 0 j ≠ 0 →
      ∃ G : Fin logv → F, VP c pub priv L 0 (sched 0 b) (padG L G) ≠ 0 := by
    intro b j hw
    have hj : j < 2 ^ logv := by
      by_contra hge
      exact hw (wires_suppP hwf pub priv _ (Nat.zero_le _) (show 2 ^ logv ≤ j by omega))
    refine ⟨fun k => if bit_value j k.val = 1 then 1 else 0, ?_⟩
    unfold VP
    rw [padG_bits (L := L) hj,
      mle_bv _ (lt_of_lt_of_le hj (Nat.pow_le_pow_right (by norm_num) hwf.2.1))]
    exact hw
  have hdec : ∀ (b : F) (j : ℕ), c.wires pub priv (sched 0 b) 0 j
      = c.honest pub priv 0 j + b * c.assertVec pub priv 0 j := fun b j => by
    rw [QuadCircuit.wires_decomp hde pub priv _ hnl j]
    simp [sched]
  by_cases hout : ∃ j, c.honest pub priv 0 j ≠ 0
  · obtain ⟨j, hj⟩ := hout
    obtain ⟨G, hG⟩ := hcube 0 j (by rw [hdec, zero_mul, add_zero]; exact hj)
    exact ⟨0, G, hG⟩
  · push Not at hout
    obtain ⟨j, hj⟩ := htop hout
    obtain ⟨G, hG⟩ := hcube 1 j (by rw [hdec, hout j, zero_add, one_mul]; exact hj)
    exact ⟨1, G, hG⟩

/--
**`ZkFieldData.hinit` at the profile**, at `Sat := Satisfied`: for a code whose `begin_circuit`
state has both points at the padded output point, an unsatisfied candidate with nothing pending
vanishes on at most `(logv + 2)·|F|^(logv+1)` of the triples `(G, beta₀, alpha₀)`.
-/
theorem zk_hinitP [SumcheckInterp F] {C X Q Msg : Type} {M : ℕ}
    (hwf : WellFormedP c logv lw L) (pub : Fin c.ninp → F) (hiso : c.Isolated) (hde : c.DeadEnd)
    {Lift : Type} (wOf : Lift → Fin c.ninp → F)
    (V : ZkCode C F X Q Msg (Fin logv → F) M c.ninp L 0)
    (hst0 : ∀ G, (V.st0 G).g0 = padG L G ∧ (V.st0 G).g1 = padG L G) :
    ∀ ℓ : Lift, ¬ c.Satisfied pub (wOf ℓ) →
      (∀ j, ¬ (zkHonestP hwf pub wOf (cPendP c pub L lw wOf)).Pend ℓ j []) →
      (univ.filter fun p : (Fin logv → F) × F × F =>
        (zkHonestP hwf pub wOf (cPendP c pub L lw wOf)).sum ℓ 0 (V.st0 p.1) p.2.1 p.2.2 [] = 0).card
        ≤ (logv + 2) * Fintype.card F ^ (logv + 1) := by
  refine hinit_of_output (V := V) (fun ℓ b G => VP c pub (wOf ℓ) L 0 (sched 0 b) (padG L G))
    ?_ (fun ℓ b => outExtP_mlin hwf.2.1 pub (wOf ℓ) b)
    (fun ℓ b G => VP_affine pub (wOf ℓ) 0 b (padG L G)) ?_
  · intro ℓ G b a
    show partialSum _ [] = _
    rw [partialSum_nil, lpoly_rel hwf, (hst0 G).1, (hst0 G).2]
  · intro ℓ hns hnp
    refine outExtP_ne hwf pub hiso hde (wOf ℓ) hns fun ly hly hlt j => ?_
    by_contra hj
    obtain ⟨k, rfl⟩ : ∃ k, ly = k + 1 := ⟨ly - 1, by omega⟩
    exact hnp k (cPendP_sees hwf pub wOf ℓ k hlt ⟨j, hj⟩)

end Init

/-! ## 5. The field half's analysis data, at the profile -/

section FieldData

variable [DecidableEq F] [Fintype F]
variable {c : QuadCircuit F} {logv L : ℕ} {lw : ℕ → ℕ}

/--
**A `ZkFieldData` at the deployed width profile**, at `Sat ℓ := c.Satisfied pub (wOf ℓ)`: the
boundary is `zkBoundaryP` (round count `2 · lw ly` per layer), the layer-0 count is `zk_hinitP` at
`binit = (logv + 2)·|F|^(logv+1)`, and the decoders' balances are the only further inputs.  Under
`WellFormedP`, `Isolated`, `DeadEnd`, for a code that agrees with the construction (`CodeAgreesP`,
and `begin_circuit` puts both points at the padded output point) and candidates whose committed
columns are their witnesses (`AsgAgrees`).
-/
noncomputable def zkFieldDataP [SumcheckInterp F] {C X Q Msg : Type} [Fintype C] [DecidableEq X]
    [Fintype Q] [DecidableEq Q] {M : ℕ} (hwf : WellFormedP c logv lw L) (pub : Fin c.ninp → F)
    (hiso : c.Isolated) (hde : c.DeadEnd) (V : ZkCode C F X Q Msg (Fin logv → F) M c.ninp L 0)
    (hV : CodeAgreesP c pub L V) (hst0 : ∀ G, (V.st0 G).g0 = padG L G ∧ (V.st0 G).g1 = padG L G)
    {Lift : Type} (wOf : Lift → Fin c.ninp → F) (asg : Lift → LigeroAssignment c.ninp M F)
    (hasg : AsgAgrees asg wOf) (kinit kpair k kchal kq : ℕ)
    (hbalInit : ∀ y : (Fin logv → F) × F × F,
      (univ.filter fun c' : C => V.decodeInit c' = y).card ≤ kinit)
    (hbalPair : ∀ y : F × F, (univ.filter fun c' : C => V.decodePair c' = y).card ≤ kpair)
    (hbalF : ∀ y : F, (univ.filter fun c' : C => V.decodeF c' = y).card ≤ k)
    (hbalChal : ∀ y : X, (univ.filter fun c' : C => V.decodeChal c' = y).card ≤ kchal)
    (hbalQuery : ∀ y : Q, (univ.filter fun c' : C => V.decodeQuery c' = y).card ≤ kq)
    {nl : ℕ} (hnl : c.nl = nl) :
    ZkFieldData C F X Q Msg (Fin logv → F) Lift M c.ninp L 0 nl (fun ly => 2 * lw ly) V
      (zkHonestP hwf pub wOf (cPendP c pub L lw wOf)) asg (fun ℓ => c.Satisfied pub (wOf ℓ)) where
  B := zkBoundaryP hwf pub hde V hV wOf asg hasg hnl
  binit := (logv + 2) * Fintype.card F ^ (logv + 1)
  hinit := zk_hinitP hwf pub hiso hde wOf V hst0
  kinit := kinit
  kpair := kpair
  k := k
  kchal := kchal
  kq := kq
  hbalInit := hbalInit
  hbalPair := hbalPair
  hbalF := hbalF
  hbalChal := hbalChal
  hbalQuery := hbalQuery

/-- **`zkFieldDataP` is exact** when the decoders are exactly balanced: its layer-0 count is the
Schwartz–Zippel value the row's `zkBound` charges. -/
theorem zkFieldDataP_exactAt [SumcheckInterp F] {C X Q Msg : Type} [Fintype C] [DecidableEq X]
    [Fintype X] [Fintype Q] [DecidableEq Q] {M : ℕ} (hwf : WellFormedP c logv lw L)
    (pub : Fin c.ninp → F) (hiso : c.Isolated) (hde : c.DeadEnd)
    (V : ZkCode C F X Q Msg (Fin logv → F) M c.ninp L 0) (hV : CodeAgreesP c pub L V)
    (hst0 : ∀ G, (V.st0 G).g0 = padG L G ∧ (V.st0 G).g1 = padG L G)
    {Lift : Type} (wOf : Lift → Fin c.ninp → F) (asg : Lift → LigeroAssignment c.ninp M F)
    (hasg : AsgAgrees asg wOf) (kinit kpair k kchal kq : ℕ)
    (hbalInit : ∀ y : (Fin logv → F) × F × F,
      (univ.filter fun c' : C => V.decodeInit c' = y).card ≤ kinit)
    (hbalPair : ∀ y : F × F, (univ.filter fun c' : C => V.decodePair c' = y).card ≤ kpair)
    (hbalF : ∀ y : F, (univ.filter fun c' : C => V.decodeF c' = y).card ≤ k)
    (hbalChal : ∀ y : X, (univ.filter fun c' : C => V.decodeChal c' = y).card ≤ kchal)
    (hbalQuery : ∀ y : Q, (univ.filter fun c' : C => V.decodeQuery c' = y).card ≤ kq)
    {nl : ℕ} (hnl : c.nl = nl) (hkinit : kinit * Fintype.card F ^ (logv + 2) ≤ Fintype.card C)
    (hkpair : kpair * (Fintype.card F * Fintype.card F) ≤ Fintype.card C)
    (hk : k * Fintype.card F ≤ Fintype.card C) (hkchal : kchal * Fintype.card X ≤ Fintype.card C)
    (hkq : kq * Fintype.card Q ≤ Fintype.card C) :
    (zkFieldDataP hwf pub hiso hde V hV hst0 wOf asg hasg kinit kpair k kchal kq hbalInit hbalPair
      hbalF hbalChal hbalQuery hnl).ExactAt :=
  ⟨le_rfl, hkinit, hkpair, hk, hkchal, hkq⟩

end FieldData

end Lfzk.ZkArithProfile
