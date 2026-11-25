import LfzkV1.ZkSim
import LfzkV1.ConcreteCircuitBridge
import Mathlib.Algebra.MvPolynomial.SchwartzZippel

/-! Polynomial replay of the v1 rows at fixed messages and pad indices. -/

open BigOperators SumcheckV1 LfzkV1.Arith

set_option autoImplicit false
open MvPolynomial

namespace LfzkV1.ResidualReplay125

variable {σ : Type*} {F : Type} [Field F]

abbrev Poly (σ F : Type*) [Field F] := MvPolynomial σ F

theorem degree_add {p q : Poly σ F} {d : ℕ}
    (hp : p.totalDegree ≤ d) (hq : q.totalDegree ≤ d) :
    (p + q).totalDegree ≤ d :=
  (totalDegree_add p q).trans (max_le hp hq)

theorem degree_sub {p q : Poly σ F} {d : ℕ}
    (hp : p.totalDegree ≤ d) (hq : q.totalDegree ≤ d) :
    (p - q).totalDegree ≤ d :=
  (totalDegree_sub p q).trans (max_le hp hq)

theorem degree_mul {p q : Poly σ F} {d e : ℕ}
    (hp : p.totalDegree ≤ d) (hq : q.totalDegree ≤ e) :
    (p * q).totalDegree ≤ d + e :=
  (totalDegree_mul p q).trans (Nat.add_le_add hp hq)

theorem degree_const (a : F) (d : ℕ) : (C a : Poly σ F).totalDegree ≤ d := by
  simp

theorem degree_scale (a : F) {p : Poly σ F} {d : ℕ}
    (hp : p.totalDegree ≤ d) : (p * C a).totalDegree ≤ d := by
  simpa using degree_mul hp (degree_const (σ := σ) a 0)

theorem degree_const_mul (a : F) {p : Poly σ F} {d : ℕ}
    (hp : p.totalDegree ≤ d) : (C a * p).totalDegree ≤ d := by
  rw [mul_comm]
  exact degree_scale a hp

/-- A replay coordinate is either an observed scalar or one of the unseen scalars. -/
noncomputable def coordinate (c : F ⊕ σ) : Poly σ F := c.elim C X

theorem degree_coordinate (c : F ⊕ σ) : (coordinate c).totalDegree ≤ 1 := by
  cases c <;> simp [coordinate, totalDegree_X]

/-- Constant and pad coefficients of an actual constraint-builder expression. -/
structure Expression (σ F : Type*) [Field F] (M : ℕ) where
  known : Poly σ F
  pad : Fin M → Poly σ F

variable {M : ℕ}

noncomputable def Expression.eval (x : σ → F) (e : Expression σ F M) : _root_.Expression M F :=
  (MvPolynomial.eval x e.known, fun i => MvPolynomial.eval x (e.pad i))

def Expression.Bounded (e : Expression σ F M) (d : ℕ) : Prop :=
  e.known.totalDegree ≤ d ∧ ∀ i, (e.pad i).totalDegree ≤ d

noncomputable def Expression.zero : Expression σ F M := ⟨0, fun _ => 0⟩

@[simp] theorem Expression.eval_zero (x : σ → F) :
    (Expression.zero : Expression σ F M).eval x = _root_.Expression.zero M F := by
  simp [Expression.zero, Expression.eval, _root_.Expression.zero]

theorem Expression.zero_bounded (d : ℕ) : (Expression.zero : Expression σ F M).Bounded d := by
  simp [Expression.zero, Expression.Bounded]

noncomputable def Expression.first (a : Poly σ F) (m0 m1 : F) (p0 p1 : Fin M) :
    Expression σ F M where
  known := C m0 + a * C m1
  pad i := (if i = p0 then 1 else 0) + (if i = p1 then a else 0)

@[simp] theorem Expression.eval_first (x : σ → F) (a : Poly σ F) (m0 m1 : F)
    (p0 p1 : Fin M) :
    (Expression.first a m0 m1 p0 p1).eval x = builder_first (MvPolynomial.eval x a) m0 m1 p0 p1 := by
  change (_, _) = (_, _)
  congr 1
  · simp [Expression.first, _root_.Expression.axpy, _root_.Expression.zero]
  · funext i
    simp only [Expression.first, _root_.Expression.axpy, _root_.Expression.zero, map_add]
    split_ifs <;> simp

theorem Expression.first_bounded {a : Poly σ F} (ha : a.totalDegree ≤ 1)
    (m0 m1 : F) (p0 p1 : Fin M) : (Expression.first a m0 m1 p0 p1).Bounded 1 := by
  refine ⟨degree_add (degree_const m0 1) (degree_scale m1 ha), fun i => degree_add ?_ ?_⟩
  · split_ifs <;> simp
  · split_ifs <;> first | assumption | simp

structure Round (σ F : Type*) [Field F] (M : ℕ) where
  tr0 : F
  tr2 : F
  pp0 : Fin M
  pp2 : Fin M
  challenge : Poly σ F

noncomputable def Round.eval (x : σ → F) (r : Round σ F M) : RoundData M F :=
  ⟨r.tr0, r.tr2, r.pp0, r.pp2, MvPolynomial.eval x r.challenge⟩

section Interpolation

variable [SumcheckV1Interp F]

noncomputable def lag (r : Poly σ F) : Poly σ F × Poly σ F × Poly σ F :=
  ( (r - 1) * (r - C (pt2 : F)) * C (pt2 : F)⁻¹
  , r * (r - C (pt2 : F)) * C (1 - (pt2 : F))⁻¹
  , r * (r - 1) * C ((pt2 : F) * ((pt2 : F) - 1))⁻¹ )

theorem lag_bounded {r : Poly σ F} (hr : r.totalDegree ≤ 1) :
    (lag r).1.totalDegree ≤ 2 ∧ (lag r).2.1.totalDegree ≤ 2 ∧ (lag r).2.2.totalDegree ≤ 2 := by
  have h₁ : (r - 1).totalDegree ≤ 1 := degree_sub hr (by simp)
  have h₂ := degree_sub hr (degree_const (σ := σ) (pt2 : F) 1)
  exact ⟨degree_scale _ (degree_mul h₁ h₂), degree_scale _ (degree_mul hr h₂),
    degree_scale _ (degree_mul hr h₁)⟩

noncomputable def Expression.step (e : Expression σ F M) (r : Round σ F M) :
    Expression σ F M :=
  let (l0, l1, l2) := lag r.challenge
  ⟨(e.known - C r.tr0) * l1 + C r.tr0 * l0 + C r.tr2 * l2,
    fun i =>
      (e.pad i - (if i = r.pp0 then 1 else 0)) * l1
        + (if i = r.pp0 then l0 else 0) + (if i = r.pp2 then l2 else 0)⟩

@[simp] theorem Expression.eval_step (x : σ → F) (e : Expression σ F M) (r : Round σ F M) :
    (e.step r).eval x = builder_next (e.eval x) (r.eval x) := by
  change (_, _) = (_, _)
  congr 1
  · simp [Expression.step, Expression.eval, Round.eval, lag, lag_coeffs,
      _root_.Expression.axpy, _root_.Expression.axmy, _root_.Expression.scale]
    ring
  · funext i
    simp only [Expression.step, Expression.eval, Round.eval, lag, lag_coeffs,
      _root_.Expression.axpy, _root_.Expression.axmy, _root_.Expression.scale, map_add, map_sub,
      map_mul, eval_C]
    split_ifs <;> simp <;> ring

theorem Expression.step_bounded {e : Expression σ F M} {d : ℕ} (he : e.Bounded d)
    {r : Round σ F M} (hr : r.challenge.totalDegree ≤ 1) : (e.step r).Bounded (d + 2) := by
  obtain ⟨h0, h1, h2⟩ := lag_bounded hr
  have hd : 2 ≤ d + 2 := by omega
  have h₀ := h0.trans hd
  have h₂ := h2.trans hd
  refine ⟨degree_add (degree_add ?_ ((degree_const_mul _ h0).trans hd))
    ((degree_const_mul _ h2).trans hd), fun i => degree_add (degree_add ?_ ?_) ?_⟩
  · exact degree_mul (degree_sub he.1 (degree_const _ d)) h1
  · exact degree_mul (degree_sub (he.2 i) (by split_ifs <;> simp)) h1
  · split_ifs <;> first | assumption | simp
  · split_ifs <;> first | assumption | simp

noncomputable def Expression.run (e : Expression σ F M) : List (Round σ F M) → Expression σ F M
  | [] => e
  | r :: rs => (e.step r).run rs

@[simp] theorem Expression.eval_run (x : σ → F) (e : Expression σ F M)
    (rs : List (Round σ F M)) :
    (e.run rs).eval x = builder_run (e.eval x) (rs.map (Round.eval x)) := by
  induction rs generalizing e with
  | nil => rfl
  | cons r rs ih => rw [Expression.run, ih, eval_step, List.map_cons, builder_run]

theorem Expression.run_bounded {e : Expression σ F M} {d : ℕ} (he : e.Bounded d)
    {rs : List (Round σ F M)} (hr : ∀ r ∈ rs, r.challenge.totalDegree ≤ 1) :
    (e.run rs).Bounded (d + 2 * rs.length) := by
  induction rs generalizing e d with
  | nil => simpa [Expression.run] using he
  | cons r rs ih =>
    have h := ih (e := e.step r) (d := d + 2) (step_bounded he (hr r (by simp)))
      (fun r' hm => hr r' (by simp [hm]))
    simpa only [Expression.run, List.length_cons, Nat.mul_succ, Nat.add_right_comm d 2, Nat.add_assoc]
      using h

end Interpolation

section Wiring

variable {L : ℕ}

/-- The polynomial form of an equality-vector coordinate. -/
noncomputable def basis (i : ℕ) (v : Fin L → Poly σ F) : Poly σ F :=
  ∏ j : Fin L, if bit_value i j.val = 1 then v j else (1 - v j)

theorem eval_basis (x : σ → F) (i : ℕ) (v : Fin L → Poly σ F) :
    eval x (basis i v) = eq_mle_basis i (Vector.ofFn fun j => eval x (v j)) := by
  rw [basis, map_prod, eq_mle_basis]
  refine Finset.prod_congr rfl fun j _ => ?_
  split_ifs <;> simp [Vector.get]

theorem degree_basis (i : ℕ) {v : Fin L → Poly σ F} {d : Fin L → ℕ}
    (hv : ∀ j, (v j).totalDegree ≤ d j) : (basis i v).totalDegree ≤ ∑ j, d j := by
  unfold basis
  refine (totalDegree_finsetProd _ _).trans ?_
  exact Finset.sum_le_sum fun j _ => by
    split_ifs
    · exact hv j
    · exact degree_sub (by simp) (hv j)

/-- Entries beyond the active width have constant polynomials, so zero padding adds no degree. -/
theorem degree_basis_width (i width : ℕ) {v : Fin L → Poly σ F}
    (hv : ∀ j, (v j).totalDegree ≤ if j.val < width then 1 else 0) :
    (basis i v).totalDegree ≤ width := by
  exact (degree_basis i hv).trans (by rw [Finset.sum_boole, Fin.card_filter_val_lt]; exact Nat.min_le_right _ _)

/-- Polynomial form of the sparse gate wiring coefficient returned by `bindGhAll`. -/
noncomputable def wiring [DecidableEq F] (gates : List (GateTerm F)) (b a : Poly σ F)
    (g0 g1 h0 h1 : Fin L → Poly σ F) : Poly σ F :=
  ∑ k : Fin gates.length, (if (gates.get k).v = 0 then b else C (gates.get k).v)
    * (basis (gates.get k).g g0 + a * basis (gates.get k).g g1)
    * basis (gates.get k).h0 h0 * basis (gates.get k).h1 h1

theorem eval_wiring [DecidableEq F] (x : σ → F) (gates : List (GateTerm F)) (b a : Poly σ F)
    (g0 g1 h0 h1 : Fin L → Poly σ F) :
    eval x (wiring gates b a g0 g1 h0 h1) =
      bindGhAll gates (eval x b) (eval x a) (Vector.ofFn fun j => eval x (g0 j))
        (Vector.ofFn fun j => eval x (g1 j)) (Vector.ofFn fun j => eval x (h0 j))
        (Vector.ofFn fun j => eval x (h1 j)) := by
  rw [wiring, map_sum, bindGhAll]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [prepV]
  split_ifs <;> simp [eval_basis]

theorem degree_wiring [DecidableEq F] (gates : List (GateTerm F)) {b a : Poly σ F}
    {g0 g1 h0 h1 : Fin L → Poly σ F} {gw hw : ℕ}
    (hb : b.totalDegree ≤ 1) (ha : a.totalDegree ≤ 1)
    (hg0 : ∀ j, (g0 j).totalDegree ≤ if j.val < gw then 1 else 0)
    (hg1 : ∀ j, (g1 j).totalDegree ≤ if j.val < gw then 1 else 0)
    (hh0 : ∀ j, (h0 j).totalDegree ≤ if j.val < hw then 1 else 0)
    (hh1 : ∀ j, (h1 j).totalDegree ≤ if j.val < hw then 1 else 0) :
    (wiring gates b a g0 g1 h0 h1).totalDegree ≤ gw + 2 * hw + 2 := by
  unfold wiring
  apply totalDegree_finsetSum_le
  intro k _
  have hb' : (if (gates.get k).v = 0 then b else C (gates.get k).v).totalDegree ≤ 1 := by
    split_ifs
    · exact hb
    · exact degree_const _ _
  have hg' := degree_add ((degree_basis_width (gates.get k).g gw hg0).trans
    (show gw ≤ 1 + gw by omega)) (degree_mul ha (degree_basis_width (gates.get k).g gw hg1))
  exact (degree_mul
    (degree_mul (degree_mul hb' hg') (degree_basis_width _ hw hh0))
    (degree_basis_width _ hw hh1)).trans (by omega)

noncomputable def inCoefficient (a : Poly σ F) (l r : Fin L → Poly σ F) (i : ℕ) : Poly σ F :=
  basis i l + a * basis i r

theorem eval_inCoefficient (x : σ → F) (a : Poly σ F) (l r : Fin L → Poly σ F) (i : ℕ) :
    eval x (inCoefficient a l r i) =
      eq_mle_basis i (Vector.ofFn fun j => eval x (l j)) +
        eval x a * eq_mle_basis i (Vector.ofFn fun j => eval x (r j)) := by
  simp [inCoefficient, eval_basis]

theorem degree_inCoefficient {a : Poly σ F} {l r : Fin L → Poly σ F} {hw : ℕ}
    (ha : a.totalDegree ≤ 1)
    (hl : ∀ j, (l j).totalDegree ≤ if j.val < hw then 1 else 0)
    (hr : ∀ j, (r j).totalDegree ≤ if j.val < hw then 1 else 0) (i : ℕ) :
    (inCoefficient a l r i).totalDegree ≤ 1 + hw :=
  degree_add ((degree_basis_width i hw hl).trans (by omega))
    (degree_mul ha (degree_basis_width i hw hr))

end Wiring

section Rows

variable {ninp : ℕ}

/-- A polynomial linear row, with separate columns from the same Ligero assignment. -/
structure Row (σ F : Type*) [Field F] (ninp M : ℕ) where
  cw : Fin ninp → Poly σ F
  cp : Fin M → Poly σ F
  rhs : Poly σ F

noncomputable def Row.eval (x : σ → F) (r : Row σ F ninp M) : LigeroRow ninp M F :=
  ⟨fun i => MvPolynomial.eval x (r.cw i), fun i => MvPolynomial.eval x (r.cp i), MvPolynomial.eval x r.rhs⟩

def Row.Bounded (r : Row σ F ninp M) (d : ℕ) : Prop :=
  (∀ i, (r.cw i).totalDegree ≤ d) ∧ (∀ i, (r.cp i).totalDegree ≤ d) ∧ r.rhs.totalDegree ≤ d

/-- At fixed assignment the row is one multivariable polynomial equation. -/
noncomputable def Row.residual (r : Row σ F ninp M) (wcol : Fin ninp → F) (pad : Fin M → F) :
    Poly σ F :=
  (∑ i, r.cw i * C (wcol i)) + (∑ j, r.cp j * C (pad j)) - r.rhs

theorem Row.eval_residual_eq_zero (r : Row σ F ninp M) (x : σ → F)
    (wcol : Fin ninp → F) (pad : Fin M → F) :
    MvPolynomial.eval x (r.residual wcol pad) = 0 ↔ (r.eval x).Sat wcol pad := by
  simp [Row.residual, Row.eval, LigeroRow.Sat, map_sum, sub_eq_zero]

theorem Row.degree_residual {r : Row σ F ninp M} {d : ℕ}
    (hr : r.Bounded d) (wcol : Fin ninp → F) (pad : Fin M → F) :
    (r.residual wcol pad).totalDegree ≤ d :=
  degree_sub (degree_add
    (totalDegree_finsetSum_le fun i _ => degree_scale _ (hr.1 i))
    (totalDegree_finsetSum_le fun j _ => degree_scale _ (hr.2.1 j))) hr.2.2

noncomputable def Row.layer (e : Expression σ F M) (q : Poly σ F) (wc0 wc1 : F)
    (dwL dwR dwLR : Fin M) : Row σ F ninp M where
  cw := fun _ => 0
  cp i := e.pad i - (if i = dwL then q * C wc1 else 0) -
    (if i = dwR then q * C wc0 else 0) - (if i = dwLR then q else 0)
  rhs := q * C wc0 * C wc1 - e.known

theorem Row.eval_layer (x : σ → F) (e : Expression σ F M) (q : Poly σ F) (wc0 wc1 : F)
    (dwL dwR dwLR : Fin M) :
    (Row.layer (ninp := ninp) e q wc0 wc1 dwL dwR dwLR).eval x =
      layerRow ninp (e.eval x) (MvPolynomial.eval x q) wc0 wc1 dwL dwR dwLR := by
  have h : ∀ i, ((Row.layer (ninp := ninp) e q wc0 wc1 dwL dwR dwLR).eval x).cp i =
      (layerRow ninp (e.eval x) (MvPolynomial.eval x q) wc0 wc1 dwL dwR dwLR).cp i := by
    intro i
    simp only [Row.layer, Row.eval, layerRow, builder_finalize, Expression.eval,
      map_sub]
    split_ifs <;> simp
  rw [Row.eval, layerRow, LigeroRow.mk.injEq]
  exact ⟨by simp [Row.layer], funext h,
    by simp [Row.layer, builder_finalize, Expression.eval]⟩

theorem Row.layer_bounded {e : Expression σ F M} {d : ℕ} (he : e.Bounded d)
    {q : Poly σ F} (hq : q.totalDegree ≤ d) (wc0 wc1 : F) (dwL dwR dwLR : Fin M) :
    (Row.layer (ninp := ninp) e q wc0 wc1 dwL dwR dwLR).Bounded d := by
  refine ⟨fun _ => by simp [Row.layer], fun i => ?_, ?_⟩
  · unfold Row.layer
    refine degree_sub (degree_sub (degree_sub (he.2 i) ?_) ?_) ?_
    · split_ifs
      · exact degree_scale _ hq
      · simp
    · split_ifs
      · exact degree_scale _ hq
      · simp
    · split_ifs <;> first | exact hq | simp
  · exact degree_sub (degree_scale _ (degree_scale _ hq)) he.1

noncomputable def Row.input (npub : ℕ) (b : Fin ninp → Poly σ F) (pub_binding : Poly σ F)
    (wc0 wc1 : F) (a : Poly σ F) (dwL dwR : Fin M) : Row σ F ninp M where
  cw i := if npub ≤ i.val then b i else 0
  cp j := (if j = dwL then -1 else 0) + (if j = dwR then -a else 0)
  rhs := C wc0 + a * C wc1 - pub_binding

theorem Row.eval_input (x : σ → F) (npub : ℕ) (b : Fin ninp → Poly σ F)
    (pub_binding : Poly σ F) (wc0 wc1 : F) (a : Poly σ F) (dwL dwR : Fin M) :
    (Row.input npub b pub_binding wc0 wc1 a dwL dwR).eval x =
      inputRow npub (fun i => MvPolynomial.eval x (b i)) (MvPolynomial.eval x pub_binding)
        (wc0 + MvPolynomial.eval x a * wc1) (MvPolynomial.eval x a) dwL dwR := by
  rw [Row.eval, inputRow, LigeroRow.mk.injEq]
  refine ⟨?_, ?_, ?_⟩
  · funext i
    dsimp [Row.input]
    split_ifs <;> simp
  · funext j
    simp only [Row.input, map_add]
    split_ifs <;> simp
  · simp [Row.input]

theorem Row.input_bounded (npub : ℕ) {d : ℕ} {b : Fin ninp → Poly σ F}
    (hb : ∀ i, (b i).totalDegree ≤ d) {pub_binding : Poly σ F}
    (hp : pub_binding.totalDegree ≤ d) (wc0 wc1 : F) {a : Poly σ F}
    (ha : a.totalDegree ≤ d) (dwL dwR : Fin M) :
    (Row.input npub b pub_binding wc0 wc1 a dwL dwR).Bounded d := by
  refine ⟨fun i => ?_, fun j => ?_, degree_sub
    (degree_add (degree_const _ _) (degree_scale _ ha)) hp⟩
  · dsimp [Row.input]
    split_ifs
    · exact hb i
    · simp
  · dsimp [Row.input]
    apply degree_add
    · split_ifs <;> simp
    · split_ifs <;> simp_all

end Rows

section Sequence

variable {ninp : ℕ}

noncomputable def Row.zero : Row σ F ninp M := ⟨fun _ => 0, fun _ => 0, 0⟩

theorem Row.zero_bounded (d : ℕ) : (Row.zero : Row σ F ninp M).Bounded d := by
  simp [Row.zero, Row.Bounded]

section Layers

variable [SumcheckV1Interp F]

/-- At each layer close, the data held constant in the replay recovers the exact verifier row. -/
structure Layer (σ F : Type*) [Field F] (M : ℕ) where
  start : Expression σ F M
  rounds : List (Round σ F M)
  wiring : Poly σ F
  wc0 : F
  wc1 : F
  dwL : Fin M
  dwR : Fin M
  dwLR : Fin M

noncomputable def Layer.data (x : σ → F) (l : Layer σ F M) : LayerRowData M F :=
  ⟨builder_run (l.start.eval x) (l.rounds.map (Round.eval x)),
    eval x l.wiring, l.wc0, l.wc1, l.dwL, l.dwR, l.dwLR⟩

noncomputable def Layer.row (l : Layer σ F M) : Row σ F ninp M :=
  Row.layer (l.start.run l.rounds) l.wiring l.wc0 l.wc1 l.dwL l.dwR l.dwLR

theorem Layer.eval_row (x : σ → F) (l : Layer σ F M) :
    l.row.eval x = layerRow ninp (l.data x).e (l.data x).eqq (l.data x).wc0 (l.data x).wc1
      (l.data x).var_dwL (l.data x).var_dwR (l.data x).var_dwLR := by
  simp [Layer.row, Layer.data, Row.eval_layer]

/-- A deployed binary layer has at most 40 rounds and a wiring factor of degree at most 62. -/
theorem Layer.row_bounded81 (l : Layer σ F M) (hstart : l.start.Bounded 1)
    (hrounds : l.rounds.length ≤ 40)
    (hchal : ∀ r ∈ l.rounds, r.challenge.totalDegree ≤ 1)
    (hwire : l.wiring.totalDegree ≤ 62) : (l.row (ninp := ninp)).Bounded 81 := by
  have h := Expression.run_bounded hstart hchal
  have hd : 1 + 2 * l.rounds.length ≤ 81 := by omega
  apply Row.layer_bounded
  · exact ⟨h.1.trans hd, fun i => (h.2 i).trans hd⟩
  · exact hwire.trans (by decide)

end Layers

/-- Linear rows depend on the replay variables. The quadratic pad triples remain fixed. -/
structure System (σ F : Type*) [Field F] (ninp M : ℕ) where
  linear : List (Row σ F ninp M)
  quad : List (Fin M × Fin M × Fin M)

noncomputable def System.eval (x : σ → F) (S : System σ F ninp M) : LigeroSystem ninp M F :=
  ⟨S.linear.map (Row.eval x), S.quad⟩

noncomputable def System.rowAt (S : System σ F ninp M) (i : ℕ) : Row σ F ninp M :=
  (S.linear[i]?).getD Row.zero

def System.Bounded (S : System σ F ninp M) (d : ℕ) : Prop :=
  ∀ row ∈ S.linear, Row.Bounded row d

theorem System.rowAt_bounded {S : System σ F ninp M} {d : ℕ} (hS : S.Bounded d) (i : ℕ) :
    (S.rowAt i).Bounded d := by
  rcases h : S.linear[i]? with _ | row
  · simpa [System.rowAt, h] using (Row.zero_bounded d : (Row.zero : Row σ F ninp M).Bounded d)
  · simpa [System.rowAt, h] using hS _ (List.mem_of_getElem? h)

theorem System.eval_sat_iff (S : System σ F ninp M) (x : σ → F)
    (wcol : Fin ninp → F) (pad : Fin M → F) :
    (S.eval x).Sat wcol pad ↔
      (∀ t ∈ S.quad, pad t.2.2 = pad t.1 * pad t.2.1) ∧
      ∀ i, MvPolynomial.eval x ((S.rowAt i).residual wcol pad) = 0 := by
  rw [LigeroSystem.Sat, and_comm]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h i
    apply (Row.eval_residual_eq_zero _ _ _ _).mpr
    rcases hi : S.linear[i]? with _ | row
    · simp [System.rowAt, hi, Row.zero, Row.eval, LigeroRow.Sat]
    · exact h _ (List.mem_map.mpr ⟨row, List.mem_of_getElem? hi, by simp [System.rowAt, hi]⟩)
  · intro h row hrow
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hrow
    obtain ⟨i, hlt, hi⟩ := List.getElem_of_mem hp
    simpa [System.rowAt, List.getElem?_eq_getElem hlt, hi] using
      (Row.eval_residual_eq_zero _ _ _ _).mp (h i)

/-- These are the layer rows in verifier order, followed by its one input row. -/
noncomputable def System.build [SumcheckV1Interp F] (ls : List (Layer σ F M)) (npub : ℕ)
    (b : Fin ninp → Poly σ F) (binding : Poly σ F) (wc0 wc1 : F)
    (a : Poly σ F) (dwL dwR : Fin M) : System σ F ninp M :=
  ⟨ls.map Layer.row ++ [Row.input npub b binding wc0 wc1 a dwL dwR],
    ls.map fun l => (l.dwL, l.dwR, l.dwLR)⟩

theorem System.eval_build [SumcheckV1Interp F] (x : σ → F) (ls : List (Layer σ F M))
    (npub : ℕ) (b : Fin ninp → Poly σ F) (binding : Poly σ F) (wc0 wc1 : F)
    (a : Poly σ F) (dwL dwR : Fin M) :
    (System.build ls npub b binding wc0 wc1 a dwL dwR).eval x =
      buildSystemMulti npub (ls.map (Layer.data x)) (fun i => MvPolynomial.eval x (b i))
        (MvPolynomial.eval x binding) (wc0 + MvPolynomial.eval x a * wc1)
        (MvPolynomial.eval x a) dwL dwR := by
  simp only [System.build, System.eval, buildSystemMulti, List.map_append, List.map_map,
    List.map_cons, List.map_nil, Function.comp_def, Layer.eval_row, Row.eval_input]
  rfl

theorem System.build_bounded81 [SumcheckV1Interp F] {ls : List (Layer σ F M)}
    (hstart : ∀ l ∈ ls, l.start.Bounded 1) (hrounds : ∀ l ∈ ls, l.rounds.length ≤ 40)
    (hchal : ∀ l ∈ ls, ∀ r ∈ l.rounds, r.challenge.totalDegree ≤ 1)
    (hwire : ∀ l ∈ ls, l.wiring.totalDegree ≤ 62)
    (npub : ℕ) {b : Fin ninp → Poly σ F} (hb : ∀ i, (b i).totalDegree ≤ 21)
    {binding : Poly σ F} (hbinding : binding.totalDegree ≤ 21)
    (wc0 wc1 : F) {a : Poly σ F} (ha : a.totalDegree ≤ 1) (dwL dwR : Fin M) :
    (System.build ls npub b binding wc0 wc1 a dwL dwR).Bounded 81 := by
  intro row hrow
  rcases List.mem_append.mp hrow with hl | hi
  · obtain ⟨l, hm, rfl⟩ := List.mem_map.mp hl
    exact l.row_bounded81 (hstart l hm) (hrounds l hm) (hchal l hm) (hwire l hm)
  · have he := List.mem_singleton.mp hi
    subst row
    exact Row.input_bounded npub (fun i => (hb i).trans (by decide))
      (hbinding.trans (by decide)) wc0 wc1 (ha.trans (by decide)) dwL dwR

end Sequence

section Identity

variable {n : ℕ} {ι : Type*} {F : Type} [Field F] [Fintype F]

open Classical in
/-- If a replayed row is nonzero, charge only that chosen equation. -/
theorem nonidentity_bound (p : ι → Poly (Fin n) F) {d : ℕ}
    (hp : ∀ i, (p i).totalDegree ≤ d) (hnz : ∃ i, p i ≠ 0) :
    ((Finset.univ.filter fun x : Fin n → F => ∀ i, eval x (p i) = 0).card : ℚ≥0)
      / (Fintype.card F ^ n : ℚ≥0) ≤ (d : ℚ≥0) / Fintype.card F := by
  classical
  obtain ⟨i, hi⟩ := hnz
  have hsz := schwartz_zippel_totalDegree hi (Finset.univ : Finset F)
  simp only [Finset.card_univ] at hsz
  have hpi : (Fintype.piFinset fun _ : Fin n => (Finset.univ : Finset F))
      = Finset.univ := by ext; simp
  rw [hpi] at hsz
  calc
    _ ≤ ((Finset.univ.filter fun x : Fin n → F => eval x (p i) = 0).card : ℚ≥0)
        / (Fintype.card F ^ n : ℚ≥0) := by
      gcongr
      exact fun h => h i
    _ ≤ (p i).totalDegree / (Fintype.card F : ℚ≥0) := hsz
    _ ≤ _ := by gcongr; exact hp i

omit [Fintype F] in
/-- On the identity branch, the same rows vanish under every replay assignment. -/
theorem identity_accepts (p : ι → Poly (Fin n) F) (h : ∀ i, p i = 0)
    (x : Fin n → F) (i : ι) : eval x (p i) = 0 := by simp [h]

end Identity

end LfzkV1.ResidualReplay125
