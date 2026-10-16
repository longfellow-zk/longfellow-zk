import Bcs.TotalOracle
import Bcs.Potential

/-!
# Weighted positive increases on a total random oracle

The value charged at one hash point may be a nonnegative integer weight,
rather than a Boolean bad-answer indicator.  Holding that point's coordinate
out gives the same exact fiber identity as the existing Boolean compiler.
Rational potentials can be multiplied by a common denominator before using
this result.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Bcs.TotalOracle

open Finset
open scoped Classical

variable {Q C : Type} [Fintype Q] [DecidableEq Q] [Fintype C]

/-- Swap the answer at one coordinate with an auxiliary answer. -/
def swapEquiv (q : Q) : ((Q → C) × C) ≃ ((Q → C) × C) where
  toFun := swapCoord q
  invFun := swapCoord q
  left_inv := swapCoord_swapCoord q
  right_inv := swapCoord_swapCoord q

/-- Weighted form of `card_coord_mul`: an off-coordinate weight can be
evaluated at the oracle's answer and then averaged over that answer. -/
theorem sum_coord_mul (q : Q) (wt : (Q → C) → C → ℕ)
    (hoff : ∀ H H' : Q → C, AgreeOff q H H' → ∀ c, wt H c = wt H' c) :
    (∑ H : Q → C, wt H (H q)) * Fintype.card C =
      ∑ H : Q → C, ∑ c : C, wt H c := by
  classical
  let σ := swapEquiv (C := C) q
  have hswap : ∀ p : (Q → C) × C,
      wt p.1 (p.1 q) = wt (σ p).1 (σ p).2 := by
    intro ⟨H, c⟩
    change wt H (H q) = wt (Function.update H q c) (H q)
    exact hoff H (Function.update H q c) (agreeOff_update q H c) (H q)
  have hsum := Fintype.sum_equiv σ
    (fun p : (Q → C) × C => wt p.1 (p.1 q))
    (fun p : (Q → C) × C => wt p.1 p.2) hswap
  have hsum' : (∑ H : Q → C, Fintype.card C * wt H (H q)) =
      ∑ H : Q → C, ∑ c : C, wt H c := by
    simpa only [Fintype.sum_prod_type, Finset.sum_const, smul_eq_mul,
      Finset.card_univ] using hsum
  calc
    (∑ H : Q → C, wt H (H q)) * Fintype.card C =
        Fintype.card C * ∑ H : Q → C, wt H (H q) := by ring
    _ = ∑ H : Q → C, Fintype.card C * wt H (H q) := by
          rw [Finset.mul_sum]
    _ = _ := hsum'

/-- Sum all weighted positive increases without replacing each local budget
by the maximum over the whole random oracle. -/
theorem sum_all_coords_mul (wt : Q → (Q → C) → C → ℕ)
    (hoff : ∀ q (H H' : Q → C), AgreeOff q H H' →
      ∀ c, wt q H c = wt q H' c) :
    (∑ H : Q → C, ∑ q : Q, wt q H (H q)) * Fintype.card C =
      ∑ H : Q → C, ∑ q : Q, ∑ c : C, wt q H c := by
  calc
    (∑ H : Q → C, ∑ q : Q, wt q H (H q)) * Fintype.card C =
        ∑ q : Q, (∑ H : Q → C, wt q H (H q)) * Fintype.card C := by
          rw [Finset.sum_comm, Finset.sum_mul]
    _ = ∑ q : Q, ∑ H : Q → C, ∑ c : C, wt q H c := by
          apply Finset.sum_congr rfl
          intro q _
          exact sum_coord_mul q (wt q) (hoff q)
    _ = _ := Finset.sum_comm

/-- A classical adversary may choose which hash points to inspect.  If that
choice is independent of each point's *own* answer, at most `T` charged
points cost `T` times the local positive-increase budget.  The argument is
valid even when points are queried speculatively or out of transcript order. -/
theorem charged_weight_sum_le (charged : Q → (Q → C) → Prop)
    (hchargedOff : ∀ q (H H' : Q → C), AgreeOff q H H' →
      (charged q H ↔ charged q H'))
    (wt : Q → (Q → C) → C → ℕ)
    (hwtOff : ∀ q (H H' : Q → C), AgreeOff q H H' →
      ∀ c, wt q H c = wt q H' c)
    (T β : ℕ)
    (hcount : ∀ H : Q → C, (univ.filter fun q => charged q H).card ≤ T)
    (hlocal : ∀ q H, ∑ c : C, wt q H c ≤ β) :
    (∑ H : Q → C, ∑ q : Q,
      if charged q H then wt q H (H q) else 0) * Fintype.card C ≤
      T * β * Fintype.card C ^ Fintype.card Q := by
  classical
  let W : Q → (Q → C) → C → ℕ :=
    fun q H c => if charged q H then wt q H c else 0
  have hWoff : ∀ q (H H' : Q → C), AgreeOff q H H' →
      ∀ c, W q H c = W q H' c := by
    intro q H H' hoff c
    simp only [W]
    rw [propext (hchargedOff q H H' hoff)]
    split
    · exact hwtOff q H H' hoff c
    · rfl
  rw [show (∑ H : Q → C, ∑ q : Q,
      if charged q H then wt q H (H q) else 0) =
      ∑ H : Q → C, ∑ q : Q, W q H (H q) from rfl]
  rw [sum_all_coords_mul W hWoff]
  calc
    (∑ H : Q → C, ∑ q : Q, ∑ c : C, W q H c) ≤
        ∑ _H : Q → C, T * β := by
          apply Finset.sum_le_sum
          intro H _
          calc
            (∑ q : Q, ∑ c : C, W q H c) ≤
                ∑ q : Q, if charged q H then β else 0 := by
                  apply Finset.sum_le_sum
                  intro q _
                  by_cases hc : charged q H
                  · simpa only [W, hc, ↓reduceIte] using hlocal q H
                  · simp [W, hc]
            _ = (univ.filter fun q : Q => charged q H).card * β := by
                  rw [← Finset.sum_filter]
                  simp [Finset.sum_const, mul_comm]
            _ ≤ T * β := Nat.mul_le_mul_right _ (hcount H)
    _ = T * β * Fintype.card C ^ Fintype.card Q := by
          simp [mul_comm]

end Bcs.TotalOracle

namespace Bcs.TotalOracle

open Finset
open scoped Classical

variable {Q C : Type} [Fintype Q] [DecidableEq Q] [Fintype C]

/-- Exact fiber identity for rational charges.  In particular, no integral
rounding of a graded potential is needed by the random-oracle compiler. -/
theorem sum_coord_mul_rat (q : Q) (wt : (Q → C) → C → ℚ)
    (hoff : ∀ H H' : Q → C, AgreeOff q H H' → ∀ c, wt H c = wt H' c) :
    (∑ H : Q → C, wt H (H q)) * Fintype.card C =
      ∑ H : Q → C, ∑ c : C, wt H c := by
  classical
  let σ := swapEquiv (C := C) q
  have hswap : ∀ p : (Q → C) × C,
      wt p.1 (p.1 q) = wt (σ p).1 (σ p).2 := by
    intro ⟨H, c⟩
    change wt H (H q) = wt (Function.update H q c) (H q)
    exact hoff H (Function.update H q c) (agreeOff_update q H c) (H q)
  have hsum := Fintype.sum_equiv σ
    (fun p : (Q → C) × C => wt p.1 (p.1 q))
    (fun p : (Q → C) × C => wt p.1 p.2) hswap
  have hsum' : (∑ H : Q → C, (Fintype.card C : ℚ) * wt H (H q)) =
      ∑ H : Q → C, ∑ c : C, wt H c := by
    simpa only [Fintype.sum_prod_type, Finset.sum_const, smul_eq_mul,
      Finset.card_univ, nsmul_eq_mul, Nat.cast_ofNat] using hsum
  calc
    (∑ H : Q → C, wt H (H q)) * Fintype.card C =
        (Fintype.card C : ℚ) * ∑ H : Q → C, wt H (H q) := by ring
    _ = ∑ H : Q → C, (Fintype.card C : ℚ) * wt H (H q) := by
          rw [Finset.mul_sum]
    _ = _ := hsum'

/-- A causal point charge has a fixed total cost after conditioning on every
answer except its own.  The event may have been found by searching several
proof prefixes; that search appears in `charged`, which must be off-coordinate. -/
theorem charged_rational_sum_le (charged : Q → (Q → C) → Prop)
    (hchargedOff : ∀ q (H H' : Q → C), AgreeOff q H H' →
      (charged q H ↔ charged q H'))
    (wt : Q → (Q → C) → C → ℚ)
    (hwtOff : ∀ q (H H' : Q → C), AgreeOff q H H' →
      ∀ c, wt q H c = wt q H' c)
    (T : ℕ) (β : ℚ)
    (hβ : 0 ≤ β)
    (hcount : ∀ H : Q → C, (univ.filter fun q => charged q H).card ≤ T)
    (hlocal : ∀ q H, ∑ c : C, wt q H c ≤ β) :
    (∑ H : Q → C, ∑ q : Q,
      if charged q H then wt q H (H q) else 0) * Fintype.card C ≤
      T * β * (Fintype.card C : ℚ) ^ Fintype.card Q := by
  classical
  let W : Q → (Q → C) → C → ℚ :=
    fun q H c => if charged q H then wt q H c else 0
  have hWoff : ∀ q (H H' : Q → C), AgreeOff q H H' →
      ∀ c, W q H c = W q H' c := by
    intro q H H' hoff c
    simp only [W]
    rw [propext (hchargedOff q H H' hoff)]
    split
    · exact hwtOff q H H' hoff c
    · rfl
  have hsum : (∑ H : Q → C, ∑ q : Q, W q H (H q)) * Fintype.card C =
      ∑ H : Q → C, ∑ q : Q, ∑ c : C, W q H c := by
    calc
      (∑ H : Q → C, ∑ q : Q, W q H (H q)) * Fintype.card C =
          ∑ q : Q, (∑ H : Q → C, W q H (H q)) * Fintype.card C := by
            rw [Finset.sum_comm, Finset.sum_mul]
      _ = ∑ q : Q, ∑ H : Q → C, ∑ c : C, W q H c := by
            apply Finset.sum_congr rfl
            intro q _
            exact sum_coord_mul_rat q (W q) (hWoff q)
      _ = _ := Finset.sum_comm
  change (∑ H : Q → C, ∑ q : Q, W q H (H q)) * Fintype.card C ≤ _
  rw [hsum]
  calc
    (∑ H : Q → C, ∑ q : Q, ∑ c : C, W q H c) ≤
        ∑ _H : Q → C, (T : ℚ) * β := by
          apply Finset.sum_le_sum
          intro H _
          calc
            (∑ q : Q, ∑ c : C, W q H c) ≤
                ∑ q : Q, if charged q H then β else 0 := by
                  apply Finset.sum_le_sum
                  intro q _
                  by_cases hc : charged q H
                  · simpa only [W, hc, ↓reduceIte] using hlocal q H
                  · simp [W, hc]
            _ = ((univ.filter fun q : Q => charged q H).card : ℚ) * β := by
                  rw [← Finset.sum_filter]
                  simp [Finset.sum_const, mul_comm]
            _ ≤ (T : ℚ) * β := by
                  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcount H) hβ
    _ = T * β * (Fintype.card C : ℚ) ^ Fintype.card Q := by
          simp [mul_comm]

/-- An extraction-failure event is bounded by the sum of the positive
increases exposed at causal hash points.  This form can be used with a
maximum-over-prefixes potential: its telescope supplies `haccept`, while
the protocol's local transition theorem supplies `hlocal`. -/
theorem potential_event_ratio_le [Nonempty C]
    (accepts : (Q → C) → Prop) [DecidablePred accepts]
    (charged : Q → (Q → C) → Prop)
    (hchargedOff : ∀ q (H H' : Q → C), AgreeOff q H H' →
      (charged q H ↔ charged q H'))
    (wt : Q → (Q → C) → C → ℚ)
    (hwtOff : ∀ q (H H' : Q → C), AgreeOff q H H' →
      ∀ c, wt q H c = wt q H' c)
    (T : ℕ) (β : ℚ) (hβ : 0 ≤ β)
    (hcount : ∀ H : Q → C, (univ.filter fun q => charged q H).card ≤ T)
    (hlocal : ∀ q H, ∑ c : C, wt q H c ≤ β)
    (hwt_nonneg : ∀ q H c, 0 ≤ wt q H c)
    (haccept : ∀ H, accepts H →
      1 ≤ ∑ q : Q, if charged q H then wt q H (H q) else 0) :
    ((univ.filter accepts).card : ℚ) /
        (Fintype.card C : ℚ) ^ Fintype.card Q ≤
      (T : ℚ) * β / Fintype.card C := by
  classical
  have hpoint (H : Q → C) :
      (if accepts H then (1 : ℚ) else 0) ≤
        ∑ q : Q, if charged q H then wt q H (H q) else 0 := by
    by_cases ha : accepts H
    · simpa only [ha, ↓reduceIte] using haccept H ha
    · simp only [ha, ↓reduceIte]
      exact Finset.sum_nonneg fun q _ => by
        split
        · exact hwt_nonneg q H (H q)
        · exact le_rfl
  have hsum : ((univ.filter accepts).card : ℚ) ≤
      ∑ H : Q → C, ∑ q : Q,
        if charged q H then wt q H (H q) else 0 := by
    calc
      ((univ.filter accepts).card : ℚ) =
          ∑ H : Q → C, if accepts H then (1 : ℚ) else 0 := by
            rw [Finset.natCast_card_filter]
      _ ≤ _ := Finset.sum_le_sum fun H _ => hpoint H
  have hcharge := charged_rational_sum_le charged hchargedOff wt hwtOff
    T β hβ hcount hlocal
  have hC : (0 : ℚ) < Fintype.card C := by exact_mod_cast Fintype.card_pos
  have hpow : (0 : ℚ) < (Fintype.card C : ℚ) ^ Fintype.card Q := pow_pos hC _
  rw [div_le_div_iff₀ hpow hC]
  have hmain := mul_le_mul_of_nonneg_right hsum (le_of_lt hC)
  nlinarith [hmain]

/-- Point-dependent version used when field rounds, the Ligero challenge,
and the column query have different positive-increase budgets. -/
theorem charged_rational_sum_le_budget
    (charged : Q → (Q → C) → Prop)
    (hchargedOff : ∀ q (H H' : Q → C), AgreeOff q H H' →
      (charged q H ↔ charged q H'))
    (wt : Q → (Q → C) → C → ℚ)
    (hwtOff : ∀ q (H H' : Q → C), AgreeOff q H H' →
      ∀ c, wt q H c = wt q H' c)
    (budget : Q → ℚ) (B : ℚ)
    (hlocal : ∀ q H, ∑ c : C, wt q H c ≤ budget q)
    (htotal : ∀ H : Q → C,
      ∑ q ∈ (univ.filter fun q => charged q H), budget q ≤ B) :
    (∑ H : Q → C, ∑ q : Q,
      if charged q H then wt q H (H q) else 0) * Fintype.card C ≤
      B * (Fintype.card C : ℚ) ^ Fintype.card Q := by
  classical
  let W : Q → (Q → C) → C → ℚ :=
    fun q H c => if charged q H then wt q H c else 0
  have hWoff : ∀ q (H H' : Q → C), AgreeOff q H H' →
      ∀ c, W q H c = W q H' c := by
    intro q H H' hoff c
    simp only [W]
    rw [propext (hchargedOff q H H' hoff)]
    split
    · exact hwtOff q H H' hoff c
    · rfl
  have hsum : (∑ H : Q → C, ∑ q : Q, W q H (H q)) * Fintype.card C =
      ∑ H : Q → C, ∑ q : Q, ∑ c : C, W q H c := by
    calc
      (∑ H : Q → C, ∑ q : Q, W q H (H q)) * Fintype.card C =
          ∑ q : Q, (∑ H : Q → C, W q H (H q)) * Fintype.card C := by
            rw [Finset.sum_comm, Finset.sum_mul]
      _ = ∑ q : Q, ∑ H : Q → C, ∑ c : C, W q H c := by
            apply Finset.sum_congr rfl
            intro q _
            exact sum_coord_mul_rat q (W q) (hWoff q)
      _ = _ := Finset.sum_comm
  change (∑ H : Q → C, ∑ q : Q, W q H (H q)) * Fintype.card C ≤ _
  rw [hsum]
  calc
    (∑ H : Q → C, ∑ q : Q, ∑ c : C, W q H c) ≤
        ∑ _H : Q → C, B := by
          apply Finset.sum_le_sum
          intro H _
          calc
            (∑ q : Q, ∑ c : C, W q H c) ≤
                ∑ q : Q, if charged q H then budget q else 0 := by
                  apply Finset.sum_le_sum
                  intro q _
                  by_cases hc : charged q H
                  · simpa only [W, hc, ↓reduceIte] using hlocal q H
                  · simp [W, hc]
            _ = ∑ q ∈ (univ.filter fun q : Q => charged q H), budget q := by
                  rw [Finset.sum_filter]
            _ ≤ B := htotal H
    _ = B * (Fintype.card C : ℚ) ^ Fintype.card Q := by simp [mul_comm]

theorem potential_event_ratio_le_budget [Nonempty C]
    (accepts : (Q → C) → Prop) [DecidablePred accepts]
    (charged : Q → (Q → C) → Prop)
    (hchargedOff : ∀ q (H H' : Q → C), AgreeOff q H H' →
      (charged q H ↔ charged q H'))
    (wt : Q → (Q → C) → C → ℚ)
    (hwtOff : ∀ q (H H' : Q → C), AgreeOff q H H' →
      ∀ c, wt q H c = wt q H' c)
    (budget : Q → ℚ) (B : ℚ)
    (hlocal : ∀ q H, ∑ c : C, wt q H c ≤ budget q)
    (htotal : ∀ H : Q → C,
      ∑ q ∈ (univ.filter fun q => charged q H), budget q ≤ B)
    (hwt_nonneg : ∀ q H c, 0 ≤ wt q H c)
    (haccept : ∀ H, accepts H →
      1 ≤ ∑ q : Q, if charged q H then wt q H (H q) else 0) :
    ((univ.filter accepts).card : ℚ) /
        (Fintype.card C : ℚ) ^ Fintype.card Q ≤
      B / Fintype.card C := by
  classical
  have hpoint (H : Q → C) :
      (if accepts H then (1 : ℚ) else 0) ≤
        ∑ q : Q, if charged q H then wt q H (H q) else 0 := by
    by_cases ha : accepts H
    · simpa only [ha, ↓reduceIte] using haccept H ha
    · simp only [ha, ↓reduceIte]
      exact Finset.sum_nonneg fun q _ => by
        split
        · exact hwt_nonneg q H (H q)
        · exact le_rfl
  have hsum : ((univ.filter accepts).card : ℚ) ≤
      ∑ H : Q → C, ∑ q : Q,
        if charged q H then wt q H (H q) else 0 := by
    calc
      ((univ.filter accepts).card : ℚ) =
          ∑ H : Q → C, if accepts H then (1 : ℚ) else 0 := by
            rw [Finset.natCast_card_filter]
      _ ≤ _ := Finset.sum_le_sum fun H _ => hpoint H
  have hcharge := charged_rational_sum_le_budget charged hchargedOff wt hwtOff
    budget B hlocal htotal
  have hC : (0 : ℚ) < Fintype.card C := by exact_mod_cast Fintype.card_pos
  have hpow : (0 : ℚ) < (Fintype.card C : ℚ) ^ Fintype.card Q := pow_pos hC _
  rw [div_le_div_iff₀ hpow hC]
  have hmain := mul_le_mul_of_nonneg_right hsum (le_of_lt hC)
  nlinarith [hmain]

end Bcs.TotalOracle
