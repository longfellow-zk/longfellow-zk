import Bcs.StoppedPotential

/-! Potentials indexed by the remaining budget, and a finite-horizon
root/child search calculation. These abstract lemmas do not assume that
a concrete FS execution follows the ordered renewal process. -/
namespace Bcs.StoppedPotential
open Bcs.TotalOracle.Footprint
open scoped Classical
variable {State Coin : Type} [Fintype Coin]

theorem stoppedValue_le_timePotential (terminal : State → Prop) (next : State → Coin → State)
    (potential : ℕ → State → ℚ)
    (hzero : ∀ s, (if terminal s then (1 : ℚ) else 0) ≤ potential 0 s)
    (hterminal : ∀ n s, terminal s → 1 ≤ potential n s)
    (hstep : ∀ n s, ¬ terminal s →
      average (fun c => potential n (next s c)) ≤ potential (n+1) s)
    (n : ℕ) (s : State) : stoppedValue terminal next n s ≤ potential n s := by
  induction n generalizing s with
  | zero => exact hzero s
  | succ n ih =>
    by_cases ht : terminal s
    · simpa only [stoppedValue,if_pos ht] using hterminal (n+1) s ht
    · exact (by simpa only [stoppedValue,if_neg ht] using
        (average_mono (fun c => ih (next s c))).trans (hstep n s ht))

noncomputable def renewalReady (c : ℚ) : ℕ → ℚ
  | 0 => 0
  | n+1 => c+(1-c)*renewalReady c n
noncomputable def renewalSearch (r c : ℚ) : ℕ → ℚ
  | 0 => 0
  | n+1 => r*renewalReady c n+(1-r)*renewalSearch r c n

theorem renewalReady_nonneg (c : ℚ) (hc : 0 ≤ c) (hc1 : c ≤ 1) (n : ℕ) :
    0 ≤ renewalReady c n := by
  induction n with
  | zero => rfl
  | succ n ih => exact add_nonneg hc (mul_nonneg (sub_nonneg.mpr hc1) ih)

theorem renewalSearch_nonneg (r c : ℚ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hc : 0 ≤ c) (hc1 : c ≤ 1) (n : ℕ) : 0 ≤ renewalSearch r c n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    exact add_nonneg (mul_nonneg hr (renewalReady_nonneg c hc hc1 n))
      (mul_nonneg (sub_nonneg.mpr hr1) ih)

theorem renewalReady_le (c : ℚ) (hc : 0 ≤ c) (hc1 : c ≤ 1) (n : ℕ) :
    renewalReady c n ≤ n*c := by
  induction n with
  | zero => simp [renewalReady]
  | succ n ih =>
    rw [renewalReady]
    have hn := renewalReady_nonneg c hc hc1 n
    push_cast
    nlinarith [mul_nonneg hc hn]

/-- Ordered search must encounter both a root and a later child hit.
The number of ordered opportunities is choose(n,2), not n². -/
theorem renewalSearch_le_pairs (r c : ℚ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hc : 0 ≤ c) (hc1 : c ≤ 1) (n : ℕ) :
    renewalSearch r c n ≤ (n.choose 2 : ℚ)*r*c := by
  induction n with
  | zero => simp [renewalSearch]
  | succ n ih =>
    rw [renewalSearch, Nat.choose_succ_succ]
    simp only [Nat.choose_one_right,Nat.cast_add]
    have hn := renewalSearch_nonneg r c hr hr1 hc hc1 n
    have hb := mul_le_mul_of_nonneg_left (renewalReady_le c hc hc1 n) hr
    nlinarith [mul_nonneg hr hn]

/-- A root lookup is also allowed an immediate child attempt. This is
more generous than the ordered process and avoids treating the first child
as a necessarily separate query. It still does not model a full ROM cache. -/
noncomputable def renewalImmediate (r c : ℚ) : ℕ → ℚ
  | 0 => 0
  | n+1 => r*(c+(1-c)*renewalReady c n)+(1-r)*renewalImmediate r c n

theorem renewalImmediate_nonneg (r c : ℚ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hc : 0 ≤ c) (hc1 : c ≤ 1) (n : ℕ) : 0 ≤ renewalImmediate r c n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    exact add_nonneg (mul_nonneg hr (add_nonneg hc
      (mul_nonneg (sub_nonneg.mpr hc1) (renewalReady_nonneg c hc hc1 n))))
      (mul_nonneg (sub_nonneg.mpr hr1) ih)

theorem renewalImmediate_le_pairs (r c : ℚ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hc : 0 ≤ c) (hc1 : c ≤ 1) (n : ℕ) :
    renewalImmediate r c n ≤ ((n+1).choose 2 : ℚ)*r*c := by
  induction n with
  | zero => simp [renewalImmediate]
  | succ n ih =>
    rw [renewalImmediate, Nat.choose_succ_succ]
    simp only [Nat.choose_one_right,Nat.cast_add,Nat.cast_one]
    have hn := renewalImmediate_nonneg r c hr hr1 hc hc1 n
    have hb := renewalReady_le c hc hc1 (n+1)
    rw [renewalReady] at hb
    have hm := mul_le_mul_of_nonneg_left hb hr
    push_cast at hm
    nlinarith [mul_nonneg hr hn]

/-- A static renewal barrier need not be attained under a small work cap.
The factor depends on the finite horizon relative to the field size. -/
theorem renewalSearch_le_budget (r c q cap B : ℚ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hc : 0 ≤ c) (hc1 : c ≤ 1) (_hq : 0 < q) (_hcap : 0 ≤ cap)
    (hbound : cap*r*c/2 ≤ B/q) (n : ℕ) (hn : (n : ℚ) ≤ cap) :
    renewalSearch r c n ≤ n*(B/q) := by
  have hp := renewalSearch_le_pairs r c hr hr1 hc hc1 n
  have hchoose : (n.choose 2 : ℚ) ≤ (n : ℚ)^2/2 := by
    have hnat := Nat.mul_le_mul_left n (Nat.sub_le n 1)
    have he := Nat.choose_two_right n
    rw [he]
    have hdiv : n*(n-1)/2 ≤ n*n/2 := Nat.div_le_div_right hnat
    have hfloor : ((n*n/2 : ℕ) : ℚ) ≤ (n : ℚ)^2/2 := by
      have h := Nat.div_mul_le_self (n*n) 2
      have hh := Nat.cast_le (α := ℚ).mpr h
      push_cast at hh
      nlinarith
    exact (Nat.cast_le.mpr hdiv).trans hfloor
  have hrc : 0 ≤ r*c := mul_nonneg hr hc
  have hc' := mul_le_mul_of_nonneg_right hchoose hrc
  have hm := mul_nonneg (sub_nonneg.mpr hn) (show 0 ≤ (n : ℚ)*r*c by positivity)
  have hb := mul_le_mul_of_nonneg_left hbound (Nat.cast_nonneg n)
  nlinarith
theorem renewalImmediate_le_budget (r c q cap B : ℚ) (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (hc : 0 ≤ c) (hc1 : c ≤ 1) (_hq : 0 < q) (_hcap : 0 ≤ cap)
    (hbound : cap*r*c/2 ≤ B/q) (n : ℕ) (hn : (n : ℚ) ≤ cap) :
    renewalImmediate r c n ≤ (n+1)*(B/q) := by
  have hp := renewalImmediate_le_pairs r c hr hr1 hc hc1 n
  have he : ((n+1).choose 2 : ℚ) = (n : ℚ)*(n+1)/2 := by
    have hh := Nat.choose_two_right (n+1)
    rw [Nat.add_sub_cancel] at hh
    have hpar : 2 ∣ (n+1)*n := by simpa only [Nat.mul_comm] using Nat.two_dvd_mul_add_one n
    rw [hh]
    exact (Nat.cast_div hpar (by norm_num : (2 : ℚ) ≠ 0)).trans (by push_cast; ring)
  rw [he] at hp
  have hm := mul_nonneg (sub_nonneg.mpr hn) (show 0 ≤ ((n : ℚ)+1)*r*c by positivity)
  have hb := mul_le_mul_of_nonneg_left hbound (show 0 ≤ (n : ℚ)+1 by positivity)
  nlinarith

end Bcs.StoppedPotential
