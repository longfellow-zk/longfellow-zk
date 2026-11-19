import LfzkV2.Linear.TerminalSampling
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.Int.Interval

/-! Collision counting for the two full-prime-field rescalings in the current
product-tree adapter. Quotient advice is allowed to depend on both challenges.
The original bits, coefficients and target must already be fixed. The count
therefore includes every allowed quotient rather than treating advice as fixed.
Concrete binary-field generator and circuit-layout correspondence are separate. -/
namespace LfzkV2.Current.Adapter
open Finset
open scoped Classical

variable {p bits : ℕ} [Fact p.Prime]

def residual (weights : Fin bits → ZMod p) (values : Fin bits → Bool) (target : ZMod p) : ZMod p :=
  (∑ i, if values i then weights i else 0) - target

def scaledSum (weights : Fin bits → ZMod p) (values : Fin bits → Bool) (alpha : ZMod p) : ℕ :=
  ∑ i, if values i then (alpha * weights i).val else 0

def difference (weights : Fin bits → ZMod p) (values : Fin bits → Bool)
    (target alpha : ZMod p) (quotient : ℕ) : ℤ :=
  scaledSum weights values alpha - (alpha * target).val - (quotient : ℤ) * p

theorem difference_cast (weights : Fin bits → ZMod p) (values : Fin bits → Bool)
    (target alpha : ZMod p) (quotient : ℕ) :
    (difference weights values target alpha quotient : ZMod p) =
      alpha * residual weights values target := by
  simp only [difference, scaledSum, residual, Int.cast_sub, Int.cast_natCast,
    Int.cast_mul, Nat.cast_sum, Int.cast_sum, Nat.cast_ite, Int.cast_ite,
    Nat.cast_zero, Int.cast_zero, ZMod.natCast_zmod_val,
    ZMod.natCast_self, mul_zero, sub_zero, mul_sub, mul_sum]
  congr 1
  apply sum_congr rfl
  intro i _
  split <;> simp_all

/-- There are at most `bits` selected canonical coefficients. A quotient in
`[0,K)` gives an integer difference of magnitude at most `K*p`, for `bits ≤ K`. -/
theorem difference_bound (weights : Fin bits → ZMod p) (values : Fin bits → Bool)
    (target alpha : ZMod p) {K quotient : ℕ} (hbits : bits ≤ K) (hk : quotient < K) :
    (difference weights values target alpha quotient).natAbs ≤ K * p := by
  have hsum : scaledSum weights values alpha ≤ bits * (p-1) := by
    apply (sum_le_sum fun i _ => show (if values i then (alpha * weights i).val else 0) ≤ p-1 by
      split
      · have := (alpha * weights i).val_lt; omega
      · omega).trans_eq
    simp
  have htarget := (alpha * target).val_lt
  have hp := Fact.out (p := p.Prime)
  have hsum' : (scaledSum weights values alpha : ℤ) ≤ (K : ℤ) * p := by
    exact_mod_cast hsum.trans (Nat.mul_le_mul hbits (Nat.sub_le _ _))
  have hsum0 : (0 : ℤ) ≤ scaledSum weights values alpha := by positivity
  have ht : ((alpha * target).val : ℤ) < p := by exact_mod_cast htarget
  have hk' : (quotient : ℤ) + 1 ≤ K := by exact_mod_cast hk
  have hp' : (0 : ℤ) < p := by exact_mod_cast hp.pos
  have hbounds : -(↑(K*p) : ℤ) ≤ difference weights values target alpha quotient ∧
      difference weights values target alpha quotient ≤ (K*p : ℕ) := by
    dsimp [difference]
    constructor <;> nlinarith
  omega

/-- Possible residues when a bounded integer is a multiple of the binary
multiplicative-group order. This set is independent of the rescaling answer. -/
noncomputable def residues (p M H : ℕ) : Finset (ZMod p) :=
  (Icc (-(H : ℤ)) H).image fun z : ℤ => ((M : ℤ) * z : ℤ)

theorem residues_card (p M H : ℕ) : (residues p M H).card ≤ 2 * H + 1 := by
  apply (card_image_le).trans_eq
  simp
  omega

theorem cast_mem_residues {M bound : ℕ} (hM : 0 < M) (d : ℤ)
    (hbound : d.natAbs ≤ bound) (hdiv : (M : ℤ) ∣ d) :
    (d : ZMod p) ∈ residues p M (bound / M) := by
  obtain ⟨z, rfl⟩ := hdiv
  have hz : z.natAbs ≤ bound / M := by
    apply (Nat.le_div_iff_mul_le hM).mpr
    simpa [Int.natAbs_mul, Nat.mul_comm] using hbound
  apply mem_image.mpr
  refine ⟨z, mem_Icc.mpr ?_, rfl⟩
  omega

def Bad (weights : Fin bits → ZMod p) (values : Fin bits → Bool) (target : ZMod p)
    (M K : ℕ) (alpha : Linear.TerminalSampling.Nonzero (ZMod p)) : Prop :=
  ∃ quotient < K, (M : ℤ) ∣ difference weights values target alpha.val quotient

theorem bad_card (weights : Fin bits → ZMod p) (values : Fin bits → Bool) (target : ZMod p)
    {M K : ℕ} (hM : 0 < M) (hbits : bits ≤ K) (hfalse : residual weights values target ≠ 0) :
    (univ.filter (Bad weights values target M K)).card ≤ 2 * (K*p/M) + 1 := by
  apply le_trans ?_ (residues_card p M (K*p/M))
  apply card_le_card_of_injOn (fun a : Linear.TerminalSampling.Nonzero (ZMod p) =>
    a.val * residual weights values target)
  · intro a ha
    obtain ⟨k, hk, hdiv⟩ := (mem_filter.mp ha).2
    change a.val * residual weights values target ∈ residues p M (K*p/M)
    rw [← difference_cast weights values target a.val k]
    exact cast_mem_residues hM _ (difference_bound weights values target a.val hbits hk) hdiv
  · intro a _ b _ h
    exact Subtype.ext (mul_right_cancel₀ hfalse h)

/-- Both challenges occur in one answer block. Even jointly adaptive quotient
advice cannot escape the Cartesian product of the two single-answer bad sets. -/
theorem two_bad_card (weights : Fin bits → ZMod p) (values : Fin bits → Bool) (target : ZMod p)
    {M K : ℕ} (hM : 0 < M) (hbits : bits ≤ K) (hfalse : residual weights values target ≠ 0) :
    (univ.filter fun a : Linear.TerminalSampling.Nonzero (ZMod p) ×
        Linear.TerminalSampling.Nonzero (ZMod p) =>
      Bad weights values target M K a.1 ∧ Bad weights values target M K a.2).card ≤
      (2 * (K*p/M) + 1)^2 := by
  have heq : (univ.filter fun a : Linear.TerminalSampling.Nonzero (ZMod p) ×
        Linear.TerminalSampling.Nonzero (ZMod p) =>
      Bad weights values target M K a.1 ∧ Bad weights values target M K a.2) =
      (univ.filter (Bad weights values target M K)) ×ˢ
        (univ.filter (Bad weights values target M K)) := by ext a; simp
  rw [heq, card_product, sq]
  exact Nat.mul_le_mul (bad_card weights values target hM hbits hfalse)
    (bad_card weights values target hM hbits hfalse)

theorem two_bad_probability_le (weights : Fin bits → ZMod p) (values : Fin bits → Bool)
    (target : ZMod p) {M K : ℕ} (hM : 0 < M) (hbits : bits ≤ K)
    (hfalse : residual weights values target ≠ 0) :
    ((univ.filter fun a : Linear.TerminalSampling.Nonzero (ZMod p) ×
        Linear.TerminalSampling.Nonzero (ZMod p) =>
      Bad weights values target M K a.1 ∧ Bad weights values target M K a.2).card : ℚ) /
        Fintype.card (Linear.TerminalSampling.Nonzero (ZMod p) ×
          Linear.TerminalSampling.Nonzero (ZMod p)) ≤
      ((2 * (K*p/M) + 1 : ℕ) : ℚ)^2 / ((p-1 : ℕ) : ℚ)^2 := by
  have hc := (Nat.cast_le (α := ℚ)).mpr (two_bad_card weights values target hM hbits hfalse)
  have h := div_le_div_of_nonneg_right hc
    (show (0 : ℚ) ≤ ((p-1 : ℕ) : ℚ)^2 by positivity)
  simpa [Fintype.card_prod, Linear.TerminalSampling.nonzero_card, ZMod.card, sq] using h

/-- Each mux leaf selects either one or its public group power. Decoding the
quotient bits gives `quotient`; its base is `g^(-p)`, as in the Rust adapter. -/
def ProductCheck {G : Type} [CommGroup G] (g : G)
    (weights : Fin bits → ZMod p) (values : Fin bits → Bool)
    (target alpha : ZMod p) (quotient : ℕ) : Prop :=
  (∏ i, if values i then g ^ (alpha * weights i).val else 1) *
      (g ^ (-(p : ℤ))) ^ quotient = g ^ (alpha * target).val

theorem product_check_iff {G : Type} [CommGroup G] (g : G) {M : ℕ} (horder : orderOf g = M)
    (weights : Fin bits → ZMod p) (values : Fin bits → Bool)
    (target alpha : ZMod p) (quotient : ℕ) :
    ProductCheck g weights values target alpha quotient ↔
      (M : ℤ) ∣ difference weights values target alpha quotient := by
  have hprod : (∏ i, if values i then g ^ (alpha * weights i).val else 1) =
      g ^ scaledSum weights values alpha := by
    rw [scaledSum, ← prod_pow_eq_pow_sum]
    apply prod_congr rfl
    intro i _
    split <;> simp_all
  have hq : (g ^ (-(p : ℤ))) ^ quotient = g ^ (-(p : ℤ) * (quotient : ℤ)) := by
    rw [← zpow_natCast, ← zpow_mul]
  rw [ProductCheck, hprod, ← zpow_natCast g (scaledSum weights values alpha),
    ← zpow_natCast g (alpha * target).val, hq, ← zpow_add,
    ← mul_inv_eq_one, ← zpow_sub, ← orderOf_dvd_iff_zpow_eq_one, horder]
  have he : (scaledSum weights values alpha : ℤ) + -(p : ℤ) * (quotient : ℤ) -
      (alpha * target).val = difference weights values target alpha quotient := by
    dsimp [difference]
    ring
  rw [he]

end LfzkV2.Current.Adapter
