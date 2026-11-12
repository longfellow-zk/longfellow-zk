import Survival.Parameters
import Mathlib.Data.Nat.Choose.Cast

/-! Independent exact arithmetic for the captured rate-1/7 profile.
These are numerical certificates, not a proof of the runtime bridge.
Constants are copied from Current/Parameters/Rate7 and AdapterParameters.
-/
namespace Survival.Rate7

def q : ℕ := 2^128
def prime : ℕ := 2^256 - 2^224 + 2^192 + 2^96 - 1
def rate : ℚ := 2/((q-1 : ℕ) : ℚ)
def tail (columns : ℕ) : ℚ := (columns.choose 84 : ℚ) / (2443 : ℕ).choose 84
def rank (field : ℕ) : ℚ := ((2443 : ℕ).choose 374 : ℚ) / (field : ℚ)^13
def parentBudget : ℚ := rank q + rank prime +
  (1/(q : ℚ)+1/(prime : ℚ)) *
    (1-tail 866+(1272737905242889781956743699885451 : ℚ)*tail 866)
def openingBudget : ℚ := tail 866 + tail 876 + tail 874

/-- Exact parameter-dependent coefficient: the opaque Polygero allowance is `c/q`. -/
def polygeroConstant : ℚ := q * parentBudget

/-- Normalize the exact opaque allowance by the application hazard. -/
def polygeroFraction : ℚ := polygeroConstant * (q-1 : ℕ) / (2*q)

/-- A checked decimal enclosure, not a rounded constant used in the bound. -/
theorem polygeroConstant_interval :
    100000123121490824416/(10^20 : ℚ) < polygeroConstant ∧
      polygeroConstant < 100000123121490824417/(10^20 : ℚ) := by
  simp only [polygeroConstant, parentBudget, rank, tail, q, prime, Nat.choose_eq_fast_choose]
  decide +kernel

theorem polygeroFraction_mul_rate : polygeroFraction * rate = parentBudget := by
  norm_num [polygeroFraction, polygeroConstant, rate, q]
  ring

theorem polygeroFraction_nonneg : 0 ≤ polygeroFraction := by
  have positive : 0 < polygeroConstant := lt_trans (by norm_num) polygeroConstant_interval.1
  unfold polygeroFraction
  positivity

theorem polygeroFraction_le : polygeroFraction ≤ 51/100 := by
  have upper := polygeroConstant_interval.2
  norm_num [polygeroFraction, q]
  linarith

theorem rate_nonneg : 0 ≤ rate := by norm_num [rate, q]
theorem rate_small : rate ≤ 1/1024 := by norm_num [rate, q]

theorem opening_budget : openingBudget ≤ rate := by
  simp only [openingBudget, tail, rate, q, Nat.choose_eq_fast_choose]
  decide +kernel

theorem query_budget (queries : ℕ) (budget : queries < q/2) : rate*queries ≤ 1 := by
  have integerBound : queries ≤ 2^127-1 := by
    norm_num [q] at budget
    omega
  norm_num at integerBound
  have rationalBound : (queries : ℚ) ≤ 170141183460469231731687303715884105727 := by
    exact_mod_cast integerBound
  norm_num [rate, q]
  linarith

def correction (queries rounds : ℕ) : ℚ :=
  ((queries.choose 2 : ℚ)+rounds+15)/(q : ℚ)^2

/-- The exact runtime failure bound, with Polygero charged at `c/q`. -/
def failureBound (queries rounds : ℕ) : ℚ :=
  polygeroConstant*queries/q +
    (1-polygeroConstant*((q : ℚ)-1)/(2*q)) * (1-(1-rate)^queries) + correction queries rounds

theorem failureBound_eq (queries rounds : ℕ) :
    failureBound queries rounds = Hybrid.envelope rate polygeroFraction queries + correction queries rounds := by
  norm_num only [failureBound, Hybrid.envelope, polygeroFraction, rate, q,
    Nat.reducePow, Nat.reduceSub, Nat.cast_ofNat]
  ring

theorem failureBound_le_linear (queries rounds : ℕ) :
    failureBound queries rounds ≤ rate*queries + correction queries rounds := by
  have bernoulli := one_add_mul_le_pow (show (-2 : ℚ) ≤ -rate by norm_num [rate, q]) queries
  have saturation : 1-(1-rate)^queries ≤ rate*queries := by
    change 1+(queries : ℚ)*(-rate) ≤ (1+-rate)^queries at bernoulli
    simp only [← sub_eq_add_neg] at bernoulli
    linarith
  have coefficient : 0 ≤ 1-polygeroFraction := by have := polygeroFraction_le; linarith
  rw [failureBound_eq, Hybrid.envelope]
  nlinarith [mul_le_mul_of_nonneg_left saturation coefficient]

/-- Polynomial consequence, retaining the verifier-only round correction. -/
theorem failureBound_le_polynomial (queries rounds : ℕ) :
    failureBound queries rounds ≤
      2*queries/q + (2*q/((q : ℚ)-1))*(queries : ℚ)^2/(q : ℚ)^2 +
        ((rounds : ℚ)+15)/(q : ℚ)^2 := by
  apply (failureBound_le_linear queries rounds).trans
  have choose : (queries.choose 2 : ℚ) = (queries : ℚ)*((queries : ℚ)-1)/2 := by
    simpa using Nat.cast_choose_two ℚ queries
  have count : (queries : ℚ) ≤ (queries : ℚ)^2 := by
    have natural : queries ≤ queries*queries := by nlinarith
    exact_mod_cast (show queries ≤ queries^2 by simpa only [pow_two] using natural)
  rw [correction, choose]
  norm_num [rate, q]
  nlinarith

private theorem survival_second_order (p : ℚ) (nonnegative : 0 ≤ p) (atMostOne : p ≤ 1) (n : ℕ) :
    1-(1-p)^n ≤ p*n - p^2*n*((n : ℚ)-1)/2*(1-p)^n := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      have scaled := mul_le_mul_of_nonneg_left ih (sub_nonneg.mpr atMostOne)
      have power : (1-p)^(n+1) ≤ 1 := pow_le_one₀ (by linarith) (by linarith)
      have slack := mul_nonneg (show 0 ≤ p^2*(n : ℚ) by positivity) (sub_nonneg.mpr power)
      simp only [pow_succ, Nat.cast_add, Nat.cast_one] at *
      nlinarith only [scaled, slack]

/-- Keep the birthday coefficient at one half; three units of constant
slack cover the nonzero-field denominator after using survival curvature. -/
theorem failureBound_le_birthday (queries rounds : ℕ) (budget : queries < q/2) :
    failureBound queries rounds ≤
      2*queries/q + (queries : ℚ)^2/(2*(q : ℚ)^2) + ((rounds : ℚ)+18)/(q : ℚ)^2 := by
  have survival := Parameters.survival_third rate rate_nonneg rate_small queries (query_budget queries budget)
  have second := survival_second_order rate rate_nonneg (show rate ≤ 1 by norm_num [rate, q]) queries
  have pairs : 0 ≤ (queries : ℚ)*((queries : ℚ)-1) := by
    have count : queries ≤ queries^2 := by nlinarith
    have cast : (queries : ℚ) ≤ (queries : ℚ)^2 := by exact_mod_cast count
    nlinarith only [cast]
  have coefficient : 0 ≤ rate^2*(queries : ℚ)*((queries : ℚ)-1)/2 := by
    nlinarith only [mul_nonneg (sq_nonneg rate) pairs]
  have curved : 1-(1-rate)^queries ≤ rate*queries-rate^2*queries*((queries : ℚ)-1)/6 := by
    nlinarith only [second, mul_le_mul_of_nonneg_left survival coefficient]
  have weighted := mul_le_mul_of_nonneg_left curved
    (show 0 ≤ 1-polygeroFraction by have := polygeroFraction_le; linarith)
  have choose := Nat.cast_choose_two ℚ queries
  rw [failureBound_eq, Hybrid.envelope, correction, choose]
  have share := polygeroFraction_le
  have shareLower := polygeroFraction_nonneg
  have saving := mul_nonneg (sub_nonneg.mpr share) coefficient
  norm_num [rate, q] at weighted coefficient saving ⊢
  nlinarith only [weighted, saving, sq_nonneg ((queries : ℚ)-137/49)]

/-- Convenient all-budget approximation for the supported mdoc schedules. -/
theorem mdoc_approximation (queries rounds : ℕ) (budget : queries < q/2) (roundBound : rounds ≤ 500) :
    failureBound queries rounds ≤
      (queries : ℚ)/2^127 + (queries : ℚ)^2/2^257 + 1/2^246 := by
  apply (failureBound_le_birthday queries rounds budget).trans
  have cast : (rounds : ℚ) ≤ 500 := by exact_mod_cast roundBound
  norm_num [q, pow_succ]
  linarith only [cast]

theorem hash_budget (queries rounds : ℕ) (budget : queries < q/2) (fits : rounds < 2^64) :
    correction queries rounds ≤ 1/8 := by
  have integerBound : queries ≤ 2^127-1 := by
    norm_num [q] at budget
    omega
  have monotone := Nat.choose_le_choose 2 integerBound
  have castBound : (queries.choose 2 : ℚ) ≤ ((2^127-1 : ℕ).choose 2 : ℚ) := by
    exact_mod_cast monotone
  have maximum : (((2^127-1 : ℕ).choose 2 : ℚ)) =
      14474011154664524427946373126085988481403536308014366657334667045415315046401 := by
    simp only [Nat.choose_eq_fast_choose]
    decide +kernel
  rw [maximum] at castBound
  have roundBound : (rounds : ℚ) ≤ 18446744073709551616 := by
    have upper : rounds ≤ 18446744073709551616 := by norm_num at fits; omega
    exact_mod_cast upper
  unfold correction
  apply (div_le_iff₀ (by norm_num [q] : (0 : ℚ) < (q : ℚ)^2)).mpr
  norm_num [q]
  linarith

/-- The exact Polygero allowance also covers auxiliary hash queries. -/
theorem auxiliary_exact_budget (queries : ℕ) (budget : queries < q/2) :
    (2*queries : ℚ)/(q : ℚ)^2 ≤ polygeroFraction*rate := by
  have integerBound : queries ≤ 2^127-1 := by norm_num [q] at budget; omega
  have rationalBound : (queries : ℚ) ≤ 170141183460469231731687303715884105727 := by
    exact_mod_cast integerBound
  have constantLower : 1 ≤ polygeroConstant := le_trans (by norm_num) polygeroConstant_interval.1.le
  rw [polygeroFraction_mul_rate]
  have scaled := constantLower
  unfold polygeroConstant at scaled
  norm_num [q] at scaled ⊢
  linarith

theorem failureBound_nonvacuous (queries rounds : ℕ) (budget : queries < q/2) (fits : rounds < 2^64) :
    failureBound queries rounds ≤ 577/600 :=
  failureBound_eq queries rounds ▸
    Parameters.hybrid_margin rate polygeroFraction (correction queries rounds) rate_nonneg rate_small
      polygeroFraction_nonneg polygeroFraction_le queries (query_budget queries budget)
      (hash_budget queries rounds budget fits)

theorem failureBound_lt_one (queries rounds : ℕ) (budget : queries < q/2) (fits : rounds < 2^64) :
    failureBound queries rounds < 1 :=
  lt_of_le_of_lt (failureBound_nonvacuous queries rounds budget fits) (by norm_num)

end Survival.Rate7
