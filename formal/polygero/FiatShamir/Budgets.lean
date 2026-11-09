import polygero.FiatShamir.ResponseMass
import polygero.FiatShamir.Balance

/-! Exact raw-answer budgets for the two FS query roles. -/
noncomputable section
namespace RecursivePolygero.NonrecursiveFS
open Polynomial Finset Codes RecursivePolygero RecursivePolygero.Local
open ProfileAnalysis
open scoped Classical
attribute [local instance] Classical.propDecidable
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

theorem balanced_sum_le
    {C X : Type} [Fintype C] [Fintype X] [DecidableEq X] [Nonempty X]
    (decode : C → X) (k : ℕ)
    (hfiber : ∀ x, (univ.filter fun c : C => decode c = x).card ≤ k)
    (hsize : k*Fintype.card X ≤ Fintype.card C)
    (weight : X → ℚ) (hweight : ∀ x, 0 ≤ weight x)
    (bound : ℚ) (hbound : 0 ≤ bound) (hmean : mean weight ≤ bound) :
    ∑ c : C, weight (decode c) ≤ Fintype.card C*bound := by
  have h := Balance.decoded_mean_le decode weight hweight k hfiber bound hmean
  exact h.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hsize) hbound)

section Budgets
variable (I : Instance F) (p : HahnSystemCertificate I)
variable {C : Type} [Fintype C] [Nonempty C]
variable [DecidableEq I.layer.Coin] [DecidableEq I.layer.Query]
variable (decodeCoin : C → I.layer.Coin) (decodeQuery : C → I.layer.Query)
variable (kCoin kQuery : ℕ)
variable (hcoin : ∀ coin, (univ.filter fun a : C => decodeCoin a = coin).card ≤ kCoin)
variable (hquery : ∀ Q, (univ.filter fun b : C => decodeQuery b = Q).card ≤ kQuery)
variable (hkCoin : kCoin*Fintype.card I.layer.Coin ≤ Fintype.card C)
variable (hkQuery : kQuery*Fintype.card I.layer.Query ≤ Fintype.card C)
variable (σ : I.layer.Statement) (W : I.layer.Oracle)
variable (hfalse : ∀ w, ¬ I.layer.satisfies σ w)

omit [Nonempty C] [DecidableEq I.layer.Coin] in
include kQuery hquery hkQuery in
private theorem query_raw_le (c : I.layer.Coin) (payload : I.layer.Payload) :
    (∑ b : C, if I.layer.verify σ W c payload (decodeQuery b) then (1 : ℚ) else 0) ≤
      Fintype.card C*fraction I σ W c payload := by
  apply balanced_sum_le decodeQuery kQuery hquery hkQuery
    (fun Q => indicator (I.layer.verify σ W c payload Q)) (fun _ => indicator_nonneg _)
  · unfold fraction; positivity
  · exact (query_mean I σ W c payload).le

include kCoin kQuery hcoin hquery hkCoin hkQuery hfalse in
theorem fixed_response_raw_le (payload : I.layer.Payload) :
    (∑ a : C, ∑ b : C,
      if I.layer.verify σ W (decodeCoin a) payload (decodeQuery b) then (1 : ℚ) else 0) ≤
      (Fintype.card C : ℚ)^2*p.error := by
  have hc := balanced_sum_le decodeCoin kCoin hcoin hkCoin
    (fun c => fraction I σ W c payload)
    (by intro c; unfold fraction; positivity)
    p.error p.error_nonneg (response_mean_le I p σ W hfalse (fun _ => payload))
  calc
    _ ≤ ∑ a : C, Fintype.card C*fraction I σ W (decodeCoin a) payload :=
      sum_le_sum (fun a _ => query_raw_le I decodeQuery kQuery hquery hkQuery σ W (decodeCoin a) payload)
    _ = Fintype.card C*∑ a : C, fraction I σ W (decodeCoin a) payload := (mul_sum ..).symm
    _ ≤ Fintype.card C*(Fintype.card C*p.error) := mul_le_mul_of_nonneg_left hc (by positivity)
    _ = _ := by ring

omit [Nonempty C] [DecidableEq I.layer.Query] in
include kCoin hcoin hkCoin in
theorem rank_raw_le :
    (∑ a : C, if rankBad I W (decodeCoin a) then (1 : ℚ) else 0) ≤
      Fintype.card C*p.rankError := by
  exact balanced_sum_le decodeCoin kCoin hcoin hkCoin
    (fun c => indicator (rankBad I W c)) (fun _ => indicator_nonneg _)
    p.rankError (by unfold ProfileParameters.rankError; positivity)
    (ProfileAnalysis.rank_bad_mean I p.toProfileParameters W)

omit [Nonempty C] [DecidableEq I.layer.Coin] in
include kQuery hquery hkQuery in
theorem low_raw_le (c : I.layer.Coin) (payload : I.layer.Payload) :
    (∑ b : C, if ¬rankBad I W c ∧ ¬p.error < fraction I σ W c payload ∧
      I.layer.verify σ W c payload (decodeQuery b) then (1 : ℚ) else 0) ≤
      Fintype.card C*p.error := by
  by_cases hb : rankBad I W c
  · simp [hb]; exact mul_nonneg (Nat.cast_nonneg _) p.error_nonneg
  by_cases hh : p.error < fraction I σ W c payload
  · simp [hh]; exact mul_nonneg (Nat.cast_nonneg _) p.error_nonneg
  · simp only [hb,not_false_eq_true,hh,true_and]
    exact (query_raw_le I decodeQuery kQuery hquery hkQuery σ W c payload).trans
      (mul_le_mul_of_nonneg_left (le_of_not_gt hh) (by positivity))

include kCoin kQuery hcoin hquery hkCoin hkQuery hfalse in
theorem high_raw_le :
    (∑ payload : I.layer.Payload, ∑ a : C, ∑ b : C,
      if ¬rankBad I W (decodeCoin a) ∧ p.error < fraction I σ W (decodeCoin a) payload ∧
        I.layer.verify σ W (decodeCoin a) payload (decodeQuery b) then (1 : ℚ) else 0) ≤
      (Fintype.card C : ℚ)^2*(highBudget I p) := by
  let mass := fun c : I.layer.Coin => if rankBad I W c then (0 : ℚ) else
    ∑ payload : I.layer.Payload, if p.error < fraction I σ W c payload
      then fraction I σ W c payload else 0
  have hmass c : 0 ≤ mass c := by
    dsimp [mass]
    split_ifs
    · exact le_rfl
    · apply sum_nonneg
      intro payload _
      split_ifs
      · unfold fraction; positivity
      · exact le_rfl
  have hc := balanced_sum_le decodeCoin kCoin hcoin hkCoin mass hmass
    (highBudget I p) (highBudget_nonneg I p) (high_mass_mean I p σ W hfalse)
  have hp a : (∑ payload : I.layer.Payload, ∑ b : C,
      if ¬rankBad I W (decodeCoin a) ∧ p.error < fraction I σ W (decodeCoin a) payload ∧
        I.layer.verify σ W (decodeCoin a) payload (decodeQuery b) then (1 : ℚ) else 0) ≤
      Fintype.card C*mass (decodeCoin a) := by
    by_cases hb : rankBad I W (decodeCoin a)
    · simp [mass,hb]
    · simp only [mass,hb,if_false,not_false_eq_true,true_and,mul_sum]
      apply sum_le_sum
      intro payload _
      by_cases hh : p.error < fraction I σ W (decodeCoin a) payload
      · simp only [hh,true_and,ite_true]
        exact query_raw_le I decodeQuery kQuery hquery hkQuery σ W (decodeCoin a) payload
      · simp [hh]
  calc
    _ = ∑ a : C, ∑ payload : I.layer.Payload, ∑ b : C,
      if ¬rankBad I W (decodeCoin a) ∧ p.error < fraction I σ W (decodeCoin a) payload ∧
        I.layer.verify σ W (decodeCoin a) payload (decodeQuery b) then (1 : ℚ) else 0 := sum_comm
    _ ≤ ∑ a : C, Fintype.card C*mass (decodeCoin a) := sum_le_sum (fun a _ => hp a)
    _ = Fintype.card C*∑ a : C, mass (decodeCoin a) := (mul_sum ..).symm
    _ ≤ Fintype.card C*(Fintype.card C*(highBudget I p)) := mul_le_mul_of_nonneg_left hc (by positivity)
    _ = _ := by ring
end Budgets
end RecursivePolygero.NonrecursiveFS
