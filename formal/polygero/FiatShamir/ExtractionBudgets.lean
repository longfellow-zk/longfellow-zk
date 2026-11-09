import polygero.FiatShamir.Budgets

/-! Raw-answer budgets for acceptance without a decoded witness. The statement
can depend on earlier transcript challenges and need not be false. -/

noncomputable section
namespace RecursivePolygero.NonrecursiveFS
open Finset ProfileAnalysis
open scoped Classical
attribute [local instance] Classical.propDecidable
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

theorem failure_query_mean (I : Instance F) (σ : I.layer.Statement) (W : I.layer.Oracle)
    (c : I.layer.Coin) (a : I.layer.Payload) :
    mean (fun Q => indicator (I.layer.verify σ W c a Q ∧ scanRecoverAt I σ W c a = none)) =
      failureFraction I σ W c a := by
  by_cases hn : scanRecoverAt I σ W c a = none
  · simpa only [hn, and_true, failureFraction, if_pos] using query_mean I σ W c a
  · simp [hn, failureFraction, indicator]

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

omit [Nonempty C] [DecidableEq I.layer.Coin] in
include kQuery hquery hkQuery in
theorem failure_query_raw_le (c : I.layer.Coin) (payload : I.layer.Payload) :
    (∑ b : C, if I.layer.verify σ W c payload (decodeQuery b) ∧
      scanRecoverAt I σ W c payload = none then (1 : ℚ) else 0) ≤
      Fintype.card C*failureFraction I σ W c payload := by
  have h := balanced_sum_le decodeQuery kQuery hquery hkQuery
    (fun Q => indicator (I.layer.verify σ W c payload Q ∧ scanRecoverAt I σ W c payload = none))
    (fun _ => indicator_nonneg _) (failureFraction I σ W c payload)
    (by unfold failureFraction fraction; split_ifs <;> positivity)
    (failure_query_mean I σ W c payload).le
  convert! h using 1
  apply sum_congr rfl
  intro b _
  unfold indicator
  split_ifs <;> rfl

include kCoin kQuery hcoin hquery hkCoin hkQuery in
theorem failure_fixed_response_raw_le (payload : I.layer.Payload) :
    (∑ a : C, ∑ b : C,
      if I.layer.verify σ W (decodeCoin a) payload (decodeQuery b) ∧
        scanRecoverAt I σ W (decodeCoin a) payload = none then (1 : ℚ) else 0) ≤
      (Fintype.card C : ℚ)^2*p.error := by
  have hc := balanced_sum_le decodeCoin kCoin hcoin hkCoin
    (fun c => failureFraction I σ W c payload)
    (by intro c; unfold failureFraction fraction; split_ifs <;> positivity)
    p.error p.error_nonneg (extraction_failure_mean_le I p σ W (fun _ => payload))
  calc
    _ ≤ ∑ a : C, Fintype.card C*failureFraction I σ W (decodeCoin a) payload :=
      sum_le_sum (fun a _ => failure_query_raw_le I decodeQuery kQuery hquery hkQuery σ W (decodeCoin a) payload)
    _ = Fintype.card C*∑ a : C, failureFraction I σ W (decodeCoin a) payload := (mul_sum ..).symm
    _ ≤ Fintype.card C*(Fintype.card C*p.error) := mul_le_mul_of_nonneg_left hc (by positivity)
    _ = _ := by ring

omit [Nonempty C] [DecidableEq I.layer.Coin] in
include kQuery hquery hkQuery in
theorem failure_low_raw_le (c : I.layer.Coin) (payload : I.layer.Payload) :
    (∑ b : C, if ¬rankBad I W c ∧ ¬p.error < fraction I σ W c payload ∧
      (I.layer.verify σ W c payload (decodeQuery b) ∧ scanRecoverAt I σ W c payload = none)
      then (1 : ℚ) else 0) ≤ Fintype.card C*p.error := by
  apply le_trans _ (low_raw_le I p decodeQuery kQuery hquery hkQuery σ W c payload)
  apply sum_le_sum
  intro b _
  by_cases hn : scanRecoverAt I σ W c payload = none
  · simp only [hn, and_true, le_refl]
  · simp only [hn, and_false, if_false]
    split_ifs <;> norm_num

include kCoin kQuery hcoin hquery hkCoin hkQuery in
theorem failure_high_raw_le :
    (∑ payload : I.layer.Payload, ∑ a : C, ∑ b : C,
      if ¬rankBad I W (decodeCoin a) ∧ p.error < fraction I σ W (decodeCoin a) payload ∧
        (I.layer.verify σ W (decodeCoin a) payload (decodeQuery b) ∧
          scanRecoverAt I σ W (decodeCoin a) payload = none) then (1 : ℚ) else 0) ≤
      (Fintype.card C : ℚ)^2*highBudget I p := by
  let mass := fun c : I.layer.Coin => if rankBad I W c then (0 : ℚ) else
    ∑ payload : I.layer.Payload, if scanRecoverAt I σ W c payload = none ∧
      p.error < fraction I σ W c payload then fraction I σ W c payload else 0
  have hmass c : 0 ≤ mass c := by
    dsimp [mass]
    split_ifs
    · exact le_rfl
    · apply sum_nonneg
      intro payload _
      split_ifs
      · unfold fraction; positivity
      · exact le_rfl
  have hmean : mean mass ≤ highBudget I p := by
    exact extraction_high_mass_mean I p σ W
  have hc := balanced_sum_le decodeCoin kCoin hcoin hkCoin mass hmass
    (highBudget I p) (highBudget_nonneg I p) hmean
  have hp a : (∑ payload : I.layer.Payload, ∑ b : C,
      if ¬rankBad I W (decodeCoin a) ∧ p.error < fraction I σ W (decodeCoin a) payload ∧
        (I.layer.verify σ W (decodeCoin a) payload (decodeQuery b) ∧
          scanRecoverAt I σ W (decodeCoin a) payload = none) then (1 : ℚ) else 0) ≤
      Fintype.card C*mass (decodeCoin a) := by
    by_cases hb : rankBad I W (decodeCoin a)
    · simp [mass, hb]
    simp only [mass, hb, if_false, not_false_eq_true, true_and, mul_sum]
    apply sum_le_sum
    intro payload _
    by_cases hn : scanRecoverAt I σ W (decodeCoin a) payload = none
    · by_cases hh : p.error < fraction I σ W (decodeCoin a) payload
      · simpa only [hn, hh, true_and, and_true, if_true, failureFraction] using
          failure_query_raw_le I decodeQuery kQuery hquery hkQuery σ W (decodeCoin a) payload
      · simp [hh]
    · simp [hn]
  calc
    _ = ∑ a : C, ∑ payload : I.layer.Payload, ∑ b : C,
      if ¬rankBad I W (decodeCoin a) ∧ p.error < fraction I σ W (decodeCoin a) payload ∧
        (I.layer.verify σ W (decodeCoin a) payload (decodeQuery b) ∧
          scanRecoverAt I σ W (decodeCoin a) payload = none) then (1 : ℚ) else 0 := sum_comm
    _ ≤ ∑ a : C, Fintype.card C*mass (decodeCoin a) := sum_le_sum (fun a _ => hp a)
    _ = Fintype.card C*∑ a : C, mass (decodeCoin a) := (mul_sum ..).symm
    _ ≤ Fintype.card C*(Fintype.card C*highBudget I p) := mul_le_mul_of_nonneg_left hc (by positivity)
    _ = _ := by ring

end Budgets
end RecursivePolygero.NonrecursiveFS
