import polygero.Algebra.Counting.RandomTarget

/-!
# A selection-safe random-target incidence bound

The interactive envelope takes a maximum over systems. First-hit FS
charging may instead need their summed excess mass. This theorem supplies
that stronger conclusion when the relevant fixed family has bounded total
excess. A family of at most `q` systems can use the existing capacity
certificate. No such bound is claimed for an arbitrary larger family.
-/

namespace RecursivePolygero.SystemException

open Finset ProfileAnalysis
open scoped Classical

/-- The rank event and the base are each paid once; only the excess carries
system multiplicity. `T` must be fixed before target and challenge sampling. -/
noncomputable def incidence {Z G I : Type*} (T : Finset I) (a : I → ℚ)
    (target : Z → I → Prop) (exceptional : Z → G → I → Prop)
    (bad : G → Prop) (theta : ℚ) (z : Z) (g : G) : ℚ :=
  indicator (bad g) + (1 - indicator (bad g)) * theta +
    ∑ i ∈ T, max 0 (a i - theta) * indicator (¬bad g ∧ (target z i ∨ exceptional z g i))

/-- Coverage turns the summed excess into a pointwise majorant of the
interactive maximum. This condition is independent of the size/capacity
condition used to bound its mean. -/
theorem envelope_le_incidence {Z G I : Type*} [Fintype I] [DecidableEq I]
    (T : Finset I) (a : I → ℚ) (target : Z → I → Prop)
    (exceptional : Z → G → I → Prop) (bad : G → Prop)
    (theta : ℚ) (z : Z) (g : G)
    (hcover : ∀ i, theta < a i → target z i ∨ exceptional z g i → i ∈ T) :
    envelope a (fun i => target z i ∨ exceptional z g i) (bad g) theta ≤
      incidence T a target exceptional bad theta z g := by
  by_cases hb : bad g
  · simp [envelope, incidence, indicator, hb]
  · simp only [envelope, incidence, indicator, hb, not_false_eq_true,
      true_and, if_false, sub_zero, one_mul, zero_add]
    have hn (i : I) : 0 ≤ max 0 (a i - theta) *
        (if target z i ∨ exceptional z g i then (1 : ℚ) else 0) := by
      split_ifs <;> positivity
    apply maximum_le
    · exact le_add_of_nonneg_right (sum_nonneg (fun i _ => hn i))
    · intro i hi
      by_cases hhigh : theta < a i
      · have hs := single_le_sum (s := T) (fun j _ => hn j) (hcover i hhigh hi)
        simp only [if_pos hi, mul_one, max_eq_right (sub_nonneg.mpr hhigh.le)] at hs
        linarith
      · exact (le_of_not_gt hhigh).trans (le_add_of_nonneg_right (sum_nonneg (fun j _ => hn j)))

/-- A bound on the whole relevant family's excess removes the witness-list
factor even after replacing the interactive maximum by an incidence sum. -/
theorem random_target_incidence_mean
    {Z G I : Type*} [Fintype Z] [Nonempty Z] [Fintype G] [Nonempty G]
    (T : Finset I) (a : I → ℚ) (target : Z → I → Prop)
    (exceptional : Z → G → I → Prop) (bad : G → Prop)
    (theta mu rate : ℚ) (q : ℕ) (hq : 0 < q)
    (htheta : theta ≤ 1) (hr0 : 0 ≤ rate) (hr1 : rate ≤ 1)
    (hmu : mu + 1 / (q : ℚ) ≤ 1)
    (hbad : mean (fun g => indicator (bad g)) ≤ mu)
    (htarget : ∀ i ∈ T, mean (fun z => indicator (target z i)) ≤ rate)
    (hexception : ∀ z i, i ∈ T → mean (fun g => indicator (exceptional z g i)) ≤ 1 / (q : ℚ))
    (hexcess : ∑ i ∈ T, max 0 (a i - theta) ≤ 1 - theta) :
    mean (fun z => mean (incidence T a target exceptional bad theta z)) ≤
      profile q mu theta + (1 - profile q mu theta) * rate := by
  let alpha := mean (fun g => indicator (bad g))
  let freq := (1 - alpha) * rate + (1 - rate) / (q : ℚ)
  have hqQ : (0 : ℚ) < q := by exact_mod_cast hq
  have halpha : alpha + 1 / (q : ℚ) ≤ 1 := by dsimp [alpha]; linarith
  have ha1 : alpha ≤ 1 := by
    have : (0 : ℚ) ≤ 1 / q := by positivity
    linarith
  have hf0 : 0 ≤ freq := by dsimp [freq]; positivity
  have hf (i : I) (hi : i ∈ T) :
      mean (fun z => mean (fun g => indicator (¬bad g ∧ (target z i ∨ exceptional z g i)))) ≤ freq := by
    simpa only [freq, alpha, mul_one_div] using
      target_gated_frequency (fun z => target z i) (fun z g => exceptional z g i)
        bad rate (1 / (q : ℚ)) (htarget i hi) (fun z => hexception z i hi)
        (by dsimp [alpha] at halpha; linarith)
  have hsum : mean (fun z => mean (fun g =>
      ∑ i ∈ T, max 0 (a i - theta) * indicator (¬bad g ∧ (target z i ∨ exceptional z g i)))) ≤
        (1 - theta) * freq := by
    simp_rw [mean_finset_sum, mean_mul_left]
    calc
      _ ≤ ∑ i ∈ T, max 0 (a i - theta) * freq :=
        sum_le_sum fun i hi => mul_le_mul_of_nonneg_left (hf i hi) (le_max_left _ _)
      _ = (∑ i ∈ T, max 0 (a i - theta)) * freq := (sum_mul ..).symm
      _ ≤ (1 - theta) * freq := mul_le_mul_of_nonneg_right hexcess hf0
  have hbase : mean (fun g => (1 - indicator (bad g)) * theta) = (1 - alpha) * theta := by
    simp_rw [mul_comm _ theta]
    rw [mean_mul_left, mean_sub, mean_const]
  unfold incidence
  simp_rw [mean_add, hbase, mean_const]
  have hm := mul_nonneg (sub_nonneg.mpr hbad)
    (mul_nonneg (sub_nonneg.mpr htheta) (sub_nonneg.mpr hr1))
  dsimp [freq, alpha] at hsum
  unfold profile
  dsimp [alpha]
  simp only [div_eq_mul_inv] at hsum ⊢
  nlinarith only [hsum, hm]

/-- The existing capacity certificate suffices for a fixed family with at
most `q` systems. The size premise is the additional FS fan-out obligation. -/
theorem random_target_incidence_mean_of_small_family
    {Z G I : Type*} [Fintype Z] [Nonempty Z] [Fintype G] [Nonempty G]
    (T : Finset I) (a : I → ℚ) (target : Z → I → Prop)
    (exceptional : Z → G → I → Prop) (bad : G → Prop)
    (theta mu rate : ℚ) (q : ℕ) (hq : 0 < q)
    (htheta : theta ≤ 1) (hr0 : 0 ≤ rate) (hr1 : rate ≤ 1)
    (hmu : mu + 1 / (q : ℚ) ≤ 1)
    (hbad : mean (fun g => indicator (bad g)) ≤ mu)
    (htarget : ∀ i ∈ T, mean (fun z => indicator (target z i)) ≤ rate)
    (hexception : ∀ z i, i ∈ T → mean (fun g => indicator (exceptional z g i)) ≤ 1 / (q : ℚ))
    (hT : T.card ≤ q)
    (hcapacity : ∀ S : Finset I, S.card ≤ q → ∑ i ∈ S, max 0 (a i - theta) ≤ 1 - theta) :
    mean (fun z => mean (incidence T a target exceptional bad theta z)) ≤
      profile q mu theta + (1 - profile q mu theta) * rate :=
  random_target_incidence_mean T a target exceptional bad theta mu rate q hq
    htheta hr0 hr1 hmu hbad htarget hexception (hcapacity T hT)

end RecursivePolygero.SystemException
