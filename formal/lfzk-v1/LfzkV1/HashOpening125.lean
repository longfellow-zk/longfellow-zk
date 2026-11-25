import LfzkV1.LigeroHighMass125V7
import LfzkV1.TwoFieldV1Rows
import LfzkV1.ZkPotentialBalance

/-! Opening probabilities for the smaller of the two v7 hash lifts. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LfzkV1.HashOpening125

open Finset LigeroFamily CodingTheory LfzkV1.LigeroHighMass125
open LfzkV1.LiftOpening125
open scoped Classical

private abbrev cert (i : Fin 4) := (OpeningGeometry125.result i).certificate
private abbrev liftRadius (i : Fin 4) := (cert i).e + (cert i).g
private abbrev v7Query (i : Fin 4) := QuerySet (cert i).n (cert i).openings

private theorem opening_pos (i : Fin 4) : 0 < (cert i).n.choose (cert i).openings := by
  apply Nat.choose_pos
  fin_cases i <;> decide +kernel

private theorem secondarySize_eq (i : Fin 4) :
    ((cert i).n + ((cert i).n - (cert i).d)) / 2 = OpeningGeometry125.secondarySize i := by
  fin_cases i <;> decide +kernel

private theorem agreementCap_eq (i : Fin 4) :
    (cert i).n - (cert i).d = (cert i).k - 1 := by
  fin_cases i <;> decide +kernel

private theorem ratio_le_power {a b p : ℕ} (hb : 0 < b) (h : 2 ^ p * a ≤ b) :
    (a : ℚ) / b ≤ 1 / 2 ^ p := by
  rw [div_le_div_iff₀ (by exact_mod_cast hb) (by positivity), one_mul, mul_comm]
  exact_mod_cast h

variable {F E : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype E] [DecidableEq E]
variable {w nw nq : ℕ} (i : Fin 4)
variable {C : MultiplicativeCode F (cert i).openings w (cert i).n}
variable {oracle : Ligero.V1.Oracle F nw nq (cert i).n 1}

local notation "Lift" => SchemeLiftCandidate C oracle (liftRadius i)
local notation "Query" => v7Query i

/-- The opened columns choose at most one compatible lift outside this tail. -/
theorem ambiguousRate_le (hmin : HasMinimumDistanceAtLeast C.baseCode (cert i).d)
    (hcard : Fintype.card Lift ≤ 2) :
    ((univ.filter fun q : Query =>
      ∃ x y : Lift, x ≠ y ∧ Compatible x q (cert i).g ∧ Compatible y q (cert i).g).card : ℚ) /
      (cert i).n.choose (cert i).openings ≤ 1 / 2 ^ 202 := by
  apply ratio_le_power (opening_pos i)
  have h := card_ambiguous_le agreement (fun x q => Compatible x q (cert i).g)
    (cert i).g ((cert i).n - (cert i).d) hcard
    (fun _ _ hne => agreement_inter_card_le hmin hne)
    (fun _ _ _ hx hy => common_openings_of_compatible hx hy)
  rw [agreementCap_eq] at h
  exact (Nat.mul_le_mul_left _ h).trans (OpeningGeometry125.ambiguousTail i)

/-- When the opening precedes the initial draw, it already needs almost
all its positions to agree with the fixed secondary lift. -/
theorem secondaryCompatibleRate_le (hmin : HasMinimumDistanceAtLeast C.baseCode (cert i).d)
    (x : Lift) (hsecondary : primary C oracle ((cert i).e + (cert i).g) ≠ some x) :
    ((univ.filter fun q : Query => Compatible x q (cert i).g).card : ℚ) /
      (cert i).n.choose (cert i).openings ≤ 1 / 2 ^ 32 := by
  have hx := secondary_of_ne_primary hmin x hsecondary
  rw [secondarySize_eq] at hx
  let b := (cert i).openings - (cert i).g
  have hsub : (univ.filter fun q : Query => Compatible x q (cert i).g) ⊆
      univ.filter fun q => b ≤ (q.coordinates ∩ agreement x).card := by
    intro q hq
    have hcomp : (q.coordinates \ agreement x).card ≤ (cert i).g := (mem_filter.mp hq).2
    have hsplit := card_sdiff_add_card_inter q.coordinates (agreement x)
    rw [QuerySet.card_coordinates] at hsplit
    exact mem_filter.mpr ⟨mem_univ _, by dsimp [b]; omega⟩
  have hcount := (card_le_card hsub).trans (card_manyInside_le (agreement x))
  have hcap := Nat.mul_le_mul_right (((cert i).n - b).choose ((cert i).openings - b))
    (Nat.choose_le_choose b hx)
  apply ratio_le_power (opening_pos i)
  exact (Nat.mul_le_mul_left _ (hcount.trans hcap)).trans (OpeningGeometry125.openingFirstTail i)

variable (statement : ConstraintSystem F nw nq w E)
variable {ch : SchemeChallenge F NoMask nw nq 1 E}
variable {u v : Response F (cert i).openings w (cert i).n 1}

/-- Outside the three terminal exceptions, the opened columns select a
single lift and that lift satisfies the sampled statement. -/
theorem selected_lift_of_accepts (hmin : HasMinimumDistanceAtLeast C.baseCode (cert i).d)
    {query : Query}
    (hpass : SchemeVerifier.Accepts C Ligero.V1.scheme statement ch u query (openSchemeOracle oracle query))
    (hhigh : highCutoff i ≤ (columns (C := C) oracle statement ch u).card)
    (hgood : u ∉ badHighResponses (C := C) oracle statement (highCutoff i) (cert i).e (cert i).g ch)
    (hunique : ¬ ∃ x y : Lift, x ≠ y ∧ Compatible x query (cert i).g ∧ Compatible y query (cert i).g) :
    ∃ x : Lift, statement.Satisfies x.decodedMessages ∧ Compatible x query (cert i).g ∧
      u ∈ liftedResponses statement x (highCutoff i) (cert i).g ch ∧
      ∀ y : Lift, Compatible y query (cert i).g → x = y := by
  have ha : (cert i).n - (cert i).e ≤ highCutoff i := by fin_cases i <;> decide +kernel
  have hd : (cert i).e + (cert i).g < (cert i).d := by fin_cases i <;> decide +kernel
  have hmem : u ∈ policyResponseAgreementList (SchemeVerifier.policy C Ligero.V1.scheme)
      oracle statement ch (highCutoff i) :=
    mem_filter.mpr ⟨mem_univ _, ⟨query, hpass⟩, hhigh⟩
  obtain ⟨x, hs, hprox, hrem⟩ :=
    satisfying_lift_of_not_mem_badHighResponses oracle statement hmin hd ha hmem hgood
  have hcomp := compatible_of_remainingBadColumns (hpass 0).1 hrem
  refine ⟨x, hs, hcomp, mem_filter.mpr ⟨hmem, hprox, hrem⟩, ?_⟩
  intro y hy
  by_contra hne
  exact hunique ⟨x, y, hne, hcomp, hy⟩

theorem secondaryResponse_unique (hmin : HasMinimumDistanceAtLeast C.baseCode (cert i).d)
    (hk : C.k = (cert i).k) (x : Lift)
    (hsecondary : primary C oracle ((cert i).e + (cert i).g) ≠ some x)
    (hu : u ∈ liftedResponses statement x (highCutoff i) (cert i).g ch)
    (hv : v ∈ liftedResponses statement x (highCutoff i) (cert i).g ch) : u = v := by
  apply liftedResponse_unique statement x _ hu hv
  have hsize := secondary_of_ne_primary hmin x hsecondary
  rw [secondarySize_eq] at hsize
  rw [hk, highCutoff, Nat.add_sub_cancel]
  exact (Nat.add_le_add_right hsize _).trans_lt (OpeningGeometry125.uniqueHighResponse i)

/-- After a canonical field continuation and its batch have fixed a response,
the fresh opening has this stronger tail. -/
theorem secondaryResponse_openingRate_le (hmin : HasMinimumDistanceAtLeast C.baseCode (cert i).d)
    (x : Lift) (hsecondary : primary C oracle ((cert i).e + (cert i).g) ≠ some x)
    (hu : u ∈ liftedResponses statement x (highCutoff i) (cert i).g ch) :
    openingRate (C := C) oracle statement ch u ≤ 1 / 2 ^ 108 := by
  have hsize := secondary_of_ne_primary hmin x hsecondary
  rw [secondarySize_eq] at hsize
  have hsub : offsetColumns x (offsetOf statement x ch u) ⊆ agreement x := inter_subset_left
  have hcount := columns_le_offsetColumns_add statement x hu
  have htotal : (columns (C := C) oracle statement ch u).card ≤
      OpeningGeometry125.secondarySize i + (cert i).g := by
    have := card_le_card hsub
    have := min_le_left (cert i).g x.badColumns.card
    omega
  refine (fixed_response_opening_density (C := C) oracle statement ch u).trans ?_
  unfold hypergeometricRatio
  apply ratio_le_power (opening_pos i)
  exact (Nat.mul_le_mul_left _ (Nat.choose_le_choose _ htotal)).trans
    (OpeningGeometry125.initialFirstTail i)

section RawQuery

open LfzkV1.TwoFieldV1Rows (ExactDecoder)
attribute [local instance 10000] Classical.propDecidable

variable {Answer : Type} [Fintype Answer]

private theorem decoded_opening_count_le (d : ExactDecoder Answer Query)
    (event : Query → Prop) (ρ : ℚ) (hρ : 0 ≤ ρ)
    (hmean : ((univ.filter event).card : ℚ) / (cert i).n.choose (cert i).openings ≤ ρ) :
    ∑ a : Answer, (if event (d.decode a) then (1 : ℚ) else 0) ≤ Fintype.card Answer * ρ := by
  have hq : 0 < Fintype.card Query := by rw [QuerySet.fintype_card]; exact opening_pos i
  letI : Nonempty Query := Fintype.card_pos_iff.mp hq
  have hcap : (d.k : ℚ) * Fintype.card Query ≤ Fintype.card Answer := by exact_mod_cast d.hexact
  have h := ZkPotentialBalance.decoded_query_charge_le d.decode event 1 zero_le_one d.k d.hbal ρ
    (by simpa only [one_mul, QuerySet.fintype_card] using hmean)
  exact h.trans (mul_le_mul_of_nonneg_right hcap hρ)

theorem ambiguous_decoded_le (d : ExactDecoder Answer Query)
    (hmin : HasMinimumDistanceAtLeast C.baseCode (cert i).d)
    (hcard : Fintype.card Lift ≤ 2) :
    (∑ a : Answer, if ∃ x y : Lift, x ≠ y ∧ Compatible x (d.decode a) (cert i).g ∧
      Compatible y (d.decode a) (cert i).g then (1 : ℚ) else 0) ≤ Fintype.card Answer * (1 / 2 ^ 202) := by
  exact decoded_opening_count_le i d (fun q : Query =>
    ∃ x y : Lift, x ≠ y ∧ Compatible x q (cert i).g ∧ Compatible y q (cert i).g)
    (1 / 2 ^ 202) (by positivity) (by
      convert ambiguousRate_le (C := C) (oracle := oracle) i hmin hcard using 2
      apply congrArg (fun s : Finset Query => (s.card : ℚ))
      ext q
      simp)

theorem secondaryCompatible_decoded_le (d : ExactDecoder Answer Query)
    (hmin : HasMinimumDistanceAtLeast C.baseCode (cert i).d)
    (x : Lift) (hsecondary : primary C oracle (liftRadius i) ≠ some x) :
    ∑ a : Answer, (if Compatible x (d.decode a) (cert i).g then (1 : ℚ) else 0) ≤
      Fintype.card Answer * (1 / 2 ^ 32) :=
  decoded_opening_count_le i d _ _ (by positivity) (secondaryCompatibleRate_le i hmin x hsecondary)

theorem secondaryResponse_decoded_le (d : ExactDecoder Answer Query)
    (hmin : HasMinimumDistanceAtLeast C.baseCode (cert i).d)
    (x : Lift) (hsecondary : primary C oracle (liftRadius i) ≠ some x)
    (hu : u ∈ liftedResponses statement x (highCutoff i) (cert i).g ch) :
    ∑ a : Answer, (if SchemeVerifier.Accepts C Ligero.V1.scheme statement ch u (d.decode a)
      (openSchemeOracle oracle (d.decode a)) then (1 : ℚ) else 0) ≤
      Fintype.card Answer * (1 / 2 ^ 108) :=
  decoded_opening_count_le i d _ _ (by positivity)
    (secondaryResponse_openingRate_le i statement hmin x hsecondary hu)

end RawQuery

end LfzkV1.HashOpening125
