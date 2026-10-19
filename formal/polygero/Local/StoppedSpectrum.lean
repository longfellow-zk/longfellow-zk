import polygero.Local.WeightedExceptions
import Bcs.StoppedPotential

/-! Overlap-safe capacity spectra for exposed-parent stopping potentials.

The transform below is a concave majorant of the least repeatable-child
potential. Its subadditivity is essential: different reduced systems can
have the same exceptional challenge. These lemmas concern the conditional
exposed-parent process; they do not discharge arbitrary-order ROM queries.
-/
namespace RecursivePolygero.ProfileAnalysis.StoppedSpectrum

set_option maxHeartbeats 1000000

open Finset Bcs.StoppedPotential Codes LigeroFamily Local Local.Polygero Counting
open scoped Classical

/-- The linear continuation at `2 * rate` removes the convex corner of
`repeatPrice`. This retains its exact value above that point. -/
noncomputable def price (rate capacity : ℚ) : ℚ :=
  if capacity ≤ 2 * rate then capacity / (4 * rate) else 1 - rate / capacity

theorem price_nonneg (rate capacity : ℚ) (hr : 0 < rate) (hc : 0 ≤ capacity) :
    0 ≤ price rate capacity := by
  unfold price
  split_ifs with h
  · positivity
  · have hcp : 0 < capacity := by linarith
    have hd : rate / capacity ≤ 1 := (div_le_one hcp).mpr (by linarith)
    linarith

theorem price_zero (rate : ℚ) (hr : 0 < rate) : price rate 0 = 0 := by
  simp [price, show (0 : ℚ) ≤ 2 * rate by positivity]

theorem repeatPrice_le_price (rate capacity : ℚ) (hr : 0 < rate)
    (hc : 0 ≤ capacity) : repeatPrice rate capacity ≤ price rate capacity := by
  by_cases hz : capacity = 0
  · simp [hz, repeatPrice, price_zero rate hr]
  have hcp : 0 < capacity := lt_of_le_of_ne hc (Ne.symm hz)
  simp only [repeatPrice, if_neg hz]
  apply max_le (price_nonneg rate capacity hr hc)
  unfold price
  split_ifs with h
  · apply (le_div_iff₀ (show 0 < 4 * rate by positivity)).mpr
    have he : capacity * ((1 - rate / capacity) * (4 * rate)) =
        4 * rate * (capacity - rate) := by field_simp
    apply le_of_mul_le_mul_left (a := capacity) (b := (1 - rate / capacity) * (4 * rate))
      (c := capacity) ?_ hcp
    rw [he]
    nlinarith [sq_nonneg (capacity - 2 * rate)]
  · rfl

/-- A uniform low-capacity baseline consumes query rate, rather than a
positive potential at every fresh parent. In particular there is no
unconditional `price theta` term in the parent average. -/
theorem repeatPrice_baseline_le (rate baseline capacity : ℚ)
    (hb : 0 ≤ baseline) (hbr : baseline ≤ rate) (hc : 0 ≤ capacity) :
    repeatPrice rate (baseline + capacity) ≤ repeatPrice (rate-baseline) capacity := by
  apply repeatPrice_le_of_child (baseline+capacity)
    (repeatPrice (rate-baseline) capacity) rate (add_nonneg hb hc)
    (repeatPrice_nonneg _ _)
  have hchild := repeatPrice_child_step capacity (rate-baseline) hc (sub_nonneg.mpr hbr)
  nlinarith [mul_nonneg hb (repeatPrice_nonneg (rate-baseline) capacity)]

/-- Decreasing average price is the algebraic form of subadditivity.
The proof includes the mixed case across the linear/reciprocal seam. -/
theorem price_scale (rate x y : ℚ) (hr : 0 < rate)
    (hx : 0 ≤ x) (hxy : x ≤ y) : x * price rate y ≤ y * price rate x := by
  have hy : 0 ≤ y := hx.trans hxy
  unfold price
  split_ifs with hycut hxcut hxcut
  · ring_nf
    rfl
  · exfalso
    exact hxcut (hxy.trans hycut)
  · have hyp : 0 < y := by linarith
    rw [← mul_div_assoc]
    apply (le_div_iff₀ (show 0 < 4 * rate by positivity)).mpr
    have hsq := mul_nonneg hx (sq_nonneg (y - 2 * rate))
    have he₂ : y * (x * (1 - rate / y) * (4 * rate)) =
        4 * rate * x * (y - rate) := by field_simp
    have hmul : y * (x * (1 - rate / y) * (4 * rate)) ≤ y * (y * x) := by
      rw [he₂]
      nlinarith
    exact le_of_mul_le_mul_left hmul hyp
  · have hxp : 0 < x := by linarith
    have hyp : 0 < y := hxp.trans_le hxy
    have hprod : rate * (x + y) ≤ x * y := by
      have h₁ := mul_nonneg (show 0 ≤ x - 2 * rate by linarith)
        (show 0 ≤ y - rate by linarith)
      nlinarith
    have hh := mul_nonneg (sub_nonneg.mpr hxy) (sub_nonneg.mpr hprod)
    have he : (y * (1 - rate / x) - x * (1 - rate / y)) * (x * y) =
        (y - x) * (x * y - rate * (x + y)) := by field_simp; ring
    rw [← he] at hh
    exact sub_nonneg.mp ((mul_nonneg_iff_of_pos_right (mul_pos hxp hyp)).mp hh)

theorem price_add_le (rate x y : ℚ) (hr : 0 < rate)
    (hx : 0 ≤ x) (hy : 0 ≤ y) :
    price rate (x + y) ≤ price rate x + price rate y := by
  by_cases hz : x + y = 0
  · have hxx : x = 0 := by linarith
    have hyy : y = 0 := by linarith
    simp [hxx, hyy, price_zero rate hr]
  have hp : 0 < x + y := lt_of_le_of_ne (add_nonneg hx hy) (Ne.symm hz)
  have h₁ := price_scale rate x (x+y) hr hx (by linarith)
  have h₂ := price_scale rate y (x+y) hr hy (by linarith)
  apply le_of_mul_le_mul_left (a := x+y) (b := price rate (x+y))
    (c := price rate x + price rate y) ?_ hp
  nlinarith

theorem price_sum_le {D : Type} (T : Finset D) (capacity : D → ℚ)
    (rate : ℚ) (hr : 0 < rate) (hc : ∀ d ∈ T, 0 ≤ capacity d) :
    price rate (∑ d ∈ T, capacity d) ≤ ∑ d ∈ T, price rate (capacity d) := by
  induction T using Finset.induction_on with
  | empty => simp [price_zero rate hr]
  | @insert d T hd ih =>
    simp only [sum_insert hd]
    exact (price_add_le rate (capacity d) (∑ e ∈ T, capacity e) hr
      (hc d (mem_insert_self _ _))
      (sum_nonneg (fun e he => hc e (mem_insert_of_mem he)))).trans
      (add_le_add le_rfl (ih (fun e he => hc e (mem_insert_of_mem he))))

theorem price_le_one (rate capacity : ℚ) (hr : 0 < rate) (hc : 0 ≤ capacity) :
    price rate capacity ≤ 1 := by
  unfold price
  split_ifs with h
  · apply (div_le_one (show 0 < 4 * rate by positivity)).mpr
    linarith
  · have hcp : 0 < capacity := by linarith
    linarith [div_nonneg hr.le hc]

theorem price_mono (rate x y : ℚ) (hr : 0 < rate)
    (hx : 0 ≤ x) (hxy : x ≤ y) : price rate x ≤ price rate y := by
  have hy : 0 ≤ y := hx.trans hxy
  unfold price
  split_ifs with hxcut hycut hycut
  · exact div_le_div_of_nonneg_right hxy (by positivity)
  · have hyp : 0 < y := by linarith
    have h₁ : x / (4 * rate) ≤ 1/2 := by
      apply (div_le_iff₀ (show 0 < 4 * rate by positivity)).mpr
      linarith
    have h₂ : rate / y ≤ 1/2 := by
      apply (div_le_iff₀ hyp).mpr
      linarith
    linarith
  · exfalso
    exact hxcut (hxy.trans hycut)
  · have hxp : 0 < x := by linarith
    linarith [div_le_div_of_nonneg_left hr.le hxp hxy]

open Counting

theorem price_indicator (rate capacity : ℚ) (hr : 0 < rate) (E : Prop) :
    price rate (capacity * indicator E) = price rate capacity * indicator E := by
  by_cases h : E <;> simp [indicator, h, price_zero rate hr]

/-- The conditional parent price is bounded by one price for each system.
Exceptions may overlap arbitrarily; no uniqueness premise is used. -/
theorem repeatPrice_sum_indicator_le {D : Type} (T : Finset D)
    (capacity : D → ℚ) (E : D → Prop) (rate : ℚ) (hr : 0 < rate)
    (hc : ∀ d ∈ T, 0 ≤ capacity d) :
    repeatPrice rate (∑ d ∈ T, capacity d * indicator (E d)) ≤
      ∑ d ∈ T, price rate (capacity d) * indicator (E d) := by
  calc
    _ ≤ price rate (∑ d ∈ T, capacity d * indicator (E d)) :=
      repeatPrice_le_price _ _ hr
        (sum_nonneg (fun d hd => mul_nonneg (hc d hd) (indicator_nonneg _)))
    _ ≤ ∑ d ∈ T, price rate (capacity d * indicator (E d)) :=
      price_sum_le T _ rate hr (fun d hd => mul_nonneg (hc d hd) (indicator_nonneg _))
    _ = _ := sum_congr rfl (fun _ _ => price_indicator _ _ hr _)

/-- A generic tail certificate. Nonnegative weights on any number of
capacity cuts can be priced using cumulative tail cardinalities. -/
theorem sum_price_le_of_tail_majorant {D J : Type} (T : Finset D) (cuts : Finset J)
    (capacity : D → ℚ) (rate base : ℚ) (weight cutoff : J → ℚ) (bound : J → ℕ)
    (hw : ∀ j ∈ cuts, 0 ≤ weight j)
    (hmajor : ∀ d ∈ T, price rate (capacity d) ≤ base +
      ∑ j ∈ cuts, weight j * indicator (cutoff j < capacity d))
    (htail : ∀ j ∈ cuts, (T.filter (fun d => cutoff j < capacity d)).card ≤ bound j) :
    (∑ d ∈ T, price rate (capacity d)) ≤ T.card * base +
      ∑ j ∈ cuts, weight j * bound j := by
  calc
    _ ≤ ∑ d ∈ T, (base + ∑ j ∈ cuts, weight j *
        indicator (cutoff j < capacity d)) := sum_le_sum hmajor
    _ = T.card * base + ∑ j ∈ cuts, weight j *
        (T.filter (fun d => cutoff j < capacity d)).card := by
      rw [sum_add_distrib, sum_comm]
      congr 1
      · simp
      · apply sum_congr rfl
        intro j hj
        rw [← mul_sum]
        congr 1
        simp only [indicator]
        convert (@sum_boole D ℚ _ (fun d => cutoff j < capacity d)
          (fun _ => Classical.propDecidable _) T) using 1
        apply congrArg (fun S : Finset D => (S.card : ℚ))
        ext d
        simp
    _ ≤ _ := add_le_add le_rfl (sum_le_sum (fun j hj =>
      mul_le_mul_of_nonneg_left (by exact_mod_cast htail j hj) (hw j hj)))

/-- A finite layer-cake majorant. The threshold convention is strict on
each lower endpoint, so capacities equal to a cut are handled correctly. -/
theorem price_layers_le (rate : ℚ) (hr : 0 < rate) (level : ℕ → ℚ)
    (hlevel : Monotone level) (hzero : 0 ≤ level 0)
    (n : ℕ) (capacity : ℚ) (hc : 0 ≤ capacity) (hupper : capacity ≤ level n) :
    price rate capacity ≤ price rate (level 0) +
      ∑ i ∈ range n, (price rate (level (i+1)) - price rate (level i)) *
        indicator (level i < capacity) := by
  induction n with
  | zero => simpa using price_mono rate _ _ hr hc hupper
  | succ n ih =>
    by_cases h : capacity ≤ level n
    · rw [sum_range_succ]
      have hcoef : 0 ≤ price rate (level (n+1)) - price rate (level n) :=
        sub_nonneg.mpr (price_mono rate _ _ hr
          (hzero.trans (hlevel (by omega))) (hlevel (by omega)))
      have hterm := mul_nonneg hcoef (indicator_nonneg (level n < capacity))
      linarith [ih h]
    · have hind (i : ℕ) (hi : i ∈ range (n+1)) : indicator (level i < capacity) = 1 := by
        have hile : i ≤ n := by have := mem_range.mp hi; omega
        simp [indicator, (hlevel hile).trans_lt (lt_of_not_ge h)]
      have hsum : (∑ i ∈ range (n+1),
          (price rate (level (i+1)) - price rate (level i)) *
            indicator (level i < capacity)) =
          price rate (level (n+1)) - price rate (level 0) := by
        calc
          _ = ∑ i ∈ range (n+1), (price rate (level (i+1)) - price rate (level i)) :=
            sum_congr rfl (fun i hi => by rw [hind i hi, mul_one])
          _ = _ := sum_range_sub (fun i => price rate (level i)) (n+1)
      rw [hsum]
      linarith [price_mono rate _ _ hr hc hupper]

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

noncomputable def spectrum (I : Instance F) (p : HahnSystemCertificate I)
    (W : I.layer.Oracle) (rate : ℚ) : ℚ :=
  ∑ d ∈ highSystems I p W, price rate (systemCap I W d)

/-- A genuine stopped-price mean for Polygero's actual high-system
exceptions, stronger than their Boolean list cover. This is a local
Bellman input; the full ROM query-order bridge is a separate obligation. -/
theorem weightedExceptions_repeatPrice_mean_le (I : Instance F) (p : HahnSystemCertificate I)
    (sigma : I.layer.Statement) (W : I.layer.Oracle) (rate : ℚ) (hr : 0 < rate) :
    mean (fun coin => repeatPrice rate (weightedExceptions I p sigma W coin)) ≤
      spectrum I p W rate / Nat.card F := by
  calc
    _ ≤ mean (fun coin => ∑ d ∈ highSystems I p W, price rate (systemCap I W d) *
        indicator (coin ∈ systemExceptions p.positive_degree I.layout sigma d)) := by
      apply mean_mono
      intro coin
      exact repeatPrice_sum_indicator_le _ _ _ rate hr (fun d hd => by
        unfold systemCap
        positivity)
    _ = ∑ d ∈ highSystems I p W, price rate (systemCap I W d) *
        mean (fun coin => indicator
          (coin ∈ systemExceptions p.positive_degree I.layout sigma d)) := by
      rw [SystemException.mean_finset_sum]
      apply sum_congr rfl
      intro d hd
      exact mean_mul_left _ _
    _ ≤ ∑ d ∈ highSystems I p W, price rate (systemCap I W d) * (1 / Nat.card F) := by
      apply sum_le_sum
      intro d hd
      exact mul_le_mul_of_nonneg_left (systemExceptions_mean I p.toProfileParameters sigma W d)
        (price_nonneg _ _ hr (by unfold systemCap; positivity))
    _ = _ := by rw [← sum_mul]; unfold spectrum; ring

/-- The complete low-query baseline is absorbed in the slope before
pricing the high exceptions. This avoids a large baseline potential on
the overwhelmingly common nonexceptional parent challenges. -/
theorem baseline_weightedExceptions_repeatPrice_mean_le
    (I : Instance F) (p : HahnSystemCertificate I) (sigma : I.layer.Statement)
    (W : I.layer.Oracle) (rate baseline : ℚ) (hb : 0 ≤ baseline) (hbr : baseline < rate) :
    mean (fun coin => repeatPrice rate (baseline + weightedExceptions I p sigma W coin)) ≤
      spectrum I p W (rate-baseline) / Nat.card F := by
  calc
    _ ≤ mean (fun coin => repeatPrice (rate-baseline) (weightedExceptions I p sigma W coin)) := by
      apply mean_mono
      intro coin
      apply repeatPrice_baseline_le rate baseline _ hb hbr.le
      unfold weightedExceptions
      exact sum_nonneg (fun d hd => mul_nonneg (by unfold systemCap; positivity)
        (indicator_nonneg _))
    _ ≤ _ := weightedExceptions_repeatPrice_mean_le I p sigma W _ (sub_pos.mpr hbr)

/-- Conditional attempt-capacity majorant, including rank failure and a
uniform low-capacity baseline. This is a local majorant, not a concrete
ROM state machine. -/
noncomputable def conditionalCapacity (I : Instance F) (p : HahnSystemCertificate I)
    (sigma : I.layer.Statement) (W : I.layer.Oracle) (baseline : ℚ)
    (coin : I.layer.Coin) : ℚ :=
  if coin.2 ∈ ReducedSystems.badChallenges
      (LigeroFamily.PolynomialDirect.primaryCode I.domain I.primary_le)
      (oracleWords W.ordinary) W.proximityMask
  then 1 else baseline + weightedExceptions I p sigma W coin

/-- The exposed-parent Bellman price includes the rank term exactly once
at its fresh parent average. -/
theorem conditionalCapacity_repeatPrice_mean_le
    (I : Instance F) (p : HahnSystemCertificate I) (sigma : I.layer.Statement)
    (W : I.layer.Oracle) (rate baseline : ℚ) (hb : 0 ≤ baseline) (hbr : baseline < rate) :
    mean (fun coin => repeatPrice rate (conditionalCapacity I p sigma W baseline coin)) ≤
      p.toProfileParameters.rankError + spectrum I p W (rate-baseline) / Nat.card F := by
  have hr : 0 < rate := hb.trans_lt hbr
  let bad := fun coin : I.layer.Coin => coin.2 ∈ ReducedSystems.badChallenges
    (LigeroFamily.PolynomialDirect.primaryCode I.domain I.primary_le)
    (oracleWords W.ordinary) W.proximityMask
  calc
    _ ≤ mean (fun coin => indicator (bad coin) +
        repeatPrice rate (baseline + weightedExceptions I p sigma W coin)) := by
      apply mean_mono
      intro coin
      change repeatPrice rate (if bad coin then 1 else
        baseline + weightedExceptions I p sigma W coin) ≤ indicator (bad coin) +
          repeatPrice rate (baseline + weightedExceptions I p sigma W coin)
      by_cases h : bad coin
      · have hone : repeatPrice rate 1 ≤ 1 :=
          (repeatPrice_le_price rate 1 hr (by norm_num)).trans
            (price_le_one rate 1 hr (by norm_num))
        simpa only [if_pos h, indicator, if_pos h] using
          hone.trans (le_add_of_nonneg_right (repeatPrice_nonneg rate
            (baseline + weightedExceptions I p sigma W coin)))
      · simp [h, indicator]
    _ = mean (fun coin => indicator (bad coin)) +
        mean (fun coin => repeatPrice rate (baseline + weightedExceptions I p sigma W coin)) :=
      mean_add _ _
    _ ≤ _ := add_le_add (rank_bad_mean I p.toProfileParameters W)
      (baseline_weightedExceptions_repeatPrice_mean_le I p sigma W rate baseline hb hbr)

/-- A larger-cut Hahn certificate controls every tail of the spectrum.
No matching or disjointness of exceptional challenges is required. -/
theorem spectrum_tail_card_le (I : Instance F) (p p' : HahnSystemCertificate I)
    (hsmall : p'.listBound < Nat.card F) (W : I.layer.Oracle) :
    ((highSystems I p W).filter (fun d => p'.threshold < systemCap I W d)).card ≤
      p'.listBound := by
  apply le_trans (card_le_card ?_) (highSystems_card_le I p' hsmall W)
  intro d hd
  exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hd).2⟩

/-- A tail only needs a combinatorial list certificate; it does not need
a new Hahn excess certificate at that cut. This lets integer-occupancy
tails plug directly into the stopped spectrum. -/
theorem systemCap_tail_card_le_of_uniformFamilyBound
    (I : Instance F) (p : HahnSystemCertificate I) (W : I.layer.Oracle)
    (T : Finset (systems I.domain I.primary_le W)) (cutoff bound : ℕ)
    (hcut : p.overlapSize < cutoff)
    (hb : CodingTheory.UniformFamilyBound I.n cutoff p.overlapSize bound)
    (hhigh : ∀ d ∈ T, (Nat.choose (cutoff-1) I.t : ℚ) / Nat.choose I.n I.t < systemCap I W d) :
    T.card ≤ bound := by
  let E := fun d : systems I.domain I.primary_le W =>
    Classical.choose (ReducedSystems.capacity_witness
      (LigeroFamily.PolynomialDirect.primaryCode I.domain I.primary_le)
      (oracleWords W.ordinary) W.proximityMask d.1 d.2)
  have hs (d : systems I.domain I.primary_le W) :=
    Classical.choose_spec (ReducedSystems.capacity_witness
      (LigeroFamily.PolynomialDirect.primaryCode I.domain I.primary_le)
      (oracleWords W.ordinary) W.proximityMask d.1 d.2)
  apply DirectBinomial.active_card_le_of_uniformFamilyBound T E cutoff p.overlapSize bound
    hcut _ _ hb
  · intro d hd
    have hh := hhigh d hd
    unfold systemCap at hh
    rw [show Fintype.card I.layer.Query = I.n.choose I.t from QuerySet.fintype_card _ _] at hh
    have hsize := DirectBinomial.size_ge_of_choose_div_gt (Nat.choose_pos I.query_le) le_rfl hh
    exact (hs d).2 ▸ hsize
  · intro d hd e he hne
    exact ReducedSystems.associated_intersection
      (LigeroFamily.PolynomialDirect.primaryCode I.domain I.primary_le)
      (oracleWords W.ordinary) W.proximityMask p.positive_degree d.1 e.1 (E d) (E e)
      (hs d).1 (hs e).1 (fun h => hne (Subtype.ext h))

/-- Any certified cumulative tail list bounds give a certified capacity
spectrum. `level n ≥ 1` covers every actual system capacity. -/
theorem spectrum_layers_le (I : Instance F) (p : HahnSystemCertificate I)
    (hsmall : p.listBound < Nat.card F) (W : I.layer.Oracle)
    (rate : ℚ) (hr : 0 < rate) (level : ℕ → ℚ)
    (hlevel : Monotone level) (hzero : 0 ≤ level 0) (n : ℕ) (hfinal : 1 ≤ level n)
    (bound : ℕ → ℕ)
    (htail : ∀ i ∈ range n,
      ((highSystems I p W).filter (fun d => level i < systemCap I W d)).card ≤ bound i) :
    spectrum I p W rate ≤ p.listBound * price rate (level 0) +
      ∑ i ∈ range n, (price rate (level (i+1)) - price rate (level i)) * bound i := by
  have hcap (d) : 0 ≤ systemCap I W d ∧ systemCap I W d ≤ 1 := by
    refine ⟨by unfold systemCap; positivity, ?_⟩
    unfold systemCap
    rw [show Fintype.card I.layer.Query = I.n.choose I.t from QuerySet.fintype_card _ _]
    apply (div_le_one (by exact_mod_cast Nat.choose_pos I.query_le)).mpr
    exact_mod_cast Nat.choose_le_choose I.t (ReducedSystems.capacity_le_n
      (LigeroFamily.PolynomialDirect.primaryCode I.domain I.primary_le)
      (oracleWords W.ordinary) W.proximityMask d.1)
  have hmain := sum_price_le_of_tail_majorant (highSystems I p W) (range n)
    (systemCap I W) rate (price rate (level 0))
    (fun i => price rate (level (i+1)) - price rate (level i)) level bound
    (fun i hi => sub_nonneg.mpr (price_mono rate _ _ hr
      (hzero.trans (hlevel (by omega))) (hlevel (by omega))))
    (fun d hd => price_layers_le rate hr level hlevel hzero n (systemCap I W d)
      (hcap d).1 ((hcap d).2.trans hfinal)) htail
  have hc : ((highSystems I p W).card : ℚ) ≤ p.listBound := by
    exact_mod_cast highSystems_card_le I p hsmall W
  exact hmain.trans (add_le_add (mul_le_mul_of_nonneg_right hc
    (price_nonneg _ _ hr hzero)) le_rfl)

/-- Two certified list cuts already improve the Boolean `L/|F|` price.
More cuts can use `sum_price_le_of_tail_majorant` without changing the
overlap argument. -/
theorem spectrum_two_cuts_le (I : Instance F) (p p' : HahnSystemCertificate I)
    (hsmall : p.listBound < Nat.card F) (hsmall' : p'.listBound < Nat.card F)
    (W : I.layer.Oracle) (rate : ℚ) (hr : 0 < rate) :
    spectrum I p W rate ≤ p.listBound * price rate p'.threshold +
      p'.listBound * (1 - price rate p'.threshold) := by
  let T := highSystems I p W
  let b := price rate p'.threshold
  have hb : 0 ≤ b := price_nonneg _ _ hr p'.threshold_nonneg
  have hb' : b ≤ 1 := price_le_one _ _ hr p'.threshold_nonneg
  have hlocal (d) (hd : d ∈ T) : price rate (systemCap I W d) ≤
      b + (1-b) * indicator (p'.threshold < systemCap I W d) := by
    by_cases h : p'.threshold < systemCap I W d
    · simp only [indicator, if_pos h, mul_one]
      have hcap : 0 ≤ systemCap I W d := by unfold systemCap; positivity
      linarith [price_le_one rate (systemCap I W d) hr hcap]
    · simp only [indicator, if_neg h, mul_zero, add_zero]
      exact price_mono rate _ _ hr (by unfold systemCap; positivity) (le_of_not_gt h)
  have ht := sum_price_le_of_tail_majorant T ({()} : Finset Unit) (systemCap I W) rate b
    (fun _ => 1-b) (fun _ => p'.threshold) (fun _ => p'.listBound)
    (fun _ _ => by linarith) (fun d hd => by simpa using hlocal d hd)
    (fun _ _ => spectrum_tail_card_le I p p' hsmall' W)
  have hc : (T.card : ℚ) ≤ p.listBound := by
    exact_mod_cast highSystems_card_le I p hsmall W
  change (∑ d ∈ T, price rate (systemCap I W d)) ≤ _
  simp only [sum_singleton] at ht
  calc
    _ ≤ T.card * b + (1-b) * p'.listBound := ht
    _ ≤ p.listBound * b + (1-b) * p'.listBound :=
      add_le_add (mul_le_mul_of_nonneg_right hc hb) le_rfl
    _ = _ := by dsimp [b]; ring

/-- A capacity-spectrum certificate pays the best-parent search step of
the exposed-parent Bellman model. The caller still must connect the ROM
query process to that model, including reverse query order. -/
theorem weightedExceptions_fresh_parent_best_step
    (I : Instance F) (p : HahnSystemCertificate I) (sigma : I.layer.Statement)
    (W : I.layer.Oracle) (rate current : ℚ) (hr : 0 < rate) (hcurrent : 0 ≤ current)
    (hspectrum : spectrum I p W rate / Nat.card F ≤ rate) :
    Bcs.TotalOracle.Footprint.average (fun coin => max current
      (repeatPrice rate (weightedExceptions I p sigma W coin))) ≤ current + rate := by
  apply fresh_parent_best_step _ rate current hcurrent
  exact (weightedExceptions_repeatPrice_mean_le I p sigma W rate hr).trans hspectrum

/-- Correct fresh-parent obligation with the baseline and rank term.
This still concerns an exposed-parent search model. -/
theorem conditionalCapacity_fresh_parent_best_step
    (I : Instance F) (p : HahnSystemCertificate I) (sigma : I.layer.Statement)
    (W : I.layer.Oracle) (rate baseline current : ℚ)
    (hb : 0 ≤ baseline) (hbr : baseline < rate) (hcurrent : 0 ≤ current)
    (hspectrum : p.toProfileParameters.rankError +
      spectrum I p W (rate-baseline) / Nat.card F ≤ rate) :
    Bcs.TotalOracle.Footprint.average (fun coin => max current
      (repeatPrice rate (conditionalCapacity I p sigma W baseline coin))) ≤ current + rate := by
  apply fresh_parent_best_step _ rate current hcurrent
  exact (conditionalCapacity_repeatPrice_mean_le I p sigma W rate baseline hb hbr).trans hspectrum

end RecursivePolygero.ProfileAnalysis.StoppedSpectrum
