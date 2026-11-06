import LfzkV2.Current.JointResponse
import polygero.FiatShamir.Nonrecursive

/-! Summed mass of complete joint responses whose extraction fails. The
parent answer samples both fields' coins; the child answer samples one set
of columns. The proof uses a union bound only for system exceptions, never
for two supposedly independent opening events. -/
noncomputable section
namespace LfzkV2.Current.JointResponse
open RecursivePolygero LigeroFamily Finset Local Local.Polygero ProfileAnalysis Counting
open scoped Classical

private theorem mean_pair_add {A B : Type} [Fintype A] [Fintype B] [Nonempty A] [Nonempty B]
    (f : A → ℚ) (g : B → ℚ) :
    mean (fun c : A × B => f c.1 + g c.2) = mean f + mean g := by
  rw [mean_prod]
  simp only [mean_add, mean_const]

variable {k s n t : ℕ} (P R : Joint.Participant k s n t)

theorem capacity_excess (S : Joint.Participant k s n t) (p : HahnSystemCertificate S.backend)
    (W : Oracle P R) (T : Finset (Label P R W)) (hT : T.card ≤ Nat.card S.Carrier) :
    ∑ d ∈ T, max 0 (capacity P R W d-p.threshold) ≤ 1-p.threshold := by
  have hk : 1 ≤ k := by simpa only [S.dimension] using p.positive_degree
  apply JointFamilies.capacity_excess (P.associated W.1) (R.associated W.2)
    (overlap := k+2*s-1) (q := Nat.card S.Carrier)
    (cutoff := p.columnCutoff) (bound := p.listBound)
    (by simpa only [S.columns, S.openings] using Nat.choose_pos S.backend.query_le)
    p.threshold_lt_one.le
    (by simpa only [ProfileParameters.overlapSize, S.dimension, S.batching] using p.overlap_lt_cutoff)
    (by simpa only [ProfileParameters.columnFloorAt, S.columns, S.openings] using p.floor_le)
    (P.associated_overlap hk W.1) (R.associated_overlap hk W.2)
    (by simpa only [ProfileParameters.overlapSize, S.dimension, S.batching, S.columns] using p.active_bound)
    (by simpa only [ProfileParameters.overlapSize, S.dimension, S.batching, S.columns,
      S.openings] using p.excess_condition) T hT

private theorem capacity_gap (S : Joint.Participant k s n t) (p : HahnSystemCertificate S.backend)
    (ε : ℚ) (hε : p.error ≤ ε) :
    1-p.threshold ≤ (Nat.card S.Carrier : ℚ)*(ε-p.threshold) := by
  have hq : (0 : ℚ) < Nat.card S.Carrier := by exact_mod_cast Nat.card_pos (α := S.Carrier)
  have hgap := (div_le_iff₀ hq).mp (NonrecursiveFS.error_gap S.backend p)
  nlinarith

/-- The complete joint high-capacity label set has fewer than the chosen
field's cardinality. This is a bound on all joint labels, before either
field's exceptional coins are tested, so the same set is used for both. -/
theorem capacity_high_card_lt (S : Joint.Participant k s n t) (p : HahnSystemCertificate S.backend)
    (W : Oracle P R) (ε : ℚ) (hε : p.error ≤ ε) :
    (univ.filter fun d : Label P R W => ε < capacity P R W d).card < Nat.card S.Carrier :=
  RestrictedExcess.above_threshold_card_lt (capacity P R W) (Nat.card S.Carrier) Nat.card_pos
    p.threshold ε (capacity_gap S p ε hε) (capacity_excess P R S p W)

theorem capacity_high_mass (S : Joint.Participant k s n t) (p : HahnSystemCertificate S.backend)
    (W : Oracle P R) (ε : ℚ) (hε : p.error ≤ ε) :
    (∑ d : Label P R W, if ε < capacity P R W d then capacity P R W d else 0) ≤
      1-p.threshold+((Nat.card S.Carrier : ℚ)-1)*p.threshold := by
  rw [← sum_filter]
  exact RestrictedExcess.high_mass_of_restricted (capacity P R W) (Nat.card S.Carrier) Nat.card_pos
    p.threshold ε p.threshold_nonneg ((NonrecursiveFS.threshold_le_error S.backend p).trans hε)
    (capacity_gap S p ε hε) (capacity_excess P R S p W)

/-- Every high-capacity joint label has an actual common set reaching the
active cutoff. A uniform family certificate therefore bounds the complete
label set, rather than a projection or an assumed number of response pairs. -/
theorem capacity_high_card_le_active (S : Joint.Participant k s n t)
    (p : HahnSystemCertificate S.backend) (W : Oracle P R) (ε : ℚ) (hθ : p.threshold ≤ ε)
    (hactive : CodingTheory.UniformFamilyBound n p.columnCutoff (k+2*s-1) p.listBound) :
    (univ.filter fun d : Label P R W => ε < capacity P R W d).card ≤ p.listBound := by
  let D := JointFamilies.capacitySet (P.associated W.1) (R.associated W.2)
  have hk : 1 ≤ k := by simpa only [S.dimension] using p.positive_degree
  have hoverlap : k+2*s-1 < p.columnCutoff := by
    simpa only [ProfileParameters.overlapSize, S.dimension, S.batching] using p.overlap_lt_cutoff
  have hfloor : (((p.columnCutoff-1).choose t : ℚ)/n.choose t) ≤ p.threshold := by
    simpa only [ProfileParameters.columnFloorAt, S.columns, S.openings] using p.floor_le
  apply DirectBinomial.active_card_le_of_uniformFamilyBound _ D p.columnCutoff (k+2*s-1)
    p.listBound hoverlap ?_ ?_ hactive
  · intro d hd
    have hgt := hθ.trans_lt (mem_filter.mp hd).2
    have hsize := DirectBinomial.size_ge_of_choose_div_gt
      (show 0 < n.choose t by simpa only [S.columns, S.openings] using Nat.choose_pos S.backend.query_le)
      hfloor hgt
    simpa only [D, (JointFamilies.capacitySet_spec (P.associated W.1) (R.associated W.2) d).2]
      using hsize
  · intro d _ e _ hne
    exact associated_overlap P R hk W d e _ _
      (JointFamilies.capacitySet_spec (P.associated W.1) (R.associated W.2) d).1
      (JointFamilies.capacitySet_spec (P.associated W.1) (R.associated W.2) e).1 hne

/-- Restricted excess applies to the whole active joint family because its
actual size is at most the certified list bound, and that bound is at most q.
No raised `1/q` baseline is needed for this finite-family route. -/
theorem capacity_high_mass_active (S : Joint.Participant k s n t)
    (p : HahnSystemCertificate S.backend) (W : Oracle P R) (ε : ℚ) (hθ : p.threshold ≤ ε)
    (hactive : CodingTheory.UniformFamilyBound n p.columnCutoff (k+2*s-1) p.listBound)
    (hbound : p.listBound ≤ Nat.card S.Carrier) :
    (∑ d : Label P R W, if ε < capacity P R W d then capacity P R W d else 0) ≤
      1-p.threshold+(p.listBound : ℚ)*p.threshold := by
  let T := univ.filter fun d : Label P R W => ε < capacity P R W d
  have hc : T.card ≤ p.listBound := capacity_high_card_le_active P R S p W ε hθ hactive
  have he := capacity_excess P R S p W T (hc.trans hbound)
  have hs : (∑ d ∈ T, max 0 (capacity P R W d-p.threshold)) =
      (∑ d ∈ T, capacity P R W d)-(T.card : ℚ)*p.threshold := by
    calc
      _ = ∑ d ∈ T, (capacity P R W d-p.threshold) := by
        apply sum_congr rfl
        intro d hd
        exact max_eq_right (by have := (mem_filter.mp hd).2; linarith)
      _ = _ := by simp only [sum_sub_distrib, sum_const, nsmul_eq_mul]
  have hm := mul_le_mul_of_nonneg_right (show (T.card : ℚ) ≤ p.listBound by exact_mod_cast hc)
    p.threshold_nonneg
  rw [← sum_filter]
  change ∑ d ∈ T, capacity P R W d ≤ _
  rw [hs] at he
  linarith

private theorem high_assignment (p : ProfileParameters P.backend) (r : ProfileParameters R.backend)
    (σ : Statement P R) (W : Oracle P R) (c : Coin P R) (hb : ¬ rankBad P R W c)
    (ε : ℚ) (hε : 0 ≤ ε) (hp : p.columnFloor ≤ ε) (hr : r.columnFloor ≤ ε) :
    ∃ label : ↥(univ.filter fun a : Response P R => failure P R σ W c a ∧
        ε < fraction P R σ W c a) → Label P R W,
      Function.Injective label ∧ ∀ a : ↥(univ.filter fun a : Response P R =>
        failure P R σ W c a ∧ ε < fraction P R σ W c a),
        fraction P R σ W c a ≤ capacity P R W (label a) ∧
        exception P R p r σ W c (label a) := by
  let A := univ.filter fun a : Response P R => failure P R σ W c a ∧ ε < fraction P R σ W c a
  have hl (a : ↥A) := large_of_fraction P R p r σ W c a ε hp hr (mem_filter.mp a.2).2.2
  have hass (a : ↥A) := assign P R p r σ W c a hb (hl a).1 (hl a).2
  choose label hlabel using hass
  refine ⟨label,?_,?_⟩
  · intro a b hab
    apply Subtype.ext
    apply response_eq P R p r σ W c hb (label a) a.1 b.1 (hlabel a).1
      (by simpa only [hab] using (hlabel b).1)
    · intro x hx
      rcases mem_insert.mp hx with hx | hx
      · simpa only [hx] using (hl a).1
      · simpa only [mem_singleton.mp hx] using (hl b).1
    · intro x hx
      rcases mem_insert.mp hx with hx | hx
      · simpa only [hx] using (hl a).2
      · simpa only [mem_singleton.mp hx] using (hl b).2
  · intro a
    exact ⟨(hlabel a).2, exception_of_failure P R p r σ W c hb (label a) a
      (hlabel a).1 (hl a).1 (hl a).2 (hε.trans_lt (mem_filter.mp a.2).2.2)
      (mem_filter.mp a.2).2.1⟩

private theorem high_mass_le_systems (p : ProfileParameters P.backend) (r : ProfileParameters R.backend)
    (σ : Statement P R) (W : Oracle P R) (c : Coin P R) (hb : ¬ rankBad P R W c)
    (ε : ℚ) (hε : 0 ≤ ε) (hp : p.columnFloor ≤ ε) (hr : r.columnFloor ≤ ε) :
    (∑ a : Response P R, if failure P R σ W c a ∧ ε < fraction P R σ W c a
      then fraction P R σ W c a else 0) ≤
      ∑ d : Label P R W, indicator (exception P R p r σ W c d) *
        (if ε < capacity P R W d then capacity P R W d else 0) := by
  let A := univ.filter fun a : Response P R => failure P R σ W c a ∧ ε < fraction P R σ W c a
  obtain ⟨label,hinj,hlabel⟩ := high_assignment P R p r σ W c hb ε hε hp hr
  let weight := fun d : Label P R W => indicator (exception P R p r σ W c d) *
    (if ε < capacity P R W d then capacity P R W d else 0)
  have hn d : 0 ≤ weight d := by
    apply mul_nonneg (indicator_nonneg _)
    split_ifs
    · unfold capacity; positivity
    · exact le_rfl
  have hw (a : ↥A) : fraction P R σ W c a ≤ weight (label a) := by
    have ha := hlabel a
    have hc := (mem_filter.mp a.2).2.2.trans_le ha.1
    simpa only [weight,indicator,if_pos ha.2,if_pos hc,one_mul] using ha.1
  have heq : (∑ a : Response P R, if failure P R σ W c a ∧ ε < fraction P R σ W c a
      then fraction P R σ W c a else 0) = ∑ a : ↥A, fraction P R σ W c a := by
    rw [← sum_filter]
    exact sum_subtype A (fun _ => Iff.rfl) (fraction P R σ W c)
  rw [heq]
  calc
    _ ≤ ∑ a : ↥A, weight (label a) := sum_le_sum (fun a _ => hw a)
    _ = ∑ d ∈ univ.image label, weight d := (sum_image (fun _ _ _ _ h => hinj h)).symm
    _ ≤ ∑ d, weight d := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun d _ _ => hn d)

theorem exception_mean (p : ProfileParameters P.backend) (r : ProfileParameters R.backend)
    (σ : Statement P R) (W : Oracle P R) (d : Label P R W) :
    mean (fun c : Coin P R => indicator (exception P R p r σ W c d)) ≤
      1/(Nat.card P.Carrier : ℚ) + 1/(Nat.card R.Carrier : ℚ) := by
  calc
    _ ≤ mean (fun c : Coin P R =>
        indicator (c.1 ∈ systemExceptions p.positive_degree P.backend.layout σ.1 d.1.1) +
        indicator (c.2 ∈ systemExceptions r.positive_degree R.backend.layout σ.2 d.1.2)) := by
      apply mean_mono
      intro c
      simp only [exception, indicator]
      split_ifs <;> simp_all
    _ = mean (fun c : P.Coin =>
        indicator (c ∈ systemExceptions p.positive_degree P.backend.layout σ.1 d.1.1)) +
        mean (fun c : R.Coin =>
        indicator (c ∈ systemExceptions r.positive_degree R.backend.layout σ.2 d.1.2)) := by
      exact mean_pair_add
        (fun c : P.Coin => indicator (c ∈ systemExceptions p.positive_degree P.backend.layout σ.1 d.1.1))
        (fun c : R.Coin => indicator (c ∈ systemExceptions r.positive_degree R.backend.layout σ.2 d.1.2))
    _ ≤ _ := add_le_add (systemExceptions_mean P.backend p σ.1 W.1 d.1.1)
      (systemExceptions_mean R.backend r σ.2 W.2 d.1.2)

/-- This sum ranges over complete response pairs, not a projection onto one
field. Rank failures are charged separately at the parent query. -/
def highMass (σ : Statement P R) (W : Oracle P R) (ε : ℚ) (c : Coin P R) : ℚ :=
  if rankBad P R W c then 0 else ∑ a : Response P R,
    if failure P R σ W c a ∧ ε < fraction P R σ W c a then fraction P R σ W c a else 0

theorem highMass_nonneg (σ : Statement P R) (W : Oracle P R) (ε : ℚ) (c : Coin P R) :
    0 ≤ highMass P R σ W ε c := by
  unfold highMass
  split_ifs
  · exact le_rfl
  · apply sum_nonneg
    intro a _
    split_ifs
    · exact fraction_nonneg P R σ W c a
    · exact le_rfl

/-- All response assignment needs is enough columns for both payloads.
The stronger field-error threshold is a choice of geometric certificate, not
an extra requirement of the response-uniqueness or exception arguments. -/
private theorem extraction_high_mass_le_capacity_of_floor (p : ProfileParameters P.backend)
    (r : ProfileParameters R.backend) (σ : Statement P R) (W : Oracle P R)
    (ε : ℚ) (hε : 0 ≤ ε) (hp : p.columnFloor ≤ ε) (hr : r.columnFloor ≤ ε) :
    mean (highMass P R σ W ε) ≤
      (1/(Nat.card P.Carrier : ℚ)+1/(Nat.card R.Carrier : ℚ))*
        (∑ d : Label P R W, if ε < capacity P R W d then capacity P R W d else 0) := by
  let high := fun d : Label P R W => if ε < capacity P R W d then capacity P R W d else 0
  have hn d : 0 ≤ high d := by
    dsimp [high]
    split_ifs
    · unfold capacity; positivity
    · exact le_rfl
  have hlocal (c : Coin P R) : highMass P R σ W ε c ≤
      ∑ d, indicator (exception P R p r σ W c d)*high d := by
    unfold highMass
    split_ifs with hb
    · exact sum_nonneg (fun d _ => mul_nonneg (indicator_nonneg _) (hn d))
    · exact high_mass_le_systems P R p r σ W c hb ε
        hε hp hr
  calc
    _ ≤ mean (fun c : Coin P R => ∑ d,
        indicator (exception P R p r σ W c d)*high d) :=
      mean_mono hlocal
    _ = ∑ d, mean (fun c : Coin P R =>
        indicator (exception P R p r σ W c d)*high d) :=
      SystemException.mean_finset_sum univ _
    _ = ∑ d, mean (fun c : Coin P R =>
        indicator (exception P R p r σ W c d))*high d := by
      apply sum_congr rfl
      intro d _
      simpa only [mul_comm] using mean_mul_left (high d)
        (fun c : Coin P R => indicator
          (exception P R p r σ W c d))
    _ ≤ ∑ d, (1/(Nat.card P.Carrier : ℚ)+1/(Nat.card R.Carrier : ℚ))*high d :=
      sum_le_sum (fun d _ => mul_le_mul_of_nonneg_right
        (exception_mean P R p r σ W d) (hn d))
    _ = _ := (mul_sum ..).symm

/-- Both exception probabilities multiply one shared geometric capacity
sum. Splitting this sum by the two field cardinalities would lose the fact
that the entire joint high-label set is already small in the first field. -/
theorem extraction_high_mass_le_capacity (p : HahnSystemCertificate P.backend)
    (r : HahnSystemCertificate R.backend) (σ : Statement P R) (W : Oracle P R)
    (ε : ℚ) (hp : p.error ≤ ε) (hr : r.error ≤ ε) :
    mean (highMass P R σ W ε) ≤
      (1/(Nat.card P.Carrier : ℚ)+1/(Nat.card R.Carrier : ℚ))*
        (∑ d : Label P R W, if ε < capacity P R W d then capacity P R W d else 0) :=
  extraction_high_mass_le_capacity_of_floor P R p.toProfileParameters r.toProfileParameters σ W ε
    (p.error_nonneg.trans hp)
    (p.columnFloor_le.trans ((NonrecursiveFS.threshold_le_error P.backend p).trans hp))
    (r.columnFloor_le.trans ((NonrecursiveFS.threshold_le_error R.backend r).trans hr))

/-- Retained per-field coefficient, derived from the common capacity sum. -/
theorem extraction_high_mass_mean (p : HahnSystemCertificate P.backend)
    (r : HahnSystemCertificate R.backend) (σ : Statement P R) (W : Oracle P R)
    (ε : ℚ) (hp : p.error ≤ ε) (hr : r.error ≤ ε) :
    mean (highMass P R σ W ε) ≤
      NonrecursiveFS.highBudget P.backend p + NonrecursiveFS.highBudget R.backend r := by
  apply (extraction_high_mass_le_capacity P R p r σ W ε hp hr).trans
  rw [add_mul]
  have h := add_le_add
    (mul_le_mul_of_nonneg_left (capacity_high_mass P R P p W ε hp)
      (show (0 : ℚ) ≤ 1/(Nat.card P.Carrier : ℚ) by positivity))
    (mul_le_mul_of_nonneg_left (capacity_high_mass P R R r W ε hr)
      (show (0 : ℚ) ≤ 1/(Nat.card R.Carrier : ℚ) by positivity))
  exact h.trans_eq (by unfold NonrecursiveFS.highBudget; ring)

/-- One high-label bound pays for exceptions in both fields. The first
field's certificate bounds the full joint label set; the second field's
larger cardinality therefore does not create a second baseline mass. -/
def jointHighBudget (p : HahnSystemCertificate P.backend) : ℚ :=
  (1/(Nat.card P.Carrier : ℚ)+1/(Nat.card R.Carrier : ℚ))*
    (1-p.threshold+((Nat.card P.Carrier : ℚ)-1)*p.threshold)

theorem jointHighBudget_nonneg (p : HahnSystemCertificate P.backend) :
    0 ≤ jointHighBudget P R p := by
  have hq : (1 : ℚ) ≤ Nat.card P.Carrier := by exact_mod_cast Nat.card_pos (α := P.Carrier)
  apply mul_nonneg
  · exact add_nonneg (by positivity) (by positivity)
  · exact add_nonneg (sub_nonneg.mpr p.threshold_lt_one.le)
      (mul_nonneg (sub_nonneg.mpr hq) p.threshold_nonneg)

theorem extraction_high_mass_mean_joint (p : HahnSystemCertificate P.backend)
    (r : HahnSystemCertificate R.backend) (σ : Statement P R) (W : Oracle P R)
    (ε : ℚ) (hp : p.error ≤ ε) (hr : r.error ≤ ε) :
    mean (highMass P R σ W ε) ≤ jointHighBudget P R p :=
  (extraction_high_mass_le_capacity P R p r σ W ε hp hr).trans
    (mul_le_mul_of_nonneg_left (capacity_high_mass P R P p W ε hp) (by positivity))

/-- Both participants have the same row, masking, column and query geometry,
so their minimum good-column fractions agree independently of their fields. -/
theorem columnFloor_eq (p : ProfileParameters P.backend) (r : ProfileParameters R.backend) :
    p.columnFloor = r.columnFloor := by
  simp only [ProfileParameters.columnFloor, ProfileParameters.largeSize, ProfileParameters.coreSize,
    P.columns, P.openings, P.dimension, P.batching, R.columns, R.openings, R.dimension, R.batching]

/-- With a bounded active family, the residual baseline is only a fixed
list-size multiple of θ, multiplied by the actual field-exception rates. -/
def activeHighBudget (p : HahnSystemCertificate P.backend) : ℚ :=
  (1/(Nat.card P.Carrier : ℚ)+1/(Nat.card R.Carrier : ℚ))*
    (1-p.threshold+(p.listBound : ℚ)*p.threshold)

theorem activeHighBudget_nonneg (p : HahnSystemCertificate P.backend) :
    0 ≤ activeHighBudget P R p :=
  mul_nonneg (by positivity) (add_nonneg (sub_nonneg.mpr p.threshold_lt_one.le)
    (mul_nonneg (Nat.cast_nonneg _) p.threshold_nonneg))

/-- The first field's genuine active-family certificate controls every
joint label. The threshold may equal θ; prime response uniqueness follows
from the shared column geometry, without a prime `1/p` threshold addition. -/
theorem extraction_high_mass_mean_active (p : HahnSystemCertificate P.backend)
    (r : ProfileParameters R.backend) (σ : Statement P R) (W : Oracle P R)
    (ε : ℚ) (hθ : p.threshold ≤ ε)
    (hactive : CodingTheory.UniformFamilyBound n p.columnCutoff (k+2*s-1) p.listBound)
    (hbound : p.listBound ≤ Nat.card P.Carrier) :
    mean (highMass P R σ W ε) ≤ activeHighBudget P R p := by
  have hp : p.columnFloor ≤ ε := p.columnFloor_le.trans hθ
  have hr : r.columnFloor ≤ ε := by rw [← columnFloor_eq P R p.toProfileParameters r]; exact hp
  apply (extraction_high_mass_le_capacity_of_floor P R p.toProfileParameters r σ W ε
    (p.threshold_nonneg.trans hθ) hp hr).trans
  exact mul_le_mul_of_nonneg_left (capacity_high_mass_active P R P p W ε hθ hactive hbound)
    (by positivity)

theorem rank_mean (p : ProfileParameters P.backend) (r : ProfileParameters R.backend)
    (W : Oracle P R) :
    mean (fun c : Coin P R => indicator (rankBad P R W c)) ≤ p.rankError+r.rankError := by
  calc
    _ ≤ mean (fun c : Coin P R => indicator (NonrecursiveFS.rankBad P.backend W.1 c.1) +
        indicator (NonrecursiveFS.rankBad R.backend W.2 c.2)) := by
      apply mean_mono
      intro c
      simp only [rankBad, indicator]
      split_ifs <;> simp_all
    _ = mean (fun c : P.Coin => indicator (NonrecursiveFS.rankBad P.backend W.1 c)) +
        mean (fun c : R.Coin => indicator (NonrecursiveFS.rankBad R.backend W.2 c)) := by
      exact mean_pair_add
        (fun c : P.Coin => indicator (NonrecursiveFS.rankBad P.backend W.1 c))
        (fun c : R.Coin => indicator (NonrecursiveFS.rankBad R.backend W.2 c))
    _ ≤ _ := add_le_add (rank_bad_mean P.backend p W.1) (rank_bad_mean R.backend r W.2)

/-- Active-family parent charge, with both field rank errors retained. -/
theorem parent_mass_active_le (p : HahnSystemCertificate P.backend) (r : ProfileParameters R.backend)
    (σ : Statement P R) (W : Oracle P R) (ε : ℚ) (hθ : p.threshold ≤ ε)
    (hactive : CodingTheory.UniformFamilyBound n p.columnCutoff (k+2*s-1) p.listBound)
    (hbound : p.listBound ≤ Nat.card P.Carrier) :
    mean (fun c : Coin P R => indicator (rankBad P R W c)+highMass P R σ W ε c) ≤
      p.rankError+r.rankError+activeHighBudget P R p := by
  rw [mean_add]
  exact add_le_add (rank_mean P R p.toProfileParameters r W)
    (extraction_high_mass_mean_active P R p r σ W ε hθ hactive hbound)

/-- Rank and the refined summed response mass are charged at the same
parent query. This coefficient keeps the two actual rank errors and one
joint high-response mass, without an extra field-sized label factor. -/
theorem parent_mass_joint_le (p : HahnSystemCertificate P.backend) (r : HahnSystemCertificate R.backend)
    (σ : Statement P R) (W : Oracle P R) (ε : ℚ) (hp : p.error ≤ ε) (hr : r.error ≤ ε) :
    mean (fun c : Coin P R => indicator (rankBad P R W c)+highMass P R σ W ε c) ≤
      p.rankError+r.rankError+jointHighBudget P R p := by
  rw [mean_add]
  exact add_le_add (rank_mean P R p.toProfileParameters r.toProfileParameters W)
    (extraction_high_mass_mean_joint P R p r σ W ε hp hr)

/-- A single parent-query budget covers rank failures and the sum of every
high-acceptance failing response pair. The same epsilon also bounds each
remaining child-query response, which is the form shared charging needs. -/
theorem parent_mass_le (p : HahnSystemCertificate P.backend) (r : HahnSystemCertificate R.backend)
    (σ : Statement P R) (W : Oracle P R)
    (hp : p.rankError ≤ 1/(Nat.card P.Carrier : ℚ))
    (hr : r.rankError ≤ 1/(Nat.card R.Carrier : ℚ)) :
    mean (fun c : Coin P R => indicator (rankBad P R W c) +
      highMass P R σ W (p.error+r.error) c) ≤ p.error+r.error := by
  rw [mean_add]
  have hh := extraction_high_mass_mean P R p r σ W (p.error+r.error)
    (le_add_of_nonneg_right r.error_nonneg) (le_add_of_nonneg_left p.error_nonneg)
  have hb := add_le_add (rank_mean P R p.toProfileParameters r.toProfileParameters W) hh
  have hP := NonrecursiveFS.rank_high_le_error P.backend p hp
  have hR := NonrecursiveFS.rank_high_le_error R.backend r hr
  linarith

end LfzkV2.Current.JointResponse
