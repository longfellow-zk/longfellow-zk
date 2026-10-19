import polygero.Recursion.FSListBound

/-! Commitment-dependent excess prices for the parent-query seam.

The unnormalised child-system excess has the desired interactive price,
uniformly in the child commitment. It is not a unit-cover certificate for
an accepting terminal query. The final normalization lemma explains the
factor needed when a proof separates that terminal query from the seam.
-/

namespace RecursivePolygero.FiatShamir.TwoLevel

open Finset Counting ProfileAnalysis Local Local.Polygero LigeroFamily
open scoped Classical

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {I : Instance F} (child : Child I)
variable (p : HahnSystemCertificate I) (cp : HahnSystemCertificate child.instance)

/-- The commitment fixes both the system capacities and their labels
before the parent query. Only excess above the terminal threshold is
charged. No assertion that this quantity covers unit failure is made. -/
noncomputable def queryTargetExcess (sigma : I.layer.Statement)
    (W : I.layer.Oracle) (V : child.instance.layer.Oracle)
    (D : (tupleCounts I).Index → Prop) (a : I.layer.Coin) (q : I.layer.Query) : ℚ :=
  ∑ d ∈ highSystems child.instance cp V,
    max 0 (systemCap child.instance V d - cp.threshold) *
      indicator (systemTarget child.instance cp.positive_degree V
        (Protocol.ProfileProof.inducedFamily (child := child) sigma W a D q) d)

/-- Actual child-system labels give a commitment-dependent seam price
without a child-list factor. The incoming envelope is retained pointwise
in the parent challenge, rather than replaced by an unconditional mean. -/
theorem queryTargetExcess_mean_le (hsmall : cp.listBound < Nat.card F)
    (sigma : I.layer.Statement) (W : I.layer.Oracle)
    (V : child.instance.layer.Oracle) (D : (tupleCounts I).Index → Prop)
    (a : I.layer.Coin) :
    mean (queryTargetExcess child cp sigma W V D a) ≤
      (1 - cp.threshold) * localEnvelope I p.toProfileParameters sigma W p.threshold D a := by
  let rate := localEnvelope I p.toProfileParameters sigma W p.threshold D a
  have hr : 0 ≤ rate :=
    (localEnvelope_bounds I p.toProfileParameters sigma W p.threshold
      p.threshold_nonneg p.threshold_lt_one.le D a).1
  have hf (d : systems child.instance.domain child.instance.primary_le V) :
      mean (fun q => indicator (systemTarget child.instance cp.positive_degree V
        (Protocol.ProfileProof.inducedFamily (child := child) sigma W a D q) d)) ≤ rate := by
    by_cases hfull : Local.Affine.consistent
        (LigeroFamily.PolynomialDirect.primaryCode child.instance.domain child.instance.primary_le)
        (oracleWords V.ordinary) V.proximityMask d.1 = univ
    · simpa only [systemTarget, exists_prop_of_true hfull] using
        induced_target_frequency_le child p sigma W D a
          (systemLabel child.instance cp.positive_degree V d hfull)
    · have hn (q : I.layer.Query) : ¬ systemTarget child.instance cp.positive_degree V
          (Protocol.ProfileProof.inducedFamily (child := child) sigma W a D q) d :=
          fun ⟨h, _⟩ => hfull h
      simpa only [indicator, if_neg (hn _), mean_const] using hr
  have hc := highSystems_card_le child.instance cp hsmall V
  have he := systemCap_excess_of_hahn child.instance cp V
    (highSystems child.instance cp V) (hc.trans hsmall.le)
  unfold queryTargetExcess
  rw [SystemException.mean_finset_sum]
  calc
    _ = ∑ d ∈ highSystems child.instance cp V,
        max 0 (systemCap child.instance V d - cp.threshold) *
          mean (fun q => indicator (systemTarget child.instance cp.positive_degree V
            (Protocol.ProfileProof.inducedFamily (child := child) sigma W a D q) d)) := by
      apply sum_congr rfl
      intro d _
      exact mean_mul_left _ _
    _ ≤ ∑ d ∈ highSystems child.instance cp V,
        max 0 (systemCap child.instance V d - cp.threshold) * rate := by
      exact sum_le_sum (fun d _ => mul_le_mul_of_nonneg_left (hf d) (le_max_left _ _))
    _ = (∑ d ∈ highSystems child.instance cp V,
        max 0 (systemCap child.instance V d - cp.threshold)) * rate := by rw [sum_mul]
    _ ≤ (1 - cp.threshold) * rate := mul_le_mul_of_nonneg_right he hr

/-- Outside the parent's Boolean exception cover, the weighted price is
the product of the parent threshold and unused child capacity. -/
theorem queryTargetExcess_mean_le_of_not_listBad
    (hsmall : cp.listBound < Nat.card F) (sigma : I.layer.Statement)
    (W : I.layer.Oracle) (V : child.instance.layer.Oracle) (a : I.layer.Coin)
    (hgood : ¬ listBad I p sigma W a) :
    mean (queryTargetExcess child cp sigma W V (fun _ => False) a) ≤
      (1 - cp.threshold) * p.threshold :=
  (queryTargetExcess_mean_le child p cp hsmall sigma W V (fun _ => False) a).trans
    (mul_le_mul_of_nonneg_left (envelope_le_threshold_of_not_listBad I p sigma W a hgood)
      (sub_nonneg.mpr cp.threshold_lt_one.le))

end RecursivePolygero.FiatShamir.TwoLevel

namespace RecursivePolygero.FiatShamir

open Counting
open scoped Classical

/-- A seam charge fixed before a terminal answer must pay the normalized
excess if the terminal charge has budget `theta`. This applies to arbitrary
terminal charges, not only to constant weights on the accepting event.
Consequently the unnormalised excess price above cannot by itself serve
as a pointwise cover after separating the two oracle coordinates. -/
theorem terminal_cover_requires_normalized_excess
    {A : Type} [Fintype A] (event : A → Prop)
    (terminalCharge : A → ℚ) (capacity theta seamWeight : ℚ)
    (hcapacity : mean (fun a => indicator (event a)) = capacity)
    (hpos : 0 < capacity)
    (hterminal : mean terminalCharge ≤ theta)
    (hcover : ∀ a, indicator (event a) ≤
      seamWeight * indicator (event a) + terminalCharge a) :
    (capacity - theta) / capacity ≤ seamWeight := by
  have hm := mean_mono hcover
  rw [mean_add, mean_mul_left, hcapacity] at hm
  apply (div_le_iff₀ hpos).mpr
  nlinarith

/-- The normalization lower bound is attained by assigning the terminal
event a constant fraction of its mass. -/
theorem normalized_excess_cover_exact
    {A : Type} [Fintype A] (event : A → Prop) (capacity theta : ℚ)
    (hcapacity : mean (fun a => indicator (event a)) = capacity)
    (hpos : 0 < capacity) :
    mean (fun a => (theta / capacity) * indicator (event a)) = theta ∧
      ∀ a, ((capacity - theta) / capacity) * indicator (event a) +
        (theta / capacity) * indicator (event a) = indicator (event a) := by
  constructor
  · rw [mean_mul_left, hcapacity, div_mul_cancel₀ _ hpos.ne']
  · intro a
    field_simp
    ring

end RecursivePolygero.FiatShamir
