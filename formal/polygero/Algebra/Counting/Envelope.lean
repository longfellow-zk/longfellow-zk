import polygero.Algebra.Counting.SystemExceptions

/-! Fixed response envelopes and local errors. -/
namespace RecursivePolygero.ProfileAnalysis
open Finset
attribute [local instance] Classical.propDecidable

theorem mean_prod {I J : Type*} [Fintype I] [Fintype J] (f : I × J → ℚ) :
    mean f = mean (fun i => mean (fun j => f (i,j))) := by
  simp only [mean,Fintype.sum_prod_type,Fintype.card_prod,Nat.cast_mul,← sum_div]
  ring

theorem mean_congr {I : Type*} [Fintype I] {f g : I → ℚ} (h : ∀ i, f i = g i) : mean f = mean g :=
  congrArg mean (funext h)

theorem indicator_mono {P Q : Prop} (h : P → Q) : indicator P ≤ indicator Q := by
  unfold indicator
  split_ifs <;> simp_all

noncomputable def envelope {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → ℚ) (exceptional : I → Prop) (bad : Prop) (θ : ℚ) : ℚ :=
  if bad then 1 else SystemException.maximum a exceptional θ

theorem envelope_le_one {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → ℚ) (exceptional : I → Prop) (bad : Prop) (θ : ℚ)
    (hθ : θ ≤ 1) (ha : ∀ i, a i ≤ 1) : envelope a exceptional bad θ ≤ 1 := by
  unfold envelope
  split_ifs
  · rfl
  · exact SystemException.maximum_le _ _ _ _ hθ (fun i _ => ha i)

theorem le_envelope {I : Type*} [Fintype I] [DecidableEq I]
    (a : I → ℚ) (exceptional : I → Prop) (bad : Prop) (θ : ℚ)
    (hθ : θ ≤ 1) : θ ≤ envelope a exceptional bad θ := by
  unfold envelope
  split_ifs
  · exact hθ
  · exact SystemException.le_maximum _ _ _

/-- The local profile at a certified threshold. -/
def profile (q μ θ : ℚ) : ℚ := θ+(1-θ)*(μ+1/q)

/-- The local error is increasing in the counting cutoff. -/
theorem profile_mono (q μ x θ : ℚ) (hslope : μ+1/q ≤ 1) (hxθ : x ≤ θ) :
    profile q μ x ≤ profile q μ θ := by
  have := mul_nonneg (sub_nonneg.mpr hxθ) (sub_nonneg.mpr hslope)
  unfold profile
  nlinarith only [this]

end RecursivePolygero.ProfileAnalysis
