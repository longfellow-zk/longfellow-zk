import polygero.Recursion.FSJointCompletion
import polygero.Local.CoreEnvelope

/-! Uniform coverage of the actual child-label query event by actual-core
capacity. No commitment is fixed before its prescribed hash input. -/
namespace RecursivePolygero.FiatShamir.TwoLevel
open ProfileAnalysis Counting
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {I : Instance F} (child : Child I)
variable (p : HahnSystemCertificate I) (cp : HahnSystemCertificate child.instance)

noncomputable def coreQueryCapacity (σ : I.layer.Statement) (W : I.layer.Oracle)
    (a : I.layer.Coin) : ℚ :=
  refinedConditionalCapacity I p σ W (cp.listBound*p.threshold) a

theorem coreQueryCapacity_nonneg (σ : I.layer.Statement) (W : I.layer.Oracle)
    (a : I.layer.Coin) : 0 ≤ coreQueryCapacity child p cp σ W a :=
  refinedConditionalCapacity_nonneg I p σ W _
    (mul_nonneg (Nat.cast_nonneg _) p.threshold_nonneg) a

theorem coreQueryCapacity_le (σ : I.layer.Statement) (W : I.layer.Oracle)
    (a : I.layer.Coin) : coreQueryCapacity child p cp σ W a ≤ queryCapacity child p cp σ W a :=
  refinedConditionalCapacity_le I p σ W _ a

theorem queryCapacityRisk_mean_le_core (hcp : cp.listBound < Nat.card F)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (V : child.instance.layer.Oracle)
    (a : I.layer.Coin) :
    mean (fun q => indicator (queryCapacityRisk child cp σ W V a q)) ≤
      coreQueryCapacity child p cp σ W a :=
  queryCapacityRisk_mean_le_of_exception_bound child p cp hcp σ W V a
    (refinedWeightedExceptions I p σ W a) (assignedExceptionQuery_refined_le I p σ W a)

end RecursivePolygero.FiatShamir.TwoLevel
