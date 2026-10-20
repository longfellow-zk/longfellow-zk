import polygero.Local.ListSafety

set_option maxHeartbeats 1500000
namespace RecursivePolygero.ProfileAnalysis
open Finset Counting Local Local.Polygero
open LigeroFamily.PolynomialDirect (primaryCode)
open scoped Classical
variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- Excluding the high full-system targets suffices: low-capacity target
labels are already paid by the one query baseline. -/
theorem localEnvelope_le_empty_of_excluded_targets (I : Instance F) (p : HahnSystemCertificate I)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (D : (tupleCounts I).Index → Prop)
    (hex : ∀ d ∈ highSystems I p W, ¬ systemTarget I p.positive_degree W D d)
    (coin : I.layer.Coin) :
    localEnvelope I p.toProfileParameters σ W p.threshold D coin ≤
      localEnvelope I p.toProfileParameters σ W p.threshold (fun _ => False) coin := by
  unfold localEnvelope envelope
  split_ifs
  · rfl
  · apply SystemException.maximum_le _ _ _ _ (SystemException.le_maximum _ _ _)
    intro d hd
    rcases hd with ht | he
    · by_cases hh : p.threshold < systemCap I W d
      · exact (hex d (mem_filter.mpr ⟨mem_univ _,hh⟩) ht).elim
      · exact (le_of_not_gt hh).trans (SystemException.le_maximum _ _ _)
    · exact SystemException.entry_le_maximum _ _ _ d (Or.inr he)

/-- A fixed response with no high target system retains the ordinary
single-layer IOP error, even if its target set is not empty. -/
theorem excluded_target_response_mean_le (I : Instance F) (p : HahnSystemCertificate I)
    (σ : I.layer.Statement) (W : I.layer.Oracle) (D : (tupleCounts I).Index → Prop)
    (hex : ∀ d ∈ highSystems I p W, ¬ systemTarget I p.positive_degree W D d)
    (u : I.layer.Payload) :
    mean (fun a => mean (fun q => indicator (I.layer.verify σ W a u q ∧
      outputHit D (scanRecoverAt I σ W a u)))) ≤ p.error := by
  have hp := mean_mono (fun a => (family_response_mean I p.toProfileParameters σ W p.threshold
    p.columnFloor_le p.threshold_lt_one.le D a u).trans
      (localEnvelope_le_empty_of_excluded_targets I p σ W D hex a))
  have h := localEnvelope_mean_of_hahn (Z := Unit) I p (fun _ => σ) W 0
    (by norm_num) (by norm_num) (fun _ _ => False) (by intro g; simp [indicator])
  simp only [mean_const,mul_zero,add_zero] at h
  exact hp.trans h

end RecursivePolygero.ProfileAnalysis
