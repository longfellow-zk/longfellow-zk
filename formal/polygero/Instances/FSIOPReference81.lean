import polygero.Instances.FSCompletion81

/-! Audit the IOP denominator: cutoff2714/list6 is useful for FS, but is
not the best IOP certificate for the same 81/80 verifier and extractor. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

namespace RecursivePolygero.Instances.FSIOPReference81
open FiatShamir FiatShamir.TwoLevel ProfileAnalysis Bcs.AffineBlock
open scoped Classical

def ratio (a t : ℕ) : ℚ := (a.choose t : ℚ)/Nat.choose 8192 t
def threshold (t : ℕ) : ℚ := max (ratio 1087 t)
  (DiscreteThreshold.candidate FSTwoLevel.fieldSize 1 (ratio 639 t))
def localError (t : ℕ) : ℚ := profile FSTwoLevel.fieldSize FSTwoLevel.rankError (threshold t)
def strongIOPError : ℚ := twoError (localError 81) (localError 80)

theorem checked :
    DiscreteThreshold.IsLeastIndex FSTwoLevel.fieldSize (ratio 639 80) 1 ∧
    DiscreteThreshold.IsLeastIndex FSTwoLevel.fieldSize (ratio 639 81) 1 ∧
    FSTwoLevel.rankError+1/(FSTwoLevel.fieldSize : ℚ) < 1 ∧
    (2 : ℚ)/FSTwoLevel.fieldSize-1/(FSTwoLevel.fieldSize : ℚ)^2 ≤ strongIOPError ∧
    strongIOPError ≤ (2000000001/1000000000 : ℚ)/FSTwoLevel.fieldSize ∧
    (7/5 : ℚ)*strongIOPError < FSDefect81.sameIOPError := by
  simp only [strongIOPError,localError,threshold,ratio,DiscreteThreshold.IsLeastIndex,
    DiscreteThreshold.candidate,profile,twoError,FSTwoLevel.fieldSize,FSTwoLevel.rankError,
    FSDefect81.sameIOPError,FSTwoLevel.theta,FSDefect81.parent,FSWholeBlock81.parent,
    FSBaselinePrice.row,FSDefect81.childRow,FSWholeBlock81.childRow,FSIntegerAffine.childRow,
    Nat.choose_eq_fast_choose]
  decide +kernel

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

omit [DecidableEq F] in
/-- Construct the stronger local IOP certificate at either existing query
count. Its large list bound is harmless for the interactive excess proof. -/
theorem certificate (I : Instance F) (t : ℕ) (ht : t = 80 ∨ t = 81)
    (hn : I.n = 8192) (hk : I.r+I.w = 512) (hs : I.s = 64) (hqueries : I.t = t)
    (hq : Nat.card F = FSTwoLevel.fieldSize) :
    ∃ p : HahnSystemCertificate I, p.error = localError t := by
  let params : ProfileParameters I := {
    positive_degree := by omega
    large_le := by simp only [hk,hs,hn]; omega
    query_pos := by omega
    overlap_lt := by simp only [hk,hs,hn]; omega }
  have hmu : params.rankError = FSTwoLevel.rankError := by
    simp only [ProfileParameters.rankError,ProfileParameters.coreSize,hn,hk,hs,hq]
    rfl
  have hfloor : params.columnFloor = ratio 1087 t := by
    simp only [ProfileParameters.columnFloor,ProfileParameters.largeSize,ProfileParameters.coreSize,
      hn,hk,hs,hqueries]
    rfl
  have hover : params.overlapRatio = ratio 639 t := by
    simp only [ProfileParameters.overlapRatio,ProfileParameters.overlapSize,hn,hk,hs,hqueries]
    rfl
  let pp : ProfileCertificate I := {
    toProfileParameters := params
    cutoff := 1
    cutoff_spec := by
      rw [hover,hq]
      rcases ht with rfl | rfl
      · exact checked.1
      · exact checked.2.1
    field_error_lt_one := by rw [hmu,hq]; exact checked.2.2.1 }
  refine ⟨pp.toHahnSystemCertificate, ?_⟩
  change profile (Nat.card F) params.rankError
    (max params.columnFloor (DiscreteThreshold.candidate (Nat.card F) 1 params.overlapRatio)) = _
  rw [hmu,hfloor,hover,hq]
  rfl

/-- Changing numerical certificates does not change the actual extractor. -/
theorem twoProof_run_independent {I : Instance F} (child : Child I)
    (p p' : HahnSystemCertificate I) (cp cp' : HahnSystemCertificate child.instance)
    (σ : I.layer.Statement) (W : I.layer.Oracle)
    (messages : Strategy (Protocol.step child (.terminal child.instance)).chain)
    (coins : Coins child) :
    (twoProof child p cp).run σ W messages coins = (twoProof child p' cp').run σ W messages coins := by
  simp only [twoProof,Protocol.HahnProfileProof.run,Protocol.HahnProfileProof.runTranscript,
    Protocol.HahnProfileProof.family]
  split <;> rfl

theorem interactive_failure_le_strongIOP {I : Instance F} (child : Child I)
    (h0 : FSTwoLevel.Geometry I FSDefect81.parent)
    (h1 : FSTwoLevel.Geometry child.instance FSDefect81.childRow)
    (hq : Nat.card F = FSTwoLevel.fieldSize)
    (p : HahnSystemCertificate I) (cp : HahnSystemCertificate child.instance)
    (σ : I.layer.Statement) (W : I.layer.Oracle)
    (messages : Strategy (Protocol.step child (.terminal child.instance)).chain) :
    mean (fun coins => indicator
      (executionVerify (Protocol.step child (.terminal child.instance)).chain σ W messages coins = true ∧
        Counting.outputHit (fun _ => False) ((twoProof child p cp).run σ W messages coins))) ≤
      strongIOPError := by
  obtain ⟨sp,hsp⟩ := certificate I 81 (Or.inr rfl) h0.length h0.dimension h0.masks h0.queries hq
  obtain ⟨sc,hsc⟩ := certificate child.instance 80 (Or.inl rfl) h1.length h1.dimension h1.masks h1.queries hq
  have h := (twoProof child sp sc).extraction_failure_le σ W messages
  have he : (mean (fun coins => indicator
      (executionVerify (Protocol.step child (.terminal child.instance)).chain σ W messages coins = true ∧
        Counting.outputHit (fun _ => False) ((twoProof child p cp).run σ W messages coins)))) =
      (twoProof child sp sc).familyProbability σ W messages (fun _ => False) := by
    unfold Protocol.HahnProfileProof.familyProbability
    apply mean_congr
    intro coins
    rw [twoProof_run_independent child p sp cp sc]
    congr 1
  rw [he]
  simpa only [twoProof_error,hsp,hsc,strongIOPError] using h

/-- The fixed-proof bound with the stronger IOP denominator applies to
the very same extraction failure event as the working FS certificates. -/
theorem fixed_failure_le_strongIOP {I : Instance F} (child : Child I)
    (h0 : FSTwoLevel.Geometry I FSDefect81.parent)
    (h1 : FSTwoLevel.Geometry child.instance FSDefect81.childRow)
    (hq : Nat.card F = FSTwoLevel.fieldSize)
    (p : HahnSystemCertificate I) (cp : HahnSystemCertificate child.instance)
    (σ : I.layer.Statement) (d : Proof child) :
    Bcs.FiniteProbability.density (fun H => failure child p cp σ (fun _ => False) H d) ≤
      strongIOPError := by
  obtain ⟨sp,hsp⟩ := certificate I 81 (Or.inr rfl) h0.length h0.dimension h0.masks h0.queries hq
  obtain ⟨sc,hsc⟩ := certificate child.instance 80 (Or.inl rfl) h1.length h1.dimension h1.masks h1.queries hq
  have h := fixed_failure_le_iop child sp sc σ d
  have he (H : HashInput child → Answer child) :
      failure child p cp σ (fun _ => False) H d ↔ failure child sp sc σ (fun _ => False) H d := by
    unfold TwoLevel.failure
    rw [twoProof_run_independent child p sp cp sc]
  change _ ≤ twoError (localError 81) (localError 80)
  rw [hsp,hsc] at h
  convert h using 1
  congr 1
  funext H
  exact propext (he H)

end RecursivePolygero.Instances.FSIOPReference81
