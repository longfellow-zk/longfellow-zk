import polygero.Recursion.FSRootSoundness
import polygero.Instances.FSJointChild81
import polygero.Instances.FSCoreCompiled81

set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option linter.unusedSectionVars false
namespace RecursivePolygero.Instances.FSJointChildCompiled81
open Finset FiatShamir ProfileAnalysis Bcs.AffineBlock Bcs.TotalOracle.Footprint Bcs.FiniteProbability
open Merkle Merkle.MH Merkle.RandomOracle Merkle.RandomOracle.TwoOracleTree
open FiatShamir.MerkleFS
open scoped Classical
variable {F D Enc SaltP SaltC : Type} [Field F] [Fintype F] [DecidableEq F]
  [Fintype D] [DecidableEq D] [Inhabited D] [DecidableEq Enc]
  [Inhabited SaltP] [Inhabited SaltC]
variable {I : Instance F} (child : Child I)
variable {codecP : Codec SaltP (MerkleFS.Leaf I) D Enc}
  {codecC : Codec SaltC (MerkleFS.Leaf child.instance) D Enc}
variable (decP : RoleDecoders codecP) (decC : RoleDecoders codecC)
variable {tA N TM : ℕ}
variable (body : TwoOracleTree Enc D (MerkleFS.Point child (D := D)) (MerkleFS.Answer child)
  (MerkleFS.Proof child (D := D) (SaltP := SaltP) (SaltC := SaltC)) tA N)

/-- The sharpened child slope composes with any proved local-domain
parent ABS certificate. Both commitment errors and both completion
intercepts remain in the actual digest/opening verifier bound. -/
theorem extraction_failure_bound_of_parent
    (p : HahnSystemCertificate I) (cp : HahnSystemCertificate child.instance)
    (σ : I.layer.Statement) (parentRate : Rate)
    (hparent : ∀ ctx : MerkleFS.Context child (D := D),
      OracleSound (MerkleFS.queryDomain child)
        (fun d : MerkleFS.Candidate child (D := D) => MerkleFS.queryRisk child ctx cp σ d.1 d.2.1) parentRate)
    (h1 : FSTwoLevel.Geometry child.instance FSDefect81.childRow)
    (hq : Nat.card F = FSTwoLevel.fieldSize) (hsmall : cp.listBound < Nat.card F)
    (hcut : cp.columnCutoff = 2714) (htheta : cp.threshold = FSTwoLevel.theta FSDefect81.childRow)
    (hmu : cp.toProfileParameters.rankError = FSTwoLevel.rankError)
    (ht : tA ≤ TM) (hF : MerkleFS.checkFuel child+tA ≤ TM) (hTM : 1 ≤ TM) :
    density (fun ω : (Fin TM → D) × (MerkleFS.Point child → MerkleFS.Answer child) =>
      MerkleFS.extractionFailure child decP decC body p cp σ ω.1 ω.2) ≤
      parentRate.intercept+FSJointChild81.childSlope+N*max parentRate.slope FSJointChild81.childSlope+
        MerkleFS.merkleError child (D := D) tA N := by
  exact MerkleFS.extraction_failure_bound_of_blocks child decP decC body p cp σ parentRate hparent
    (Rate.diagonal FSJointChild81.childSlope FSJointChild81.checked.2.2.1)
    (fun ctx => FSJointChild81.child_oracle_sound_joint child p cp ctx σ h1 hq hsmall hcut htheta hmu)
    ht hF hTM

/-- Concrete all-error theorem with both child ABS parameters recovered.
The remaining global slope is the unchanged parent price. -/
theorem certified_bound (h0 : FSTwoLevel.Geometry I FSDefect81.parent)
    (h1 : FSTwoLevel.Geometry child.instance FSDefect81.childRow)
    (hq : Nat.card F = FSTwoLevel.fieldSize) (hdigest : Fintype.card D = FSCompiledData.digestSize) :
    ∃ p : HahnSystemCertificate I, ∃ cp : HahnSystemCertificate child.instance,
      ∀ (σ : I.layer.Statement) (tA N TM : ℕ)
        (body : TwoOracleTree Enc D (MerkleFS.Point child (D := D)) (MerkleFS.Answer child)
          (MerkleFS.Proof child (D := D) (SaltP := SaltP) (SaltC := SaltC)) tA N),
        tA ≤ TM → FSCompiledData.checking+tA ≤ TM → 1 ≤ TM →
      density (fun ω : (Fin TM → D) × (MerkleFS.Point child → MerkleFS.Answer child) =>
        MerkleFS.extractionFailure child decP decC body p cp σ ω.1 ω.2) ≤
          FSShiftedData.rate+FSJointChild81.childSlope+N*FSShiftedData.rate+FSCompiledData.bcs tA N := by
  obtain ⟨p,cp,ha,hcut,htheta,hmu⟩ := FSShifted81.analysis_exists_with_child_data child h0 h1 hq
  refine ⟨p,cp,fun σ tA N TM body ht hF hTM => ?_⟩
  have hparent (ctx : MerkleFS.Context child (D := D)) :
      OracleSound (MerkleFS.queryDomain child)
        (fun d : MerkleFS.Candidate child (D := D) => MerkleFS.queryRisk child ctx cp σ d.1 d.2.1)
        (Rate.diagonal FSShiftedData.rate FSShiftedData.checked.rate_nonneg) :=
    MerkleFS.Capacity.query_oracle_sound child ctx cp (FiatShamir.TwoLevel.coreQueryCapacity child p cp)
      (FiatShamir.TwoLevel.coreQueryCapacity_nonneg child p cp)
      (FiatShamir.TwoLevel.queryCapacityRisk_mean_le_core child p cp ha.small) σ FSShiftedData.rate
      FSShiftedData.checked.rate_nonneg (ha.root σ) (ha.fresh σ)
  have hcheck : MerkleFS.checkFuel child = FSCompiledData.checking := by
    simp only [MerkleFS.checkFuel,h0.length,h1.length,FSCompiledData.checking]
  have hs : FSJointChild81.childSlope ≤ FSShiftedData.rate :=
    FSJointChild81.checked.2.2.2.2.le.trans FSShiftedData.checked.child
  have h := extraction_failure_bound_of_parent child decP decC body p cp σ
    (Rate.diagonal FSShiftedData.rate FSShiftedData.checked.rate_nonneg) hparent h1 hq
    ha.small hcut htheta hmu ht (by simpa only [hcheck] using hF) hTM
  simpa only [Rate.diagonal,max_eq_left hs,MerkleFS.merkleError,hcheck,hdigest,FSCompiledData.bcs] using h


include decP decC in
/-- The same sharper raw bound covers false-statement acceptance by the
actual opening verifier, with both BCS errors. -/
theorem false_statement_bound (h0 : FSTwoLevel.Geometry I FSDefect81.parent)
    (h1 : FSTwoLevel.Geometry child.instance FSDefect81.childRow)
    (hq : Nat.card F = FSTwoLevel.fieldSize) (hdigest : Fintype.card D = FSCompiledData.digestSize)
    (σ : I.layer.Statement) (hfalse : ∀ witness, ¬ I.layer.satisfies σ witness)
    (ht : tA ≤ TM) (hF : FSCompiledData.checking+tA ≤ TM) (hTM : 1 ≤ TM) :
    density (fun ω : (Fin TM → D) × (MerkleFS.Point child → MerkleFS.Answer child) =>
      MerkleFS.accepts child body (codecP := codecP) (codecC := codecC) σ ω.1 ω.2) ≤
      FSShiftedData.rate+FSJointChild81.childSlope+N*FSShiftedData.rate+FSCompiledData.bcs tA N := by
  obtain ⟨p,cp,hb⟩ := certified_bound child decP decC h0 h1 hq hdigest
  have hsub : density (fun ω : (Fin TM → D) × (MerkleFS.Point child → MerkleFS.Answer child) =>
      MerkleFS.accepts child body (codecP := codecP) (codecC := codecC) σ ω.1 ω.2) ≤
      density (fun ω : (Fin TM → D) × (MerkleFS.Point child → MerkleFS.Answer child) =>
        MerkleFS.extractionFailure child decP decC body p cp σ ω.1 ω.2) :=
    density_mono (fun ω ha => ⟨ha,MerkleFS.extractor_none_of_false child decP decC body p cp σ hfalse ω.1 ω.2⟩)
  exact hsub.trans (hb σ tA N TM body ht hF hTM)

end RecursivePolygero.Instances.FSJointChildCompiled81
