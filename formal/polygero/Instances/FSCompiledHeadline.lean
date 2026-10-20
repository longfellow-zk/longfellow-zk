import polygero.Instances.FSCompiledCorollaries

/-! End-to-end headlines for actual root/opening proofs. -/
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
namespace RecursivePolygero.Instances.FSCompiled81
open FiatShamir ProfileAnalysis Bcs.FiniteProbability
open Merkle Merkle.MH Merkle.RandomOracle
open FiatShamir.MerkleFS
open scoped Classical
variable {F D Enc SaltP SaltC : Type} [Field F] [Fintype F] [DecidableEq F]
  [Fintype D] [DecidableEq D] [Inhabited D] [DecidableEq Enc]
  [Inhabited SaltP] [Inhabited SaltC]
variable {I : Instance F} (child : Child I)
variable {codecP : Codec SaltP (MerkleFS.Leaf I) D Enc}
  {codecC : Codec SaltC (MerkleFS.Leaf child.instance) D Enc}
variable (decP : RoleDecoders codecP) (decC : RoleDecoders codecC)

/-- No omitted commitment error. The rounded complete loss is <1.402 bits
against the stronger IOP certificate and <0.904 against the working one,
with Merkle and FS queries both included in total adversarial work. -/
theorem certified_comparisons (h0 : FSTwoLevel.Geometry I FSDefect81.parent)
    (h1 : FSTwoLevel.Geometry child.instance FSDefect81.childRow)
    (hq : Nat.card F = FSTwoLevel.fieldSize) (hdigest : Fintype.card D = FSCompiledData.digestSize) :
    ∃ p : HahnSystemCertificate I, ∃ cp : HahnSystemCertificate child.instance,
      ∀ (σ : I.layer.Statement) (tA N TM : ℕ)
        (body : TwoOracleTree Enc D (MerkleFS.Point child (D := D)) (MerkleFS.Answer child)
          (MerkleFS.Proof child (D := D) (SaltP := SaltP) (SaltC := SaltC)) tA N),
        tA ≤ TM → FSCompiledData.checking+tA ≤ TM → 1 ≤ TM → N+tA ≤ FSCompiledData.fuelCap →
      let probability := density (fun ω : (Fin TM → D) × (MerkleFS.Point child → MerkleFS.Answer child) =>
        MerkleFS.extractionFailure child decP decC body p cp σ ω.1 ω.2)
      probability ≤ (2641/1000 : ℚ)*(N+tA+1)*FSIOPReference81.strongIOPError ∧
      probability ≤ (1871/1000 : ℚ)*(N+tA+1)*FSDefect81.sameIOPError := by
  obtain ⟨p,cp,ha⟩ := FSMerkle81.analysis_exists child h0 h1 hq
  obtain ⟨hsi,hss,hwi,hws,_,_,_,hsz,hwz⟩ := FSCompiledData.checked
  have hf : checkFuel child = FSCompiledData.checking := by
    simp only [checkFuel,h0.length,h1.length,FSCompiledData.checking]
  refine ⟨p,cp,fun σ tA N TM body ht hF hTM hcap => ?_⟩
  constructor
  · exact comparison_bound child decP decC body p cp ha σ hf hdigest ht (by simpa only [hf] using hF)
      hTM hcap (2641/1000) FSIOPReference81.strongIOPError hsi hss hsz
  · exact comparison_bound child decP decC body p cp ha σ hf hdigest ht (by simpa only [hf] using hF)
      hTM hcap (1871/1000) FSDefect81.sameIOPError hwi hws hwz

/- False-statement acceptance for the actual Merkle proof system. -/
include decP decC in
theorem false_statement_bound (h0 : FSTwoLevel.Geometry I FSDefect81.parent)
    (h1 : FSTwoLevel.Geometry child.instance FSDefect81.childRow)
    (hq : Nat.card F = FSTwoLevel.fieldSize) (hdigest : Fintype.card D = FSCompiledData.digestSize)
    (σ : I.layer.Statement) (hfalse : ∀ witness, ¬ I.layer.satisfies σ witness)
    {tA N TM : ℕ}
    (body : TwoOracleTree Enc D (MerkleFS.Point child (D := D)) (MerkleFS.Answer child)
      (MerkleFS.Proof child (D := D) (SaltP := SaltP) (SaltC := SaltC)) tA N)
    (ht : tA ≤ TM) (hF : FSCompiledData.checking+tA ≤ TM) (hTM : 1 ≤ TM)
    (hcap : N+tA ≤ FSCompiledData.fuelCap) :
    density (fun ω : (Fin TM → D) × (MerkleFS.Point child → MerkleFS.Answer child) =>
      MerkleFS.accepts child body (codecP := codecP) (codecC := codecC) σ ω.1 ω.2) ≤
        (2641/1000 : ℚ)*(N+tA+1)*FSIOPReference81.strongIOPError := by
  obtain ⟨p,cp,hb⟩ := certified_comparisons child decP decC h0 h1 hq hdigest
  have he : density (fun ω : (Fin TM → D) × (MerkleFS.Point child → MerkleFS.Answer child) =>
      MerkleFS.accepts child body (codecP := codecP) (codecC := codecC) σ ω.1 ω.2) =
      density (fun ω : (Fin TM → D) × (MerkleFS.Point child (D := D) → MerkleFS.Answer child) => MerkleFS.extractionFailure child decP decC body p cp σ ω.1 ω.2) := by
    apply density_congr
    intro ω
    exact ⟨fun ha => ⟨ha,extractor_none_of_false child decP decC body p cp σ hfalse ω.1 ω.2⟩,fun hf => hf.1⟩
  rw [he]
  exact (hb σ tA N TM body ht hF hTM hcap).1

end RecursivePolygero.Instances.FSCompiled81
