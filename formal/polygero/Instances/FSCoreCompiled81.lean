import polygero.Recursion.FSRootSoundness
import polygero.Instances.FSMerkleCore81
import polygero.Instances.FSCompiledCorollaries
import polygero.Instances.FSCoreCompiledData
import polygero.Recursion.FSRootBridge

set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace RecursivePolygero.Instances.FSCoreCompiled81
open Finset FiatShamir FiatShamir.TwoLevel ProfileAnalysis Bcs.TotalOracle.Footprint Bcs.FiniteProbability
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

open FSCompiled81

/-- The stationary spectrum is one producer of the root-ROM bound; the
same Merkle compiler also accepts a cache-dependent finite-horizon proof. -/
theorem extraction_failure_bound_at (p : HahnSystemCertificate I) (cp : HahnSystemCertificate child.instance)
    (rate : ℚ) (hr : 0 ≤ rate) (hchild : FSDefect81.childPrice ≤ rate)
    (ha : FSMerkleCore81.AnalysisAt child p cp rate) (σ : I.layer.Statement)
    (ht : tA ≤ TM) (hF : checkFuel child+tA ≤ TM) (hTM : 1 ≤ TM) :
    density (fun ω : (Fin TM → D) × (MerkleFS.Point child → MerkleFS.Answer child) =>
      MerkleFS.extractionFailure child decP decC body p cp σ ω.1 ω.2) ≤
      rate+FSDefect81.childPrice+N*rate+merkleError child (D := D) tA N := by
  apply extraction_failure_bound_of_root_bound child decP decC body p cp σ
    (rate+FSDefect81.childPrice+N*rate) ?_ ht hF hTM
  intro mt
  have h := FSMerkleCore81.root_failure_bound_at child p cp rate hr hchild ha
    (MerkleFS.context child body decP decC mt) σ
    (((MerkleFS.parentSetup child body).search mt).map MerkleFS.Proof.candidate)
  simpa only [Tree.run_map,MerkleFS.output,Bcs.TotalOracleCommit.Setup.proof_eq] using h

theorem extraction_failure_bound (p : HahnSystemCertificate I) (cp : HahnSystemCertificate child.instance)
    (ha : FSMerkleCore81.Analysis child p cp) (σ : I.layer.Statement)
    (ht : tA ≤ TM) (hF : checkFuel child+tA ≤ TM) (hTM : 1 ≤ TM) :
    density (fun ω : (Fin TM → D) × (MerkleFS.Point child → MerkleFS.Answer child) =>
      MerkleFS.extractionFailure child decP decC body p cp σ ω.1 ω.2) ≤
      FSCoreData.rate+FSDefect81.childPrice+N*FSCoreData.rate+
        merkleError child (D := D) tA N :=
  extraction_failure_bound_at child decP decC body p cp FSCoreData.rate
    FSCoreData.checked.rate_nonneg FSCoreData.checked.child ha σ ht hF hTM

/-- Full 81/80 theorem, with certificates selected before the adversary.
Every soundness contribution, including both commitment errors, is present. -/
theorem certified_bound (h0 : FSTwoLevel.Geometry I FSDefect81.parent)
    (h1 : FSTwoLevel.Geometry child.instance FSDefect81.childRow)
    (hq : Nat.card F = FSTwoLevel.fieldSize) (hdigest : Fintype.card D = FSCompiledData.digestSize) :
    ∃ p : HahnSystemCertificate I, ∃ cp : HahnSystemCertificate child.instance,
      ∀ (σ : I.layer.Statement) (tA N TM : ℕ)
        (body : TwoOracleTree Enc D (MerkleFS.Point child) (MerkleFS.Answer child)
          (MerkleFS.Proof child (SaltP := SaltP) (SaltC := SaltC)) tA N),
        tA ≤ TM → FSCompiledData.checking+tA ≤ TM → 1 ≤ TM →
      density (fun ω : (Fin TM → D) × (MerkleFS.Point child → MerkleFS.Answer child) =>
        MerkleFS.extractionFailure child decP decC body p cp σ ω.1 ω.2) ≤
          FSCoreData.rate+FSDefect81.childPrice+N*FSCoreData.rate+FSCompiledData.bcs tA N := by
  obtain ⟨p,cp,ha⟩ := FSMerkleCore81.analysis_exists child h0 h1 hq
  refine ⟨p,cp,fun σ tA N TM body ht hF hTM => ?_⟩
  have hf : checkFuel child = FSCompiledData.checking := by
    simp only [checkFuel,h0.length,h1.length,FSCompiledData.checking]
  have h := extraction_failure_bound child decP decC body p cp ha σ ht (by simpa only [hf] using hF) hTM
  simpa only [merkleError,hf,hdigest,FSCompiledData.bcs] using h

/-- Without adversarial Merkle queries, every accepting parent root is
paid by the retained root-guess term, for arbitrary FS query work. -/
theorem no_merkle_failure_bound {TM N : ℕ}
    (body : TwoOracleTree Enc D (MerkleFS.Point child (D := D)) (MerkleFS.Answer child)
      (MerkleFS.Proof child (D := D) (SaltP := SaltP) (SaltC := SaltC)) 0 N)
    (hcheck : checkFuel child = FSCompiledData.checking)
    (hdigest : Fintype.card D = FSCompiledData.digestSize)
    (hF : checkFuel child ≤ TM) (hTM : 1 ≤ TM)
    (p : HahnSystemCertificate I) (cp : HahnSystemCertificate child.instance) (σ : I.layer.Statement) :
    density (fun ω : (Fin TM → D) × (MerkleFS.Point child → MerkleFS.Answer child) =>
      MerkleFS.extractionFailure child decP decC body p cp σ ω.1 ω.2) ≤
        (N+1)*FSCompiledData.reserve := by
  let S := MerkleFS.parentSetup child body
  let check := MerkleFS.check child (codecP := codecP) (codecC := codecC)
  have hm := S.merkle_bad_ratio_le codecP decP check id MerkleFS.Proof.parentClaim
    (check_parent child) (by decide) (Nat.zero_le _) (by simpa using hF) hTM
  have hh : density (fun ω : (Fin TM → D) × (MerkleFS.Point child → MerkleFS.Answer child) =>
      S.MerkleAccepts codecP check id MerkleFS.Proof.parentClaim ω.1 ω.2 ∧
        ¬ MerkleFS.explainsParent child decP body ω.1 ω.2) ≤
      (Bcs.AdaptiveCommit.adaptiveNumerator (checkFuel child) 0 (N+4) : ℚ)/Fintype.card D := by
    simpa only [MerkleFS.explainsParent,density,Fintype.card_prod,Fintype.card_fun,
      Fintype.card_fin,Nat.cast_mul,Nat.cast_pow,Nat.add_comm] using hm
  refine (density_mono (fun ω hf => ⟨hf.1.2.1,not_explains_zero child decP body ω.1 ω.2⟩)).trans (hh.trans ?_)
  rw [hcheck,hdigest]
  simp only [Bcs.AdaptiveCommit.adaptiveNumerator,Nat.zero_mul,Nat.mul_zero,
    Nat.zero_div,Nat.add_zero,Nat.zero_add,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat]
  unfold FSCompiledData.reserve
  have hn : (0 : ℚ) ≤ N := Nat.cast_nonneg _
  norm_num [FSCompiledData.checking,FSCompiledData.digestSize]
  linarith

/-- Budget-aware normalization retains both adaptive Merkle errors. The
zero-Merkle branch uses actual root guessing, not a free ideal FS trial. -/
theorem comparison_bound {tA N TM : ℕ}
    (body : TwoOracleTree Enc D (MerkleFS.Point child (D := D)) (MerkleFS.Answer child)
      (MerkleFS.Proof child (D := D) (SaltP := SaltP) (SaltC := SaltC)) tA N)
    (p : HahnSystemCertificate I) (cp : HahnSystemCertificate child.instance)
    (ha : FSMerkleCore81.Analysis child p cp) (σ : I.layer.Statement)
    (hcheck : checkFuel child = FSCompiledData.checking) (hdigest : Fintype.card D = FSCompiledData.digestSize)
    (ht : tA ≤ TM) (hF : checkFuel child+tA ≤ TM) (hTM : 1 ≤ TM)
    (hcap : N+tA ≤ FSCompiledData.fuelCap) (K e : ℚ)
    (hs : FSCoreData.rate+FSCompiledData.reserve ≤ K*e)
    (hz : FSCompiledData.reserve ≤ K*e) :
    density (fun ω : (Fin TM → D) × (MerkleFS.Point child → MerkleFS.Answer child) =>
      MerkleFS.extractionFailure child decP decC body p cp σ ω.1 ω.2) ≤ K*(N+tA+1)*e := by
  by_cases hpos : 1 ≤ tA
  · have h := extraction_failure_bound child decP decC body p cp ha σ ht hF hTM
    have hbc : merkleError child (D := D) tA N = FSCompiledData.bcs tA N := by
      simp only [merkleError,hcheck,hdigest,FSCompiledData.bcs]
    rw [hbc] at h
    exact h.trans (FSCoreCompiledData.comparison tA N (by omega) (by omega) hpos K e hs)
  · have htA : tA = 0 := by omega
    subst tA
    have h := no_merkle_failure_bound child decP decC body hcheck hdigest (by simpa using hF) hTM p cp σ
    have hz' := mul_le_mul_of_nonneg_left hz (show (0 : ℚ) ≤ N+1 by positivity)
    simpa only [Nat.cast_zero,add_zero,mul_assoc,mul_comm,mul_left_comm] using h.trans hz'

/-- Certificates are chosen before the adversary; all FS and Merkle work,
including zero budgets, is included in the complete comparison. -/
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
      probability ≤ (191/100 : ℚ)*(N+tA+1)*FSIOPReference81.strongIOPError ∧
      probability ≤ (1353/1000 : ℚ)*(N+tA+1)*FSDefect81.sameIOPError := by
  obtain ⟨p,cp,ha⟩ := FSMerkleCore81.analysis_exists child h0 h1 hq
  obtain ⟨hss,hws,_,hsz,hwz⟩ := FSCoreCompiledData.checked
  have hf : checkFuel child = FSCompiledData.checking := by
    simp only [checkFuel,h0.length,h1.length,FSCompiledData.checking]
  refine ⟨p,cp,fun σ tA N TM body ht hF hTM hcap => ?_⟩
  constructor
  · exact comparison_bound child decP decC body p cp ha σ hf hdigest ht (by simpa only [hf] using hF)
      hTM hcap (191/100) FSIOPReference81.strongIOPError hss hsz
  · exact comparison_bound child decP decC body p cp ha σ hf hdigest ht (by simpa only [hf] using hF)
      hTM hcap (1353/1000) FSDefect81.sameIOPError hws hwz

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
        (191/100 : ℚ)*(N+tA+1)*FSIOPReference81.strongIOPError := by
  obtain ⟨p,cp,hb⟩ := certified_comparisons child decP decC h0 h1 hq hdigest
  have he : density (fun ω : (Fin TM → D) × (MerkleFS.Point child → MerkleFS.Answer child) =>
      MerkleFS.accepts child body (codecP := codecP) (codecC := codecC) σ ω.1 ω.2) =
      density (fun ω : (Fin TM → D) × (MerkleFS.Point child (D := D) → MerkleFS.Answer child) => MerkleFS.extractionFailure child decP decC body p cp σ ω.1 ω.2) := by
    apply density_congr
    intro ω
    exact ⟨fun ha => ⟨ha,extractor_none_of_false child decP decC body p cp σ hfalse ω.1 ω.2⟩,fun hf => hf.1⟩
  rw [he]
  exact (hb σ tA N TM body ht hF hTM hcap).1

end RecursivePolygero.Instances.FSCoreCompiled81
