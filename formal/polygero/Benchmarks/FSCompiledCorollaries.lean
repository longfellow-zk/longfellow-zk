import polygero.Benchmarks.FSCompiled81
import polygero.Benchmarks.FSCompiledData
import polygero.Recursion.FSRootCodec

set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace RecursivePolygero.Benchmarks.FSCompiled81
open Finset FiatShamir FiatShamir.TwoLevel ProfileAnalysis Bcs.TotalOracle.Footprint Bcs.FiniteProbability
open Merkle Merkle.MH Merkle.RandomOracle Merkle.RandomOracle.TwoOracleTree
open scoped Classical
variable {F D Enc SaltP SaltC : Type} [Field F] [Fintype F] [DecidableEq F]
  [Fintype D] [DecidableEq D] [Inhabited D] [DecidableEq Enc]
  [Inhabited SaltP] [Inhabited SaltC]
variable {I : Instance F} (child : Child I)
variable {codecP : Codec SaltP (MerkleFS.Leaf I) D Enc}
  {codecC : Codec SaltC (MerkleFS.Leaf child.instance) D Enc}
variable (decP : RoleDecoders codecP) (decC : RoleDecoders codecC)

/-- With no Merkle queries, no root can have a cut-trace extraction. -/
theorem not_explains_zero {N TM : ℕ}
    (body : TwoOracleTree Enc D (MerkleFS.Point child (D := D)) (MerkleFS.Answer child)
      (MerkleFS.Proof child (D := D) (SaltP := SaltP) (SaltC := SaltC)) 0 N)
    (mt : Fin TM → D) (H : MerkleFS.Point child (D := D) → MerkleFS.Answer child) :
    ¬ MerkleFS.explainsParent child decP body mt H := by
  intro hp
  obtain ⟨e,he,_,_⟩ := hp
  let S := MerkleFS.parentSetup child body
  change extract decP I.n (MerkleFS.output child body mt H).candidate.1
    (((S.atOracle H).ctxAt mt Bcs.TotalOracleCommit.Setup.emptyTape
      (MerkleFS.output child body mt H).candidate.1).2) = some e at he
  rw [Bcs.TotalOracleCommit.Setup.cutTrace_zero] at he
  simp [extract] at he

/-- The all-zero-work case is paid entirely by the retained BCS root-guess
term, rather than by an extra ideal FS trial. -/
theorem zero_work_failure_bound {TM : ℕ}
    (body : TwoOracleTree Enc D (MerkleFS.Point child (D := D)) (MerkleFS.Answer child)
      (MerkleFS.Proof child (D := D) (SaltP := SaltP) (SaltC := SaltC)) 0 0)
    (hcheck : checkFuel child = FSCompiledData.checking)
    (hdigest : Fintype.card D = FSCompiledData.digestSize)
    (hF : checkFuel child ≤ TM) (hTM : 1 ≤ TM)
    (p : HahnSystemCertificate I) (cp : HahnSystemCertificate child.instance) (σ : I.layer.Statement) :
    density (fun ω : (Fin TM → D) × (MerkleFS.Point child → MerkleFS.Answer child) =>
      MerkleFS.extractionFailure child decP decC body p cp σ ω.1 ω.2) ≤ FSCompiledData.reserve := by
  let S := MerkleFS.parentSetup child body
  let check := MerkleFS.check child (codecP := codecP) (codecC := codecC)
  have hm := S.merkle_bad_ratio_le codecP decP check id MerkleFS.Proof.parentClaim
    (check_parent child) (by decide) (Nat.zero_le _) (by simpa using hF) hTM
  have hh : density (fun ω : (Fin TM → D) × (MerkleFS.Point child → MerkleFS.Answer child) =>
      S.MerkleAccepts codecP check id MerkleFS.Proof.parentClaim ω.1 ω.2 ∧
        ¬ MerkleFS.explainsParent child decP body ω.1 ω.2) ≤
      (Bcs.AdaptiveCommit.adaptiveNumerator (checkFuel child) 0 4 : ℚ)/Fintype.card D := by
    simpa only [MerkleFS.explainsParent,density,Fintype.card_prod,Fintype.card_fun,
      Fintype.card_fin,Nat.cast_mul,Nat.cast_pow] using hm
  refine (density_mono (fun ω hf => ⟨hf.1.2.1,not_explains_zero child decP body ω.1 ω.2⟩)).trans (hh.trans ?_)
  rw [hcheck,hdigest]
  norm_num [Bcs.AdaptiveCommit.adaptiveNumerator,FSCompiledData.reserve,
    FSCompiledData.checking,FSCompiledData.digestSize]

/-- The actual extractor's output is valid for the original parent statement. -/
theorem extractor_none_of_false {N tA TM : ℕ}
    (body : TwoOracleTree Enc D (MerkleFS.Point child (D := D)) (MerkleFS.Answer child)
      (MerkleFS.Proof child (D := D) (SaltP := SaltP) (SaltC := SaltC)) tA N)
    (p : HahnSystemCertificate I) (cp : HahnSystemCertificate child.instance) (σ : I.layer.Statement)
    (hfalse : ∀ witness, ¬ I.layer.satisfies σ witness)
    (mt : Fin TM → D) (H : MerkleFS.Point child (D := D) → MerkleFS.Answer child) :
    MerkleFS.extractor child decP decC body p cp σ mt H = none := by
  unfold MerkleFS.extractor
  dsimp only
  cases he : (twoProof child p cp).run σ _ _ _ with
  | none => rfl
  | some g => exact (hfalse _ ((twoProof child p cp).run_valid _ _ _ _ g he)).elim

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
          FSBaselineAware81.price+FSDefect81.childPrice+N*FSBaselineAware81.price+FSCompiledData.bcs tA N := by
  obtain ⟨p,cp,ha⟩ := FSMerkle81.analysis_exists child h0 h1 hq
  refine ⟨p,cp,fun σ tA N TM body ht hF hTM => ?_⟩
  have hf : checkFuel child = FSCompiledData.checking := by
    simp only [checkFuel,h0.length,h1.length,FSCompiledData.checking]
  have h := extraction_failure_bound child decP decC body p cp ha σ ht (by simpa only [hf] using hF) hTM
  simpa only [merkleError,hf,hdigest,FSCompiledData.bcs] using h

/-- Quantitative comparison in total adversarial work, including all zero
budgets. The only work restriction is the explicit cap used for the
birthday term; the unnormalized theorem above has no such restriction. -/
theorem comparison_bound {tA N TM : ℕ}
    (body : TwoOracleTree Enc D (MerkleFS.Point child (D := D)) (MerkleFS.Answer child)
      (MerkleFS.Proof child (D := D) (SaltP := SaltP) (SaltC := SaltC)) tA N)
    (p : HahnSystemCertificate I) (cp : HahnSystemCertificate child.instance)
    (ha : FSMerkle81.Analysis child p cp) (σ : I.layer.Statement)
    (hcheck : checkFuel child = FSCompiledData.checking) (hdigest : Fintype.card D = FSCompiledData.digestSize)
    (ht : tA ≤ TM) (hF : checkFuel child+tA ≤ TM) (hTM : 1 ≤ TM)
    (hcap : N+tA ≤ FSCompiledData.fuelCap) (K e : ℚ)
    (hi : 2*FSBaselineAware81.price+FSDefect81.childPrice+2*FSCompiledData.reserve ≤ 2*K*e)
    (hs : FSBaselineAware81.price+FSCompiledData.reserve ≤ K*e)
    (hz : FSCompiledData.reserve ≤ K*e) :
    density (fun ω : (Fin TM → D) × (MerkleFS.Point child → MerkleFS.Answer child) =>
      MerkleFS.extractionFailure child decP decC body p cp σ ω.1 ω.2) ≤ K*(N+tA+1)*e := by
  by_cases hpos : 1 ≤ N+tA
  · have h := extraction_failure_bound child decP decC body p cp ha σ ht hF hTM
    have hbc : merkleError child (D := D) tA N = FSCompiledData.bcs tA N := by
      simp only [merkleError,hcheck,hdigest,FSCompiledData.bcs]
    rw [hbc] at h
    exact h.trans (FSCompiledData.comparison tA N (by omega) (by omega) hpos K e hi hs)
  · have hN : N = 0 := by omega
    have htA : tA = 0 := by omega
    subst N; subst tA
    simpa only [Nat.cast_zero,zero_add,mul_one] using
      (zero_work_failure_bound child decP decC body hcheck hdigest (by simpa using hF) hTM p cp σ).trans hz

end RecursivePolygero.Benchmarks.FSCompiled81
