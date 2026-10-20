import polygero.Recursion.FSRootSoundness
import polygero.Instances.FSMerkle81
import polygero.Recursion.FSRootBridge

set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace RecursivePolygero.Instances.FSCompiled81
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

/-- Complete root-based knowledge soundness: algebraic, grinding, and
both adaptive Merkle extraction errors, with no omitted BCS premise. -/
theorem extraction_failure_bound (p : HahnSystemCertificate I) (cp : HahnSystemCertificate child.instance)
    (ha : FSMerkle81.Analysis child p cp) (σ : I.layer.Statement)
    (ht : tA ≤ TM) (hF : checkFuel child+tA ≤ TM) (hTM : 1 ≤ TM) :
    density (fun ω : (Fin TM → D) × (MerkleFS.Point child → MerkleFS.Answer child) =>
      MerkleFS.extractionFailure child decP decC body p cp σ ω.1 ω.2) ≤
      FSBaselineAware81.price+FSDefect81.childPrice+N*FSBaselineAware81.price+
        merkleError child (D := D) tA N := by
  apply MerkleFS.extraction_failure_bound_of_root_bound child decP decC body p cp σ
    (FSBaselineAware81.price+FSDefect81.childPrice+N*FSBaselineAware81.price) ?_ ht hF hTM
  intro mt
  have h := FSMerkle81.root_failure_bound child p cp ha (MerkleFS.context child body decP decC mt) σ
    (((MerkleFS.parentSetup child body).search mt).map MerkleFS.Proof.candidate)
  simpa only [Tree.run_map,MerkleFS.output,Bcs.TotalOracleCommit.Setup.proof_eq] using h

end RecursivePolygero.Instances.FSCompiled81
