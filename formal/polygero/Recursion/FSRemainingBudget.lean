import Bcs.CachedPotential
import polygero.Recursion.FSRootSoundness

/-! End-to-end adapter for a remaining-budget potential on the actual ROM
cache. The Bellman inequalities are explicit obligations, not a claim that
the scalar renewal calculation already proves them for Polygero. Both
adaptive Merkle/BCS errors are retained without conditioning on their absence. -/
namespace RecursivePolygero.FiatShamir.MerkleFS.RemainingBudget
open Finset FiatShamir ProfileAnalysis Bcs.TotalOracle.Footprint Bcs.FiniteProbability
open Bcs.TotalOracle.CachedPotential
open Merkle Merkle.MH Merkle.RandomOracle Merkle.RandomOracle.TwoOracleTree
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

noncomputable def payoff (p : HahnSystemCertificate I) (cp : HahnSystemCertificate child.instance)
    (σ : I.layer.Statement) (mt : Fin TM → D)
    (out : MerkleFS.Proof child (D := D) (SaltP := SaltP) (SaltC := SaltC))
    (H : MerkleFS.Point child (D := D) → MerkleFS.Answer child) : ℚ :=
  if MerkleFS.failure child (MerkleFS.context child body decP decC mt) p cp σ out.candidate H then 1 else 0

/-- The final oracle is a genuine cached total random function. The
potential may depend on the fixed Merkle tape, but its initial bound is
uniform. The terminal inequality includes all four verifier coordinates. -/
theorem extraction_failure_bound (p : HahnSystemCertificate I) (cp : HahnSystemCertificate child.instance)
    (σ : I.layer.Statement)
    (potential : (Fin TM → D) → ℕ → Cache (MerkleFS.Point child (D := D)) (MerkleFS.Answer child) → ℚ)
    (hstop : ∀ mt n cache out,
      conditional cache (payoff child decP decC body p cp σ mt out) ≤ potential mt n cache)
    (hhit : ∀ mt n cache, potential mt n cache ≤ potential mt (n+1) cache)
    (hmiss : ∀ mt n cache q, cache q = none →
      average (fun c => potential mt n (record cache q c)) ≤ potential mt (n+1) cache)
    (bound : ℚ) (hinit : ∀ mt, potential mt N (fun _ => none) ≤ bound)
    (ht : tA ≤ TM) (hF : MerkleFS.checkFuel child+tA ≤ TM) (hTM : 1 ≤ TM) :
    density (fun ω : (Fin TM → D) × (MerkleFS.Point child (D := D) → MerkleFS.Answer child) =>
      MerkleFS.extractionFailure child decP decC body p cp σ ω.1 ω.2) ≤
      bound+MerkleFS.merkleError child (D := D) tA N := by
  apply MerkleFS.extraction_failure_bound_of_root_bound child decP decC body p cp σ bound ?_ ht hF hTM
  intro mt
  have h := totalOracle_le_timePotential (payoff child decP decC body p cp σ mt)
    (potential mt) (hstop mt) (hhit mt) (hmiss mt) ((MerkleFS.parentSetup child body).search mt)
  rw [Bcs.AffineBlock.density_eq_average]
  simpa only [payoff,MerkleFS.output,Bcs.TotalOracleCommit.Setup.proof_eq] using h.trans (hinit mt)

end RecursivePolygero.FiatShamir.MerkleFS.RemainingBudget
