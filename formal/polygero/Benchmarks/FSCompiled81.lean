import polygero.Benchmarks.FSMerkle81
import polygero.Recursion.FSRootBridge

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
variable {tA N TM : ℕ}
variable (body : TwoOracleTree Enc D (MerkleFS.Point child (D := D)) (MerkleFS.Answer child)
  (MerkleFS.Proof child (D := D) (SaltP := SaltP) (SaltC := SaltC)) tA N)

noncomputable abbrev checkFuel := 2*child.instance.n+2*I.n

noncomputable def merkleError (tA N : ℕ) : ℚ :=
  ((Bcs.AdaptiveCommit.adaptiveNumerator (checkFuel child) tA (N+4) +
    Bcs.AdaptiveCommit.adaptiveNumerator (checkFuel child) tA (N+3) : ℕ) : ℚ)/Fintype.card D

/-- Both real checks are contained in one actual Merkle-oracle execution. -/
theorem check_parent (H : Enc → D) (out : MerkleFS.Proof child (D := D) (SaltP := SaltP) (SaltC := SaltC))
    (qa : Enc × D) (hqa : qa ∈ ((checkPass codecP I.n out.parentClaim.I out.parentClaim.a
      out.parentClaim.pf (2*I.n) fun _ => default).run H).2) :
    qa ∈ ((MerkleFS.check child (codecP := codecP) (codecC := codecC) out).run H).2 := by
  rw [MerkleFS.check,Tree.run_bind]
  apply List.mem_append_left
  simpa only [Tree.run_map] using hqa

theorem check_child (H : Enc → D) (out : MerkleFS.Proof child (D := D) (SaltP := SaltP) (SaltC := SaltC))
    (qa : Enc × D) (hqa : qa ∈ ((checkPass codecC child.instance.n out.childClaim.I out.childClaim.a
      out.childClaim.pf (2*child.instance.n) fun _ => default).run H).2) :
    qa ∈ ((MerkleFS.check child (codecP := codecP) (codecC := codecC) out).run H).2 := by
  rw [MerkleFS.check,Tree.run_bind]
  apply List.mem_append_right
  simpa only [Tree.run_map] using hqa

/-- Complete root-based knowledge soundness: algebraic, grinding, and
both adaptive Merkle extraction errors, with no omitted BCS premise. -/
theorem extraction_failure_bound (p : HahnSystemCertificate I) (cp : HahnSystemCertificate child.instance)
    (ha : FSMerkle81.Analysis child p cp) (σ : I.layer.Statement)
    (ht : tA ≤ TM) (hF : checkFuel child+tA ≤ TM) (hTM : 1 ≤ TM) :
    density (fun ω : (Fin TM → D) × (MerkleFS.Point child → MerkleFS.Answer child) =>
      MerkleFS.extractionFailure child decP decC body p cp σ ω.1 ω.2) ≤
      FSBaselineAware81.price+FSDefect81.childPrice+N*FSBaselineAware81.price+
        merkleError child (D := D) tA N := by
  let S0 := MerkleFS.parentSetup child body
  let S1 := MerkleFS.childSetup child body
  let check := MerkleFS.check child (codecP := codecP) (codecC := codecC)
  let bad0 (ω : (Fin TM → D) × (MerkleFS.Point child → MerkleFS.Answer child)) :=
    S0.MerkleAccepts codecP check id MerkleFS.Proof.parentClaim ω.1 ω.2 ∧
      ¬ MerkleFS.explainsParent child decP body ω.1 ω.2
  let bad1 (ω : (Fin TM → D) × (MerkleFS.Point child → MerkleFS.Answer child)) :=
    S1.MerkleAccepts codecC check MerkleFS.childRoot MerkleFS.Proof.childClaim ω.1 ω.2 ∧
      ¬ MerkleFS.explainsChild child decC body ω.1 ω.2
  let good (ω : (Fin TM → D) × (MerkleFS.Point child → MerkleFS.Answer child)) :=
    MerkleFS.failure child (MerkleFS.context child body decP decC ω.1) p cp σ
      (MerkleFS.output child body ω.1 ω.2).candidate ω.2
  let piece : Fin 3 → _ → Prop := ![good,bad0,bad1]
  have hg : density good ≤ FSBaselineAware81.price+FSDefect81.childPrice+N*FSBaselineAware81.price := by
    change density (fun ω : (Fin TM → D) × (MerkleFS.Point child → MerkleFS.Answer child) => good (ω.1,ω.2)) ≤ _
    rw [density_product_average (fun mt H => good (mt,H))]
    change average (fun mt => density (fun H => good (mt,H))) ≤ _
    have hm (mt : Fin TM → D) : density (fun H => good (mt,H)) ≤
        FSBaselineAware81.price+FSDefect81.childPrice+N*FSBaselineAware81.price := by
      have h := FSMerkle81.root_failure_bound child p cp ha (MerkleFS.context child body decP decC mt) σ
        ((S0.search mt).map MerkleFS.Proof.candidate)
      simpa only [Tree.run_map,MerkleFS.output,Bcs.TotalOracleCommit.Setup.proof_eq,good,S0] using h
    exact (average_mono hm).trans (le_of_eq (average_const _))
  have hb0 : density bad0 ≤ (Bcs.AdaptiveCommit.adaptiveNumerator (checkFuel child) tA (N+4) : ℚ)/Fintype.card D := by
    have h := S0.merkle_bad_ratio_le codecP decP check id MerkleFS.Proof.parentClaim
      (check_parent child) (by decide) ht hF hTM
    simpa only [bad0,MerkleFS.explainsParent,density,Fintype.card_prod,Fintype.card_fun,
      Fintype.card_fin,Nat.cast_mul,Nat.cast_pow,Nat.add_comm] using h
  have hb1 : density bad1 ≤ (Bcs.AdaptiveCommit.adaptiveNumerator (checkFuel child) tA (N+3) : ℚ)/Fintype.card D := by
    have h := S1.merkle_bad_ratio_le codecC decC check MerkleFS.childRoot MerkleFS.Proof.childClaim
      (check_child child) (by decide) ht hF hTM
    simpa only [bad1,MerkleFS.explainsChild,density,Fintype.card_prod,Fintype.card_fun,
      Fintype.card_fin,Nat.cast_mul,Nat.cast_pow,Nat.add_comm] using h
  have hu := density_union_le (fun ω => MerkleFS.extractionFailure child decP decC body p cp σ ω.1 ω.2)
    piece (by
      intro ω hf
      by_cases hp : MerkleFS.explainsParent child decP body ω.1 ω.2
      · by_cases hc : MerkleFS.explainsChild child decC body ω.1 ω.2
        · exact ⟨0,MerkleFS.failure_of_explains child decP decC body p cp σ ω.1 ω.2 hf hp hc⟩
        · exact ⟨2,hf.1.2.2,hc⟩
      · exact ⟨1,hf.1.2.1,hp⟩)
  simp only [piece,Fin.sum_univ_succ,Fin.sum_univ_zero,Matrix.cons_val_zero,
    Matrix.cons_val_succ,Matrix.head_cons,add_zero] at hu
  unfold merkleError
  push_cast
  rw [add_div]
  linarith

end RecursivePolygero.Benchmarks.FSCompiled81
