import polygero.Recursion.FSRootBridge
import polygero.Recursion.FSRootComposition

/-! Parameter-independent compilation from digest-root FS failure to the
actual opening verifier. Both adaptive Merkle/BCS errors are explicit. -/
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace RecursivePolygero.FiatShamir.MerkleFS
open Finset FiatShamir FiatShamir.TwoLevel ProfileAnalysis Bcs.TotalOracle.Footprint Bcs.FiniteProbability
open Merkle Merkle.MH Merkle.RandomOracle Merkle.RandomOracle.TwoOracleTree
open Bcs.AffineBlock
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
theorem extraction_failure_bound_of_root_bound (p : HahnSystemCertificate I) (cp : HahnSystemCertificate child.instance)
    (σ : I.layer.Statement) (fsBound : ℚ)
    (hfs : ∀ mt : Fin TM → D,
      density (fun H => MerkleFS.failure child (MerkleFS.context child body decP decC mt) p cp σ
        (MerkleFS.output child body mt H).candidate H) ≤ fsBound)
    (ht : tA ≤ TM) (hF : checkFuel child+tA ≤ TM) (hTM : 1 ≤ TM) :
    density (fun ω : (Fin TM → D) × (MerkleFS.Point child → MerkleFS.Answer child) =>
      MerkleFS.extractionFailure child decP decC body p cp σ ω.1 ω.2) ≤
      fsBound+merkleError child (D := D) tA N := by
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
  have hg : density good ≤ fsBound := by
    change density (fun ω : (Fin TM → D) × (MerkleFS.Point child → MerkleFS.Answer child) => good (ω.1,ω.2)) ≤ _
    rw [density_product_average (fun mt H => good (mt,H))]
    exact (average_mono hfs).trans_eq (average_const _)
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


/-- Arbitrary parent and child ABS prices compile with both adaptive BCS errors. -/
theorem extraction_failure_bound_of_blocks
    (p : HahnSystemCertificate I) (cp : HahnSystemCertificate child.instance)
    (σ : I.layer.Statement) (parentRate : Rate)
    (hparent : ∀ ctx : MerkleFS.Context child (D := D),
      OracleSound (MerkleFS.queryDomain child)
        (fun d : MerkleFS.Candidate child (D := D) => MerkleFS.queryRisk child ctx cp σ d.1 d.2.1) parentRate)
    (childRate : Rate)
    (hchild : ∀ ctx : MerkleFS.Context child (D := D),
      OracleSound (MerkleFS.terminalDomain child)
        (fun d H => MerkleFS.failure child ctx p cp σ d H ∧
          ¬ MerkleFS.queryRisk child ctx cp σ d.1 d.2.1 H) childRate)
    (ht : tA ≤ TM) (hF : MerkleFS.checkFuel child+tA ≤ TM) (hTM : 1 ≤ TM) :
    density (fun ω : (Fin TM → D) × (MerkleFS.Point child → MerkleFS.Answer child) =>
      MerkleFS.extractionFailure child decP decC body p cp σ ω.1 ω.2) ≤
      parentRate.intercept+childRate.intercept+N*max parentRate.slope childRate.slope+
        MerkleFS.merkleError child (D := D) tA N := by
  apply MerkleFS.extraction_failure_bound_of_root_bound child decP decC body p cp σ
    (parentRate.intercept+childRate.intercept+N*max parentRate.slope childRate.slope) ?_ ht hF hTM
  intro mt
  let ctx := MerkleFS.context child body decP decC mt
  let tree := ((MerkleFS.parentSetup child body).search mt).map MerkleFS.Proof.candidate
  have h := root_oracle_sound_of_blocks child p cp ctx σ parentRate (hparent ctx)
    childRate (hchild ctx) N tree
  have hcap' {n : ℕ}
      (tr : Tree (MerkleFS.Point child (D := D)) (MerkleFS.Answer child) (MerkleFS.Candidate child (D := D)) n)
      (H : MerkleFS.Point child (D := D) → MerkleFS.Answer child) :
      queryCost univ tr H ≤ (n : ℚ) := by
    induction tr with
    | done => simp [queryCost]
    | query q next ih => simpa only [queryCost,mem_univ,if_true,Nat.cast_add,Nat.cast_one,add_comm]
        using add_le_add_left (ih (H q)) 1
  have hcap := fun H => hcap' tree H
  have hb := h.cap N hcap
  simpa only [tree,ctx,Tree.run_map,MerkleFS.output,Bcs.TotalOracleCommit.Setup.proof_eq,mul_comm] using hb



end RecursivePolygero.FiatShamir.MerkleFS
