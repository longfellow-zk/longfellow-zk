import polygero.Recursion.FSRootCommit

set_option maxHeartbeats 2000000
set_option maxRecDepth 20000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace RecursivePolygero.FiatShamir.MerkleFS
open Finset ProfileAnalysis Local Local.Polygero
open Bcs.TotalOracle Bcs.TotalOracle.Footprint
open Merkle Merkle.MH Merkle.RandomOracle Merkle.RandomOracle.TwoOracleTree
open Bcs.TotalOracleCommit TwoLevel
open scoped Classical
variable {F D Enc SaltP SaltC : Type} [Field F] [Fintype F] [DecidableEq F]
  [Fintype D] [DecidableEq D] [Inhabited D] [DecidableEq Enc]
  [Inhabited SaltP] [Inhabited SaltC]
variable {I : Instance F} (child : Child I)
variable {codecP : Codec SaltP (Leaf I) D Enc} {codecC : Codec SaltC (Leaf child.instance) D Enc}
variable (decP : RoleDecoders codecP) (decC : RoleDecoders codecC)
variable {tA N TM : ℕ}
variable (body : TwoOracleTree Enc D (Point child (D := D)) (Answer child)
  (Proof child (D := D) (SaltP := SaltP) (SaltC := SaltC)) tA N)

noncomputable def check (out : Proof child (D := D) (SaltP := SaltP) (SaltC := SaltC)) :
    Tree Enc D Unit (2*child.instance.n+2*I.n) :=
  ((checkPass codecP I.n out.parentClaim.I out.parentClaim.a out.parentClaim.pf (2*I.n) fun _ => default).map
    (fun _ => ())).bind (fun _ =>
      (checkPass codecC child.instance.n out.childClaim.I out.childClaim.a out.childClaim.pf
        (2*child.instance.n) fun _ => default).map (fun _ => ()))

def childRoot : Option (D × D) → D := fun x => x.elim default Prod.snd

noncomputable def output (mt : Fin TM → D) (H : Point child (D := D) → Answer child) :=
  (parentSetup child body).proof mt H

theorem child_output_eq (mt : Fin TM → D) (H : Point child (D := D) → Answer child) :
    (childSetup child body).proof mt H = output child body mt H := by
  rw [Bcs.TotalOracleCommit.Setup.proof_eq]
  unfold output
  rw [Bcs.TotalOracleCommit.Setup.proof_eq]
  rfl

noncomputable def explainsParent (mt : Fin TM → D) (H : Point child (D := D) → Answer child) : Prop :=
  (parentSetup child body).Explains decP id Proof.parentClaim mt H
noncomputable def explainsChild (mt : Fin TM → D) (H : Point child (D := D) → Answer child) : Prop :=
  (childSetup child body).Explains decC childRoot Proof.childClaim mt H

noncomputable def accepts (σ : I.layer.Statement) (mt : Fin TM → D)
    (H : Point child (D := D) → Answer child) : Prop :=
  algebraAccepts child σ (output child body mt H) H ∧
    (parentSetup child body).MerkleAccepts codecP (check child (codecP := codecP) (codecC := codecC))
      id Proof.parentClaim mt H ∧
    (childSetup child body).MerkleAccepts codecC (check child (codecP := codecP) (codecC := codecC))
      childRoot Proof.childClaim mt H

noncomputable def extractor (p : HahnSystemCertificate I) (cp : HahnSystemCertificate child.instance)
    (σ : I.layer.Statement) (mt : Fin TM → D) (H : Point child (D := D) → Answer child) :=
  let ctx := context child body decP decC mt
  let d := (output child body mt H).candidate
  let e := extractedCandidate child ctx d H
  (twoProof child p cp).run σ e.1 (constantMessages child e)
    (proofCoins child (liftOracle child d.1 d.2.1 H) e)

noncomputable def extractionFailure (p : HahnSystemCertificate I) (cp : HahnSystemCertificate child.instance)
    (σ : I.layer.Statement) (mt : Fin TM → D) (H : Point child (D := D) → Answer child) : Prop :=
  accepts child body (codecP := codecP) (codecC := codecC) σ mt H ∧
    extractor child decP decC body p cp σ mt H = none

/-- Merkle leaf agreement gives equality of the exact Polygero opening. -/
theorem opened_eq (J : Instance F) {Salt : Type} (claim : OpeningClaim J.n Salt (Leaf J) D)
    (q : J.layer.Query) (m : Fin J.n → Leaf J)
    (hI : claim.I = q.coordinates) (hm : ∀ j ∈ claim.I, m j = claim.a j) :
    openOracle (oracleOfLeaves J m) q = openOracle (oracleOfLeaves J claim.a) q := by
  apply Prod.ext
  · funext j
    change (m j.1).1 = (claim.a j.1).1
    rw [hm j.1 (by rw [hI]; exact j.property)]
  · funext j
    change (m j.1).2 = (claim.a j.1).2
    rw [hm j.1 (by rw [hI]; exact j.property)]

/-- All accepted equations and the recursive child statement are transported
from the submitted leaves to the actual cut-trace-extracted oracles. -/
theorem accepts_of_explains (σ : I.layer.Statement) (mt : Fin TM → D)
    (H : Point child (D := D) → Answer child)
    (ha : algebraAccepts child σ (output child body mt H) H)
    (hp : explainsParent child decP body mt H) (hc : explainsChild child decC body mt H) :
    TwoLevel.accepts child σ
      (liftOracle child (output child body mt H).candidate.1 (output child body mt H).candidate.2.1 H)
      (extractedCandidate child (context child body decP decC mt) (output child body mt H).candidate H) := by
  letI : Fintype (InnerEquations I.t) := child.instance.equationsFinite
  let out := output child body mt H
  let d := out.candidate
  let ctx := context child body decP decC mt
  change ∃ e, _ at hp
  obtain ⟨ep,hep,hmp,_⟩ := hp
  change ∃ e, _ at hc
  obtain ⟨ec,hec,hmc,_⟩ := hc
  have hcp : (childSetup child body).proof mt H = out := child_output_eq child body mt H
  have hpp : (parentSetup child body).proof mt H = out := rfl
  change extract decP I.n ((parentSetup child body).proof mt H).candidate.1
    (((parentSetup child body).atOracle H).cutTrace mt Bcs.TotalOracleCommit.Setup.emptyTape
      ((parentSetup child body).proof mt H).candidate.1) = some ep at hep
  change ∀ j ∈ ((parentSetup child body).proof mt H).parentClaim.I,
    ep.message j = ((parentSetup child body).proof mt H).parentClaim.a j at hmp
  change extract decC child.instance.n ((childSetup child body).proof mt H).candidate.2.1
    (((childSetup child body).atOracle H).cutTrace mt Bcs.TotalOracleCommit.Setup.emptyTape
      (some (((childSetup child body).proof mt H).candidate.1,
        ((childSetup child body).proof mt H).candidate.2.1))) = some ec at hec
  change ∀ j ∈ ((childSetup child body).proof mt H).childClaim.I,
    ec.message j = ((childSetup child body).proof mt H).childClaim.a j at hmc
  rw [hpp] at hep hmp
  rw [hcp] at hec hmc
  have hW : ctx.parent d.1 H = oracleOfLeaves I ep.message := by
    change cutOracle I decP d.1 _ = _
    change oracleOfLeaves I ((extract decP I.n out.candidate.1
      (((parentSetup child body).atOracle H).cutTrace mt Bcs.TotalOracleCommit.Setup.emptyTape out.candidate.1)).elim
        (fun _ => default) Extracted.message) = _
    rw [hep]
    rfl
  have hV : ctx.descendant (d.1,d.2.1) H = oracleOfLeaves child.instance ec.message := by
    change cutOracle child.instance decC d.2.1 _ = _
    change oracleOfLeaves child.instance ((extract decC child.instance.n out.candidate.2.1
      (((childSetup child body).atOracle H).cutTrace mt Bcs.TotalOracleCommit.Setup.emptyTape
        (some (out.candidate.1,out.candidate.2.1)))).elim (fun _ => default) Extracted.message) = _
    rw [hec]
    rfl
  obtain ⟨hq,hIp,hIc,hd,hv⟩ := ha
  have hpo := opened_eq I out.parentClaim d.2.2.1 ep.message hIp hmp
  have hco := opened_eq child.instance out.childClaim (H (terminal d)).2.2 ec.message hIc hmc
  have hpo' : openOracle (ctx.parent d.1 H) d.2.2.1 = parentOpened child out.parentClaim d.2.2.1 := by
    rw [hW]
    exact hpo
  have hco' : openOracle (ctx.descendant (d.1,d.2.1) H) (H (terminal d)).2.2 =
      childOpened child out.childClaim (H (terminal d)).2.2 := by
    rw [hV]
    exact hco
  rw [TwoLevel.accepts_iff]
  refine ⟨hq,?_,?_⟩
  · change directProducts d.2.2.1 (openOracle (ctx.parent d.1 H) d.2.2.1)
    rwa [hpo']
  · change child.instance.layer.verify
      (child.link.statement σ (ctx.parent d.1 H) (H (gamma d.1)).1.1 d.2.2.1)
      (ctx.descendant (d.1,d.2.1) H) (H (childGamma d.1 d.2.1 d.2.2.1)).2.1
      d.2.2.2 (H (terminal d)).2.2
    dsimp only [Instance.layer,Child.link]
    rw [hpo']
    exact Eq.mpr (congrArg (fun opening => Local.Polygero.verify child.instance.domain
      (by have := child.instance.primary_le; omega) child.instance.layout
      (coefficientStatement I.domain (by have := I.primary_le; omega) I.layout σ child.packing
        (H (gamma d.1)).1.1 d.2.2.1 (parentOpened child out.parentClaim d.2.2.1))
      (H (childGamma d.1 d.2.1 d.2.2.1)).2.1 d.2.2.2 (H (terminal d)).2.2 opening = true) hco') hv

/-- The actual extractor failure is covered by the root-context event once
both Merkle explanations hold. No conditioning of the oracle distribution. -/
theorem failure_of_explains (p : HahnSystemCertificate I) (cp : HahnSystemCertificate child.instance)
    (σ : I.layer.Statement) (mt : Fin TM → D) (H : Point child (D := D) → Answer child)
    (hf : extractionFailure child decP decC body p cp σ mt H)
    (hp : explainsParent child decP body mt H) (hc : explainsChild child decC body mt H) :
    failure child (context child body decP decC mt) p cp σ (output child body mt H).candidate H := by
  rw [failure,TwoLevel.failure_empty_iff]
  exact ⟨accepts_of_explains child decP decC body σ mt H hf.1.1 hp hc,hf.2⟩

end RecursivePolygero.FiatShamir.MerkleFS
