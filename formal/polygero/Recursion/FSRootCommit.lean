import polygero.Recursion.FSRootModel
import Bcs.CommitReplay

set_option maxHeartbeats 2000000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
namespace RecursivePolygero.FiatShamir.MerkleFS
open Finset ProfileAnalysis Local Local.Polygero Bcs.TotalOracle Bcs.TotalOracle.Footprint
open Merkle Merkle.MH Merkle.RandomOracle Merkle.RandomOracle.TwoOracleTree
open Bcs.TotalOracleCommit TwoLevel
open scoped Classical
variable {F D Enc SaltP SaltC : Type} [Field F] [Fintype F] [DecidableEq F]
  [Fintype D] [DecidableEq D] [Inhabited D] [DecidableEq Enc]
  [Inhabited SaltP] [Inhabited SaltC]
variable {I : Instance F} (child : Child I)

instance leafInhabited (J : Instance F) : Inhabited (Leaf J) :=
  ⟨(⟨fun _ _ => 0,fun _ => 0⟩,0)⟩

structure Proof where
  candidate : Candidate child (D := D)
  parentClaim : OpeningClaim I.n SaltP (Leaf I) D
  childClaim : OpeningClaim child.instance.n SaltC (Leaf child.instance) D

variable {tA N TM : ℕ}
variable (body : TwoOracleTree Enc D (Point child (D := D)) (Answer child)
  (Proof child (D := D) (SaltP := SaltP) (SaltC := SaltC)) tA N)

noncomputable def parentSetup : Bcs.TotalOracleCommit.Setup Enc D (Point child (D := D)) (Answer child)
    (Proof child (D := D) (SaltP := SaltP) (SaltC := SaltC)) D tA N 4 where
  body := body
  hashInput out k := if k = 0 then gamma out.candidate.1 else
    if k = 1 then query out.candidate.1 out.candidate.2.1 else
    if k = 2 then childGamma out.candidate.1 out.candidate.2.1 out.candidate.2.2.1 else terminal out.candidate
  dflt := Classical.choice inferInstance
  key := TwoLevel.root
  keyOut out := out.candidate.1
  hkey := by intro out k; split_ifs <;> rfl

/-- The child commitment is first named at any of the last three roles.
Its cut is allowed to occur after the parent's challenge has been read. -/
noncomputable def childSetup : Bcs.TotalOracleCommit.Setup Enc D (Point child (D := D)) (Answer child)
    (Proof child (D := D) (SaltP := SaltP) (SaltC := SaltC)) (Option (D × D)) tA N 3 where
  body := body
  hashInput out k := if k = 0 then query out.candidate.1 out.candidate.2.1 else
    if k = 1 then childGamma out.candidate.1 out.candidate.2.1 out.candidate.2.2.1 else terminal out.candidate
  dflt := Classical.choice inferInstance
  key := childCommitment child
  keyOut out := some (out.candidate.1,out.candidate.2.1)
  hkey := by intro out k; split_ifs <;> rfl

variable {codecP : Codec SaltP (Leaf I) D Enc} {codecC : Codec SaltC (Leaf child.instance) D Enc}
variable (decP : RoleDecoders codecP) (decC : RoleDecoders codecC)

noncomputable def cutOracle (J : Instance F) {Salt : Type} [Inhabited Salt]
    {codec : Codec Salt (Leaf J) D Enc} (dec : RoleDecoders codec) (rt : D) (tr : List (Enc × D)) : J.layer.Oracle :=
  oracleOfLeaves J ((extract dec J.n rt tr).elim (fun _ => default) Extracted.message)

noncomputable def context (mt : Fin TM → D) : Context child (D := D) where
  parent a H := cutOracle I decP a ((parentSetup child body).atOracle H |>.ctxAt mt Bcs.TotalOracleCommit.Setup.emptyTape a).2
  descendant ab H := cutOracle child.instance decC ab.2
    ((childSetup child body).atOracle H |>.ctxAt mt Bcs.TotalOracleCommit.Setup.emptyTape (some ab)).2
  parent_off := by
    intro a H H' ho
    have he := (parentSetup child body).ctxAt_off_finset mt a
      (univ.filter (fun x => TwoLevel.root x = a)) (by intro x hx; exact (mem_filter.mp hx).2)
      H H' (by intro x hx; exact ho x (by simpa using hx))
    exact congrArg (fun c => cutOracle I decP a c.2) he
  descendant_off := by
    intro ab H H' ho
    have he := (childSetup child body).ctxAt_off_finset mt (some ab)
      (univ.filter (fun x => childCommitment child x = some ab))
      (by intro x hx; exact (mem_filter.mp hx).2) H H'
      (by intro x hx; exact ho x (by simpa using hx))
    exact congrArg (fun c => cutOracle child.instance decC ab.2 c.2) he

/-- Both cut experiments use the same real Merkle oracle, despite their
different challenge replay schedules. -/
theorem merkleOracle_eq {fc : ℕ}
    (check : Proof child (D := D) (SaltP := SaltP) (SaltC := SaltC) → Tree Enc D Unit fc)
    (mt : Fin TM → D) (H : Point child (D := D) → Answer child) :
    (parentSetup child body).merkleOracle check mt H = (childSetup child body).merkleOracle check mt H := by
  rw [Bcs.TotalOracleCommit.Setup.merkleOracle_body,Bcs.TotalOracleCommit.Setup.merkleOracle_body]
  rfl

noncomputable def parentOpened (_child : Child I) (claim : OpeningClaim I.n SaltP (Leaf I) D) (q : I.layer.Query) :
    Local.Polygero.Opening F I.nw I.nq I.n I.t q :=
  (fun j => (claim.a j.1).1,fun j => (claim.a j.1).2)

noncomputable def childOpened (claim : OpeningClaim child.instance.n SaltC (Leaf child.instance) D)
    (q : child.instance.layer.Query) :
    Local.Polygero.Opening F child.instance.nw child.instance.nq child.instance.n child.instance.t q :=
  (fun j => (claim.a j.1).1,fun j => (claim.a j.1).2)

/-- The actual opening-only recursive verifier. Hashes contain digest roots,
the claimed parent query, and the terminal payload; they do not contain full oracles. -/
noncomputable def algebraAccepts (σ : I.layer.Statement)
    (out : Proof child (D := D) (SaltP := SaltP) (SaltC := SaltC)) (H : Point child (D := D) → Answer child) : Prop :=
  letI : Fintype (InnerEquations I.t) := child.instance.equationsFinite
  let d := out.candidate
  let a := (H (gamma d.1)).1.1
  let q := (H (query d.1 d.2.1)).1.2
  let b := (H (childGamma d.1 d.2.1 d.2.2.1)).2.1
  let t := (H (terminal d)).2.2
  q = d.2.2.1 ∧ out.parentClaim.I = d.2.2.1.coordinates ∧ out.childClaim.I = t.coordinates ∧
    directProducts d.2.2.1 (parentOpened child out.parentClaim d.2.2.1) ∧
    Local.Polygero.verify child.instance.domain (by have := child.instance.primary_le; omega)
      child.instance.layout
      (coefficientStatement I.domain (by have := I.primary_le; omega) I.layout σ child.packing
        a d.2.2.1 (parentOpened child out.parentClaim d.2.2.1))
      b d.2.2.2 t (childOpened child out.childClaim t) = true

end RecursivePolygero.FiatShamir.MerkleFS
