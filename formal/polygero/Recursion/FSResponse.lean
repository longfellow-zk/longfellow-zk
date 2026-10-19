import polygero.Recursion.FSTransfer
import polygero.Local.ResponseRigidity

/-!
# Two-level transfer for actual full-system response incidences

Response rigidity is proved from the Polygero equations, rather than
assumed as a fanout parameter. Proper systems and global FS query charging
are not covered by this local full-system theorem.
-/

namespace RecursivePolygero.FiatShamir

open Finset Counting ProfileAnalysis
open scoped Classical

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {I : Instance F} (child : Child I)
variable (p : HahnSystemCertificate I) (cp : HahnSystemCertificate child.instance)

noncomputable def fullResponseSeam
    (sigma : I.layer.Statement) (W : I.layer.Oracle)
    (V : I.layer.Coin → child.instance.layer.Oracle)
    (D : (tupleCounts I).Index → Prop) (a : I.layer.Coin)
    (T : Finset (systems child.instance.domain child.instance.primary_le (V a)))
    (q : I.layer.Query) (b : child.instance.layer.Coin) : ℚ :=
  let sigma' := child.link.statement sigma W a q
  let E := Protocol.ProfileProof.inducedFamily (child := child) sigma W a D q
  responseIncidence child.instance cp sigma' (V a) b
    (coveredFullResponses child.instance cp sigma' (V a) b E T)

theorem fullResponseSeam_le_incidence
    (sigma : I.layer.Statement) (W : I.layer.Oracle)
    (V : I.layer.Coin → child.instance.layer.Oracle)
    (D : (tupleCounts I).Index → Prop) (a : I.layer.Coin)
    (T : Finset (systems child.instance.domain child.instance.primary_le (V a)))
    (q : I.layer.Query) (b : child.instance.layer.Coin) :
    fullResponseSeam child cp sigma W V D a T q b ≤
      localIncidence child.instance cp (child.link.statement sigma W a q) (V a) T
        (Protocol.ProfileProof.inducedFamily (child := child) sigma W a D q) b :=
  responseIncidence_le_localIncidence child.instance cp _ _ _ _ _ T
    (fun _ => coveredFullResponses_cover child.instance cp _ _ _ _ T)

/-- The actual sum of covered terminal-response excesses has the same seam
budget as the earlier system incidence. No payload-cardinality factor. -/
theorem seam_fullResponse_mean_le
    (sigma : I.layer.Statement) (W : I.layer.Oracle)
    (V : I.layer.Coin → child.instance.layer.Oracle)
    (D : (tupleCounts I).Index → Prop) (a : I.layer.Coin)
    (T : Finset (systems child.instance.domain child.instance.primary_le (V a)))
    (hT : T.card ≤ Nat.card F) :
    mean (fun q => mean (fullResponseSeam child cp sigma W V D a T q)) ≤
      transfer cp.error (localEnvelope I p.toProfileParameters sigma W p.threshold D a) := by
  exact (mean_mono (fun q => mean_mono (fun b =>
    fullResponseSeam_le_incidence child cp sigma W V D a T q b))).trans
      (seam_incidence_mean_le child p cp sigma W V D a T hT)

/-- This is a two-level bound on a sum over actual responses, retaining the
random-target quantifier and the affine cross term. The covering system
family may depend on `z,a,V`, but not on the seam answers `q,b`. -/
theorem twoLevel_fullResponse_mean_le
    {Z : Type} [Fintype Z] [Nonempty Z]
    (sigma : Z → I.layer.Statement) (W : I.layer.Oracle)
    (V : Z → I.layer.Coin → child.instance.layer.Oracle)
    (D : Z → (tupleCounts I).Index → Prop) (rate : ℚ)
    (hr0 : 0 ≤ rate) (hr1 : rate ≤ 1)
    (hD : ∀ g, mean (fun z => indicator (D z g)) ≤ rate)
    (T : ∀ z a, Finset (systems child.instance.domain child.instance.primary_le (V z a)))
    (hT : ∀ z a, (T z a).card ≤ Nat.card F) :
    mean (fun z => mean (fun a => mean (fun q =>
      mean (fullResponseSeam child cp (sigma z) W (V z) (D z) a (T z a) q)))) ≤
        transfer (twoError p.error cp.error) rate := by
  exact (mean_mono (fun z => mean_mono (fun a => mean_mono (fun q => mean_mono (fun b =>
    fullResponseSeam_le_incidence child cp (sigma z) W (V z) (D z) a (T z a) q b))))).trans
      (twoLevel_incidence_mean_le child p cp sigma W V D rate hr0 hr1 hD T hT)

/-- The proper-system residual has a uniform price across the parent query:
the child oracle and its proper-system family are fixed before the seam. -/
theorem seam_properException_mean_le
    (sigma : I.layer.Statement) (W : I.layer.Oracle)
    (V : I.layer.Coin → child.instance.layer.Oracle) (a : I.layer.Coin)
    (T : Finset (systems child.instance.domain child.instance.primary_le (V a))) :
    mean (fun q => mean (fun b => indicator (properException child.instance cp
      (child.link.statement sigma W a q) (V a) T b))) ≤
      ((T.filter (fun d => Local.Affine.consistent
        (LigeroFamily.PolynomialDirect.primaryCode child.instance.domain child.instance.primary_le)
        (Local.Polygero.oracleWords (V a).ordinary) (V a).proximityMask d.1 ≠ univ)).card : ℚ) /
        Nat.card F := by
  exact mean_le (fun q => properException_mean_le child.instance cp
    (child.link.statement sigma W a q) (V a) T)

end RecursivePolygero.FiatShamir
