import polygero.Recursion.FSGrinding
import Merkle.TreeCompose

/-! A bounded adaptive implementation of the two-stage grinding search.
The program receives only answers to its explicit queries. It checks the
terminal avoiding-coordinate gate before returning a proof. -/

namespace RecursivePolygero.FiatShamir.TwoLevel

open Finset ProfileAnalysis ProfileAnalysis.HonestCompletion Local Local.Polygero
open LigeroFamily Merkle.RandomOracle
open scoped Classical

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {I : Instance F} (child : Child I)

/-- A successful parent challenge determines a fixed payload before any
child query is sampled. The good-query predicate is an executable finite
predicate; its verifier guarantee is proved by the parent algebra. -/
structure GrindingReady (sigma : I.layer.Statement) (W : I.layer.Oracle)
    (a : I.layer.Coin) where
  payload : I.layer.Payload
  goodQueries : I.layer.Query → Prop
  parent_accepts : ∀ Q, goodQueries Q → I.layer.verify sigma W a payload Q

noncomputable def grindingCompletionProof
    (hk : 1 ≤ child.instance.r + child.instance.w)
    (sigma : I.layer.Statement) (W : I.layer.Oracle) (a : I.layer.Coin)
    (payload : I.layer.Payload) (row : child.instance.WireRow false)
    (col : Fin child.instance.n) (c : F) (Q : I.layer.Query)
    (b : child.instance.layer.Coin) : Proof child :=
  (W, grindingCommitment child payload row col c, Q,
    GrindingAlgebra.canonicalPayload child.instance hk
      (child.link.statement sigma W a Q) b
      (rows child.instance (unflatten (pack child.packing payload))))

/-- Complete a good parent query using exactly the observed child coin,
then test the actual terminal answer. -/
noncomputable def grindingFinish
    (hk : 1 ≤ child.instance.r + child.instance.w)
    (sigma : I.layer.Statement) (W : I.layer.Oracle) (a : I.layer.Coin)
    (payload : I.layer.Payload) (row : child.instance.WireRow false)
    (col : Fin child.instance.n) (c : F) (Q : I.layer.Query) :
    Tree (HashInput child) (Answer child) (Option (Proof child)) 2 :=
  .query (childGamma W (grindingCommitment child payload row col c) Q) fun answer =>
    let d := grindingCompletionProof child hk sigma W a payload row col c Q answer.2.1
    .query (terminal d) fun last =>
      if col ∉ last.2.2.coordinates then .done (some d) else .done none

theorem grindingFinish_sound
    (hk : 1 ≤ child.instance.r + child.instance.w)
    (sigma : I.layer.Statement) (W : I.layer.Oracle) (a : I.layer.Coin)
    (payload : I.layer.Payload) (row : child.instance.WireRow false)
    (col : Fin child.instance.n) (c : F) (Q : I.layer.Query)
    (H : HashInput child → Answer child)
    (hroot : a = (H (gamma W)).1.1)
    (hparent : I.layer.verify sigma W a payload Q)
    (hquery : (H (query W (grindingCommitment child payload row col c))).1.2 = Q)
    (d : Proof child)
    (hout : ((grindingFinish child hk sigma W a payload row col c Q).run H).1 = some d) :
    accepts child sigma H d := by
  subst a
  let d₀ := grindingProof child hk sigma W payload row col c Q H
  have he : grindingCompletionProof child hk sigma W (H (gamma W)).1.1 payload row col c Q
      (H (childGamma W (grindingCommitment child payload row col c) Q)).2.1 = d₀ := rfl
  simp only [grindingFinish, Tree.run_query, he] at hout
  by_cases havoid : col ∉ (H (terminal d₀)).2.2.coordinates
  · simp only [if_pos havoid, Tree.run_done] at hout
    have hd := Option.some.inj hout
    subst d
    exact grindingProof_accepts child hk sigma W payload row col c Q H hparent hquery havoid
  · simp only [if_neg havoid, Tree.run_done] at hout
    cases hout

/-- Scan actual child-query inputs. A hit consumes only two more oracle
queries, while a miss proceeds to the next distinct commitment value. -/
noncomputable def grindingChildren
    (hk : 1 ≤ child.instance.r + child.instance.w)
    (sigma : I.layer.Statement) (W : I.layer.Oracle) (a : I.layer.Coin)
    (ready : GrindingReady sigma W a) (row : child.instance.WireRow false)
    (col : Fin child.instance.n) :
    (values : List F) → Tree (HashInput child) (Answer child) (Option (Proof child))
      (2 + values.length)
  | [] => .done none
  | c :: cs =>
    .query (query W (grindingCommitment child ready.payload row col c)) fun answer =>
      if ready.goodQueries answer.1.2 then
        (grindingFinish child hk sigma W a ready.payload row col c answer.1.2).weakenAdd cs.length
      else grindingChildren hk sigma W a ready row col cs

theorem grindingChildren_sound
    (hk : 1 ≤ child.instance.r + child.instance.w)
    (sigma : I.layer.Statement) (W : I.layer.Oracle) (a : I.layer.Coin)
    (ready : GrindingReady sigma W a) (row : child.instance.WireRow false)
    (col : Fin child.instance.n) (values : List F)
    (H : HashInput child → Answer child) (hroot : a = (H (gamma W)).1.1)
    (d : Proof child)
    (hout : ((grindingChildren child hk sigma W a ready row col values).run H).1 = some d) :
    accepts child sigma H d := by
  induction values with
  | nil => simp [grindingChildren] at hout
  | cons c cs ih =>
    simp only [grindingChildren, Tree.run_query] at hout
    split_ifs at hout with hgood
    · rw [Tree.run_weakenAdd] at hout
      exact grindingFinish_sound child hk sigma W a ready.payload row col c _ H hroot
        (ready.parent_accepts _ hgood) rfl d hout
    · exact ih hout

/-- Scan root commitments until the parent algebra supplies a ready
payload. All remaining work is explicitly bounded by `values.length+2`. -/
noncomputable def grindingSearch
    (hk : 1 ≤ child.instance.r + child.instance.w)
    (sigma : I.layer.Statement)
    (prepare : ∀ W a, Option (GrindingReady sigma W a))
    (row : child.instance.WireRow false) (col : Fin child.instance.n)
    (values : List F) :
    (roots : List I.layer.Oracle) → Tree (HashInput child) (Answer child)
      (Option (Proof child)) ((2 + values.length) + roots.length)
  | [] => .done none
  | W :: Ws =>
    .query (gamma W) fun answer =>
      match prepare W answer.1.1 with
      | none => grindingSearch hk sigma prepare row col values Ws
      | some ready =>
        (grindingChildren child hk sigma W answer.1.1 ready row col values).weakenAdd Ws.length

/-- Every returned proof is an accepting transcript under the very oracle
queried by this bounded program. -/
theorem grindingSearch_sound
    (hk : 1 ≤ child.instance.r + child.instance.w)
    (sigma : I.layer.Statement)
    (prepare : ∀ W a, Option (GrindingReady sigma W a))
    (row : child.instance.WireRow false) (col : Fin child.instance.n)
    (values : List F) (roots : List I.layer.Oracle)
    (H : HashInput child → Answer child) (d : Proof child)
    (hout : ((grindingSearch child hk sigma prepare row col values roots).run H).1 = some d) :
    accepts child sigma H d := by
  induction roots with
  | nil => simp [grindingSearch] at hout
  | cons W Ws ih =>
    simp only [grindingSearch, Tree.run_query] at hout
    split at hout
    · exact ih hout
    · rw [Tree.run_weakenAdd] at hout
      exact grindingChildren_sound child hk sigma W _ _ row col values H rfl d hout

theorem grindingSearch_failure (p : HahnSystemCertificate I)
    (cp : HahnSystemCertificate child.instance)
    (hk : 1 ≤ child.instance.r + child.instance.w)
    (sigma : I.layer.Statement) (hfalse : ∀ witness, ¬ I.layer.satisfies sigma witness)
    (prepare : ∀ W a, Option (GrindingReady sigma W a))
    (row : child.instance.WireRow false) (col : Fin child.instance.n)
    (values : List F) (roots : List I.layer.Oracle)
    (H : HashInput child → Answer child) (d : Proof child)
    (hout : ((grindingSearch child hk sigma prepare row col values roots).run H).1 = some d) :
    failure child p cp sigma (fun _ => False) H d :=
  failure_of_accepts_of_false child p cp sigma hfalse H d
    (grindingSearch_sound child hk sigma prepare row col values roots H d hout)

end RecursivePolygero.FiatShamir.TwoLevel
