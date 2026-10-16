import Lfzk.LigeroTranscriptInputs
import LigeroFamily.Code.ReedSolomon
import LigeroFamily.Protocol.FiniteResponse

/-!
# From transmitted Ligero slices to evaluation-form responses

The runtime interpolates the `y_ldt` and `y_dot` slices.  For the quadratic
slice it inserts `block - r` zero values between `y_quad_0` and `y_quad_2`
before interpolation.  This module gives that reconstruction and proves that
interpolation at distinct domain points retains every transmitted element.
It is the no-alias bridge from a four-slice transcript message to the
evaluation-form response counted by the V1 response-mass theorem.

The ordered interpolation nodes are explicit arguments.  An implementation
instantiation must identify them with its `InterpolatorFactory` points.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.LigeroPayloadDecode

open Lfzk.LigeroTranscriptInputs
open LigeroFamily
open Polynomial

variable {F : Type} [Field F]
variable {r w n block dblock : ℕ}

/-- The quadratic evaluations the verifier reconstructs before
interpolation: transmitted head, forced zero middle, transmitted tail. -/
def quadraticValues (_hrb : r ≤ block) (hbd : block ≤ dblock)
    (p : ResponsePayload F block dblock r) : Fin dblock → F :=
  fun i =>
    if hi : i.val < r then p.yQuad0 ⟨i.val, hi⟩
    else if hb : i.val < block then 0
    else p.yQuad2 ⟨i.val - block, by omega⟩

theorem quadraticValues_head (hrb : r ≤ block) (hbd : block ≤ dblock)
    (p : ResponsePayload F block dblock r) (i : Fin r) :
    quadraticValues hrb hbd p ⟨i.val, by omega⟩ = p.yQuad0 i := by
  simp [quadraticValues, i.isLt]

theorem quadraticValues_tail (hrb : r ≤ block) (hbd : block ≤ dblock)
    (p : ResponsePayload F block dblock r) (i : Fin (dblock - block)) :
    quadraticValues hrb hbd p ⟨block + i.val, by omega⟩ = p.yQuad2 i := by
  have hnr : ¬ block + i.val < r := by omega
  have hnb : ¬ block + i.val < block := by omega
  simp [quadraticValues, hnr, hnb]

/-- Lagrange interpolation at the ordered evaluation points used by the
runtime. -/
noncomputable def interpolate (D : ReedSolomon.Domain F r w n)
    {m : ℕ} (nodes : Fin m ↪ Position r w n) (values : Fin m → F) :
    EvaluationRow F r w n :=
  fun pos =>
    (Lagrange.interpolate Finset.univ (D.point ∘ nodes) values).eval (D.point pos)

theorem interpolate_at_node (D : ReedSolomon.Domain F r w n)
    {m : ℕ} (nodes : Fin m ↪ Position r w n) (values : Fin m → F)
    (i : Fin m) :
    interpolate D nodes values (nodes i) = values i := by
  unfold interpolate
  simpa using Lagrange.eval_interpolate_at_node values
    (D.injective.comp nodes.injective).injOn (Finset.mem_univ i)

/-- An interpolated row is determined by any `m` committed-code
evaluations.  This uses the number of interpolation nodes, which can be
smaller than the dimension of the ambient response code. -/
theorem interpolate_eq_of_code_agree (D : ReedSolomon.Domain F r w n)
    {m : ℕ} (nodes : Fin m ↪ Position r w n)
    (left right : Fin m → F) (S : Finset (Fin n))
    (hcard : m ≤ S.card)
    (hagree : ∀ j ∈ S,
      interpolate D nodes left (codePosition j) =
        interpolate D nodes right (codePosition j)) :
    interpolate D nodes left = interpolate D nodes right := by
  let p := Lagrange.interpolate Finset.univ (D.point ∘ nodes) left
  let q := Lagrange.interpolate Finset.univ (D.point ∘ nodes) right
  have hinj : Set.InjOn (D.point ∘ nodes) (Finset.univ : Finset (Fin m)) :=
    (D.injective.comp nodes.injective).injOn
  have hp : p.degree < (codePositions (r := r) (w := w) S).card := by
    have hdegree := Lagrange.degree_interpolate_lt (r := left) hinj
    have hsize : (Finset.univ : Finset (Fin m)).card ≤
        (codePositions (r := r) (w := w) S).card := by
      simpa using hcard
    exact hdegree.trans_le (by exact_mod_cast hsize)
  have hq : q.degree < (codePositions (r := r) (w := w) S).card := by
    have hdegree := Lagrange.degree_interpolate_lt (r := right) hinj
    have hsize : (Finset.univ : Finset (Fin m)).card ≤
        (codePositions (r := r) (w := w) S).card := by
      simpa using hcard
    exact hdegree.trans_le (by exact_mod_cast hsize)
  have hpq : p = q :=
    Polynomial.eq_of_degrees_lt_of_eval_index_eq
      (codePositions S) D.injective.injOn hp hq (by
        intro pos hpos
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hpos
        exact hagree j hj)
  funext pos
  exact congrArg (fun poly : F[X] => poly.eval (D.point pos)) hpq

/-- Decode the four transmitted slices as three evaluation-form rows. -/
noncomputable def decode (D : ReedSolomon.Domain F r w n)
    (baseNodes : Fin block ↪ Position r w n)
    (responseNodes : Fin dblock ↪ Position r w n)
    (hrb : r ≤ block) (hbd : block ≤ dblock)
    (p : ResponsePayload F block dblock r) : Response F r w n 1 where
  proximity _ := interpolate D baseNodes p.yLdt
  linear _ := interpolate D responseNodes p.yDot
  quadratic _ := interpolate D responseNodes (quadraticValues hrb hbd p)

/-- Distinct complete transmitted responses decode to distinct formal
responses, provided their interpolation nodes are distinct. -/
theorem decode_injective (D : ReedSolomon.Domain F r w n)
    (baseNodes : Fin block ↪ Position r w n)
    (responseNodes : Fin dblock ↪ Position r w n)
    (hrb : r ≤ block) (hbd : block ≤ dblock) :
    Function.Injective (decode D baseNodes responseNodes hrb hbd) := by
  intro p q hpq
  have hld : p.yLdt = q.yLdt := by
    funext i
    have h := congrFun (congrArg (fun x : Response F r w n 1 => x.proximity 0) hpq)
      (baseNodes i)
    simpa only [decode, interpolate_at_node] using h
  have hdot : p.yDot = q.yDot := by
    funext i
    have h := congrFun (congrArg (fun x : Response F r w n 1 => x.linear 0) hpq)
      (responseNodes i)
    simpa only [decode, interpolate_at_node] using h
  have hquad : quadraticValues hrb hbd p = quadraticValues hrb hbd q := by
    funext i
    have h := congrFun (congrArg (fun x : Response F r w n 1 => x.quadratic 0) hpq)
      (responseNodes i)
    simpa only [decode, interpolate_at_node] using h
  have h0 : p.yQuad0 = q.yQuad0 := by
    funext i
    have h := congrFun hquad ⟨i.val, by omega⟩
    simpa only [quadraticValues_head] using h
  have h2 : p.yQuad2 = q.yQuad2 := by
    funext i
    have h := congrFun hquad ⟨block + i.val, by omega⟩
    simpa only [quadraticValues_tail] using h
  rcases p with ⟨pl, pd, p0, p2⟩
  rcases q with ⟨ql, qd, q0, q2⟩
  cases hld
  cases hdot
  cases h0
  cases h2
  rfl

/-- Two transmitted payloads whose decoded triples agree at `dblock`
committed columns are identical.  Consequently distinct payloads have
overlap at most `dblock - 1`, even if the ambient response code has the
larger dimension `2*k`. -/
theorem decode_eq_of_code_agree (D : ReedSolomon.Domain F r w n)
    (baseNodes : Fin block ↪ Position r w n)
    (responseNodes : Fin dblock ↪ Position r w n)
    (hrb : r ≤ block) (hbd : block ≤ dblock)
    (p q : ResponsePayload F block dblock r)
    (S : Finset (Fin n)) (hcard : dblock ≤ S.card)
    (hprox : ∀ j ∈ S,
      (decode D baseNodes responseNodes hrb hbd p).proximity 0
        (codePosition j) =
      (decode D baseNodes responseNodes hrb hbd q).proximity 0
        (codePosition j))
    (hlinear : ∀ j ∈ S,
      (decode D baseNodes responseNodes hrb hbd p).linear 0
        (codePosition j) =
      (decode D baseNodes responseNodes hrb hbd q).linear 0
        (codePosition j))
    (hquad : ∀ j ∈ S,
      (decode D baseNodes responseNodes hrb hbd p).quadratic 0
        (codePosition j) =
      (decode D baseNodes responseNodes hrb hbd q).quadratic 0
        (codePosition j)) : p = q := by
  apply decode_injective D baseNodes responseNodes hrb hbd
  apply Response.ext
  · funext h
    have h := interpolate_eq_of_code_agree D baseNodes p.yLdt q.yLdt S
      (hbd.trans hcard) (by
        intro j hj
        simpa only [decode] using hprox j hj)
    simpa only [decode] using h
  · funext h
    have h := interpolate_eq_of_code_agree D responseNodes p.yDot q.yDot S
      hcard (by
        intro j hj
        simpa only [decode] using hlinear j hj)
    simpa only [decode] using h
  · funext h
    have h := interpolate_eq_of_code_agree D responseNodes
      (quadraticValues hrb hbd p) (quadraticValues hrb hbd q) S
      hcard (by
        intro j hj
        simpa only [decode] using hquad j hj)
    simpa only [decode] using h

/-- Any nonnegative cost summed over transmitted responses is at most the
same cost summed over all evaluation-form responses.  In particular this
allows the checked V1 response-mass envelope to count actual query inputs
without a message-alias multiplier. -/
theorem payload_mass_le [Fintype F] [DecidableEq F]
    (D : ReedSolomon.Domain F r w n)
    (baseNodes : Fin block ↪ Position r w n)
    (responseNodes : Fin dblock ↪ Position r w n)
    (hrb : r ≤ block) (hbd : block ≤ dblock)
    (cost : Response F r w n 1 → ℚ)
    (hcost : ∀ response, 0 ≤ cost response) :
    ∑ payload : ResponsePayload F block dblock r,
        cost (decode D baseNodes responseNodes hrb hbd payload) ≤
      ∑ response : Response F r w n 1, cost response :=
  ResponsePayload.mass_le_of_decode_injective
    (decode D baseNodes responseNodes hrb hbd)
    (decode_injective D baseNodes responseNodes hrb hbd) cost hcost

end Lfzk.LigeroPayloadDecode
