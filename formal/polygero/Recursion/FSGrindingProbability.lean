import polygero.Recursion.FSGrindingFresh

/-! Exact ROM success probability for the actual bounded grinding tree.
The only counting premises are the preparation and good-query masses;
all commitment construction, query freshness and terminal completion are
the concrete operations proved in `FSGrindingTree` and `FSGrindingFresh`. -/
namespace RecursivePolygero.FiatShamir.TwoLevel

open Finset ProfileAnalysis Local Local.Polygero LigeroFamily Merkle.RandomOracle
open Bcs.TotalOracle.Footprint Bcs.TotalOracle.FreshSearch
open scoped Classical

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {I : Instance F} (child : Child I)

noncomputable def grindingSuccessWeight : Option (Proof child) → ℚ
  | none => 0
  | some _ => 1

noncomputable def grindingAvoidance : ℚ :=
  ((child.instance.n - 1).choose child.instance.t : ℚ) /
    child.instance.n.choose child.instance.t

private theorem average_answer_gamma (f : I.layer.Coin → ℚ) :
    average (fun answer : Answer child => f answer.1.1) = mean f := by
  change mean (fun answer : Answer child => f answer.1.1) = _
  simp only [mean_prod, mean_const]

private theorem average_answer_query (f : I.layer.Query → ℚ) :
    average (fun answer : Answer child => f answer.1.2) = mean f := by
  change mean (fun answer : Answer child => f answer.1.2) = _
  simp only [mean_prod, mean_const]

private theorem average_answer_terminal (f : child.instance.layer.Query → ℚ) :
    average (fun answer : Answer child => f answer.2.2) = mean f := by
  change mean (fun answer : Answer child => f answer.2.2) = _
  simp only [mean_prod, mean_const]

private theorem mean_ite_const {A : Type} [Fintype A] [Nonempty A]
    (event : A → Prop) (yes no : ℚ) :
    mean (fun a => if event a then yes else no) =
      mean (fun a => indicator (event a)) * yes +
        (1 - mean (fun a => indicator (event a))) * no := by
  have he (a : A) : (if event a then yes else no) =
      no + (yes - no) * indicator (event a) := by
    by_cases h : event a <;> simp [indicator, h]
  simp_rw [he]
  rw [mean_add, mean_const, mean_mul_left]
  ring

theorem grindingFinish_iid
    (hk : 1 ≤ child.instance.r + child.instance.w)
    (sigma : I.layer.Statement) (W : I.layer.Oracle) (a : I.layer.Coin)
    (payload : I.layer.Payload) (row : child.instance.WireRow false)
    (col : Fin child.instance.n) (c : F) (Q : I.layer.Query) :
    iidExpectation (grindingSuccessWeight child)
      (grindingFinish child hk sigma W a payload row col c Q) = grindingAvoidance child := by
  have he : iidExpectation (grindingSuccessWeight child)
      (grindingFinish child hk sigma W a payload row col c Q) =
      average (fun _answer : Answer child => average (fun last : Answer child =>
        indicator (col ∉ last.2.2.coordinates))) := by
    apply congrArg average
    funext answer
    apply congrArg average
    funext last
    by_cases h : col ∉ last.2.2.coordinates <;>
      simp [iidExpectation, grindingSuccessWeight, indicator, h]
  have ha : average (fun last : Answer child => indicator (col ∉ last.2.2.coordinates)) =
      grindingAvoidance child := by
    calc
      _ = mean (fun Q : child.instance.layer.Query => indicator (col ∉ Q.coordinates)) :=
        average_answer_terminal child _
      _ = _ := query_avoids_mean child.instance.n child.instance.t col
  rw [he]
  simp_rw [ha]
  exact average_const _

theorem grindingChildren_iid
    (hk : 1 ≤ child.instance.r + child.instance.w)
    (sigma : I.layer.Statement) (W : I.layer.Oracle) (a : I.layer.Coin)
    (ready : GrindingReady sigma W a) (row : child.instance.WireRow false)
    (col : Fin child.instance.n) (values : List F) (queryMass : ℚ)
    (hgood : mean (fun Q => indicator (ready.goodQueries Q)) = queryMass) :
    iidExpectation (grindingSuccessWeight child)
      (grindingChildren child hk sigma W a ready row col values) =
      (1 - (1 - queryMass) ^ values.length) * grindingAvoidance child := by
  induction values with
  | nil => simp [grindingChildren, iidExpectation, grindingSuccessWeight]
  | cons c cs ih =>
      have he : iidExpectation (grindingSuccessWeight child)
          (grindingChildren child hk sigma W a ready row col (c :: cs)) =
          average (fun answer : Answer child => if ready.goodQueries answer.1.2
            then grindingAvoidance child else
              (1 - (1 - queryMass) ^ cs.length) * grindingAvoidance child) := by
        apply congrArg average
        funext answer
        by_cases h : ready.goodQueries answer.1.2
        · simp [h, grindingFinish_iid]
        · simp [h, ih]
      rw [he, average_answer_query child (fun Q => if ready.goodQueries Q then
        grindingAvoidance child else (1 - (1 - queryMass) ^ cs.length) * grindingAvoidance child),
        mean_ite_const, hgood]
      simp only [List.length_cons, pow_succ]
      ring

theorem grindingSearch_iid
    (hk : 1 ≤ child.instance.r + child.instance.w)
    (sigma : I.layer.Statement)
    (prepare : ∀ W a, Option (GrindingReady sigma W a))
    (row : child.instance.WireRow false) (col : Fin child.instance.n)
    (values : List F) (roots : List I.layer.Oracle) (rootMass queryMass : ℚ)
    (hready : ∀ W ∈ roots,
      mean (fun a => indicator (prepare W a ≠ none)) = rootMass)
    (hgood : ∀ W ∈ roots, ∀ a ready, prepare W a = some ready →
      mean (fun Q => indicator (ready.goodQueries Q)) = queryMass) :
    iidExpectation (grindingSuccessWeight child)
      (grindingSearch child hk sigma prepare row col values roots) =
      (1 - (1 - rootMass) ^ roots.length) *
        (1 - (1 - queryMass) ^ values.length) * grindingAvoidance child := by
  induction roots with
  | nil => simp [grindingSearch, iidExpectation, grindingSuccessWeight]
  | cons W Ws ih =>
      have htready : ∀ U ∈ Ws,
          mean (fun a => indicator (prepare U a ≠ none)) = rootMass := by
        intro U hU
        exact hready U (List.mem_cons_of_mem _ hU)
      have htgood : ∀ U ∈ Ws, ∀ a ready, prepare U a = some ready →
          mean (fun Q => indicator (ready.goodQueries Q)) = queryMass := by
        intro U hU a ready h
        exact hgood U (List.mem_cons_of_mem _ hU) a ready h
      have hi := ih htready htgood
      have he : iidExpectation (grindingSuccessWeight child)
          (grindingSearch child hk sigma prepare row col values (W :: Ws)) =
          average (fun answer : Answer child => if prepare W answer.1.1 ≠ none
            then (1 - (1 - queryMass) ^ values.length) * grindingAvoidance child
            else (1 - (1 - rootMass) ^ Ws.length) *
              (1 - (1 - queryMass) ^ values.length) * grindingAvoidance child) := by
        apply congrArg average
        funext answer
        cases hp : prepare W answer.1.1 with
        | none => simp [hp, hi]
        | some ready =>
            have hg := hgood W List.mem_cons_self answer.1.1 ready hp
            simp [hp, grindingChildren_iid, hg]
      rw [he, average_answer_gamma child (fun a => if prepare W a ≠ none then
        (1 - (1 - queryMass) ^ values.length) * grindingAvoidance child else
          (1 - (1 - rootMass) ^ Ws.length) *
            (1 - (1 - queryMass) ^ values.length) * grindingAvoidance child)]
      calc
        _ = mean (fun a =>
            (1 - (1 - rootMass) ^ Ws.length) *
              (1 - (1 - queryMass) ^ values.length) * grindingAvoidance child +
            ((1 - (1 - queryMass) ^ values.length) * grindingAvoidance child -
              (1 - (1 - rootMass) ^ Ws.length) *
                (1 - (1 - queryMass) ^ values.length) * grindingAvoidance child) *
              indicator (prepare W a ≠ none)) := by
          apply mean_congr
          intro a
          by_cases h : prepare W a ≠ none <;> simp [indicator, h]
        _ = _ := by
          rw [mean_add, mean_const, mean_mul_left, hready W List.mem_cons_self]
          simp only [List.length_cons, pow_succ]
          ring

/-- Exact success probability for the actual total-ROM query tree. The
only extra premises relative to the iid formula are distinct roots and
distinct physical commitment entry values, already sufficient for freshness. -/
theorem grindingSearch_success_probability
    (hk : 1 ≤ child.instance.r + child.instance.w)
    (sigma : I.layer.Statement)
    (prepare : ∀ W a, Option (GrindingReady sigma W a))
    (row : child.instance.WireRow false) (col : Fin child.instance.n)
    (values : List F) (hvalues : values.Nodup)
    (roots : List I.layer.Oracle) (hroots : roots.Nodup) (rootMass queryMass : ℚ)
    (hready : ∀ W ∈ roots,
      mean (fun a => indicator (prepare W a ≠ none)) = rootMass)
    (hgood : ∀ W ∈ roots, ∀ a ready, prepare W a = some ready →
      mean (fun Q => indicator (ready.goodQueries Q)) = queryMass) :
    average (fun H : HashInput child → Answer child =>
      grindingSuccessWeight child ((grindingSearch child hk sigma prepare row col values roots).run H).1) =
      (1 - (1 - rootMass) ^ roots.length) *
        (1 - (1 - queryMass) ^ values.length) * grindingAvoidance child := by
  rw [totalOracle_eq_iid _ ∅
    (grindingSearch_fresh child hk sigma prepare row col values hvalues roots hroots)]
  exact grindingSearch_iid child hk sigma prepare row col values roots rootMass queryMass hready hgood

end RecursivePolygero.FiatShamir.TwoLevel
