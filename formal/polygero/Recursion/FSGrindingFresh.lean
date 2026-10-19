import polygero.Recursion.FSGrindingTree
import Bcs.FreshSearch

/-! Structural freshness of the executable grinding search. Distinct
root commitments and distinct varied child-entry values suffice. -/

namespace RecursivePolygero.FiatShamir.TwoLevel

open Finset ProfileAnalysis Local Local.Polygero LigeroFamily Merkle.RandomOracle
open Bcs.TotalOracle.FreshSearch
open scoped Classical

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]
variable {I : Instance F} (child : Child I)

private def ShallowInput : HashInput child → Prop
  | .inl _ => True
  | .inr (.inl _) => True
  | _ => False

private def RootInput : HashInput child → Prop
  | .inl _ => True
  | _ => False

theorem grindingFinish_fresh
    (hk : 1 ≤ child.instance.r + child.instance.w)
    (sigma : I.layer.Statement) (W : I.layer.Oracle) (a : I.layer.Coin)
    (payload : I.layer.Payload) (row : child.instance.WireRow false)
    (col : Fin child.instance.n) (c : F) (Q : I.layer.Query)
    (seen : Finset (HashInput child))
    (hseen : ∀ x ∈ seen, ShallowInput child x) :
    FreshFrom seen (grindingFinish child hk sigma W a payload row col c Q) := by
  simp only [grindingFinish, FreshFrom]
  constructor
  · intro hx
    exact hseen _ hx
  · intro answer
    constructor
    · intro hx
      rcases mem_insert.mp hx with he | hm
      · cases he
      · exact hseen _ hm
    · intro last
      split_ifs <;> trivial

theorem grindingChildren_fresh
    (hk : 1 ≤ child.instance.r + child.instance.w)
    (sigma : I.layer.Statement) (W : I.layer.Oracle) (a : I.layer.Coin)
    (ready : GrindingReady sigma W a) (row : child.instance.WireRow false)
    (col : Fin child.instance.n) (values : List F) (hnodup : values.Nodup)
    (seen : Finset (HashInput child))
    (hseen : ∀ x ∈ seen, ShallowInput child x)
    (havoid : ∀ c ∈ values,
      (query W (grindingCommitment child ready.payload row col c) : HashInput child) ∉ seen) :
    FreshFrom seen (grindingChildren child hk sigma W a ready row col values) := by
  induction values generalizing seen with
  | nil => trivial
  | cons c cs ih =>
    have hn := List.nodup_cons.mp hnodup
    simp only [grindingChildren, FreshFrom]
    refine ⟨havoid c (by simp), ?_⟩
    intro answer
    have hins : ∀ x ∈ insert (query W (grindingCommitment child ready.payload row col c)) seen,
        ShallowInput child x := by
      intro x hx
      rcases mem_insert.mp hx with rfl | hm
      · trivial
      · exact hseen x hm
    by_cases hgood : ready.goodQueries answer.1.2
    · simp only [if_pos hgood, FreshFrom_weakenAdd]
      exact grindingFinish_fresh child hk sigma W a ready.payload row col c _ _ hins
    · simp only [if_neg hgood]
      apply ih hn.2 _ hins
      intro c' hc' hx
      rcases mem_insert.mp hx with he | hm
      · have hc : c' = c := grinding_query_injective child W ready.payload row col he
        exact hn.1 (hc ▸ hc')
      · exact havoid c' (List.mem_cons_of_mem _ hc') hm

theorem grindingSearch_fresh_from_roots
    (hk : 1 ≤ child.instance.r + child.instance.w)
    (sigma : I.layer.Statement)
    (prepare : ∀ W a, Option (GrindingReady sigma W a))
    (row : child.instance.WireRow false) (col : Fin child.instance.n)
    (values : List F) (hvalues : values.Nodup)
    (roots : List I.layer.Oracle) (hroots : roots.Nodup)
    (seen : Finset (HashInput child))
    (hseen : ∀ x ∈ seen, RootInput child x)
    (havoid : ∀ W ∈ roots, (gamma W : HashInput child) ∉ seen) :
    FreshFrom seen (grindingSearch child hk sigma prepare row col values roots) := by
  induction roots generalizing seen with
  | nil => trivial
  | cons W Ws ih =>
    have hn := List.nodup_cons.mp hroots
    simp only [grindingSearch, FreshFrom]
    refine ⟨havoid W (by simp), ?_⟩
    intro answer
    have hins : ∀ x ∈ insert (gamma W) seen, RootInput child x := by
      intro x hx
      rcases mem_insert.mp hx with rfl | hm
      · trivial
      · exact hseen x hm
    split
    · apply ih hn.2 _ hins
      intro W' hW' hx
      rcases mem_insert.mp hx with he | hm
      · have hW : W' = W := Sum.inl.inj he
        exact hn.1 (hW ▸ hW')
      · exact havoid W' (List.mem_cons_of_mem _ hW') hm
    · simp only [FreshFrom_weakenAdd]
      apply grindingChildren_fresh child hk sigma W _ _ row col values hvalues _
      · intro x hx
        have hr := hins x hx
        cases x with
        | inl w => trivial
        | inr rest => exact hr.elim
      · intro c _ hc
        exact hins _ hc

/-- An actual bounded search on one total random oracle is structurally
fresh on every branch. Thus the generic independent-sampling theorem
applies to its real output event. -/
theorem grindingSearch_fresh
    (hk : 1 ≤ child.instance.r + child.instance.w)
    (sigma : I.layer.Statement)
    (prepare : ∀ W a, Option (GrindingReady sigma W a))
    (row : child.instance.WireRow false) (col : Fin child.instance.n)
    (values : List F) (hvalues : values.Nodup)
    (roots : List I.layer.Oracle) (hroots : roots.Nodup) :
    FreshFrom ∅ (grindingSearch child hk sigma prepare row col values roots) :=
  grindingSearch_fresh_from_roots child hk sigma prepare row col values hvalues roots hroots
    ∅ (by simp) (by simp)

end RecursivePolygero.FiatShamir.TwoLevel
