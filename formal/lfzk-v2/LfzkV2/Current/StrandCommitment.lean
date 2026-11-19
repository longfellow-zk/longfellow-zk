import LfzkV2.Current.StrandCut

/-! Merkle target charges in the original strand search. A query names
one committed root or at most two child digests. The receiving input is
charged at its original position, without requiring any future opening to
use it and without adding verifier replay to the adversary's query budget. -/
noncomputable section
namespace LfzkV2.Current.StrandCommitment
open Merkle.RandomOracle TranscriptV2 TranscriptV2.Strand Bcs.TotalOracle
open scoped Classical

section Children
variable {Enc D : Type} [DecidableEq D]
variable (readChildren : Enc → Option (D × D))

/-- Only the two child digests of an internal Merkle input are targets.
Leaf data, transcript parents, and PRF keys are not included here. -/
def children (input : Enc) : Finset D :=
  match readChildren input with
  | none => ∅
  | some pair => {pair.1,pair.2}

theorem children_card (input : Enc) : (children readChildren input).card ≤ 2 := by
  cases decoded : readChildren input with
  | none => simp [children,decoded]
  | some pair =>
      rw [children,decoded]
      exact (Finset.card_insert_le _ _).trans (by simp)

end Children

section Prefix
variable {P A Key Out : Type} [DecidableEq P] [DecidableEq Key]

private theorem cut_before (label : P → Key) (key : Key) {fuel : ℕ}
    (tree : Tree P A Out fuel) (H : P → A) (point : P)
    (absent : ∀ answer, (point,answer) ∉ beforeLabel label key tree H) :
    (beforeLabel label key tree H).map Prod.fst ⊆ before tree H point := by
  induction tree with
  | done _ => simp [beforeLabel]
  | query q next ih =>
      by_cases stop : label q = key
      · simp [beforeLabel,stop]
      · have different : q ≠ point := by
          intro same
          subst q
          exact absent (H point) (by simp [beforeLabel,stop])
        have absent' : ∀ answer, (point,answer) ∉ beforeLabel label key (next (H q)) H := by
          intro answer member
          exact absent answer (by simp only [beforeLabel,if_neg stop]; exact List.mem_cons_of_mem _ member)
        simpa only [beforeLabel,if_neg stop,List.map_cons,before,if_neg different] using
          List.cons_subset_cons q (ih (H q) absent')

private theorem boundary_before (label : P → Key) (key : Key) {fuel : ℕ}
    (tree : Tree P A Out fuel) (H : P → A) (point : P)
    (queried : point ∈ seen tree H)
    (absent : ∀ answer, (point,answer) ∉ beforeLabel label key tree H) :
    ∃ boundary ∈ insert point (before tree H point).toFinset, label boundary = key := by
  induction tree with
  | done _ => simp [seen,Bcs.TotalOracle.queried] at queried
  | query q next ih =>
      by_cases stop : label q = key
      · refine ⟨q,?_,stop⟩
        by_cases same : q = point
        · subst q; exact Finset.mem_insert_self _ _
        · simp [before,same]
      · have different : q ≠ point := by
          intro same
          subst q
          exact absent (H point) (by simp [beforeLabel,stop])
        have queried' : point ∈ seen (next (H q)) H := by
          simpa [seen,queried_query,Ne.symm different] using queried
        have absent' : ∀ answer, (point,answer) ∉ beforeLabel label key (next (H q)) H := by
          intro answer member
          exact absent answer (by simp only [beforeLabel,if_neg stop]; exact List.mem_cons_of_mem _ member)
        obtain ⟨boundary,member,same⟩ := ih (H q) queried' absent'
        refine ⟨boundary,?_,same⟩
        simp only [before,if_neg different,List.toFinset_cons]
        exact Finset.mem_insert.mpr ((Finset.mem_insert.mp member).imp_right (Finset.mem_insert_of_mem))

end Prefix

section Named
variable {P T Key Out : Type}
variable (readChildren : P → Option (Digest × Digest))
variable (context : T → Key) (root : Key → Digest)
variable {fuel : ℕ}
variable (tree : Tree (StrandSearch.Name P T) (StrandCoupling.Sample Digest Word) Out fuel)

/-- A recognized protocol query names its committed root. Other queries
can name two Merkle children. Domain separation makes these roles exclusive
on the actual search, so a single query never needs three targets. -/
def claims : StrandSearch.Name P T → Finset Digest
  | .inl (_,some value) => {root (context value)}
  | .inl (raw,none) => children readChildren raw
  | .inr _ => ∅

theorem claims_card (point : StrandSearch.Name P T) : (claims readChildren context root point).card ≤ 2 := by
  cases point with
  | inr _ => simp [claims]
  | inl point =>
      rcases point with ⟨raw,value⟩
      cases value with
      | some value => simp [claims]
      | none => exact children_card readChildren raw

private theorem cut_member (H : StrandSearch.Name P T → StrandCoupling.Sample Digest Word)
    (key : Key) (raw : P) (value : Option T) (answer : StrandCoupling.Sample Digest Word)
    (member : ((.inl (raw,value),answer) : StrandSearch.Name P T × _) ∈
      beforeLabel (StrandCut.label context) (some key) tree H) :
    (raw,answer.1) ∈ StrandCut.trace context tree H key :=
  List.mem_filterMap.mpr ⟨(.inl (raw,value),answer),member,rfl⟩

variable [DecidableEq P]

/-- A receiving input absent from the first-context cut is charged in
the original search as soon as its output is the root or a cut-node child.
This lemma needs no future opening or verifier-replay collision assumption. -/
theorem missing_cut_hit (H : StrandSearch.Name P T → StrandCoupling.Sample Digest Word)
    (SHA : P → Digest) (key : Key) (raw : P) (logical : Option T)
    (answer : StrandCoupling.Sample Digest Word)
    (queried : ((.inl (raw,logical),answer) : StrandSearch.Name P T × _) ∈ (tree.run H).2)
    (answerSound : answer.1 = SHA raw)
    (ordinary : ∀ input value result,
      ((.inl (input,some value),result) : StrandSearch.Name P T × _) ∈ (tree.run H).2 →
        readChildren input = none)
    (absent : ∀ digest, (raw,digest) ∉ StrandCut.trace context tree H key)
    (hit : SHA raw = root key ∨ ∃ input digest, (input,digest) ∈ StrandCut.trace context tree H key ∧
      SHA raw ∈ children readChildren input) :
    DigestProjection.bad (claims readChildren context root) tree (.inl (raw,logical)) H (H (.inl (raw,logical))) := by
  let point : StrandSearch.Name P T := .inl (raw,logical)
  have pointSeen : point ∈ seen tree H := by
    exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨(point,answer),queried,rfl⟩)
  have pointAnswer : (H point).1 = SHA raw := by
    have actual := Tree.trace_sound tree H (point,answer) queried
    exact (congrArg Prod.fst actual).symm.trans answerSound
  have absentNamed : ∀ result, (point,result) ∉ beforeLabel (StrandCut.label context) (some key) tree H := by
    intro result member
    exact absent result.1 (cut_member context tree H key raw logical result member)
  refine ⟨pointSeen,?_⟩
  rw [pointAnswer]
  rcases hit with atRoot | ⟨input,digest,old,child⟩
  · obtain ⟨boundary,member,same⟩ :=
      boundary_before (StrandCut.label context) (some key) tree H point pointSeen absentNamed
    apply Finset.mem_biUnion.mpr
    refine ⟨boundary,member,?_⟩
    cases boundary with
    | inr _ => cases same
    | inl boundary =>
        rcases boundary with ⟨input,value⟩
        cases value with
        | none => cases same
        | some value =>
            have same := Option.some.inj same
            simpa only [claims,Finset.mem_singleton,same] using atRoot
  · obtain ⟨value,row,member⟩ := StrandCut.trace_source context tree H key input digest old
    have beforePoint := cut_before (StrandCut.label context) (some key) tree H point absentNamed
      (List.mem_map.mpr ⟨(.inl (input,value),(digest,row)),member,rfl⟩)
    apply Finset.mem_biUnion.mpr
    refine ⟨.inl (input,value),Finset.mem_insert_of_mem (List.mem_toFinset.mpr beforePoint),?_⟩
    cases value with
    | none => exact child
    | some value =>
        have source : ((.inl (input,some value),(digest,row)) : StrandSearch.Name P T × _) ∈
            (tree.run H).2 := by
          rw [beforeLabel_eq_takeWhile] at member
          exact (List.takeWhile_sublist _).subset member
        have empty := ordinary input value (digest,row) source
        simp only [children,empty,Finset.notMem_empty] at child

end Named
end LfzkV2.Current.StrandCommitment
