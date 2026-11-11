import Bcs.TotalOracle
import Bcs.FirstPairQuery
import Mathlib.Tactic.Ext
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.NormCast

/-! Adaptive query prefixes, stopped before the first occurrence of a point.
No fresh-answer tape or assumed query ordering is used here. -/
namespace TranscriptV2
open Finset Bcs.TotalOracle Merkle.RandomOracle
open scoped Classical

variable {P A Out : Type} [DecidableEq P]

omit [DecidableEq P] in
/-- Retain the actual raw query/answer trace in the output, without adding
queries. At an extraction cut this includes repeated calls and every sampler
block; it is not replaced by the smaller trace of fresh logical queries. -/
def recordTrace : {fuel : ℕ} → Tree P A Out fuel → Tree P A (Out × List (P × A)) fuel
  | _, .done output => .done (output,[])
  | _, .query point next => .query point fun answer =>
      (recordTrace (next answer)).map fun result => (result.1,(point,answer)::result.2)

omit [DecidableEq P] in
theorem run_recordTrace {fuel : ℕ} (tree : Tree P A Out fuel) (H : P → A) :
    (recordTrace tree).run H = (tree.run H,(tree.run H).2) := by
  induction tree with
  | done output => rfl
  | query point next ih => simp only [recordTrace,Tree.run_query,Tree.run_map,ih]

omit [DecidableEq P] in
/-- Rename inputs without changing answers, call counts, or call order. -/
def mapQueries {Raw : Type} (encode : P → Raw) : {fuel : ℕ} →
    Tree P A Out fuel → Tree Raw A Out fuel
  | _, .done out => .done out
  | _, .query point next => .query (encode point) fun answer => mapQueries encode (next answer)

omit [DecidableEq P] in
theorem run_mapQueries {Raw : Type} (encode : P → Raw) {fuel : ℕ}
    (tree : Tree P A Out fuel) (H : Raw → A) :
    (mapQueries encode tree).run H =
      let result := tree.run (H ∘ encode)
      (result.1,result.2.map fun qa => (encode qa.1,qa.2)) := by
  induction tree with
  | done out => rfl
  | query point next ih => simp only [mapQueries,Tree.run_query,ih,List.map_cons,Function.comp_apply]

omit [DecidableEq P] in
theorem mapQueries_map {Raw Result : Type} (encode : P → Raw) {fuel : ℕ}
    (tree : Tree P A Out fuel) (f : Out → Result) :
    mapQueries encode (tree.map f) = (mapQueries encode tree).map f := by
  induction tree with
  | done out => rfl
  | query point next ih => exact congrArg (Tree.query (encode point)) (funext ih)

omit [DecidableEq P] in
theorem mapQueries_comp {Middle Raw : Type} (first : P → Middle) (second : Middle → Raw)
    {fuel : ℕ} (tree : Tree P A Out fuel) :
    mapQueries second (mapQueries first tree) = mapQueries (second ∘ first) tree := by
  induction tree with
  | done out => rfl
  | query point next ih => exact congrArg (Tree.query (second (first point))) (funext ih)

omit [DecidableEq P] in
private theorem mapQueries_weaken {Raw : Type} (encode : P → Raw) {fuel : ℕ}
    (tree : Tree P A Out fuel) : mapQueries encode tree.weaken = (mapQueries encode tree).weaken := by
  induction tree with
  | done out => rfl
  | query point next ih => exact congrArg (Tree.query (encode point)) (funext ih)

omit [DecidableEq P] in
private theorem mapQueries_weakenAdd {Raw : Type} (encode : P → Raw) {fuel : ℕ}
    (tree : Tree P A Out fuel) (extra : ℕ) :
    mapQueries encode (tree.weakenAdd extra) = (mapQueries encode tree).weakenAdd extra := by
  induction extra with
  | zero => rfl
  | succ extra ih => rw [Tree.weakenAdd,mapQueries_weaken,ih,Tree.weakenAdd]

omit [DecidableEq P] in
theorem mapQueries_bind {Raw Result : Type} (encode : P → Raw) {fuel extra : ℕ}
    (tree : Tree P A Out fuel) (next : Out → Tree P A Result extra) :
    mapQueries encode (tree.bind next) =
      (mapQueries encode tree).bind fun out => mapQueries encode (next out) := by
  induction tree with
  | done out => exact mapQueries_weakenAdd encode (next out) _
  | query point child ih => exact congrArg (Tree.query (encode point)) (funext ih)

omit [DecidableEq P] in
/-- Implement a logical query by its actual bounded oracle program.
This is used for verifier replay; it does not grant the prover free queries. -/
def expandQueries {Raw Answer : Type} {cost : ℕ} (read : P → Tree Raw Answer A cost) :
    {fuel : ℕ} → Tree P A Out fuel → Tree Raw Answer Out (cost*fuel)
  | _, .done output => .done output
  | _, .query point next => (read point).bind fun answer => expandQueries read (next answer)

omit [DecidableEq P] in
theorem mapQueries_expand {Raw Other Answer : Type} {cost fuel : ℕ}
    (encode : Raw → Other) (read : P → Tree Raw Answer A cost) (tree : Tree P A Out fuel) :
    mapQueries encode (expandQueries read tree) =
      expandQueries (fun point => mapQueries encode (read point)) tree := by
  induction tree with
  | done out => rfl
  | query point next ih => simp only [expandQueries,mapQueries_bind,ih]

omit [DecidableEq P] in
/-- Expansion preserves the result and records precisely the concatenated
raw calls, including repeated inputs and rejected sampler blocks. -/
theorem expandQueries_run {Raw Answer : Type} {cost fuel : ℕ}
    (read : P → Tree Raw Answer A cost) (tree : Tree P A Out fuel) (G : Raw → Answer) :
    (expandQueries read tree).run G =
      let logical := tree.run (fun point => ((read point).run G).1)
      (logical.1,logical.2.flatMap fun qa => ((read qa.1).run G).2) := by
  induction tree with
  | done output => rfl
  | query point next ih =>
      simp only [expandQueries,Tree.run_bind,Tree.run_query,ih,List.flatMap_cons]

def before : {fuel : ℕ} → Tree P A Out fuel → (P → A) → P → List P
  | _, .done _, _, _ => []
  | _, .query q next, H, p =>
      if q = p then [] else q :: before (next (H q)) H p

theorem before_congr {fuel : ℕ} (tree : Tree P A Out fuel) (p : P)
    {H H' : P → A} (h : AgreeOff p H H') : before tree H p = before tree H' p := by
  induction tree with
  | done _ => rfl
  | query q next ih =>
    by_cases hq : q = p
    · simp [before, hq]
    · simp only [before, if_neg hq]
      have heq := h q hq
      rw [← heq]
      exact congrArg (List.cons q) (ih (H q))

/-- The stopped prefix is determined by the executed query list, not by
the syntax of the program that produced it. -/
theorem before_eq_takeWhile {fuel : ℕ} (tree : Tree P A Out fuel) (H : P → A) (p : P) :
    before tree H p = (queried tree H).takeWhile (fun q => decide (q ≠ p)) := by
  induction tree with
  | done output => rfl
  | query q next ih =>
      by_cases same : q = p
      · simp [before,queried_query,same]
      · simp [before,queried_query,same,ih]

theorem before_eq_of_queried_eq {Other : Type} {fuel extra : ℕ}
    (first : Tree P A Out fuel) (second : Tree P A Other extra) (H H' : P → A)
    (same : queried first H = queried second H') (p : P) :
    before first H p = before second H' p := by
  rw [before_eq_takeWhile,before_eq_takeWhile,same]

section Labels
variable {Key : Type} [DecidableEq Key]

/-- The extractor freezes a context before the first query naming it.
Retaining answers as well as addresses avoids reconstructing a prefix from
a final cache that might already contain later commitment information. -/
def beforeLabel (label : P → Key) (key : Key) :
    {fuel : ℕ} → Tree P A Out fuel → (P → A) → List (P × A)
  | _, .done _, _ => []
  | _, .query point next, H =>
      if label point = key then [] else (point,H point) :: beforeLabel label key (next (H point)) H

omit [DecidableEq P] in
/-- The cut is an actual prefix of the recorded execution, including
repeated queries. No unqueried oracle coordinate is present. -/
theorem beforeLabel_eq_takeWhile (label : P → Key) (key : Key)
    {fuel : ℕ} (tree : Tree P A Out fuel) (H : P → A) :
    beforeLabel label key tree H = (tree.run H).2.takeWhile (fun qa => decide (label qa.1 ≠ key)) := by
  induction tree with
  | done output => rfl
  | query point next ih =>
      by_cases sameLabel : label point = key
      · simp [beforeLabel,Tree.run_query,sameLabel]
      · simp [beforeLabel,Tree.run_query,sameLabel,ih]

omit [DecidableEq P] in
/-- Every point naming this context is outside its cut. Consequently the
cut is fixed when that point's complete answer is resampled, even for
adversarially reordered queries and contexts absent from the execution. -/
theorem beforeLabel_off (label : P → Key) {fuel : ℕ} (tree : Tree P A Out fuel)
    (point : P) (H H' : P → A) (agreement : AgreeOff point H H') :
    beforeLabel label (label point) tree H = beforeLabel label (label point) tree H' := by
  induction tree with
  | done output => rfl
  | query q next ih =>
      by_cases sameLabel : label q = label point
      · simp only [beforeLabel,sameLabel,if_true]
      · have different : q ≠ point := fun same => sameLabel (congrArg label same)
        simp only [beforeLabel,sameLabel,if_false]
        rw [← agreement q different]
        exact congrArg (List.cons (q,H q)) (ih (H q))

end Labels

theorem before_subset {fuel : ℕ} (tree : Tree P A Out fuel) (H : P → A) (p : P) :
    before tree H p ⊆ queried tree H := by
  induction tree with
  | done _ => simp [before]
  | query q next ih =>
    by_cases hq : q = p
    · simp [before, hq]
    · simp only [before, if_neg hq, queried_query]
      exact List.cons_subset_cons q (ih (H q))

theorem before_eq_of_not_queried {fuel : ℕ} (tree : Tree P A Out fuel)
    (H : P → A) (p : P) (hp : p ∉ queried tree H) :
    before tree H p = queried tree H := by
  induction tree with
  | done _ => rfl
  | query q next ih =>
    have hq : q ≠ p := by intro h; apply hp; simp [queried_query, h]
    have ht : p ∉ queried (next (H q)) H := by
      intro h; exact hp (by rw [queried_query]; exact List.mem_cons_of_mem q h)
    simp only [before, if_neg hq, queried_query, ih (H q) ht]

def seen {fuel : ℕ} (tree : Tree P A Out fuel) (H : P → A) : Finset P :=
  (queried tree H).toFinset

/-- Renaming raw addresses changes only their names, not which original
queries were executed. This belongs with query execution, independently of
any protocol composition or soundness bound. -/
theorem seen_mapQueries {Q : Type} [DecidableEq Q] (encode : P → Q)
    {fuel : ℕ} (tree : Tree P A Out fuel) (H : Q → A) :
    seen (mapQueries encode tree) H = (seen tree (H ∘ encode)).image encode := by
  ext point
  simp [seen,queried,run_mapQueries,List.map_map,Function.comp_def]

theorem seen_card_le {fuel : ℕ} (tree : Tree P A Out fuel) (H : P → A) :
    (seen tree H).card ≤ fuel :=
  (List.toFinset_card_le _).trans (queried_length_le tree H)

/-- Once the original execution reaches a context, its first-context cut
is already fixed. Appending verifier replay cannot add anything to that cut. -/
theorem beforeLabel_bind_of_queried {Key Result : Type} [DecidableEq Key]
    (label : P → Key) (key : Key) {fuel extra : ℕ}
    (tree : Tree P A Out fuel) (resume : Out → Tree P A Result extra) (H : P → A)
    (reached : ∃ point ∈ seen tree H, label point = key) :
    beforeLabel label key (tree.bind resume) H = beforeLabel label key tree H := by
  induction tree with
  | done out =>
      obtain ⟨point,member,_⟩ := reached
      simp only [seen,queried_done,List.toFinset_nil,Finset.notMem_empty] at member
  | query point next ih =>
      by_cases current : label point = key
      · simp only [Merkle.RandomOracle.Tree.bind,beforeLabel,current,if_true]
      · obtain ⟨target,member,same⟩ := reached
        have later : target ∈ seen (next (H point)) H := by
          have listed := List.mem_toFinset.mp member
          rw [queried_query] at listed
          rcases List.mem_cons.mp listed with equal | tail
          · exact False.elim (current (equal ▸ same))
          · exact List.mem_toFinset.mpr tail
        simp only [Merkle.RandomOracle.Tree.bind,beforeLabel,current,if_false]
        exact congrArg (List.cons (point,H point)) (ih (H point) ⟨target,later,same⟩)

/-- Split the recorded answers at the first query to a point. This connects
chronological invariants of a labelled trace to the stopped-prefix API. -/
theorem trace_split_before {fuel : ℕ} (tree : Tree P A Out fuel) (H : P → A)
    (point : P) (member : point ∈ seen tree H) :
    ∃ first rest answer, (tree.run H).2 = first ++ (point,answer)::rest ∧
      first.map Prod.fst = before tree H point := by
  induction tree with
  | done output => simp [seen,queried] at member
  | query next continuation ih =>
      by_cases same : next = point
      · subst next
        exact ⟨[],((continuation (H point)).run H).2,H point,rfl,by simp [before]⟩
      · have later : point ∈ seen (continuation (H next)) H := by
          simpa [seen,queried_query,Ne.symm same] using member
        obtain ⟨first,rest,answer,trace,past⟩ := ih (H next) later
        refine ⟨(next,H next)::first,rest,answer,?_,?_⟩
        · simp only [Tree.run_query,trace,List.cons_append]
        · simp only [List.map_cons,past,before,if_neg same]

theorem first_left_of_before {fuel : ℕ} (tree : Tree P A Out fuel) (H : P → A)
    (parent child : P) (member : parent ∈ before tree H child) :
    firstOfTwo tree H parent child = .left := by
  induction tree with
  | done _ => simp [before] at member
  | query point next ih =>
      by_cases isParent : point = parent
      · simp only [firstOfTwo,if_pos isParent]
      · by_cases isChild : point = child
        · simp only [before,if_pos isChild,List.not_mem_nil] at member
        · have later : parent ∈ before (next (H point)) H child := by
            simpa [before,isChild,Ne.symm isParent] using member
          simpa only [firstOfTwo,if_neg isParent,if_neg isChild] using ih (H point) later

/-- Charge bad answers only at points the adversary queried. Prefix-dependent
data may read the whole oracle off the charged point. -/
theorem queried_bad_ratio_le [Fintype P] [Fintype A] [Nonempty A] [DecidableEq A]
    {fuel Q β : ℕ} (tree : Tree P A Out fuel)
    (hbudget : ∀ H, (seen tree H).card ≤ Q)
    (Bad : P → (P → A) → A → Prop)
    (hoff : ∀ p H H', AgreeOff p H H' → ∀ a, Bad p H a → Bad p H' a)
    (hlocal : ∀ p H, (univ.filter (Bad p H)).card ≤ β) :
    ((univ.filter fun H : P → A => ∃ p ∈ seen tree H, Bad p H (H p)).card : ℚ) /
      (Fintype.card A : ℚ)^Fintype.card P ≤ (Q*β : ℚ) / Fintype.card A := by
  let Hit := fun p H a => p ∈ seen tree H ∧ Bad p H a
  let weight := fun p H => if p ∈ seen tree H then β else 0
  have hOff : ∀ p H H', AgreeOff p H H' → ∀ a, Hit p H a → Hit p H' a := by
    intro p H H' h a ha
    refine ⟨?_, hoff p H H' h a ha.2⟩
    exact List.mem_toFinset.mpr ((mem_queried_iff tree p h).mp (List.mem_toFinset.mp ha.1))
  have hLocal : ∀ p H, (univ.filter (Hit p H)).card ≤ weight p H := by
    intro p H
    by_cases hp : p ∈ seen tree H
    · simpa [Hit, weight, hp] using hlocal p H
    · simp [Hit, weight, hp]
  have hTotal : ∀ H, ∑ p, weight p H ≤ Q*β := by
    intro H
    have heq : (∑ p, weight p H) = (seen tree H).card * β := by
      simp [weight]
    rw [heq]
    exact Nat.mul_le_mul_right β (hbudget H)
  simpa only [Hit, Nat.cast_mul] using ratio_exists_coord_le _ Hit (fun _ h => h) hOff weight
    (fun p H => by simpa only [Hit] using hLocal p H) (Q*β) hTotal

/-- A scaled local count avoids divisibility assumptions on the answer space.
In particular, an empty fingerprint vector needs no special pivot coordinate. -/
theorem queried_bad_ratio_le_scaled [Fintype P] [Fintype A] [Nonempty A] [DecidableEq A]
    {fuel Q num den : ℕ} (tree : Tree P A Out fuel)
    (hbudget : ∀ H, (seen tree H).card ≤ Q)
    (Bad : P → (P → A) → A → Prop)
    (hoff : ∀ p H H', AgreeOff p H H' → ∀ a, Bad p H a → Bad p H' a)
    (hden : 0 < den)
    (hlocal : ∀ p H, (univ.filter (Bad p H)).card * den ≤ num * Fintype.card A) :
    ((univ.filter fun H : P → A => ∃ p ∈ seen tree H, Bad p H (H p)).card : ℚ) /
      (Fintype.card A : ℚ)^Fintype.card P ≤ (Q*num : ℚ) / den := by
  let β := num * Fintype.card A / den
  have hβ : ∀ p H, (univ.filter (Bad p H)).card ≤ β :=
    fun p H => (Nat.le_div_iff_mul_le hden).mpr (hlocal p H)
  have hround : (β : ℚ) * den ≤ (num : ℚ) * Fintype.card A := by
    exact_mod_cast Nat.div_mul_le_self (num * Fintype.card A) den
  apply (queried_bad_ratio_le tree hbudget Bad hoff hβ).trans
  apply (div_le_div_iff₀ (by positivity) (by exact_mod_cast hden)).mpr
  calc
    (Q : ℚ)*β*den = Q*((β : ℚ)*den) := by ring
    _ ≤ Q*((num : ℚ)*Fintype.card A) := mul_le_mul_of_nonneg_left hround (by positivity)
    _ = (Q*num : ℚ)*Fintype.card A := by ring

end TranscriptV2
