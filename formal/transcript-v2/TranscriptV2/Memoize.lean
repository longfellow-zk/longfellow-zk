import TranscriptV2.Queries
import Merkle.TwoOracle

/-! Cache repeated transcript queries before applying a syntactic call-budget
theorem. The transformation preserves interleaving with the other oracle and
uses one right call per previously unseen right input. A cap is only a total
fallback for programs exceeding their stated distinct-query bound. -/
noncomputable section
namespace TranscriptV2.Memoize
open Merkle.RandomOracle Merkle.RandomOracle.TwoOracleTree Bcs.TotalOracle Finset
open scoped Classical

variable {QL DL P A Out : Type} [DecidableEq QL] [DecidableEq P]

/-- Cached right answers are local computation. Left queries retain their
original order and budget, and every fresh right query consumes one unit. -/
def right (fallback : Out) : {leftFuel rightFuel : ℕ} →
    TwoOracleTree QL DL P A Out leftFuel rightFuel → (cap : ℕ) →
    Finset P → (P → A) → TwoOracleTree QL DL P A Out leftFuel cap
  | _, _, .done out, _, _, _ => .done out
  | _, _, .queryLeft q next, cap, known, cache =>
      .queryLeft q fun answer => right fallback (next answer) cap known cache
  | _, _, .queryRight q next, cap, known, cache =>
      if q ∈ known then right fallback (next (cache q)) cap known cache
      else match cap with
        | 0 => .done fallback
        | cap+1 => .queryRight q fun answer =>
            right fallback (next answer) cap (insert q known) (Function.update cache q answer)

/-- Support of sequential programs is a union, even when they repeat calls. -/
theorem seen_bind {Result : Type} {fuel continuation : ℕ}
    (tree : Tree P A Out fuel) (next : Out → Tree P A Result continuation) (H : P → A) :
    seen (tree.bind next) H = seen tree H ∪ seen (next (tree.run H).1) H := by
  simp only [seen,queried,Tree.run_bind,List.map_append,List.toFinset_append]

/-- A right-only verifier continuation adds at most its own call budget to
an adversary's distinct support, independently of repeated adversary calls. -/
theorem seen_bind_card_le {Result : Type} {fuel continuation cap : ℕ}
    (tree : Tree P A Out fuel) (next : Out → Tree P A Result continuation) (H : P → A)
    (hcap : (seen tree H).card ≤ cap) :
    (seen (tree.bind next) H).card ≤ cap+continuation := by
  rw [seen_bind]
  exact (card_union_le _ _).trans (Nat.add_le_add hcap (seen_card_le _ H))

private theorem seen_query {fuel : ℕ} (q : P) (next : A → Tree P A Out fuel) (H : P → A) :
    seen (.query q next) H = insert q (seen (next (H q)) H) := by
  simp [seen, queried_query]

private theorem fresh_card (s known : Finset P) (q : P) (hq : q ∉ known) :
    (s \ insert q known).card+1 = (insert q s \ known).card := by
  have he : insert q s \ known = insert q (s \ insert q known) := by
    ext x
    by_cases hx : x = q
    · subst x; simp [hq]
    · simp [hx]
  rw [he, card_insert_of_notMem (by simp)]

private theorem cache_insert (cache H : P → A) (known : Finset P) (q : P)
    (hc : ∀ p ∈ known, cache p = H p) :
    ∀ p ∈ insert q known, Function.update cache q (H q) p = H p := by
  intro p hp
  rcases mem_insert.mp hp with rfl | hp
  · simp
  · by_cases he : p = q
    · subst p; simp
    · simp [Function.update_of_ne he, hc p hp]

/-- Right-query caching preserves the final lazy left-oracle slot list as
well as the output. Removing repeated transcript calls cannot add Merkle work. -/
theorem right_left_state {leftFuel rightFuel TL : ℕ} (fallback : Out)
    (tree : TwoOracleTree QL DL P A Out leftFuel rightFuel)
    (tape : Fin TL → DL) (dflt : DL) (leftSeen : List QL)
    (H : P → A) (cap : ℕ) (known : Finset P) (cache : P → A)
    (hcache : ∀ p ∈ known, cache p = H p)
    (hcap : (seen (fixLeft tape dflt tree leftSeen) H \ known).card ≤ cap) :
    ((fixLeftState tape dflt (right fallback tree cap known cache) leftSeen).run H).1 =
      ((fixLeftState tape dflt tree leftSeen).run H).1 := by
  induction tree generalizing cap known cache leftSeen with
  | done out => rfl
  | queryLeft q next ih =>
      simp only [fixLeft] at hcap
      simp only [right, fixLeftState]
      exact ih _ _ _ _ _ hcache hcap
  | queryRight q next ih =>
      have hs : seen (fixLeft tape dflt (.queryRight q next) leftSeen) H =
          insert q (seen (fixLeft tape dflt (next (H q)) leftSeen) H) := by
        exact seen_query _ _ _
      rw [hs] at hcap
      by_cases hq : q ∈ known
      · rw [right.eq_def]
        simp only [if_pos hq, hcache q hq]
        change _ = ((fixLeftState tape dflt (next (H q)) leftSeen).run H).1
        exact ih (H q) leftSeen cap known cache hcache (by
          simpa only [insert_sdiff_of_mem _ hq] using hcap)
      · cases cap with
        | zero =>
            have hpos : 0 < (insert q (seen (fixLeft tape dflt (next (H q)) leftSeen) H) \ known).card :=
              card_pos.mpr ⟨q,by simp [hq]⟩
            omega
        | succ cap =>
            rw [right.eq_def]
            simp only [if_neg hq, fixLeftState, Tree.run_query]
            apply ih (H q) leftSeen cap (insert q known) (Function.update cache q (H q))
            · exact cache_insert cache H known q hcache
            · have he := fresh_card (seen (fixLeft tape dflt (next (H q)) leftSeen) H) known q hq
              omega

omit [DecidableEq P] in
private theorem state_output {leftFuel rightFuel TL : ℕ}
    (tree : TwoOracleTree QL DL P A Out leftFuel rightFuel)
    (tape : Fin TL → DL) (dflt : DL) (leftSeen : List QL) (H : P → A) :
    ((fixLeftState tape dflt tree leftSeen).run H).1.1 =
      ((fixLeft tape dflt tree leftSeen).run H).1 := by
  induction tree generalizing leftSeen with
  | done out => rfl
  | queryLeft q next ih => simp only [fixLeftState, fixLeft]; exact ih _ _
  | queryRight q next ih => simp only [fixLeftState, fixLeft, Tree.run_query]; exact ih _ _

/-- On a run obeying the support cap, caching preserves the original output.
The original program's number of repeated calls is unrestricted by `cap`. -/
theorem right_output {leftFuel rightFuel TL : ℕ} (fallback : Out)
    (tree : TwoOracleTree QL DL P A Out leftFuel rightFuel)
    (tape : Fin TL → DL) (dflt : DL) (leftSeen : List QL)
    (H : P → A) (cap : ℕ) (known : Finset P) (cache : P → A)
    (hcache : ∀ p ∈ known, cache p = H p)
    (hcap : (seen (fixLeft tape dflt tree leftSeen) H \ known).card ≤ cap) :
    ((fixLeft tape dflt (right fallback tree cap known cache) leftSeen).run H).1 =
      ((fixLeft tape dflt tree leftSeen).run H).1 := by
  have h := congrArg Prod.fst (right_left_state fallback tree tape dflt leftSeen H cap known cache hcache hcap)
  simpa only [state_output] using h

/-- Under the same cap, the normal form has exactly the original run's fresh
support relative to the initial cache. No query point is silently omitted. -/
theorem right_support {leftFuel rightFuel TL : ℕ} (fallback : Out)
    (tree : TwoOracleTree QL DL P A Out leftFuel rightFuel)
    (tape : Fin TL → DL) (dflt : DL) (leftSeen : List QL)
    (H : P → A) (cap : ℕ) (known : Finset P) (cache : P → A)
    (hcache : ∀ p ∈ known, cache p = H p)
    (hcap : (seen (fixLeft tape dflt tree leftSeen) H \ known).card ≤ cap) :
    seen (fixLeft tape dflt (right fallback tree cap known cache) leftSeen) H =
      seen (fixLeft tape dflt tree leftSeen) H \ known := by
  induction tree generalizing cap known cache leftSeen with
  | done out => simp [right, fixLeft, seen, queried]
  | queryLeft q next ih =>
      simp only [right, fixLeft] at hcap ⊢
      exact ih _ _ _ _ _ hcache hcap
  | queryRight q next ih =>
      have hs : seen (fixLeft tape dflt (.queryRight q next) leftSeen) H =
          insert q (seen (fixLeft tape dflt (next (H q)) leftSeen) H) := seen_query _ _ _
      rw [hs] at hcap
      by_cases hq : q ∈ known
      · rw [right.eq_def]
        simp only [if_pos hq, hcache q hq]
        rw [hs, insert_sdiff_of_mem _ hq]
        exact ih (H q) leftSeen cap known cache hcache (by
          simpa only [insert_sdiff_of_mem _ hq] using hcap)
      · cases cap with
        | zero =>
            have hpos : 0 < (insert q (seen (fixLeft tape dflt (next (H q)) leftSeen) H) \ known).card :=
              card_pos.mpr ⟨q,by simp [hq]⟩
            omega
        | succ cap =>
            rw [right.eq_def]
            simp only [if_neg hq, fixLeft, seen_query]
            have hc := cache_insert cache H known q hcache
            have hb : (seen (fixLeft tape dflt (next (H q)) leftSeen) H \ insert q known).card ≤ cap := by
              have he := fresh_card (seen (fixLeft tape dflt (next (H q)) leftSeen) H) known q hq
              omega
            rw [ih (H q) leftSeen cap (insert q known) (Function.update cache q (H q)) hc hb]
            ext p
            by_cases he : p = q
            · subst p; simp [hq]
            · simp [he]

/-- Every emitted right query is fresh, even on branches that exhaust the
cap. Cached calls therefore consume no syntactic right-oracle budget. -/
theorem right_fresh {leftFuel rightFuel TL : ℕ} (fallback : Out)
    (tree : TwoOracleTree QL DL P A Out leftFuel rightFuel)
    (tape : Fin TL → DL) (dflt : DL) (leftSeen : List QL)
    (H : P → A) (cap : ℕ) (known : Finset P) (cache : P → A) :
    (queried (fixLeft tape dflt (right fallback tree cap known cache) leftSeen) H).Nodup ∧
      ∀ p ∈ queried (fixLeft tape dflt (right fallback tree cap known cache) leftSeen) H, p ∉ known := by
  induction tree generalizing cap known cache leftSeen with
  | done out => simp [right, fixLeft, queried]
  | queryLeft q next ih =>
      simp only [right, fixLeft]
      exact ih _ _ _ _ _
  | queryRight q next ih =>
      rw [right.eq_def]
      by_cases hq : q ∈ known
      · simp only [if_pos hq]
        exact ih (cache q) leftSeen cap known cache
      · simp only [if_neg hq]
        cases cap with
        | zero => simp [fixLeft, queried]
        | succ cap =>
            simp only [fixLeft, queried_query]
            have ht := ih (H q) leftSeen cap (insert q known) (Function.update cache q (H q))
            constructor
            · apply List.nodup_cons.mpr
              refine ⟨?_,ht.1⟩
              intro hm
              exact ht.2 q hm (mem_insert_self _ _)
            · intro p hp
              rcases List.mem_cons.mp hp with rfl | hp
              · exact hq
              · exact fun hk => ht.2 p hp (mem_insert_of_mem hk)

/-- Normalize only transcript calls; the left-oracle budget is unchanged.
The fallback and initial cache value never affect cap-respecting runs. -/
def normalizeRight {leftFuel rightFuel : ℕ} (fallback : Out) (dflt : A)
    (tree : TwoOracleTree QL DL P A Out leftFuel rightFuel) (Q : ℕ) :
    TwoOracleTree QL DL P A Out leftFuel Q :=
  right fallback tree Q ∅ (fun _ => dflt)

theorem normalizeRight_output {leftFuel rightFuel TL Q : ℕ} (fallback : Out) (dflt : A)
    (tree : TwoOracleTree QL DL P A Out leftFuel rightFuel)
    (tape : Fin TL → DL) (leftDefault : DL) (H : P → A)
    (hcap : (seen (fixLeft tape leftDefault tree []) H).card ≤ Q) :
    ((fixLeft tape leftDefault (normalizeRight fallback dflt tree Q) []).run H).1 =
      ((fixLeft tape leftDefault tree []).run H).1 := by
  apply right_output
  · simp
  · simpa using hcap

theorem normalizeRight_support {leftFuel rightFuel TL Q : ℕ} (fallback : Out) (dflt : A)
    (tree : TwoOracleTree QL DL P A Out leftFuel rightFuel)
    (tape : Fin TL → DL) (leftDefault : DL) (H : P → A)
    (hcap : (seen (fixLeft tape leftDefault tree []) H).card ≤ Q) :
    seen (fixLeft tape leftDefault (normalizeRight fallback dflt tree Q) []) H =
      seen (fixLeft tape leftDefault tree []) H := by
  have h := right_support fallback tree tape leftDefault [] H Q ∅ (fun _ => dflt)
    (by simp) (by simpa using hcap)
  simpa only [normalizeRight, sdiff_empty] using h

theorem normalizeRight_left_state {leftFuel rightFuel TL Q : ℕ} (fallback : Out) (dflt : A)
    (tree : TwoOracleTree QL DL P A Out leftFuel rightFuel)
    (tape : Fin TL → DL) (leftDefault : DL) (H : P → A)
    (hcap : (seen (fixLeft tape leftDefault tree []) H).card ≤ Q) :
    ((fixLeftState tape leftDefault (normalizeRight fallback dflt tree Q) []).run H).1 =
      ((fixLeftState tape leftDefault tree []).run H).1 := by
  apply right_left_state
  · simp
  · simpa using hcap

/-- The normalized program makes exactly as many calls as the original run
has distinct right inputs, not as many as its original call fuel. -/
theorem normalizeRight_query_count {leftFuel rightFuel TL Q : ℕ} (fallback : Out) (dflt : A)
    (tree : TwoOracleTree QL DL P A Out leftFuel rightFuel)
    (tape : Fin TL → DL) (leftDefault : DL) (H : P → A)
    (hcap : (seen (fixLeft tape leftDefault tree []) H).card ≤ Q) :
    (queried (fixLeft tape leftDefault (normalizeRight fallback dflt tree Q) []) H).length =
      (seen (fixLeft tape leftDefault tree []) H).card := by
  have hn := (right_fresh fallback tree tape leftDefault [] H Q ∅ (fun _ => dflt)).1
  rw [← normalizeRight_support fallback dflt tree tape leftDefault H hcap]
  exact (List.toFinset_card_of_nodup hn).symm

end TranscriptV2.Memoize
