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

end TranscriptV2.Memoize
