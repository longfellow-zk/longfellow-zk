import Survival.History

/-! Replay the original program from a completed cache, stopping before the
current context. Actual strict ancestors on a recovered path are in that
cache. No claim about malformed off-path queries is necessary.
-/
noncomputable section
namespace Survival.PrefixCache
open Merkle.RandomOracle TranscriptV2 Bcs.TotalOracle
open scoped Classical

variable {P A Out : Type} [DecidableEq P]

def cache (fallback : A) : List (P × A) → P → A
  | [], _ => fallback
  | (point,answer)::past, target => if target = point then answer else cache fallback past target

def advance (past : List (P × A)) (point : P) (answer : A) : List (P × A) := past ++ [(point,answer)]

omit [DecidableEq P] in
theorem advance_fold (initial past : List (P × A)) :
    past.foldl (fun state qa => advance state qa.1 qa.2) initial = initial ++ past := by
  induction past generalizing initial with
  | nil => simp
  | cons qa past ih =>
      rw [List.foldl_cons, ih]
      simp only [advance, List.append_assoc, List.singleton_append, Prod.mk.eta]

theorem cache_agrees (fallback : A) (past : List (P × A)) (H : P → A)
    (sound : ∀ qa ∈ past, qa.2 = H qa.1) (point : P) (present : point ∈ past.map Prod.fst) :
    cache fallback past point = H point := by
  induction past with
  | nil => simp at present
  | cons qa past ih =>
      by_cases same : point = qa.1
      · simp only [cache, same, if_true]
        exact sound qa List.mem_cons_self
      · simp only [cache, if_neg same]
        apply ih (fun entry member => sound entry (List.mem_cons_of_mem _ member))
        simpa only [List.map_cons, List.mem_cons, same, false_or] using present

omit [DecidableEq P] in
theorem cut_agrees {Key : Type} [DecidableEq Key] (label : P → Key) (key : Key)
    {fuel : ℕ} (tree : Tree P A Out fuel) (H H' : P → A)
    (past rest : List (P × A)) (point : P) (answer : A)
    (trace : (tree.run H).2 = past ++ (point,answer)::rest)
    (bound : label point = key)
    (agree : ∀ earlier ∈ past.map Prod.fst, H' earlier = H earlier) :
    beforeLabel label key tree H' = beforeLabel label key tree H := by
  induction tree generalizing past with
  | done out => simp only [Merkle.RandomOracle.Tree.run_done] at trace; simp at trace
  | query current next ih =>
      cases past with
      | nil =>
          have equal := List.cons.inj trace |>.1
          have same : current = point := congrArg Prod.fst equal
          simp only [beforeLabel, same, bound, if_true]
      | cons qa past =>
          have parts := List.cons.inj trace
          have currentEq : current = qa.1 := congrArg Prod.fst parts.1
          have valueEq : H current = qa.2 := congrArg Prod.snd parts.1
          have sameAnswer := agree current (by simp only [List.map_cons, List.mem_cons, currentEq, true_or])
          by_cases stop : label current = key
          · simp only [beforeLabel, stop, if_true]
          · simp only [beforeLabel, stop, if_false, sameAnswer]
            congr 1
            apply ih (H current) past
            · exact parts.2
            · intro earlier member
              exact agree earlier (by simp only [List.map_cons, List.mem_cons]; exact Or.inr member)

theorem cut_cache {Key : Type} [DecidableEq Key] (label : P → Key)
    {fuel : ℕ} (tree : Tree P A Out fuel) (H : P → A) (fallback : A)
    (past rest : List (P × A)) (point : P) (answer : A)
    (trace : (tree.run H).2 = past ++ (point,answer)::rest) :
    beforeLabel label (label point) tree (cache fallback past) = beforeLabel label (label point) tree H := by
  apply cut_agrees label (label point) tree H (cache fallback past) past rest point answer trace rfl
  apply cache_agrees fallback past H
  intro qa member
  apply Merkle.RandomOracle.Tree.trace_sound tree H qa
  rw [trace]
  exact List.mem_append_left _ member

theorem before_of_first_left {fuel : ℕ} (tree : Tree P A Out fuel) (H : P → A)
    (parent child : P) (different : parent ≠ child) (queriedChild : child ∈ seen tree H)
    (ordered : firstOfTwo tree H parent child = .left) : parent ∈ before tree H child := by
  induction tree with
  | done _ => simp only [seen, queried_done, List.toFinset_nil, Finset.notMem_empty] at queriedChild
  | query point next ih =>
      by_cases hp : point = parent
      · subst point
        simp only [before, different, if_false, List.mem_cons, true_or]
      · by_cases hc : point = child
        · rw [firstOfTwo, if_neg hp, if_pos hc] at ordered
          cases ordered
        · have later : child ∈ seen (next (H point)) H := by
            simpa [seen, queried_query, Ne.symm hc] using queriedChild
          have orderTail : firstOfTwo (next (H point)) H parent child = .left := by
            simpa only [firstOfTwo, hp, hc, if_false] using ordered
          rw [before, if_neg hc]
          exact List.mem_cons_of_mem point (ih (H point) later orderTail)

theorem before_trans {fuel : ℕ} (tree : Tree P A Out fuel) (H : P → A)
    (first second third : P) (left : first ∈ before tree H second)
    (right : second ∈ before tree H third) : first ∈ before tree H third := by
  induction tree with
  | done _ => simp [before] at left
  | query point next ih =>
      by_cases ht : point = third
      · simp only [before, ht, if_true, List.not_mem_nil] at right
      · by_cases hs : point = second
        · simp only [before, hs, if_true, List.not_mem_nil] at left
        · by_cases hf : point = first
          · rw [before, if_neg ht]
            exact List.mem_cons.mpr (Or.inl hf.symm)
          · have leftTail : first ∈ before (next (H point)) H second := by
              simpa only [before, hs, if_false, List.mem_cons, Ne.symm hf, false_or] using left
            have rightTail : second ∈ before (next (H point)) H third := by
              simpa only [before, ht, if_false, List.mem_cons, Ne.symm hs, false_or] using right
            rw [before, if_neg ht]
            exact List.mem_cons_of_mem point (ih (H point) leftTail rightTail)

theorem earlier_path_before {fuel rounds : ℕ} (tree : Tree P A Out fuel) (H : P → A)
    (path : ℕ → P)
    (queriedPath : ∀ i ≤ rounds, path i ∈ seen tree H)
    (ordered : ∀ i < rounds, firstOfTwo tree H (path i) (path (i+1)) = .left)
    (different : ∀ i < rounds, path i ≠ path (i+1))
    (index : ℕ) (within : index ≤ rounds) : ∀ earlier < index, path earlier ∈ before tree H (path index) := by
  induction index with
  | zero => intro earlier impossible; omega
  | succ index ih =>
      have hi : index < rounds := by omega
      have last := before_of_first_left tree H (path index) (path (index+1)) (different index hi)
        (queriedPath (index+1) within) (ordered index hi)
      intro earlier bounded
      by_cases same : earlier = index
      · simpa only [same] using last
      · have old := ih (by omega) earlier (by omega)
        exact before_trans tree H (path earlier) (path index) (path (index+1)) old last

end Survival.PrefixCache
