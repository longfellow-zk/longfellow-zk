import TranscriptV2.Queries

/-! Parent-digest guesses in adaptive SHA queries. Unlike `Links`, a child
only names digest values: its bytes do not reveal a full parent preimage.
The stopped-prefix event includes self-reference. The quadratic bound charges
all earlier named digests against every later fresh oracle answer. -/
namespace TranscriptV2.DigestCharging
open Finset Bcs.TotalOracle Merkle.RandomOracle
open scoped Classical

variable {P D A Out : Type} [DecidableEq P] [DecidableEq D]

/-- Digests named before the first query at `p`, including names in `p`
itself. The latter covers a query which guesses its own digest. -/
def targets {fuel : ℕ} (claims : P → Finset D) (tree : Tree P A Out fuel)
    (H : P → A) (p : P) : Finset D :=
  (insert p (before tree H p).toFinset).biUnion claims

theorem targets_off {fuel : ℕ} (claims : P → Finset D) (tree : Tree P A Out fuel)
    (p : P) (H H' : P → A) (h : AgreeOff p H H') :
    targets claims tree H p = targets claims tree H' p := by
  simp only [targets,before_congr tree p h]

omit [DecidableEq D] in
theorem target_points_subset {fuel : ℕ} (tree : Tree P A Out fuel)
    (H : P → A) (p : P) (hp : p ∈ seen tree H) :
    insert p (before tree H p).toFinset ⊆ seen tree H := by
  intro q hq
  rcases mem_insert.mp hq with rfl | hq
  · exact hp
  · exact List.mem_toFinset.mpr (before_subset tree H p (List.mem_toFinset.mp hq))

theorem targets_card_le {fuel Q arity : ℕ} (claims : P → Finset D)
    (tree : Tree P A Out fuel) (hbudget : ∀ H, (seen tree H).card ≤ Q)
    (hclaims : ∀ p, (claims p).card ≤ arity) (H : P → A) (p : P)
    (hp : p ∈ seen tree H) : (targets claims tree H p).card ≤ Q*arity := by
  apply card_biUnion_le.trans
  apply (sum_le_sum fun q _ => hclaims q).trans
  simp only [sum_const,nsmul_eq_mul]
  exact Nat.mul_le_mul_right arity ((card_le_card
    (target_points_subset tree H p hp)).trans (hbudget H))

/-- Retain the number of names actually planted by this execution. Queries
which name no unknown digest contribute no guessing allowance. -/
theorem targets_card_le_sum {fuel : ℕ} (claims : P → Finset D)
    (tree : Tree P A Out fuel) (H : P → A) (p : P) (hp : p ∈ seen tree H) :
    (targets claims tree H p).card ≤ ∑ z ∈ seen tree H, (claims z).card := by
  apply card_biUnion_le.trans
  exact sum_le_sum_of_subset (target_points_subset tree H p hp)

def bad {fuel : ℕ} (claims : P → Finset D) (tree : Tree P D Out fuel)
    (p : P) (H : P → D) (a : D) : Prop :=
  p ∈ seen tree H ∧ a ∈ targets claims tree H p

/-- A named parent digest equals the answer at a point queried no earlier
than its child. Outside this event, every genuine parent relation found in
the query table points strictly backwards. -/
def Guess {fuel : ℕ} (claims : P → Finset D) (tree : Tree P D Out fuel)
    (H : P → D) : Prop :=
  ∃ p ∈ seen tree H, H p ∈ targets claims tree H p

/-- This bound needs no recoverable full parent and no order hypothesis.
The parameter `Q` counts distinct raw SHA inputs, including PRF blocks. -/
theorem guess_ratio_le [Fintype P] [Fintype D] [Nonempty D]
    {fuel Q arity : ℕ} (claims : P → Finset D) (tree : Tree P D Out fuel)
    (hbudget : ∀ H, (seen tree H).card ≤ Q)
    (hclaims : ∀ p, (claims p).card ≤ arity) :
    ((univ.filter (Guess claims tree)).card : ℚ) /
      (Fintype.card D : ℚ)^Fintype.card P ≤ (Q*(Q*arity) : ℚ) / Fintype.card D := by
  classical
  have hoff : ∀ p H H', AgreeOff p H H' → ∀ a, bad claims tree p H a → bad claims tree p H' a := by
    intro p H H' h a ha
    refine ⟨?_,?_⟩
    · exact List.mem_toFinset.mpr ((mem_queried_iff tree p h).mp
        (List.mem_toFinset.mp ha.1))
    · simpa only [targets_off claims tree p H H' h] using ha.2
  have hlocal : ∀ p H, (univ.filter (bad claims tree p H)).card ≤ Q*arity := by
    intro p H
    by_cases hp : p ∈ seen tree H
    · simpa only [bad,hp,true_and,filter_mem_eq_inter,univ_inter] using
        targets_card_le claims tree hbudget hclaims H p hp
    · simp only [bad,hp,false_and,filter_false,card_empty,zero_le]
  simpa only [Guess,bad,and_self_left,Nat.cast_mul] using
    queried_bad_ratio_le (β := Q*arity) tree hbudget (bad claims tree) hoff
      (fun p H => by simpa using hlocal p H)

/-- Exact no-guess consequence, with the temporal relation stated as a
stopped prefix rather than an assumed parent-preimage decoding operation. -/
theorem not_named_early {fuel : ℕ} (claims : P → Finset D) (tree : Tree P D Out fuel)
    (H : P → D) (h : ¬Guess claims tree H) (p : P) (hp : p ∈ seen tree H)
    (child : P) (hc : child ∈ insert p (before tree H p).toFinset) :
    H p ∉ claims child := by
  intro hd
  exact h ⟨p,hp,mem_biUnion.mpr ⟨child,hc,hd⟩⟩

omit [DecidableEq D] in
theorem before_total {fuel : ℕ} (tree : Tree P D Out fuel) (H : P → D)
    (p c : P) (hp : p ∈ seen tree H) (hc : c ∈ seen tree H) (hne : p ≠ c) :
    p ∈ before tree H c ∨ c ∈ before tree H p := by
  induction tree with
  | done _ => simp [seen,queried] at hp
  | query q next ih =>
      by_cases hqp : q = p
      · subst q
        exact Or.inl (by simp [before,hne])
      · by_cases hqc : q = c
        · subst q
          exact Or.inr (by simp [before,Ne.symm hne])
        · have hpt : p ∈ seen (next (H q)) H := by
            simpa [seen,queried_query,Ne.symm hqp] using hp
          have hct : c ∈ seen (next (H q)) H := by
            simpa [seen,queried_query,Ne.symm hqc] using hc
          rcases ih (H q) hpt hct with h | h
          · exact Or.inl (by
              simp only [before,if_neg hqc]
              exact List.mem_cons_of_mem q h)
          · exact Or.inr (by
              simp only [before,if_neg hqp]
              exact List.mem_cons_of_mem q h)

/-- In a completed search/replay trace, every matching parent digest was
queried strictly before its child, outside the counted guessing event.
Unqueried parents must be exposed by appending verifier replay before this
lemma is applied; this theorem does not silently assume their membership. -/
theorem parent_before_child {fuel : ℕ} (claims : P → Finset D)
    (tree : Tree P D Out fuel) (H : P → D) (h : ¬Guess claims tree H)
    (p child : P) (hp : p ∈ seen tree H) (hc : child ∈ seen tree H)
    (hd : H p ∈ claims child) : p ∈ before tree H child := by
  have hne : p ≠ child := by
    intro heq
    subst child
    exact not_named_early claims tree H h p hp p (mem_insert_self _ _) hd
  rcases before_total tree H p child hp hc hne with hb | hb
  · exact hb
  · exact (not_named_early claims tree H h p hp child
      (mem_insert_of_mem (List.mem_toFinset.mpr hb)) hd).elim

omit [DecidableEq D] in
theorem before_bind_of_mem {B : Type} {fuel extra : ℕ}
    (tree : Tree P D Out fuel) (replay : Out → Tree P D B extra)
    (H : P → D) (p : P) (hp : p ∈ seen tree H) :
    before (tree.bind replay) H p = before tree H p := by
  induction tree with
  | done _ => simp [seen,queried] at hp
  | query q next ih =>
      by_cases hq : q = p
      · simp only [Tree.bind,before,if_pos hq]
      · have ht : p ∈ seen (next (H q)) H := by
          simpa [seen,queried_query,Ne.symm hq] using hp
        simp only [Tree.bind,before,if_neg hq,ih (H q) ht]

omit [DecidableEq D] in
theorem seen_bind_left {B : Type} {fuel extra : ℕ}
    (tree : Tree P D Out fuel) (replay : Out → Tree P D B extra) (H : P → D) :
    seen tree H ⊆ seen (tree.bind replay) H := by
  intro p hp
  simp only [seen,queried,Tree.run_bind,List.map_append,List.toFinset_append,mem_union] at *
  exact Or.inl hp

/-- Appending verifier replay makes an omitted parent visible. If a child
was already queried by the search, the no-guess order lemma forces its parent
back into the original search prefix. Replay queries therefore cannot be
silently used to pay the adversary's algebraic query budget. -/
theorem parent_in_search {B : Type} {fuel extra : ℕ} (claims : P → Finset D)
    (tree : Tree P D Out fuel) (replay : Out → Tree P D B extra) (H : P → D)
    (h : ¬Guess claims (tree.bind replay) H) (parent child : P)
    (hp : parent ∈ seen (tree.bind replay) H) (hc : child ∈ seen tree H)
    (hd : H parent ∈ claims child) : parent ∈ seen tree H := by
  have hc' := seen_bind_left tree replay H hc
  have hb := parent_before_child claims (tree.bind replay) H h parent child hp hc' hd
  rw [before_bind_of_mem tree replay H child hc] at hb
  exact List.mem_toFinset.mpr (before_subset tree H child hb)


omit [DecidableEq P] [DecidableEq D] in
theorem backward_path {rounds : ℕ} (path : Fin (rounds+1) → P) (member : P → Prop)
    (step : ∀ i : Fin rounds, member (path i.succ) → member (path ⟨i.val,by omega⟩))
    (terminal : member (path ⟨rounds,by omega⟩)) : ∀ i, member (path i) := by
  have descend : ∀ d, (hd : d ≤ rounds) →
      member (path ⟨rounds-d,by omega⟩) := by
    intro d
    induction d with
    | zero => intro _; simpa only [Nat.sub_zero] using terminal
    | succ d ih =>
        intro hd
        let i : Fin rounds := ⟨rounds-(d+1),by omega⟩
        have hc : member (path i.succ) := by
          have heq : i.succ = (⟨rounds-d,by omega⟩ : Fin (rounds+1)) := by
            apply Fin.ext
            dsimp [i]
            omega
          rw [heq]
          exact ih (by omega)
        exact step i hc
  intro i
  have hd := descend (rounds-i.val) (by omega)
  have heq : (⟨rounds-(rounds-i.val),by omega⟩ : Fin (rounds+1)) = i := by
    apply Fin.ext
    change rounds-(rounds-i.val) = i.val
    omega
  simpa only [heq] using hd

/-- Backward induction recovers every node of an accepted replay path in
the original search once its final query is known. The path may be built
from oracle-dependent verifier messages: no full-preimage parent decoder or
serialized round index is needed. -/
theorem path_in_search {B : Type} {fuel extra rounds : ℕ} (claims : P → Finset D)
    (tree : Tree P D Out fuel) (replay : Out → Tree P D B extra) (H : P → D)
    (h : ¬Guess claims (tree.bind replay) H) (path : Fin (rounds+1) → P)
    (visible : ∀ i, path i ∈ seen (tree.bind replay) H)
    (step : ∀ i : Fin rounds, H (path ⟨i.val,by omega⟩) ∈ claims (path i.succ))
    (terminal : path ⟨rounds,by omega⟩ ∈ seen tree H) :
    ∀ i, path i ∈ seen tree H := by
  apply backward_path path (fun p => p ∈ seen tree H) _ terminal
  intro i hc
  exact parent_in_search claims tree replay H h _ _ (visible _) hc (step i)

end TranscriptV2.DigestCharging
