import TranscriptV2.DigestCharging
import TranscriptV2.SharedCharging

/-! Digest-only ordering for grouped answers `(digest, challenges)`. This
reuses the stopped-prefix SHA correction and leaves all generic algebraic
bad-answer and shared-pair charging theorems unchanged. -/
namespace TranscriptV2.DigestProjection
open Finset Bcs.TotalOracle Merkle.RandomOracle
open scoped Classical

variable {P D C Out : Type} [DecidableEq P] [DecidableEq D]

def bad {fuel : ℕ} (claims : P → Finset D) (tree : Tree P (D × C) Out fuel)
    (p : P) (H : P → D × C) (a : D × C) : Prop :=
  p ∈ seen tree H ∧ a.1 ∈ DigestCharging.targets claims tree H p

def Guess {fuel : ℕ} (claims : P → Finset D) (tree : Tree P (D × C) Out fuel)
    (H : P → D × C) : Prop := ∃ p ∈ seen tree H, (H p).1 ∈ DigestCharging.targets claims tree H p

noncomputable def charge {fuel : ℕ} (claims : P → Finset D) (tree : Tree P (D × C) Out fuel)
    (H : P → D × C) : ℚ :=
  ∑ p ∈ seen tree H, if bad claims tree p H (H p) then 1 else 0

theorem charge_nonneg {fuel : ℕ} (claims : P → Finset D) (tree : Tree P (D × C) Out fuel)
    (H : P → D × C) : 0 ≤ charge claims tree H := by
  apply sum_nonneg
  intro point _
  split_ifs <;> norm_num

theorem guess_charged {fuel : ℕ} (claims : P → Finset D) (tree : Tree P (D × C) Out fuel)
    (H : P → D × C) (guessed : Guess claims tree H) : 1 ≤ charge claims tree H := by
  obtain ⟨point,member,hit⟩ := guessed
  have current : bad claims tree point H (H point) := ⟨member,hit⟩
  have term := single_le_sum (f := fun p => if bad claims tree p H (H p) then (1 : ℚ) else 0)
    (fun p _ => by split_ifs <;> norm_num) member
  simpa only [charge,if_pos current] using term

theorem bad_off {fuel : ℕ} (claims : P → Finset D) (tree : Tree P (D × C) Out fuel)
    (p : P) (H H' : P → D × C) (h : AgreeOff p H H') (a : D × C) :
    bad claims tree p H a → bad claims tree p H' a := by
  intro ⟨hp,ha⟩
  refine ⟨?_,?_⟩
  · exact List.mem_toFinset.mpr ((mem_queried_iff tree p h).mp (List.mem_toFinset.mp hp))
  · simpa only [DigestCharging.targets_off claims tree p H H' h] using ha

theorem bad_card_le [Fintype D] [Fintype C] {fuel Q arity : ℕ}
    (claims : P → Finset D) (tree : Tree P (D × C) Out fuel)
    (budget : ∀ H, (seen tree H).card ≤ Q)
    (arityBound : ∀ p, (claims p).card ≤ arity) (p : P) (H : P → D × C) :
    (univ.filter (bad claims tree p H)).card ≤ Q*arity*Fintype.card C := by
  by_cases hp : p ∈ seen tree H
  · have heq : univ.filter (bad claims tree p H) =
        (DigestCharging.targets claims tree H p) ×ˢ (univ : Finset C) := by
      ext a
      simp [bad,hp]
    rw [heq,card_product,card_univ]
    exact Nat.mul_le_mul_right _ (DigestCharging.targets_card_le claims tree budget arityBound H p hp)
  · simp only [bad,hp,false_and,filter_false,card_empty,zero_le]

private theorem bad_sum_le_claims [Fintype D] [Nonempty D] [Fintype C]
    {fuel : ℕ} (claims : P → Finset D) (tree : Tree P (D × C) Out fuel)
    (p : P) (H : P → D × C) :
    (∑ a : D × C, if bad claims tree p H a then (1 : ℚ) else 0) ≤
      Fintype.card C * ∑ z ∈ seen tree H, ((claims z).card : ℚ) := by
  by_cases hp : p ∈ seen tree H
  · have sets : univ.filter (bad claims tree p H) =
        (DigestCharging.targets claims tree H p) ×ˢ (univ : Finset C) := by
      ext a
      simp [bad,hp]
    rw [sum_boole,sets,card_product,card_univ,Nat.cast_mul,mul_comm]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [← Nat.cast_sum]
    exact Nat.cast_le.mpr (DigestCharging.targets_card_le_sum claims tree H p hp)
  · simp only [bad,hp,false_and,if_false,sum_const_zero]
    positivity

/-- Guessing cost proportional to the actual number of planted names. The
factor `Q` counts later opportunities to hit a target; the other factor is
not replaced by `Q`, so those target-planting queries can pay for this cost
in the same budget as the algebraic queries. -/
theorem guess_sum_le_claims [Fintype P] [Fintype D] [Nonempty D]
    [Fintype C] [Nonempty C] {fuel Q : ℕ} (claims : P → Finset D)
    (tree : Tree P (D × C) Out fuel) (queries : ∀ H, (seen tree H).card ≤ Q) :
    (∑ H : P → D × C, ∑ p ∈ seen tree H,
      if bad claims tree p H (H p) then (1 : ℚ) else 0) ≤
      (Q : ℚ)/Fintype.card D *
        ∑ H : P → D × C, ∑ z ∈ seen tree H, ((claims z).card : ℚ) := by
  let mass := fun H : P → D × C => ∑ z ∈ seen tree H, ((claims z).card : ℚ)
  have off p H H' (same : AgreeOff p H H') a :
      (if bad claims tree p H a then (1 : ℚ) else 0) =
        (if bad claims tree p H' a then (1 : ℚ) else 0) := by
    have iff : bad claims tree p H a ↔ bad claims tree p H' a :=
      ⟨bad_off claims tree p H H' same a,
        bad_off claims tree p H' H (fun z hz => (same z hz).symm) a⟩
    rw [iff]
  have localMean p H :
      (∑ a : D × C, if bad claims tree p H a then (1 : ℚ) else 0) ≤
        Fintype.card (D × C) * (mass H/Fintype.card D) := by
    have scale : (Fintype.card (D × C) : ℚ) * (mass H/Fintype.card D) =
        Fintype.card C * mass H := by
      rw [Fintype.card_prod,Nat.cast_mul]
      have nonzero : (Fintype.card D : ℚ) ≠ 0 := by positivity
      field_simp
    rw [scale]
    exact bad_sum_le_claims claims tree p H
  have bound := queried_weight_adaptive_sum_le tree
    (fun p H a => if bad claims tree p H a then (1 : ℚ) else 0)
    off (fun _ H => mass H/Fintype.card D) localMean
  apply bound.trans
  rw [mul_sum]
  apply sum_le_sum
  intro H _
  simp only [sum_const,nsmul_eq_mul]
  change ((seen tree H).card : ℚ) * (mass H/Fintype.card D) ≤
    (Q : ℚ)/Fintype.card D * mass H
  rw [div_mul_eq_mul_div,mul_div_assoc]
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast queries H) (by dsimp [mass]; positivity)

/-- Count target hits only at receiving inputs in a fixed byte domain.
The restriction is on the query name, never on whether a later verifier
uses its answer. Thus the stopped-prefix independence is unchanged. -/
noncomputable def receivingCharge {fuel : ℕ} (receives : P → Prop)
    (claims : P → Finset D) (tree : Tree P (D × C) Out fuel) (H : P → D × C) : ℚ :=
  ∑ p ∈ seen tree H, if receives p ∧ bad claims tree p H (H p) then 1 else 0

theorem receivingCharge_nonneg {fuel : ℕ} (receives : P → Prop)
    (claims : P → Finset D) (tree : Tree P (D × C) Out fuel) (H : P → D × C) :
    0 ≤ receivingCharge receives claims tree H := by
  apply sum_nonneg
  intro p _
  split_ifs <;> norm_num

/-- An actual receiving hit contributes one unit without selecting any
future authentication path in the definition of the charge. -/
theorem receiving_hit_charged {fuel : ℕ} (receives : P → Prop)
    (claims : P → Finset D) (tree : Tree P (D × C) Out fuel) (H : P → D × C)
    (p : P) (receiving : receives p) (hit : bad claims tree p H (H p)) :
    1 ≤ receivingCharge receives claims tree H := by
  have term := single_le_sum
    (f := fun z => if receives z ∧ bad claims tree z H (H z) then (1 : ℚ) else 0)
    (fun _ _ => by split_ifs <;> norm_num) hit.1
  simpa only [receivingCharge,if_pos (And.intro receiving hit)] using term

/-- A receiving query pays at most `Q * arity / |D|`. Retaining the
number of eligible receiving slots lets auxiliary work share the original
query budget with ordinary algebraic work. No acceptance condition occurs. -/
theorem receiving_sum_le [Fintype P] [Fintype D] [Nonempty D]
    [Fintype C] [Nonempty C] {fuel Q arity : ℕ}
    (receives auxiliary : P → Prop) (eligible : ∀ p, receives p → auxiliary p)
    (claims : P → Finset D) (tree : Tree P (D × C) Out fuel)
    (queries : ∀ H, (seen tree H).card ≤ Q)
    (claimBound : ∀ p, (claims p).card ≤ arity) :
    (∑ H : P → D × C, receivingCharge receives claims tree H) ≤
      ∑ H : P → D × C, ∑ p ∈ seen tree H,
        if auxiliary p then (Q*arity : ℚ)/Fintype.card D else 0 := by
  let weight := fun p H (a : D × C) =>
    if receives p ∧ bad claims tree p H a then (1 : ℚ) else 0
  have off p H H' (same : AgreeOff p H H') a : weight p H a = weight p H' a := by
    have sameBad : bad claims tree p H a ↔ bad claims tree p H' a :=
      ⟨bad_off claims tree p H H' same a,
        bad_off claims tree p H' H (fun z hz => (same z hz).symm) a⟩
    simp only [weight, sameBad]
  have localMean p H : (∑ a, weight p H a) ≤ Fintype.card (D × C) *
      (if auxiliary p then (Q*arity : ℚ)/Fintype.card D else 0) := by
    by_cases receiving : receives p
    · have bound := bad_card_le claims tree queries claimBound p H
      have count : (∑ a : D × C, weight p H a) ≤ (Q*arity*Fintype.card C : ℚ) := by
        simpa only [weight,receiving,true_and,sum_boole,Nat.cast_mul] using (Nat.cast_le (α := ℚ)).mpr bound
      apply count.trans_eq
      rw [if_pos (eligible p receiving),Fintype.card_prod,Nat.cast_mul]
      have nonzero : (Fintype.card D : ℚ) ≠ 0 := by positivity
      field_simp
    · simp only [weight,receiving,false_and,if_false,sum_const_zero]
      exact mul_nonneg (Nat.cast_nonneg _) (by split_ifs <;> positivity)
  exact queried_weight_adaptive_sum_le tree weight off
    (fun p _ => if auxiliary p then (Q*arity : ℚ)/Fintype.card D else 0) localMean

theorem guess_ratio_le [Fintype P] [Fintype D] [Nonempty D] [Fintype C] [Nonempty C]
    [DecidableEq C] {fuel Q arity : ℕ} (claims : P → Finset D)
    (tree : Tree P (D × C) Out fuel) (budget : ∀ H, (seen tree H).card ≤ Q)
    (arityBound : ∀ p, (claims p).card ≤ arity) :
    ((univ.filter (Guess claims tree)).card : ℚ) /
        (Fintype.card (D × C) : ℚ)^Fintype.card P ≤ (Q*(Q*arity) : ℚ) / Fintype.card D := by
  have h := queried_bad_ratio_le (β := Q*arity*Fintype.card C) tree budget
    (bad claims tree) (bad_off claims tree)
    (fun p H => by simpa using bad_card_le claims tree budget arityBound p H)
  have hC : (Fintype.card C : ℚ) ≠ 0 := by positivity
  apply (show ((univ.filter (Guess claims tree)).card : ℚ) /
      (Fintype.card (D × C) : ℚ)^Fintype.card P ≤
      (Q*(Q*arity*Fintype.card C) : ℚ) / Fintype.card (D × C) from by
    simpa only [Guess,bad,and_self_left,Nat.cast_mul] using h).trans_eq
  simp only [Fintype.card_prod,Nat.cast_mul]
  field_simp

theorem parent_before_child {fuel : ℕ} (claims : P → Finset D)
    (tree : Tree P (D × C) Out fuel) (H : P → D × C) (h : ¬Guess claims tree H)
    (parent child : P) (hp : parent ∈ seen tree H) (hc : child ∈ seen tree H)
    (hd : (H parent).1 ∈ claims child) : parent ∈ before tree H child := by
  have noEarly : child ∉ insert parent (before tree H parent).toFinset := by
    intro hm
    exact h ⟨parent,hp,mem_biUnion.mpr ⟨child,hm,hd⟩⟩
  have hne : parent ≠ child := by
    intro heq
    subst child
    exact noEarly (mem_insert_self _ _)
  rcases DigestCharging.before_total tree H parent child hp hc hne with hb | hb
  · exact hb
  · exact (noEarly (mem_insert_of_mem (List.mem_toFinset.mpr hb))).elim

theorem parent_in_search {B : Type} {fuel extra : ℕ} (claims : P → Finset D)
    (tree : Tree P (D × C) Out fuel) (replay : Out → Tree P (D × C) B extra)
    (H : P → D × C) (h : ¬Guess claims (tree.bind replay) H) (parent child : P)
    (hp : parent ∈ seen (tree.bind replay) H) (hc : child ∈ seen tree H)
    (hd : (H parent).1 ∈ claims child) : parent ∈ seen tree H := by
  have hc' := DigestCharging.seen_bind_left tree replay H hc
  have hb := parent_before_child claims (tree.bind replay) H h parent child hp hc' hd
  rw [DigestCharging.before_bind_of_mem tree replay H child hc] at hb
  exact List.mem_toFinset.mpr (before_subset tree H child hb)

theorem path_in_search {B : Type} {fuel extra rounds : ℕ} (claims : P → Finset D)
    (tree : Tree P (D × C) Out fuel) (replay : Out → Tree P (D × C) B extra)
    (H : P → D × C) (h : ¬Guess claims (tree.bind replay) H) (path : Fin (rounds+1) → P)
    (visible : ∀ i, path i ∈ seen (tree.bind replay) H)
    (step : ∀ i : Fin rounds, (H (path ⟨i.val,by omega⟩)).1 ∈ claims (path i.succ))
    (terminal : path ⟨rounds,by omega⟩ ∈ seen tree H) : ∀ i, path i ∈ seen tree H := by
  apply DigestCharging.backward_path path (fun p => p ∈ seen tree H) _ terminal
  intro i hc
  exact parent_in_search claims tree replay H h _ _ (visible _) hc (step i)

namespace Replay

/-- A target first matched by a fresh verifier query. Targets can have been
planted during search or replay; neither case receives algebraic-query budget. -/
def bad {B : Type} {fuel extra : ℕ} (claims : P → Finset D)
    (tree : Tree P (D × C) Out fuel) (replay : Out → Tree P (D × C) B extra)
    (p : P) (H : P → D × C) (a : D × C) : Prop :=
  p ∈ seen (tree.bind replay) H \ seen tree H ∧
    a.1 ∈ DigestCharging.targets claims (tree.bind replay) H p

theorem bad_off {B : Type} {fuel extra : ℕ} (claims : P → Finset D)
    (tree : Tree P (D × C) Out fuel) (replay : Out → Tree P (D × C) B extra)
    (p : P) (H H' : P → D × C) (same : AgreeOff p H H') (a : D × C) :
    bad claims tree replay p H a → bad claims tree replay p H' a := by
  rintro ⟨member,hit⟩
  have missing := (mem_sdiff.mp member).2
  have unchanged := run_eq_of_not_mem tree p same (by simpa only [seen,List.mem_toFinset] using missing)
  have searchSame : seen tree H = seen tree H' := by simp only [seen,queried,unchanged]
  have present : p ∈ seen (tree.bind replay) H' := by
    exact List.mem_toFinset.mpr ((mem_queried_iff (tree.bind replay) p same).mp
      (List.mem_toFinset.mp (mem_sdiff.mp member).1))
  refine ⟨mem_sdiff.mpr ⟨present,searchSame ▸ missing⟩,?_⟩
  simpa only [DigestCharging.targets_off claims (tree.bind replay) p H H' same] using hit

/-- A hit at an adversarial query keeps exactly its original stopped
prefix. Every other hit is charged to a new verifier query, so replay cannot
manufacture an adversarial algebraic-query allowance. -/
theorem guess_split {B : Type} {fuel extra : ℕ} (claims : P → Finset D)
    (tree : Tree P (D × C) Out fuel) (replay : Out → Tree P (D × C) B extra)
    (H : P → D × C) (hit : Guess claims (tree.bind replay) H) :
    Guess claims tree H ∨ ∃ p, bad claims tree replay p H (H p) := by
  obtain ⟨p,member,target⟩ := hit
  by_cases old : p ∈ seen tree H
  · apply Or.inl
    refine ⟨p,old,?_⟩
    simpa only [DigestCharging.targets,DigestCharging.before_bind_of_mem tree replay H p old] using target
  · exact Or.inr ⟨p,mem_sdiff.mpr ⟨member,old⟩,target⟩

omit [DecidableEq D] in
private theorem new_card_le {B : Type} {fuel extra : ℕ}
    (tree : Tree P (D × C) Out fuel) (replay : Out → Tree P (D × C) B extra)
    (H : P → D × C) : (seen (tree.bind replay) H \ seen tree H).card ≤ extra := by
  have subset : seen (tree.bind replay) H \ seen tree H ⊆ seen (replay (tree.run H).1) H := by
    intro p member
    have both := mem_sdiff.mp member
    simp only [seen,queried,Tree.run_bind,List.map_append,List.toFinset_append,mem_union] at both
    exact both.1.resolve_left both.2
  exact (card_le_card subset).trans (seen_card_le _ _)

/-- Charge only newly sampled verifier coordinates. For grouped streams,
`replayQueries` counts new rows or nodes, not rejected draws or repeated reads.
Singleton targets cost `replayQueries * (Q + replayQueries) / |Digest|`. -/
theorem guess_ratio_le_support [Fintype P] [Fintype D] [Nonempty D]
    [Fintype C] [Nonempty C] [DecidableEq C] {B : Type} {fuel extra Q replayQueries arity : ℕ}
    (claims : P → Finset D) (tree : Tree P (D × C) Out fuel)
    (replay : Out → Tree P (D × C) B extra) (queries : ∀ H, (seen tree H).card ≤ Q)
    (fresh : ∀ H, (seen (tree.bind replay) H \ seen tree H).card ≤ replayQueries)
    (claimBound : ∀ p, (claims p).card ≤ arity) :
    ((univ.filter fun H => ∃ p, bad claims tree replay p H (H p)).card : ℚ) /
      (Fintype.card (D × C) : ℚ)^Fintype.card P ≤
        (replayQueries*(Q+replayQueries)*arity : ℚ)/Fintype.card D := by
  have combined H : (seen (tree.bind replay) H).card ≤ Q+replayQueries := by
    have subset : seen tree H ⊆ seen (tree.bind replay) H := by
      simp only [seen,queried,Tree.run_bind,List.map_append,List.toFinset_append]
      exact subset_union_left
    have count := card_sdiff_add_card_eq_card subset
    have searchBound := queries H
    have replayBound := fresh H
    omega
  let beta := (Q+replayQueries)*arity*Fintype.card C
  let weight := fun p H => if p ∈ seen (tree.bind replay) H \ seen tree H then beta else 0
  have hlocal p H : (univ.filter (bad claims tree replay p H)).card ≤ weight p H := by
    by_cases member : p ∈ seen (tree.bind replay) H \ seen tree H
    · have sets : univ.filter (bad claims tree replay p H) =
          DigestCharging.targets claims (tree.bind replay) H p ×ˢ (univ : Finset C) := by
        ext a
        simp [bad,member]
      have targets := DigestCharging.targets_card_le claims (tree.bind replay) combined claimBound H p
        (mem_sdiff.mp member).1
      simp only [sets,card_product,card_univ,weight,if_pos member]
      exact Nat.mul_le_mul_right _ targets
    · simp only [bad,member,false_and,filter_false,card_empty,zero_le]
  have htotal H : (∑ p, weight p H) ≤ replayQueries*beta := by
    have total : (∑ p, weight p H) = (seen (tree.bind replay) H \ seen tree H).card*beta := by
      simp only [weight,← sum_filter,filter_mem_eq_inter,univ_inter,sum_const,nsmul_eq_mul,Nat.cast_id]
    rw [total]
    exact Nat.mul_le_mul_right beta (fresh H)
  have bound := ratio_exists_coord_le
    (fun H => ∃ p, bad claims tree replay p H (H p)) (bad claims tree replay)
    (fun _ h => h) (bad_off claims tree replay) weight hlocal (replayQueries*beta) htotal
  apply bound.trans_eq
  simp only [beta,Fintype.card_prod,Nat.cast_mul,Nat.cast_add]
  have nonzero : (Fintype.card C : ℚ) ≠ 0 := by positivity
  field_simp

/-- The syntactic replay-fuel bound is a special case of support accounting. -/
theorem guess_ratio_le [Fintype P] [Fintype D] [Nonempty D]
    [Fintype C] [Nonempty C] [DecidableEq C] {B : Type} {fuel extra Q arity : ℕ}
    (claims : P → Finset D) (tree : Tree P (D × C) Out fuel)
    (replay : Out → Tree P (D × C) B extra) (queries : ∀ H, (seen tree H).card ≤ Q)
    (claimBound : ∀ p, (claims p).card ≤ arity) :
    ((univ.filter fun H => ∃ p, bad claims tree replay p H (H p)).card : ℚ) /
      (Fintype.card (D × C) : ℚ)^Fintype.card P ≤
        (extra*(Q+extra)*arity : ℚ)/Fintype.card D :=
  guess_ratio_le_support claims tree replay queries (new_card_le tree replay) claimBound

end Replay

end TranscriptV2.DigestProjection
