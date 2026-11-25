import Bcs.QueryRoleCompiler
import LfzkV1.LigeroHighMass125V7
import LfzkV1.TwoFieldV1Rows

/-!
# Query-order charges for the legacy Ligero transcript

The opening input names a complete response and determines its batching
prefix. The first observed input of the pair is determined before either
answer. At an unobserved opening the submitted response is fixed by the
adversary output. If both inputs are unobserved, that output fixes the pair
before either analytical lookup.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

namespace LfzkV1.LigeroOrder125

open Bcs.TotalOracle Merkle.RandomOracle Finset
open scoped Classical

variable {Q C Out P R S : Type}
variable [Fintype Q] [DecidableEq Q] [Fintype C] [Nonempty C]
variable [Fintype P] [Fintype R]
variable {N : ℕ}

noncomputable def indicator (p : Prop) : ℚ := if p then 1 else 0

private theorem indicator_nonneg (p : Prop) : 0 ≤ indicator p := by
  unfold indicator
  split_ifs <;> norm_num

private theorem sum_indicator_eq_card {A : Type} [Fintype A] (p : A → Prop)
    [DecidablePred p] :
    (∑ a : A, indicator (p a)) = ((univ.filter p).card : ℚ) := by
  simp only [card_filter, Nat.cast_sum]
  apply sum_congr rfl
  intro a _
  by_cases h : p a <;> simp [indicator, h]

/-- Observed batching inputs, whether or not their opening was queried. -/
noncomputable def batchCount (tree : Tree Q C Out N) (batch : P → Q) (H : Q → C) : ℚ :=
  ∑ p : P, indicator (batch p ∈ queried tree H)

/-- Observed openings which precede the corresponding batching input. -/
noncomputable def earlyCount (tree : Tree Q C Out N) (batch : P → Q) (opening : P → R → Q)
    (H : Q → C) : ℚ :=
  ∑ i : P × R, indicator (firstOfTwo tree H (batch i.1) (opening i.1 i.2) = .right)

/-- Observed openings after the corresponding batching input. -/
noncomputable def lateCount (tree : Tree Q C Out N) (batch : P → Q) (opening : P → R → Q)
    (H : Q → C) : ℚ :=
  ∑ i : P × R, indicator (firstOfTwo tree H (batch i.1) (opening i.1 i.2) = .left ∧
    opening i.1 i.2 ∈ queried tree H)

/-- One submitted opening can be absent from the original adversary run. -/
noncomputable def appendedCount (tree : Tree Q C Out N) (selected : Out → P × R)
    (opening : P → R → Q) (H : Q → C) : ℚ :=
  let i := selected (tree.run H).1
  indicator (opening i.1 i.2 ∉ queried tree H)

/-- Batching labels which occurred in the search. -/
theorem batchCount_eq (tree : Tree Q C Out N) (batch : P → Q) (H : Q → C) :
    batchCount tree batch H = ((univ.filter fun p => batch p ∈ queried tree H).card : ℚ) :=
  sum_indicator_eq_card _

/-- An observed opening is counted once, regardless of its position. -/
theorem openingCounts_eq (tree : Tree Q C Out N) (batch : P → Q)
    (opening : P → R → Q) (H : Q → C) :
    earlyCount tree batch opening H + lateCount tree batch opening H =
      ((univ.filter fun i : P × R => opening i.1 i.2 ∈ queried tree H).card : ℚ) := by
  classical
  have hsplit (i : P × R) :
      indicator (firstOfTwo tree H (batch i.1) (opening i.1 i.2) = .right) +
        indicator (firstOfTwo tree H (batch i.1) (opening i.1 i.2) = .left ∧
          opening i.1 i.2 ∈ queried tree H) =
      indicator (opening i.1 i.2 ∈ queried tree H) := by
    cases h : firstOfTwo tree H (batch i.1) (opening i.1 i.2) with
    | neither =>
      have hn : opening i.1 i.2 ∉ queried tree H := fun hm =>
        firstOfTwo_ne_neither_of_right_mem tree H _ _ hm h
      simp [indicator, hn]
    | left => simp [indicator]
    | right => simp [indicator, firstOfTwo_right_mem tree H _ _ h]
  unfold earlyCount lateCount
  rw [← sum_add_distrib]
  simp_rw [hsplit]
  exact sum_indicator_eq_card _

private theorem observed_counts_eq (tree : Tree Q C Out N) (batch : P → Q)
    (opening : P → R → Q) (H : Q → C) :
    batchCount tree batch H + earlyCount tree batch opening H + lateCount tree batch opening H =
    (((univ.filter fun p => batch p ∈ queried tree H).card +
      (univ.filter fun i : P × R => opening i.1 i.2 ∈ queried tree H).card : ℕ) : ℚ) := by
  rw [add_assoc, batchCount_eq, openingCounts_eq, Nat.cast_add]

/-- Domain separation and injective encodings make all three observed roles
share the original adversary query budget. -/
theorem observed_counts_le (tree : Tree Q C Out N) (batch : P → Q) (opening : P → R → Q)
    (hb : Function.Injective batch)
    (ho : Function.Injective (fun i : P × R => opening i.1 i.2))
    (hne : ∀ p q r, batch p ≠ opening q r) (H : Q → C) :
    batchCount tree batch H + earlyCount tree batch opening H + lateCount tree batch opening H ≤ N := by
  rw [observed_counts_eq]
  exact_mod_cast queried_role_count_le tree batch opening hb ho hne H

/-- Additional observed query roles use the same budget when their concrete
inputs are outside the batching and opening namespaces. -/
theorem observed_counts_with_other_le
    (tree : Tree Q C Out N) (batch : P → Q) (opening : P → R → Q)
    (hb : Function.Injective batch)
    (ho : Function.Injective (fun i : P × R => opening i.1 i.2))
    (hne : ∀ p q r, batch p ≠ opening q r) (H : Q → C)
    (other : Finset Q) (hother : other ⊆ (queried tree H).toFinset)
    (hbatch : ∀ p, batch p ∉ other) (hopen : ∀ p u, opening p u ∉ other) :
    batchCount tree batch H + earlyCount tree batch opening H + lateCount tree batch opening H +
      other.card ≤ N := by
  classical
  let B := univ.filter fun p => batch p ∈ queried tree H
  let O := univ.filter fun i : P × R => opening i.1 i.2 ∈ queried tree H
  let seenBatch := B.image batch
  let seenOpen := O.image fun i => opening i.1 i.2
  have hbCard : seenBatch.card = B.card := card_image_of_injective B hb
  have hoCard : seenOpen.card = O.card := card_image_of_injective O ho
  have hd : Disjoint seenBatch seenOpen := by
    apply disjoint_left.mpr
    intro q hqb hqo
    obtain ⟨p, _, hp⟩ := mem_image.mp hqb
    obtain ⟨⟨p', r⟩, _, hpr⟩ := mem_image.mp hqo
    exact hne p p' r (hp.trans hpr.symm)
  have hdo : Disjoint (seenBatch ∪ seenOpen) other := by
    apply disjoint_left.mpr
    intro q hq hqOther
    rcases mem_union.mp hq with hb' | ho'
    · obtain ⟨p, _, rfl⟩ := mem_image.mp hb'
      exact hbatch p hqOther
    · obtain ⟨⟨p, r⟩, _, rfl⟩ := mem_image.mp ho'
      exact hopen p r hqOther
  have hsub : (seenBatch ∪ seenOpen) ∪ other ⊆ (queried tree H).toFinset := by
    intro q hq
    rcases mem_union.mp hq with hq | hq
    · rcases mem_union.mp hq with hb' | ho'
      · obtain ⟨p, hp, rfl⟩ := mem_image.mp hb'
        exact List.mem_toFinset.mpr (mem_filter.mp hp).2
      · obtain ⟨⟨p, r⟩, hpr, rfl⟩ := mem_image.mp ho'
        exact List.mem_toFinset.mpr (mem_filter.mp hpr).2
    · exact hother hq
  have hcount : B.card + O.card + other.card ≤ N := by
    rw [← hbCard, ← hoCard, ← card_union_of_disjoint hd, ← card_union_of_disjoint hdo]
    exact (card_le_card hsub).trans ((List.toFinset_card_le _).trans (queried_length_le tree H))
  rw [observed_counts_eq]
  exact_mod_cast hcount

theorem appended_count_le (tree : Tree Q C Out N) (selected : Out → P × R)
    (opening : P → R → Q) (H : Q → C) :
    appendedCount tree selected opening H ≤ 1 := by
  dsimp only [appendedCount, indicator]
  split_ifs <;> norm_num

private theorem neither_absent (tree : Tree Q C Out N) (H : Q → C) (x y : Q)
    (h : firstOfTwo tree H x y = .neither) :
    x ∉ queried tree H ∧ y ∉ queried tree H := by
  induction tree with
  | done _ => simp [queried]
  | query q next ih =>
    rw [queried_query]
    by_cases hx : q = x
    · simp [firstOfTwo, hx] at h
    by_cases hy : q = y
    · simp only [firstOfTwo, if_neg hx, if_pos hy] at h
      cases h
    have hh : firstOfTwo (next (H q)) H x y = .neither :=
      by simpa [firstOfTwo, hx, hy] using h
    have hnot := ih (H q) hh
    simp [Ne.symm hx, Ne.symm hy, hnot.1, hnot.2]

private theorem sum_at_pair_eq (x y : Q) (hne : x ≠ y)
    (f : (Q → C) → C → C → ℚ)
    (hoff : ∀ H H', (∀ q, q ≠ x → q ≠ y → H q = H' q) → ∀ a b, f H a b = f H' a b) :
    (∑ H : Q → C, f H (H x) (H y)) =
      (∑ H : Q → C, ∑ a : C, ∑ b : C, f H a b) / (Fintype.card C : ℚ) ^ 2 := by
  have hq : (0 : ℚ) < Fintype.card C := by exact_mod_cast Fintype.card_pos (α := C)
  have hx := sum_coord_mul_rat x (fun H a => f H a (H y)) (by
    intro H H' h a
    rw [h y hne.symm]
    exact hoff H H' (fun z hz _ => h z hz) a (H' y))
  have hy (a : C) := sum_coord_mul_rat y (fun H b => f H a b) (by
    intro H H' h b
    exact hoff H H' (fun z _ hz => h z hz) a b)
  apply (eq_div_iff (pow_ne_zero _ hq.ne')).mpr
  calc
    _ = ((∑ H : Q → C, f H (H x) (H y)) * Fintype.card C) * Fintype.card C := by ring
    _ = (∑ H : Q → C, ∑ a : C, f H a (H y)) * Fintype.card C := by rw [hx]
    _ = ∑ a : C, (∑ H : Q → C, f H a (H y)) * Fintype.card C := by rw [sum_comm, sum_mul]
    _ = ∑ a : C, ∑ H : Q → C, ∑ b : C, f H a b := by simp only [hy]
    _ = _ := sum_comm

private theorem sum_at_pair_le {I : Type} [Fintype I] (x y : I → Q)
    (hne : ∀ i, x i ≠ y i) (f : I → (Q → C) → C → C → ℚ)
    (hoff : ∀ i H H', (∀ q, q ≠ x i → q ≠ y i → H q = H' q) →
      ∀ a b, f i H a b = f i H' a b)
    (budget : (Q → C) → ℚ)
    (hlocal : ∀ H, ∑ i : I, ∑ a : C, ∑ b : C, f i H a b ≤
      (Fintype.card C : ℚ) ^ 2 * budget H) :
    (∑ H : Q → C, ∑ i : I, f i H (H (x i)) (H (y i))) ≤ ∑ H : Q → C, budget H := by
  have hq : (0 : ℚ) < Fintype.card C := by exact_mod_cast Fintype.card_pos (α := C)
  rw [sum_comm]
  simp_rw [sum_at_pair_eq _ _ (hne _) _ (hoff _), div_eq_mul_inv, ← sum_mul]
  rw [sum_comm]
  change (∑ H : Q → C, ∑ i : I, ∑ a : C, ∑ b : C, f i H a b) *
      ((Fintype.card C : ℚ) ^ 2)⁻¹ ≤ _
  rw [← div_eq_mul_inv, div_le_iff₀ (pow_pos hq _), sum_mul]
  exact sum_le_sum fun H _ => by simpa only [mul_comm] using hlocal H

private theorem sum_at_opening_le {I : Type} [Fintype I] (y : I → Q)
    (f : I → (Q → C) → C → ℚ)
    (hoff : ∀ i H H', AgreeOff (y i) H H' → ∀ b, f i H b = f i H' b)
    (budget : (Q → C) → ℚ) (hlocal : ∀ H, ∑ i : I, ∑ b : C, f i H b ≤
      (Fintype.card C : ℚ) * budget H) :
    (∑ H : Q → C, ∑ i : I, f i H (H (y i))) ≤ ∑ H : Q → C, budget H := by
  have hq : (0 : ℚ) < Fintype.card C := by exact_mod_cast Fintype.card_pos (α := C)
  apply le_of_mul_le_mul_right ?_ hq
  rw [sum_comm, sum_mul]
  simp_rw [sum_coord_mul_rat _ _ (hoff _)]
  rw [sum_comm, sum_mul]
  exact sum_le_sum fun H _ => by simpa only [mul_comm] using hlocal H

/-- Count the event that the submitted response is low-agreement or bad
high-agreement and passes its opening. The high batch, early opening, late
opening, and appended opening charges retain their actual counts. The
analytical lookups may evaluate both submitted inputs without counting the
same terminal event twice. -/
theorem ordered_ligero_charge_le
    (tree : Tree Q C Out N) (selected : Out → P × R)
    (batch : P → Q) (opening : P → R → Q)
    (hne : ∀ p r, batch p ≠ opening p r)
    (state : P → (Q → C) → S)
    (hoff : ∀ p r H H', (∀ q, q ≠ batch p → q ≠ opening p r → H q = H' q) →
      state p H = state p H')
    (badHigh low : S → P → R → C → C → Prop)
    (β α η : ℚ) (hae : α ≤ η)
    (hhigh : ∀ s p, ∑ r : R, ∑ a : C, ∑ b : C, indicator (badHigh s p r a b) ≤
      (Fintype.card C : ℚ)^2 * β)
    (hlow : ∀ s p r a, ∑ b : C, indicator (low s p r a b) ≤ Fintype.card C * α)
    (hearly : ∀ s p r, ∑ a : C, ∑ b : C, indicator (low s p r a b ∨ badHigh s p r a b) ≤
      (Fintype.card C : ℚ)^2 * η) :
    (∑ H : Q → C,
      let i := selected (tree.run H).1
      indicator (low (state i.1 H) i.1 i.2 (H (batch i.1)) (H (opening i.1 i.2)) ∨
        badHigh (state i.1 H) i.1 i.2 (H (batch i.1)) (H (opening i.1 i.2)))) ≤
      ∑ H : Q → C, (β * batchCount tree batch H + η * earlyCount tree batch opening H +
        α * lateCount tree batch opening H + η * appendedCount tree selected opening H) := by
  classical
  let chosen (H : Q → C) := selected (tree.run H).1
  let x (i : P × R) := batch i.1
  let y (i : P × R) := opening i.1 i.2
  let order (i : P × R) (H : Q → C) := firstOfTwo tree H (x i) (y i)
  let early (i : P × R) (H : Q → C) :=
    order i H = .right ∨ (order i H = .neither ∧ chosen H = i)
  let late (i : P × R) (H : Q → C) :=
    order i H = .left ∧ (y i ∈ queried tree H ∨ chosen H = i)
  let highWt (i : P × R) (H : Q → C) (a b : C) :=
    indicator (order i H = .left ∧ badHigh (state i.1 H) i.1 i.2 a b)
  let earlyWt (i : P × R) (H : Q → C) (a b : C) :=
    indicator (early i H ∧ (low (state i.1 H) i.1 i.2 a b ∨ badHigh (state i.1 H) i.1 i.2 a b))
  let lateWt (i : P × R) (H : Q → C) (b : C) :=
    indicator (late i H ∧ low (state i.1 H) i.1 i.2 (H (x i)) b)
  let addEarly (H : Q → C) := indicator (order (chosen H) H = .neither)
  let addLate (H : Q → C) := indicator (order (chosen H) H = .left ∧ y (chosen H) ∉ queried tree H)
  have hne' (i : P × R) : x i ≠ y i := hne i.1 i.2
  have horder (i : P × R) (H H' : Q → C) (h : ∀ q, q ≠ x i → q ≠ y i → H q = H' q) :
      order i H = order i H' := firstOfTwo_congr_off tree H H' (x i) (y i) h
  have hglobal (i : P × R) (H H' : Q → C) (h : ∀ q, q ≠ x i → q ≠ y i → H q = H' q)
      (hn : order i H = .neither) : chosen H = chosen H' := by
    obtain ⟨hx, hy⟩ := neither_absent tree H (x i) (y i) hn
    have hr : tree.run H' = tree.run H := by
      apply Tree.run_congr_on_trace tree H H'
      intro entry hm
      have hsame := h entry.1
        (fun heq => hx (List.mem_map.mpr ⟨entry, hm, heq⟩))
        (fun heq => hy (List.mem_map.mpr ⟨entry, hm, heq⟩))
      exact ((Tree.trace_sound tree H entry hm).trans hsame).symm
    exact congrArg (fun res => selected res.1) hr.symm
  have hearlyOff (i : P × R) (H H' : Q → C) (h : ∀ q, q ≠ x i → q ≠ y i → H q = H' q) :
      early i H ↔ early i H' := by
    have hor := horder i H H' h
    by_cases hn : order i H = .neither
    · simp [early, ← hor, hn, hglobal i H H' h hn]
    · simp [early, ← hor, hn]
  have hlateOff (i : P × R) (H H' : Q → C) (h : AgreeOff (y i) H H') :
      late i H ↔ late i H' := by
    have hor := horder i H H' (fun z _ hz => h z hz)
    by_cases hm : y i ∈ queried tree H
    · simp [late, ← hor, hm, (mem_queried_iff tree (y i) h).mp hm]
    · have hr := run_eq_of_not_mem tree (y i) h hm
      have hc : chosen H = chosen H' := congrArg (fun res => selected res.1) hr.symm
      simp [late, ← hor, hm, (mem_queried_iff tree (y i) h).not.mp hm, hc]
  have hH : (∑ H : Q → C, ∑ i : P × R, highWt i H (H (x i)) (H (y i))) ≤
      ∑ H : Q → C, β * batchCount tree batch H := by
    apply sum_at_pair_le x y hne' highWt
      (fun i H H' h a b => by simp only [highWt, horder i H H' h, hoff i.1 i.2 H H' h])
    intro H
    rw [Fintype.sum_prod_type]
    unfold batchCount
    simp only [mul_sum]
    apply sum_le_sum
    intro p _
    by_cases hm : batch p ∈ queried tree H
    · simp only [indicator, hm, if_true, mul_one]
      calc
        _ ≤ ∑ r : R, ∑ a : C, ∑ b : C,
            indicator (badHigh (state p H) p r a b) := by
          apply sum_le_sum
          intro r _
          by_cases ho : order (p, r) H = .left
          · simp [highWt, ho]
          · simpa [highWt, ho, indicator] using
              (sum_nonneg fun a _ => sum_nonneg fun b _ =>
                indicator_nonneg (badHigh (state p H) p r a b))
        _ ≤ _ := hhigh (state p H) p
    · have hn (r : R) : order (p, r) H ≠ .left := fun h =>
        hm (firstOfTwo_left_mem tree H _ _ h)
      simp [highWt, hn, indicator, hm]
  have hEsplit (H : Q → C) :
      (∑ i : P × R, indicator (early i H)) = earlyCount tree batch opening H + addEarly H := by
    have hdisj (i : P × R) :
        indicator (early i H) = indicator (order i H = .right) +
        indicator (order (chosen H) H = .neither ∧ i = chosen H) := by
      by_cases h : i = chosen H
      · subst i
        cases ho : order (chosen H) H <;> simp [early, indicator, ho]
      · simp [early, indicator, h, Ne.symm h]
    simp_rw [hdisj, sum_add_distrib]
    change _ = (∑ i : P × R, indicator (order i H = .right)) + _
    congr 1
    by_cases hn : order (chosen H) H = .neither
    · simp [addEarly, indicator, hn]
    · simp [addEarly, indicator, hn]
  have hLsplit (H : Q → C) :
      (∑ i : P × R, indicator (late i H)) = lateCount tree batch opening H + addLate H := by
    have hdisj (i : P × R) :
        indicator (late i H) = indicator (order i H = .left ∧ y i ∈ queried tree H) +
        indicator ((order (chosen H) H = .left ∧ y (chosen H) ∉ queried tree H) ∧ i = chosen H) := by
      by_cases h : i = chosen H
      · subst i
        by_cases hleft : order (chosen H) H = .left <;>
          by_cases hmem : y (chosen H) ∈ queried tree H <;> simp [late, indicator, hleft, hmem]
      · simp [late, indicator, h, Ne.symm h]
    simp_rw [hdisj, sum_add_distrib]
    change _ = (∑ i : P × R, indicator (order i H = .left ∧ y i ∈ queried tree H)) + _
    congr 1
    by_cases hn : order (chosen H) H = .left ∧ y (chosen H) ∉ queried tree H
    · simp [addLate, indicator, hn]
    · simp [addLate, indicator, show ¬(order (chosen H) H = .left ∧ y (chosen H) ∉ queried tree H) from hn]
  have hE : (∑ H : Q → C, ∑ i : P × R, earlyWt i H (H (x i)) (H (y i))) ≤
      ∑ H : Q → C, η * (earlyCount tree batch opening H + addEarly H) := by
    apply sum_at_pair_le x y hne' earlyWt (fun i H H' h a b => by
      simp only [earlyWt, hearlyOff i H H' h, hoff i.1 i.2 H H' h])
    intro H
    rw [← hEsplit, mul_sum, mul_sum]
    apply sum_le_sum
    intro i _
    by_cases h : early i H
    · have htrue : indicator True = 1 := by simp [indicator]
      simpa only [earlyWt, h, true_and, if_true, htrue, mul_one, mul_assoc] using
        hearly (state i.1 H) i.1 i.2
    · simp [earlyWt, indicator, h]
  have hL : (∑ H : Q → C, ∑ i : P × R, lateWt i H (H (y i))) ≤
      ∑ H : Q → C, α * (lateCount tree batch opening H + addLate H) := by
    apply sum_at_opening_le y lateWt (fun i H H' h b => by
      simp only [lateWt, hlateOff i H H' h, hoff i.1 i.2 H H' (fun z _ hz => h z hz),
        h (x i) (hne' i)])
    intro H
    rw [← hLsplit, mul_sum, mul_sum]
    apply sum_le_sum
    intro i _
    by_cases h : late i H
    · simpa [lateWt, indicator, h, mul_assoc] using hlow (state i.1 H) i.1 i.2 (H (x i))
    · simp [lateWt, indicator, h]
  have happ (H : Q → C) : addEarly H + addLate H = appendedCount tree selected opening H := by
    change _ = indicator (y (chosen H) ∉ queried tree H)
    cases ho : order (chosen H) H with
    | neither =>
      have hn := (neither_absent tree H (x (chosen H)) (y (chosen H)) ho).2
      simp [addEarly, addLate, indicator, ho, hn]
    | left => simp [addEarly, addLate, indicator, ho]
    | right =>
      have hm := firstOfTwo_right_mem tree H (x (chosen H)) (y (chosen H)) ho
      simp [addEarly, addLate, indicator, ho, hm]
  have hcover (H : Q → C) :
      let i := chosen H
      indicator (low (state i.1 H) i.1 i.2 (H (x i)) (H (y i)) ∨
        badHigh (state i.1 H) i.1 i.2 (H (x i)) (H (y i))) ≤
      ∑ i : P × R, (highWt i H (H (x i)) (H (y i)) + earlyWt i H (H (x i)) (H (y i)) +
        lateWt i H (H (y i))) := by
    dsimp only
    let i := chosen H
    have hnonneg (j : P × R) :
        0 ≤ highWt j H (H (x j)) (H (y j)) + earlyWt j H (H (x j)) (H (y j)) +
          lateWt j H (H (y j)) := add_nonneg
          (add_nonneg (indicator_nonneg _) (indicator_nonneg _)) (indicator_nonneg _)
    refine le_trans ?_ (single_le_sum (fun j _ => hnonneg j) (mem_univ i))
    change indicator (low (state i.1 H) i.1 i.2 (H (x i)) (H (y i)) ∨
        badHigh (state i.1 H) i.1 i.2 (H (x i)) (H (y i))) ≤
      highWt i H (H (x i)) (H (y i)) + earlyWt i H (H (x i)) (H (y i)) + lateWt i H (H (y i))
    have hchosen : chosen H = i := rfl
    cases ho : order i H with
    | left =>
      by_cases h : badHigh (state i.1 H) i.1 i.2 (H (x i)) (H (y i))
      all_goals simp [highWt, earlyWt, lateWt, early, late, indicator, ho, hchosen, h]
      all_goals split_ifs <;> norm_num
    | right =>
      simp [highWt, earlyWt, lateWt, early, late, indicator, ho]
      split_ifs <;> norm_num
    | neither =>
      simp [highWt, earlyWt, lateWt, early, late, indicator, ho, hchosen]
      split_ifs <;> norm_num
  refine (sum_le_sum fun H _ => hcover H).trans ?_
  simp only [sum_add_distrib]
  refine (add_le_add (add_le_add hH hE) hL).trans ?_
  simp only [← sum_add_distrib]
  apply sum_le_sum
  intro H _
  rw [← happ H]
  have ha := mul_le_mul_of_nonneg_right hae (indicator_nonneg (order (chosen H) H = .left ∧
    y (chosen H) ∉ queried tree H))
  change α * addLate H ≤ η * addLate H at ha
  linarith only [ha]


section Decode

open LfzkV1.TwoFieldV1Rows

variable {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

private theorem decode_one (d : ExactDecoder C B) (f : B → ℚ) (hpos : ∀ b, 0 ≤ f b)
    (ε : ℚ) (he : 0 ≤ ε) (h : ∑ b, f b ≤ Fintype.card B * ε) :
    ∑ c, f (d.decode c) ≤ Fintype.card C * ε := by
  have hcap : (d.k : ℚ) * Fintype.card B ≤ Fintype.card C := by exact_mod_cast d.hexact
  calc
    _ ≤ d.k * ∑ b, f b := ZkPotentialBalance.decoded_weight_sum_le d.decode f hpos d.k d.hbal
    _ ≤ d.k * (Fintype.card B * ε) := mul_le_mul_of_nonneg_left h (by positivity)
    _ ≤ _ := by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hcap he

private theorem decode_pair (d : ExactDecoder C A) (e : ExactDecoder C B)
    (f : A → B → ℚ) (hpos : ∀ a b, 0 ≤ f a b)
    (ε : ℚ) (he : 0 ≤ ε) (h : ∑ a, ∑ b, f a b ≤ (Fintype.card A : ℚ) * Fintype.card B * ε) :
    ∑ c, ∑ t, f (d.decode c) (e.decode t) ≤ (Fintype.card C : ℚ)^2 * ε := by
  have hd : (d.k : ℚ) * Fintype.card A ≤ Fintype.card C := by exact_mod_cast d.hexact
  have he' : (e.k : ℚ) * Fintype.card B ≤ Fintype.card C := by exact_mod_cast e.hexact
  have hcap := mul_le_mul hd he' (by positivity : 0 ≤ (e.k : ℚ) * Fintype.card B)
    (Nat.cast_nonneg (α := ℚ) _)
  calc
    _ ≤ (d.k * e.k : ℚ) * ∑ a, ∑ b, f a b :=
      ZkPotentialBalance.decoded_pair_weight_sum_le d.decode e.decode f hpos d.k e.k d.hbal e.hbal
    _ ≤ (d.k * e.k : ℚ) * ((Fintype.card A : ℚ) * Fintype.card B * ε) :=
      mul_le_mul_of_nonneg_left h (by positivity)
    _ = ((d.k : ℚ) * Fintype.card A * ((e.k : ℚ) * Fintype.card B)) * ε := by ring
    _ ≤ _ := by rw [pow_two]; exact mul_le_mul_of_nonneg_right hcap he

end Decode

section V7

open LigeroFamily CodingTheory LfzkV1.LigeroHighMass125 LfzkV1.TwoFieldV1Rows

variable {F Equations : Type} [Field F] [Fintype F] [DecidableEq F]
variable [Fintype Equations] [DecidableEq Equations]
variable {w nw nq : ℕ} [Nonempty (SchemeTestedRow NoMask nw nq 1)]
variable (i : Fin 4)

private abbrev cert (i : Fin 4) := (OpeningGeometry125.result i).certificate
private abbrev v7n (i : Fin 4) := (cert i).n
private abbrev v7r (i : Fin 4) := (cert i).openings
local notation "Challenge" => SchemeChallenge F NoMask nw nq 1 Equations
local notation "Openings" => QuerySet (v7n i) (v7r i)
local notation "Reply" => Response F (v7r i) w (v7n i) 1
local notation "Code" => MultiplicativeCode F (v7r i) w (v7n i)
local notation "Context" => Ligero.V1.Oracle F nw nq (v7n i) 1 × ConstraintSystem F nw nq w Equations

/-- An accepted complete response in the bad-high family. -/
def badHighEvent {n r : ℕ} (code : MultiplicativeCode F r w n)
    (s : Ligero.V1.Oracle F nw nq n 1 × ConstraintSystem F nw nq w Equations)
    (u : Response F r w n 1) (ch : Challenge) (q : QuerySet n r) : Prop :=
  u ∈ badHighResponses (C := code) s.1 s.2 (highCutoff i) (cert i).e (cert i).g ch ∧
    SchemeVerifier.Accepts code Ligero.V1.scheme s.2 ch u q (openSchemeOracle s.1 q)

/-- An accepted response whose agreement is below the high cutoff. -/
def lowEvent {n r : ℕ} (code : MultiplicativeCode F r w n)
    (s : Ligero.V1.Oracle F nw nq n 1 × ConstraintSystem F nw nq w Equations)
    (u : Response F r w n 1) (ch : Challenge) (q : QuerySet n r) : Prop :=
  (columns (C := code) s.1 s.2 ch u).card < highCutoff i ∧
    SchemeVerifier.Accepts code Ligero.V1.scheme s.2 ch u q (openSchemeOracle s.1 q)

private theorem count_openings (code : Code) (s : Context) (u : Reply) (ch : Challenge)
    (p : Prop) (hr : (cert i).openings ≤ (cert i).n) :
    (∑ q : Openings, indicator (p ∧
      SchemeVerifier.Accepts code Ligero.V1.scheme s.2 ch u q (openSchemeOracle s.1 q))) =
    Fintype.card Openings * (if p then openingRate (C := code) s.1 s.2 ch u else 0) := by
  classical
  by_cases h : p
  · simp only [h, true_and, if_true]
    rw [sum_indicator_eq_card, QuerySet.fintype_card]
    unfold openingRate
    have hn : ((cert i).n.choose (cert i).openings : ℚ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos hr).ne'
    field_simp
    congr 2
  · simp [h, indicator]

private theorem numeric_terminal_counts (code : Code) (s : Context)
    (hfield : Fintype.card F = (cert i).fieldSize) (hk : code.k = (cert i).k)
    (hmin : HasMinimumDistanceAtLeast code.baseCode (cert i).d)
    (hRS : JBAgreement.RSPresentation (cert i).n (cert i).k code.baseCode) :
    (∑ u : Reply, ∑ ch : Challenge, ∑ q : Openings, indicator (badHighEvent i code s u ch q)) ≤
        (Fintype.card Challenge : ℚ) * Fintype.card Openings * (319 / (100 * 2 ^ 128)) ∧
    (∀ u ch, ∑ q : Openings, indicator (lowEvent i code s u ch q) ≤
        (Fintype.card Openings : ℚ) * (1593 / (500 * 2 ^ 128))) ∧
    (∀ u, ∑ ch : Challenge, ∑ q : Openings,
      indicator (lowEvent i code s u ch q ∨ badHighEvent i code s u ch q) ≤
        (Fintype.card Challenge : ℚ) * Fintype.card Openings * (3188 / (500 * 2 ^ 128))) := by
  classical
  letI : Nonempty Challenge := ⟨fun _ => ⟨0, 0, 0⟩⟩
  have hc : (0 : ℚ) < Fintype.card Challenge := by exact_mod_cast Fintype.card_pos
  have hr : (cert i).openings ≤ (cert i).n := by fin_cases i <;> decide +kernel
  have hcount (u : Reply) (ch : Challenge) := count_openings i code s u ch
  refine ⟨?_, ?_, ?_⟩
  · unfold badHighEvent
    simp_rw [count_openings i code s _ _ _ hr]
    rw [sum_comm]
    simp only [← mul_sum]
    have hsum (ch : Challenge) :
        let replies := badHighResponses (C := code) s.1 s.2 (highCutoff i) (cert i).e (cert i).g ch
        (∑ u : Reply, @ite ℚ (u ∈ replies) (Classical.propDecidable _)
          (openingRate (C := code) s.1 s.2 ch u) 0) =
          ∑ u ∈ replies, openingRate (C := code) s.1 s.2 ch u := by
      let replies := badHighResponses (C := code) s.1 s.2 (highCutoff i) (cert i).e (cert i).g ch
      let wt (u : Reply) := @ite ℚ (u ∈ replies) (Classical.propDecidable _)
        (openingRate (C := code) s.1 s.2 ch u) 0
      change (∑ u : Reply, wt u) = _
      calc
        _ = ∑ u ∈ replies, wt u :=
          (sum_subset (subset_univ replies) (fun u _ hu => by simp [wt, hu])).symm
        _ = _ := sum_congr rfl (fun u hu => by simp [wt, hu])
    simp_rw [hsum]
    have hh := (div_le_iff₀ hc).mp (v7_badHigh_opening_mass_le i code s.1 s.2 hfield hk hmin hRS)
    calc
      _ ≤ (Fintype.card Openings : ℚ) *
          ((319 / (100 * (2 ^ 128)) : ℚ) * Fintype.card Challenge) :=
        mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg _)
      _ = _ := by ring
  · intro u ch
    unfold lowEvent
    rw [hcount u ch _ hr]
    split_ifs with hl
    · exact mul_le_mul_of_nonneg_left
        ((fixed_response_opening_density (C := code) s.1 s.2 ch u).trans (v7_lowOpening_le i hl))
        (by positivity)
    · rw [mul_zero]
      positivity
  · intro u
    unfold lowEvent badHighEvent
    simp_rw [← or_and_right, count_openings i code s _ _ _ hr, ← mul_sum]
    have hh := (div_le_iff₀ hc).mp
      (v7_fixed_bad_or_low_opening_le i code s.1 s.2 hfield hk hmin hRS u)
    calc
      _ ≤ (Fintype.card Openings : ℚ) *
          ((3188 / (500 * (2 ^ 128)) : ℚ) * Fintype.card Challenge) := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        convert hh using 1
        apply sum_congr rfl
        intro ch _
        by_cases hp : (columns (C := code) s.1 s.2 ch u).card < highCutoff i ∨
          u ∈ badHighResponses (C := code) s.1 s.2 (highCutoff i) (cert i).e (cert i).g ch
        all_goals simp only [hp, if_true, if_false]
      _ = _ := by ring

set_option maxHeartbeats 1000000 in
/-- Exact decoders preserve the three v7 local charges. The statement and
committed oracle come from the pair's prefix state, separate from the two
fresh ideal answers. The wire responses embed in the full response space,
whose total bad-high mass bounds the image of the wire encoder. -/
theorem v7_ordered_charge_le {Wire : Type} [Fintype Wire] (code : Code)
    (toResponse : Wire ↪ Reply)
    (tree : Tree Q C Out N) (selected : Out → P × Wire)
    (batch : P → Q) (opening : P → Wire → Q)
    (hne : ∀ p u, batch p ≠ opening p u)
    (context : P → (Q → C) → Context)
    (hoff : ∀ p u H H', (∀ q, q ≠ batch p → q ≠ opening p u → H q = H' q) →
      context p H = context p H')
    (decodeBatch : P → ExactDecoder C Challenge) (decodeOpen : P → ExactDecoder C Openings)
    (hfield : Fintype.card F = (cert i).fieldSize) (hk : code.k = (cert i).k)
    (hmin : HasMinimumDistanceAtLeast code.baseCode (cert i).d)
    (hRS : JBAgreement.RSPresentation (cert i).n (cert i).k code.baseCode) :
    (∑ H : Q → C,
      let j := selected (tree.run H).1
      let a := (decodeBatch j.1).decode (H (batch j.1))
      let b := (decodeOpen j.1).decode (H (opening j.1 j.2))
      indicator (lowEvent i code (context j.1 H) (toResponse j.2) a b ∨
        badHighEvent i code (context j.1 H) (toResponse j.2) a b)) ≤
      ∑ H : Q → C, (319 / (100 * 2 ^ 128) * batchCount tree batch H +
        3188 / (500 * 2 ^ 128) * earlyCount tree batch opening H +
        1593 / (500 * 2 ^ 128) * lateCount tree batch opening H +
        3188 / (500 * 2 ^ 128) * appendedCount tree selected opening H) := by
  let high (s : Context) (p : P) (u : Wire) (a b : C) :=
    badHighEvent i code s (toResponse u) ((decodeBatch p).decode a) ((decodeOpen p).decode b)
  let low (s : Context) (p : P) (u : Wire) (a b : C) :=
    lowEvent i code s (toResponse u) ((decodeBatch p).decode a) ((decodeOpen p).decode b)
  apply ordered_ligero_charge_le tree selected batch opening hne context hoff high low
    (319 / (100 * 2 ^ 128)) (1593 / (500 * 2 ^ 128)) (3188 / (500 * 2 ^ 128)) (by norm_num)
  · intro s p
    have h : (∑ u : Wire, ∑ ch : Challenge, ∑ q : Openings,
        indicator (badHighEvent i code s (toResponse u) ch q)) ≤
        (Fintype.card Challenge : ℚ) * Fintype.card Openings * (319 / (100 * 2 ^ 128)) := by
      let mass (u : Reply) := ∑ ch : Challenge, ∑ q : Openings,
        indicator (badHighEvent i code s u ch q)
      change (∑ u : Wire, mass (toResponse u)) ≤ _
      calc
        _ = ∑ u ∈ (univ : Finset Wire).map toResponse, mass u := (sum_map _ _ _).symm
        _ ≤ ∑ u : Reply, mass u := sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun _ _ _ =>
          sum_nonneg fun _ _ => sum_nonneg fun _ _ => indicator_nonneg _)
        _ ≤ _ := (numeric_terminal_counts i code s hfield hk hmin hRS).1
    rw [sum_comm] at h
    have h' : ∑ ch : Challenge, ∑ q : Openings, ∑ u : Wire,
        indicator (badHighEvent i code s (toResponse u) ch q) ≤
        (Fintype.card Challenge : ℚ) * Fintype.card Openings * (319 / (100 * 2 ^ 128)) := by
      simpa only [sum_comm (s := (univ : Finset Openings)) (t := (univ : Finset Wire))] using h
    rw [sum_comm]
    change (∑ a : C, ∑ u : Wire, ∑ b : C,
      indicator (badHighEvent i code s (toResponse u) ((decodeBatch p).decode a) ((decodeOpen p).decode b))) ≤ _
    simp_rw [sum_comm (s := (univ : Finset Wire)) (t := (univ : Finset C))]
    exact decode_pair (decodeBatch p) (decodeOpen p) (fun a b => ∑ u : Wire,
      indicator (badHighEvent i code s (toResponse u) a b))
      (fun _ _ => sum_nonneg fun _ _ => indicator_nonneg _) _ (by positivity) h'
  · intro s p u a
    have h := (numeric_terminal_counts i code s hfield hk hmin hRS).2.1 (toResponse u) ((decodeBatch p).decode a)
    exact decode_one (decodeOpen p)
      (fun q => indicator (lowEvent i code s (toResponse u) ((decodeBatch p).decode a) q))
      (fun _ => indicator_nonneg _) _ (by positivity) h
  · intro s p u
    have h := (numeric_terminal_counts i code s hfield hk hmin hRS).2.2 (toResponse u)
    exact decode_pair (decodeBatch p) (decodeOpen p)
      (fun a b => indicator (lowEvent i code s (toResponse u) a b ∨ badHighEvent i code s (toResponse u) a b))
      (fun _ _ => indicator_nonneg _) _ (by positivity) h

end V7

end LfzkV1.LigeroOrder125
