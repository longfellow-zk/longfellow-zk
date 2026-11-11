import Bcs.FirstPairLocalContext
import Bcs.FinalQuery
import Bcs.PotentialOracle
import Mathlib.Tactic.Positivity.Finset

/-!
# A shared query budget for parent and response roles

Single-answer response charges and two-answer first-pair charges retain their
actual query counts until the final inequality. Domain separation then lets
both roles share the adversary's one query budget.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Bcs.TotalOracle
open Finset Merkle.RandomOracle
open scoped Classical

variable {Q C J : Type} [Fintype Q] [DecidableEq Q] [Fintype C] [Nonempty C]
  [Fintype J]

omit [Nonempty C] in
private theorem single_weight_sum_le
    (point : J → Q) (weight : J → (Q → C) → C → ℚ)
    (hoff : ∀ i H H', AgreeOff (point i) H H' → ∀ c, weight i H c = weight i H' c)
    (budget : J → (Q → C) → ℚ)
    (hlocal : ∀ i H, ∑ c, weight i H c ≤ budget i H) :
    (Fintype.card C : ℚ) * (∑ H : Q → C, ∑ i, weight i H (H (point i))) ≤
      ∑ H : Q → C, ∑ i, budget i H := by
  calc
    _ = ∑ i, (∑ H : Q → C, weight i H (H (point i))) * Fintype.card C := by
      rw [sum_comm, mul_sum]
      apply sum_congr rfl
      intro i _
      ring
    _ = ∑ i, ∑ H : Q → C, ∑ c, weight i H c := by
      apply sum_congr rfl
      intro i _
      exact sum_coord_mul_rat (point i) (weight i) (hoff i)
    _ ≤ ∑ i, ∑ H : Q → C, budget i H :=
      sum_le_sum (fun i _ => sum_le_sum (fun H _ => hlocal i H))
    _ = _ := sum_comm

private theorem pair_weight_sum_le
    (first second : J → Q) (hneq : ∀ i, first i ≠ second i)
    (weight : J → (Q → C) → C → C → ℚ)
    (hoff : ∀ i H H', (∀ z, z ≠ first i → z ≠ second i → H z = H' z) →
      ∀ a b, weight i H a b = weight i H' a b)
    (budget : J → (Q → C) → ℚ)
    (hbudget : ∀ i H H', (∀ z, z ≠ first i → z ≠ second i → H z = H' z) →
      budget i H = budget i H')
    (hlocal : ∀ i H, ∑ a, ∑ b, weight i H a b ≤ budget i H) :
    (Fintype.card C : ℚ)^2 *
      (∑ H : Q → C, ∑ i, weight i H (H (first i)) (H (second i))) ≤
        ∑ H : Q → C, ∑ i, budget i H := by
  have hpair (i : J) : (Fintype.card C : ℚ)^2 *
      (∑ H : Q → C, weight i H (H (first i)) (H (second i))) ≤
        ∑ H : Q → C, budget i H := by
    let rep := fun off : AwayFromTwo (first i) (second i) → C =>
      (splitTwo (C := C) (first i) (second i) (hneq i)).symm
        (off, (Classical.choice inferInstance, Classical.choice inferInstance))
    have hrep (H : Q → C) : ∀ z, z ≠ first i → z ≠ second i →
        rep (fun z => H z.1) z = H z := by
      intro z hx hy
      simp [rep, splitTwo, hx, hy]
    have hw := sum_two_fresh_weight (first i) (second i) (hneq i)
      (fun off a b => weight i (rep off) a b)
    have hb := sum_two_fresh_weight (first i) (second i) (hneq i)
      (fun off _ _ => budget i (rep off))
    simp_rw [hoff i _ _ (hrep _)] at hw
    simp_rw [hbudget i _ _ (hrep _)] at hb
    rw [hw, hb]
    simp only [sum_const, card_univ, nsmul_eq_mul]
    have hsum : (∑ off : AwayFromTwo (first i) (second i) → C,
        ∑ a, ∑ b, weight i (rep off) a b) ≤ ∑ off, budget i (rep off) :=
      sum_le_sum (fun off _ => hlocal i (rep off))
    simpa only [mul_sum, pow_two, mul_assoc] using
      mul_le_mul_of_nonneg_left hsum (sq_nonneg (Fintype.card C : ℚ))
  rw [sum_comm, mul_sum]
  calc
    _ ≤ ∑ i, ∑ H : Q → C, budget i H := sum_le_sum (fun i _ => hpair i)
    _ = _ := sum_comm

omit [Fintype Q] [Fintype C] [Nonempty C] in
/-- The parent inputs and the response inputs occupy disjoint query roles. -/
theorem queried_role_count_le
    {Out Parent Response : Type} [Fintype Parent] [Fintype Response] {N : ℕ}
    (tree : Tree Q C Out N) (parent : Parent → Q) (child : Parent → Response → Q)
    (hparent : Function.Injective parent)
    (hchild : Function.Injective (fun i : Parent × Response => child i.1 i.2))
    (hdisjoint : ∀ p p' r, parent p ≠ child p' r) (H : Q → C) :
    (univ.filter fun p => parent p ∈ queried tree H).card +
      (univ.filter fun i : Parent × Response => child i.1 i.2 ∈ queried tree H).card ≤ N := by
  let P := univ.filter fun p => parent p ∈ queried tree H
  let R := univ.filter fun i : Parent × Response => child i.1 i.2 ∈ queried tree H
  have hp : (P.image parent).card = P.card := card_image_of_injOn (fun _ _ _ _ h => hparent h)
  have hr : (R.image (fun i => child i.1 i.2)).card = R.card :=
    card_image_of_injOn (fun _ _ _ _ h => hchild h)
  have hd : Disjoint (P.image parent) (R.image (fun i => child i.1 i.2)) := by
    apply disjoint_left.mpr
    intro z hz hz'
    obtain ⟨p,_,hpz⟩ := mem_image.mp hz
    obtain ⟨i,_,hiz⟩ := mem_image.mp hz'
    exact hdisjoint p i.1 i.2 (hpz.trans hiz.symm)
  have hs : P.image parent ∪ R.image (fun i => child i.1 i.2) ⊆
      (queried tree H).toFinset := by
    intro z hz
    rcases mem_union.mp hz with hz | hz
    · obtain ⟨p,hp,rfl⟩ := mem_image.mp hz
      exact List.mem_toFinset.mpr (mem_filter.mp hp).2
    · obtain ⟨i,hi,rfl⟩ := mem_image.mp hz
      exact List.mem_toFinset.mpr (mem_filter.mp hi).2
  change P.card+R.card ≤ N
  rw [← hp, ← hr, ← card_union_of_disjoint hd]
  exact (card_le_card hs).trans ((List.toFinset_card_le _).trans (queried_length_le tree H))

/-- Parent-first high responses, parent-first low responses, and child-first
complete responses share one query budget. The child-first branch uses the
ordinary response-uniform IOP bound. No response policy is assumed. -/
theorem tree_query_role_sum_le
    {Out Parent Response State : Type} [Fintype Parent] [Fintype Response]
    [Nonempty Response] {N : ℕ}
    (tree : Tree Q C Out N) (parent : Parent → Q) (child : Parent → Response → Q)
    (hparent : Function.Injective parent)
    (hchild : Function.Injective (fun i : Parent × Response => child i.1 i.2))
    (hdisjoint : ∀ p p' r, parent p ≠ child p' r)
    (state : Parent → (Q → C) → State)
    (hstateOff : ∀ p r H H', (∀ z, z ≠ parent p → z ≠ child p r → H z = H' z) →
      state p H = state p H')
    (event : State → Parent → Response → C → C → Prop)
    (bad : State → Parent → C → Prop)
    (high : State → Parent → Response → C → Prop)
    (epsilon mu beta : ℚ) (he : 0 ≤ epsilon)
    (hmb : mu+beta ≤ epsilon)
    (hiop : ∀ s p r, ∑ a : C, ∑ b : C,
      (if event s p r a b then (1 : ℚ) else 0) ≤ (Fintype.card C : ℚ)^2*epsilon)
    (hrank : ∀ s p, ∑ a : C, (if bad s p a then (1 : ℚ) else 0) ≤ Fintype.card C*mu)
    (hlow : ∀ s p r a, ∑ b : C,
      (if ¬bad s p a ∧ ¬high s p r a ∧ event s p r a b then (1 : ℚ) else 0) ≤
        Fintype.card C*epsilon)
    (hhigh : ∀ s p, ∑ r : Response, ∑ a : C, ∑ b : C,
      (if ¬bad s p a ∧ high s p r a ∧ event s p r a b then (1 : ℚ) else 0) ≤
        (Fintype.card C : ℚ)^2*beta) :
    let order := fun p r H => firstOfTwo tree H (parent p) (child p r)
    (∑ H : Q → C,
      ((∑ p : Parent, if parent p ∈ queried tree H ∧ bad (state p H) p (H (parent p))
        then (1 : ℚ) else 0) +
      ∑ i : Parent × Response,
        ((if order i.1 i.2 H = .right ∧ event (state i.1 H) i.1 i.2
            (H (parent i.1)) (H (child i.1 i.2)) then (1 : ℚ) else 0) +
         (if child i.1 i.2 ∈ queried tree H ∧ order i.1 i.2 H = .left ∧
            ¬bad (state i.1 H) i.1 (H (parent i.1)) ∧
            ¬high (state i.1 H) i.1 i.2 (H (parent i.1)) ∧
            event (state i.1 H) i.1 i.2 (H (parent i.1)) (H (child i.1 i.2))
          then (1 : ℚ) else 0) +
         (if order i.1 i.2 H = .left ∧ ¬bad (state i.1 H) i.1 (H (parent i.1)) ∧
            high (state i.1 H) i.1 i.2 (H (parent i.1)) ∧
            event (state i.1 H) i.1 i.2 (H (parent i.1)) (H (child i.1 i.2))
          then (1 : ℚ) else 0)))) ≤
      (N : ℚ)*epsilon*(Fintype.card C : ℚ)^Fintype.card Q := by
  classical
  let q : ℚ := Fintype.card C
  have hq : 0 < q := by dsimp [q]; exact_mod_cast Fintype.card_pos (α := C)
  let order := fun p r H => firstOfTwo tree H (parent p) (child p r)
  have ho p r H H' (h : ∀ z, z ≠ parent p → z ≠ child p r → H z = H' z) :
      order p r H = order p r H' := firstOfTwo_congr_off tree H H' _ _ h
  have hs p H H' (h : AgreeOff (parent p) H H') : state p H = state p H' :=
    hstateOff p (Classical.choice inferInstance) H H' (fun z hz _ => h z hz)
  let cp := fun H : Q → C => ∑ p : Parent,
    if parent p ∈ queried tree H then (1 : ℚ) else 0
  let ce := fun H : Q → C => ∑ i : Parent × Response,
    if order i.1 i.2 H = .right then (1 : ℚ) else 0
  let cl := fun H : Q → C => ∑ i : Parent × Response,
    if child i.1 i.2 ∈ queried tree H ∧ order i.1 i.2 H = .left then (1 : ℚ) else 0
  let rankWeight := fun (p : Parent) (H : Q → C) (a : C) =>
    if parent p ∈ queried tree H ∧ bad (state p H) p a then (1 : ℚ) else 0
  let earlyWeight := fun (i : Parent × Response) (H : Q → C) (a b : C) =>
    if order i.1 i.2 H = .right ∧ event (state i.1 H) i.1 i.2 a b then (1 : ℚ) else 0
  let lateWeight := fun (i : Parent × Response) (H : Q → C) (b : C) =>
    if child i.1 i.2 ∈ queried tree H ∧ order i.1 i.2 H = .left ∧
      ¬bad (state i.1 H) i.1 (H (parent i.1)) ∧
      ¬high (state i.1 H) i.1 i.2 (H (parent i.1)) ∧
      event (state i.1 H) i.1 i.2 (H (parent i.1)) b then (1 : ℚ) else 0
  let highWeight := fun (i : Parent × Response) (H : Q → C) (a b : C) =>
    if order i.1 i.2 H = .left ∧ ¬bad (state i.1 H) i.1 a ∧
      high (state i.1 H) i.1 i.2 a ∧ event (state i.1 H) i.1 i.2 a b then (1 : ℚ) else 0
  let highBudget := fun (s : State) (p : Parent) (r : Response) => ∑ a : C, ∑ b : C,
    if ¬bad s p a ∧ high s p r a ∧ event s p r a b then (1 : ℚ) else 0
  have hbudget0 s p r : 0 ≤ highBudget s p r := by
    apply sum_nonneg
    intro a _
    exact sum_nonneg (fun _ _ => by split_ifs <;> norm_num)
  have hR := single_weight_sum_le parent rankWeight
    (fun p H H' h a => by
      simp only [rankWeight, hs p H H' h, mem_queried_iff tree (parent p) h])
    (fun p H => if parent p ∈ queried tree H then q*mu else 0)
    (fun p H => by
      by_cases hp : parent p ∈ queried tree H
      · simpa [rankWeight, hp, q] using hrank (state p H) p
      · simp [rankWeight, hp])
  have hR' : (∑ H : Q → C, ∑ p, rankWeight p H (H (parent p))) ≤
      mu * ∑ H : Q → C, cp H := by
    have hsum : (∑ H : Q → C, ∑ p : Parent,
        if parent p ∈ queried tree H then q*mu else 0) =
        q*(mu*∑ H : Q → C, cp H) := by
      simp only [cp, mul_sum, mul_ite, mul_one, mul_zero]
    rw [hsum] at hR
    exact (mul_le_mul_iff_of_pos_left hq).mp hR
  have hL := single_weight_sum_le (fun i : Parent × Response => child i.1 i.2) lateWeight
    (fun i H H' h b => by
      have hp : H (parent i.1) = H' (parent i.1) := h _ (hdisjoint i.1 i.1 i.2)
      have hoff : ∀ z, z ≠ parent i.1 → z ≠ child i.1 i.2 → H z = H' z := fun z _ hz => h z hz
      simp only [lateWeight, hp, hstateOff i.1 i.2 H H' hoff, ho i.1 i.2 H H' hoff,
        mem_queried_iff tree (child i.1 i.2) h])
    (fun i H => if child i.1 i.2 ∈ queried tree H ∧ order i.1 i.2 H = .left
      then q*epsilon else 0)
    (fun i H => by
      by_cases hg : child i.1 i.2 ∈ queried tree H ∧ order i.1 i.2 H = .left
      · simpa only [lateWeight, hg.1, hg.2, true_and, ite_true, q] using
          hlow (state i.1 H) i.1 i.2 (H (parent i.1))
      · have hfalse b : ¬(child i.1 i.2 ∈ queried tree H ∧ order i.1 i.2 H = .left ∧
            ¬bad (state i.1 H) i.1 (H (parent i.1)) ∧
            ¬high (state i.1 H) i.1 i.2 (H (parent i.1)) ∧
            event (state i.1 H) i.1 i.2 (H (parent i.1)) b) := fun h => hg ⟨h.1,h.2.1⟩
        simp only [lateWeight, if_neg (hfalse _), sum_const_zero, if_neg hg, le_refl])
  have hL' : (∑ H : Q → C, ∑ i : Parent × Response,
      lateWeight i H (H (child i.1 i.2))) ≤ epsilon * ∑ H : Q → C, cl H := by
    have hsum : (∑ H : Q → C, ∑ i : Parent × Response,
        if child i.1 i.2 ∈ queried tree H ∧ order i.1 i.2 H = .left
        then q*epsilon else 0) = q*(epsilon*∑ H : Q → C, cl H) := by
      simp only [cl, mul_sum, mul_ite, mul_one, mul_zero]
    rw [hsum] at hL
    exact (mul_le_mul_iff_of_pos_left hq).mp hL
  have hE := pair_weight_sum_le
    (fun i : Parent × Response => parent i.1) (fun i => child i.1 i.2)
    (fun i => hdisjoint i.1 i.1 i.2) earlyWeight
    (fun i H H' h a b => by simp only [earlyWeight, ho i.1 i.2 H H' h,
      hstateOff i.1 i.2 H H' h])
    (fun i H => if order i.1 i.2 H = .right then q^2*epsilon else 0)
    (fun i H H' h => by rw [ho i.1 i.2 H H' h])
    (fun i H => by
      by_cases hg : order i.1 i.2 H = .right
      · simpa [earlyWeight, hg, q] using hiop (state i.1 H) i.1 i.2
      · simp [earlyWeight, hg])
  have hE' : (∑ H : Q → C, ∑ i : Parent × Response,
      earlyWeight i H (H (parent i.1)) (H (child i.1 i.2))) ≤
        epsilon*∑ H : Q → C, ce H := by
    have hsum : (∑ H : Q → C, ∑ i : Parent × Response,
        if order i.1 i.2 H = .right then q^2*epsilon else 0) =
        q^2*(epsilon*∑ H : Q → C, ce H) := by
      simp only [ce, mul_sum, mul_ite, mul_one, mul_zero]
    rw [hsum] at hE
    exact (mul_le_mul_iff_of_pos_left (pow_pos hq 2)).mp hE
  have hH := pair_weight_sum_le
    (fun i : Parent × Response => parent i.1) (fun i => child i.1 i.2)
    (fun i => hdisjoint i.1 i.1 i.2) highWeight
    (fun i H H' h a b => by simp only [highWeight, ho i.1 i.2 H H' h,
      hstateOff i.1 i.2 H H' h])
    (fun i H => if order i.1 i.2 H = .left then highBudget (state i.1 H) i.1 i.2 else 0)
    (fun i H H' h => by rw [ho i.1 i.2 H H' h, hstateOff i.1 i.2 H H' h])
    (fun i H => by
      by_cases hg : order i.1 i.2 H = .left
      · simp [highWeight, highBudget, hg]
      · simp [highWeight, hg])
  have hHbound (H : Q → C) :
      (∑ i : Parent × Response,
        if order i.1 i.2 H = .left then highBudget (state i.1 H) i.1 i.2 else 0) ≤
        q^2*beta*cp H := by
    rw [Fintype.sum_prod_type]
    change _ ≤ q^2*beta*∑ p : Parent, _
    rw [mul_sum]
    apply sum_le_sum
    intro p _
    by_cases hp : parent p ∈ queried tree H
    · simp only [hp, ite_true, mul_one]
      calc
        _ ≤ ∑ r : Response, highBudget (state p H) p r := sum_le_sum (fun r _ => by
          split_ifs
          · exact le_rfl
          · exact hbudget0 _ _ _)
        _ ≤ _ := hhigh (state p H) p
    · have hn r : order p r H ≠ .left := fun h => hp
        (firstOfTwo_left_mem tree H (parent p) (child p r) h)
      simp [hp, hn]
  have hH' : (∑ H : Q → C, ∑ i : Parent × Response,
      highWeight i H (H (parent i.1)) (H (child i.1 i.2))) ≤
        beta*∑ H : Q → C, cp H := by
    have htot := hH.trans (sum_le_sum (fun H _ => hHbound H))
    have heq : (∑ H : Q → C, q^2*beta*cp H) = q^2*(beta*∑ H : Q → C, cp H) := by
      simp [mul_sum, mul_assoc]
    rw [heq] at htot
    exact (mul_le_mul_iff_of_pos_left (pow_pos hq 2)).mp htot
  have hcount (H : Q → C) : cp H+ce H+cl H ≤ N := by
    have hsplit (i : Parent × Response) :
        (if order i.1 i.2 H = .right then (1 : ℚ) else 0) +
        (if child i.1 i.2 ∈ queried tree H ∧ order i.1 i.2 H = .left then (1 : ℚ) else 0) =
        (if child i.1 i.2 ∈ queried tree H then (1 : ℚ) else 0) := by
      cases h : order i.1 i.2 H with
      | neither =>
        have hn : child i.1 i.2 ∉ queried tree H := fun hm =>
          firstOfTwo_ne_neither_of_right_mem tree H _ _ hm h
        simp [hn]
      | left => simp
      | right =>
        have hm := firstOfTwo_right_mem tree H (parent i.1) (child i.1 i.2) h
        simp [hm]
    have heq : ce H+cl H = ∑ i : Parent × Response,
        if child i.1 i.2 ∈ queried tree H then (1 : ℚ) else 0 := by
      rw [← sum_add_distrib]
      exact sum_congr rfl (fun i _ => hsplit i)
    rw [add_assoc, heq]
    have h := queried_role_count_le tree parent child hparent hchild hdisjoint H
    simpa [cp, ← sum_filter] using (show
      ((univ.filter fun p => parent p ∈ queried tree H).card : ℚ) +
      ((univ.filter fun i : Parent × Response => child i.1 i.2 ∈ queried tree H).card : ℚ) ≤ N from by
        exact_mod_cast h)
  have hcp : 0 ≤ ∑ H : Q → C, cp H := sum_nonneg (fun H _ => sum_nonneg (fun _ _ => by split_ifs <;> norm_num))
  have hsumcount : (∑ H : Q → C, (cp H+ce H+cl H)) ≤ ∑ _H : Q → C, (N : ℚ) :=
    sum_le_sum (fun H _ => hcount H)
  simp only [sum_add_distrib, sum_const, card_univ, Fintype.card_fun, nsmul_eq_mul] at hsumcount
  have hmain := add_le_add (add_le_add hR' hE') (add_le_add hL' hH')
  have hmub := mul_le_mul_of_nonneg_right hmb hcp
  have htotal := mul_le_mul_of_nonneg_left hsumcount he
  simp only [sum_add_distrib] at *
  change _ ≤ (N : ℚ)*epsilon*q^Fintype.card Q
  dsimp only [rankWeight, earlyWeight, lateWeight, highWeight, order] at hmain
  simp only [Nat.cast_pow] at htotal
  change epsilon * _ ≤ epsilon * (q ^ Fintype.card Q * (N : ℚ)) at htotal
  nlinarith only [hmain, hmub, htotal]

/-- Append the verifier lookup, covering arbitrary final response selection and zero-query provers. -/
theorem tree_query_role_final_ratio_le
    {Out Parent Response State : Type} [Fintype Parent] [Fintype Response]
    [Nonempty Response] {N : ℕ}
    (tree : Tree Q C Out N) (selected : Out → Parent × Response) (parent : Parent → Q) (child : Parent → Response → Q)
    (hparent : Function.Injective parent)
    (hchild : Function.Injective (fun i : Parent × Response => child i.1 i.2))
    (hdisjoint : ∀ p p' r, parent p ≠ child p' r)
    (state : Parent → (Q → C) → State)
    (hstateOff : ∀ p r H H', (∀ z, z ≠ parent p → z ≠ child p r → H z = H' z) →
      state p H = state p H')
    (event : State → Parent → Response → C → C → Prop)
    (bad : State → Parent → C → Prop)
    (high : State → Parent → Response → C → Prop)
    (epsilon mu beta : ℚ) (he : 0 ≤ epsilon)
    (hmb : mu+beta ≤ epsilon)
    (hiop : ∀ s p r, ∑ a : C, ∑ b : C,
      (if event s p r a b then (1 : ℚ) else 0) ≤ (Fintype.card C : ℚ)^2*epsilon)
    (hrank : ∀ s p, ∑ a : C, (if bad s p a then (1 : ℚ) else 0) ≤ Fintype.card C*mu)
    (hlow : ∀ s p r a, ∑ b : C,
      (if ¬bad s p a ∧ ¬high s p r a ∧ event s p r a b then (1 : ℚ) else 0) ≤
        Fintype.card C*epsilon)
    (hhigh : ∀ s p, ∑ r : Response, ∑ a : C, ∑ b : C,
      (if ¬bad s p a ∧ high s p r a ∧ event s p r a b then (1 : ℚ) else 0) ≤
        (Fintype.card C : ℚ)^2*beta) :
    let failure := fun H : Q → C =>
      let i := selected (tree.run H).1
      event (state i.1 H) i.1 i.2 (H (parent i.1)) (H (child i.1 i.2))
    ((univ.filter failure).card : ℚ) / (Fintype.card C : ℚ)^Fintype.card Q ≤
      (N+1 : ℕ)*epsilon := by
  classical
  let point : Out → Q := fun out => child (selected out).1 (selected out).2
  let extended := appendFinalQuery tree point
  let order := fun p r H => firstOfTwo extended H (parent p) (child p r)
  let rank : Parent → (Q → C) → ℚ := fun p H =>
    if parent p ∈ queried extended H ∧ bad (state p H) p (H (parent p)) then 1 else 0
  let response : Parent × Response → (Q → C) → ℚ := fun i H =>
    (if order i.1 i.2 H = .right ∧ event (state i.1 H) i.1 i.2
        (H (parent i.1)) (H (child i.1 i.2)) then 1 else 0) +
    (if child i.1 i.2 ∈ queried extended H ∧ order i.1 i.2 H = .left ∧
        ¬bad (state i.1 H) i.1 (H (parent i.1)) ∧
        ¬high (state i.1 H) i.1 i.2 (H (parent i.1)) ∧
        event (state i.1 H) i.1 i.2 (H (parent i.1)) (H (child i.1 i.2)) then 1 else 0) +
    (if order i.1 i.2 H = .left ∧ ¬bad (state i.1 H) i.1 (H (parent i.1)) ∧
        high (state i.1 H) i.1 i.2 (H (parent i.1)) ∧
        event (state i.1 H) i.1 i.2 (H (parent i.1)) (H (child i.1 i.2)) then 1 else 0)
  have hr0 p H : 0 ≤ rank p H := by dsimp [rank]; split_ifs <;> norm_num
  have hs0 i H : 0 ≤ response i H := by dsimp [response]; split_ifs <;> norm_num
  have hpoint H :
      (if (let i := selected (tree.run H).1;
        event (state i.1 H) i.1 i.2 (H (parent i.1)) (H (child i.1 i.2))) then (1 : ℚ) else 0) ≤
        (∑ p : Parent, rank p H)+(∑ i : Parent × Response, response i H) := by
    let i := selected (tree.run H).1
    have hm : child i.1 i.2 ∈ queried extended H := appendFinalQuery_mem tree point H
    have hn : order i.1 i.2 H ≠ .neither :=
      firstOfTwo_ne_neither_of_right_mem extended H _ _ hm
    have hr := single_le_sum (fun p _ => hr0 p H) (mem_univ i.1)
    have hs := single_le_sum (fun j _ => hs0 j H) (mem_univ i)
    have hR : 0 ≤ ∑ p : Parent, rank p H := sum_nonneg (fun p _ => hr0 p H)
    have hS : 0 ≤ ∑ j : Parent × Response, response j H := sum_nonneg (fun j _ => hs0 j H)
    change (if event (state i.1 H) i.1 i.2 (H (parent i.1)) (H (child i.1 i.2)) then (1 : ℚ) else 0) ≤ _
    by_cases ha : event (state i.1 H) i.1 i.2 (H (parent i.1)) (H (child i.1 i.2))
    · simp only [if_pos ha]
      cases ho : order i.1 i.2 H with
      | neither => exact False.elim (hn ho)
      | right =>
        have hresp : 1 ≤ response i H := by simp [response, ho, ha]
        linarith
      | left =>
        have hp : parent i.1 ∈ queried extended H := firstOfTwo_left_mem extended H _ _ ho
        by_cases hbad : bad (state i.1 H) i.1 (H (parent i.1))
        · have hrank : rank i.1 H = 1 := by simp [rank, hp, hbad]
          linarith
        · have hresp : 1 ≤ response i H := by
            by_cases hhi : high (state i.1 H) i.1 i.2 (H (parent i.1)) <;>
              simp [response, ho, ha, hm, hbad, hhi]
          linarith
    · simp only [if_neg ha]
      linarith
  have hbound := tree_query_role_sum_le extended parent child hparent hchild hdisjoint
    state hstateOff event bad high epsilon mu beta he hmb hiop hrank hlow hhigh
  change (∑ H : Q → C, ((∑ p : Parent, rank p H)+
    ∑ i : Parent × Response, response i H)) ≤
      (1+N : ℕ)*epsilon*(Fintype.card C : ℚ)^Fintype.card Q at hbound
  have hden : (0 : ℚ) < (Fintype.card C : ℚ)^Fintype.card Q := by positivity
  rw [div_le_iff₀ hden]
  have hc : ((univ.filter fun H : Q → C =>
      let i := selected (tree.run H).1;
      event (state i.1 H) i.1 i.2 (H (parent i.1)) (H (child i.1 i.2))).card : ℚ) =
      ∑ H : Q → C, if (let i := selected (tree.run H).1;
        event (state i.1 H) i.1 i.2 (H (parent i.1)) (H (child i.1 i.2))) then (1 : ℚ) else 0 := by
    simp only [card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [hc]
  exact (sum_le_sum (fun H _ => hpoint H)).trans (by simpa only [Nat.add_comm 1 N] using hbound)

end Bcs.TotalOracle
