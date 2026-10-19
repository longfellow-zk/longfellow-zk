import Bcs.AffineBlock
import Bcs.FinalQueryContext

/-! Localize existing one/two-coordinate charges before replacing actual
spending by the adversary's total fuel. -/
namespace Bcs.TotalOracle
open Finset Merkle.RandomOracle AffineBlock Footprint
open scoped Classical

theorem queryCost_eq_filter_length {Q C Out : Type} [DecidableEq Q]
    (domain : Finset Q) {N : ℕ} (tree : Tree Q C Out N) (H : Q → C) :
    queryCost domain tree H = ((queried tree H).filter (fun q => q ∈ domain)).length := by
  induction tree with
  | done => simp [queryCost, queried]
  | query q next ih =>
    rw [queryCost, queried_query]
    by_cases h : q ∈ domain <;> simp [h, ih, Nat.cast_add, add_comm]

theorem queried_domain_card_le {Q C Out : Type} [DecidableEq Q]
    (domain : Finset Q) {N : ℕ} (tree : Tree Q C Out N) (H : Q → C) :
    (((queried tree H).toFinset.filter (fun q => q ∈ domain)).card : ℚ) ≤
      queryCost domain tree H := by
  rw [queryCost_eq_filter_length]
  have he : (queried tree H).toFinset.filter (fun q => q ∈ domain) =
      ((queried tree H).filter (fun q => q ∈ domain)).toFinset := by ext q; simp
  rw [he]
  exact_mod_cast List.toFinset_card_le _

theorem queryCost_append_le {Q C Out : Type} [DecidableEq Q]
    (domain : Finset Q) {N : ℕ} (tree : Tree Q C Out N)
    (point : Out → Q) (H : Q → C) :
    queryCost domain (appendFinalQuery tree point) H ≤ queryCost domain tree H + 1 := by
  simp only [queryCost_eq_filter_length, queried, appendFinalQuery, Tree.run_bind,
    Tree.run_query, Tree.run_done, List.map_append, List.map_cons, List.map_nil,
    List.filter_append, List.length_append, Nat.cast_add]
  by_cases h : point (tree.run H).1 ∈ domain <;> simp [h]

theorem charged_two_fresh_weight_expected_le
    {Q C I : Type} [Fintype Q] [DecidableEq Q] [Fintype I]
    [Fintype C] [Nonempty C]
    (first second : I → Q) (hneq : ∀ i, first i ≠ second i)
    (charged : ∀ i, (AwayFromTwo (first i) (second i) → C) → Prop)
    (weight : ∀ i, (AwayFromTwo (first i) (second i) → C) → C → C → ℚ)
    (budget : ∀ i, (AwayFromTwo (first i) (second i) → C) → ℚ)
    (total : (Q → C) → ℚ)
    (hlocal : ∀ i off,
      ∑ a : C, ∑ b : C, weight i off a b ≤ budget i off)
    (htotal : ∀ H : Q → C,
      (∑ i : I, if charged i (fun z => H z.1) then
        budget i (fun z => H z.1) else 0) ≤ total H) :
    (∑ H : Q → C, ∑ i : I,
      if charged i (fun z => H z.1) then
        weight i (fun z => H z.1) (H (first i)) (H (second i)) else 0) /
        (Fintype.card C : ℚ) ^ Fintype.card Q ≤
      average total / (Fintype.card C : ℚ) ^ 2 := by
  classical
  let q : ℚ := Fintype.card C
  have hq : 0 < q := by
    dsimp [q]
    exact_mod_cast Fintype.card_pos
  have hden : 0 < q ^ Fintype.card Q := pow_pos hq _
  have hpair (i : I) :
      q ^ 2 * (∑ H : Q → C,
        if charged i (fun z => H z.1) then
          weight i (fun z => H z.1) (H (first i)) (H (second i)) else 0) ≤
      ∑ H : Q → C,
        if charged i (fun z => H z.1) then
          budget i (fun z => H z.1) else 0 := by
    let Off := AwayFromTwo (first i) (second i) → C
    have hw := sum_two_fresh_weight (first i) (second i) (hneq i)
      (fun off a b => if charged i off then weight i off a b else 0)
    have hb := sum_two_fresh_weight (first i) (second i) (hneq i)
      (fun off _ _ => if charged i off then budget i off else 0)
    have hle :
        (∑ off : Off, ∑ a : C, ∑ b : C,
          if charged i off then weight i off a b else 0) ≤
        ∑ off : Off,
          if charged i off then budget i off else 0 := by
      apply Finset.sum_le_sum
      intro off _
      by_cases hc : charged i off
      · simpa only [hc, ↓reduceIte] using hlocal i off
      · simp [hc]
    have hconst :
        (∑ off : Off, ∑ a : C, ∑ b : C,
          if charged i off then budget i off else 0) =
        q ^ 2 * ∑ off : Off,
          if charged i off then budget i off else 0 := by
      simp [q, pow_two, Finset.mul_sum, mul_left_comm, mul_comm]
    change q ^ 2 *
      (∑ H : Q → C,
        if charged i (fun z => H z.1) then
          weight i (fun z => H z.1) (H (first i)) (H (second i)) else 0) ≤ _
    rw [hw, hb, hconst]
    exact mul_le_mul_of_nonneg_left hle (le_of_lt (pow_pos hq 2))
  have hsum :
      q ^ 2 * (∑ H : Q → C, ∑ i : I,
        if charged i (fun z => H z.1) then
          weight i (fun z => H z.1) (H (first i)) (H (second i)) else 0) ≤
      (∑ H : Q → C, total H) := by
    calc
      _ = ∑ i : I, q ^ 2 * (∑ H : Q → C,
          if charged i (fun z => H z.1) then
            weight i (fun z => H z.1) (H (first i)) (H (second i)) else 0) := by
              rw [Finset.sum_comm]
              simp only [Finset.mul_sum]
      _ ≤ ∑ i : I, ∑ H : Q → C,
          if charged i (fun z => H z.1) then
            budget i (fun z => H z.1) else 0 :=
            Finset.sum_le_sum fun i _ => hpair i
      _ = ∑ H : Q → C, ∑ i : I,
          if charged i (fun z => H z.1) then
            budget i (fun z => H z.1) else 0 := Finset.sum_comm
      _ ≤ ∑ H : Q → C, total H :=
        Finset.sum_le_sum fun H _ => htotal H
  change (∑ H : Q → C, ∑ i : I,
      if charged i (fun z => H z.1) then
        weight i (fun z => H z.1) (H (first i)) (H (second i)) else 0) /
      q ^ Fintype.card Q ≤ average total / q ^ 2
  rw [div_le_div_iff₀ hden (pow_pos hq 2)]
  have he : average total * q ^ Fintype.card Q = ∑ H : Q → C, total H := by
    simp only [average, Fintype.card_fun, Nat.cast_pow, q]
    exact div_mul_cancel₀ _ hden.ne'
  rw [he]
  simpa only [mul_comm] using hsum

theorem tree_first_pair_grouped_domain_le
    {Q C Out Parent Response : Type}
    [Fintype Q] [DecidableEq Q] [Fintype C] [Nonempty C]
    [Fintype Parent] [Fintype Response] {N : ℕ}
    (tree : Tree Q C Out N) (domain : Finset Q)
    (parent : Parent → Q) (child : Parent → Response → Q)
    (hparent : Function.Injective parent)
    (hchild : Function.Injective
      (fun i : Parent × Response => child i.1 i.2))
    (hdisjoint : ∀ p p' r, parent p ≠ child p' r)
    (hpDomain : ∀ p, parent p ∈ domain)
    (hcDomain : ∀ p r, child p r ∈ domain)
    (budget : Parent → Response → ℚ)
    (hnonneg : ∀ p r, 0 ≤ budget p r)
    (beta : ℚ) (hbeta : 0 ≤ beta)
    (hsumBudget : ∀ p, ∑ r : Response, budget p r ≤ beta)
    (H : Q → C) :
    (∑ p : Parent, ∑ r : Response,
      if firstOfTwoOffResult tree (parent p) (child p r)
          (hdisjoint p p r) (fun z => H z.1) ≠ .neither then
        budget p r else 0) ≤ queryCost domain tree H * beta := by
  classical
  let selected (p : Parent) (r : Response) :=
    firstOfTwoOffResult tree (parent p) (child p r)
      (hdisjoint p p r) (fun z => H z.1)
  let qset := (queried tree H).toFinset.filter (fun q => q ∈ domain)
  let parents := (univ : Finset Parent).filter
    (fun p => parent p ∈ qset)
  let children := (univ : Finset (Parent × Response)).filter
    (fun i => child i.1 i.2 ∈ qset)
  have hleft (p : Parent) (r : Response)
      (h : selected p r = .left) : parent p ∈ qset := by
    have hh : firstOfTwo tree H (parent p) (child p r) = .left := by
      rw [← firstOfTwoOff_eq tree (parent p) (child p r)
        (hdisjoint p p r) H]
      exact h
    exact mem_filter.mpr ⟨List.mem_toFinset.mpr
      (firstOfTwo_left_mem tree H (parent p) (child p r) hh), hpDomain p⟩
  have hright (p : Parent) (r : Response)
      (h : selected p r = .right) : child p r ∈ qset := by
    have hh : firstOfTwo tree H (parent p) (child p r) = .right := by
      rw [← firstOfTwoOff_eq tree (parent p) (child p r)
        (hdisjoint p p r) H]
      exact h
    exact mem_filter.mpr ⟨List.mem_toFinset.mpr
      (firstOfTwo_right_mem tree H (parent p) (child p r) hh), hcDomain p r⟩
  have hsingle (p : Parent) (r : Response) : budget p r ≤ beta :=
    (Finset.single_le_sum (fun s _ => hnonneg p s)
      (Finset.mem_univ r)).trans (hsumBudget p)
  have hsplit :
      (∑ p : Parent, ∑ r : Response,
        if selected p r ≠ .neither then budget p r else 0) =
      (∑ p : Parent, ∑ r : Response,
        if selected p r = .left then budget p r else 0) +
      (∑ p : Parent, ∑ r : Response,
        if selected p r = .right then budget p r else 0) := by
    calc
      _ = ∑ p : Parent, ∑ r : Response,
        ((if selected p r = .left then budget p r else 0) +
         (if selected p r = .right then budget p r else 0)) := by
          apply Finset.sum_congr rfl
          intro p _
          apply Finset.sum_congr rfl
          intro r _
          cases h : selected p r <;> simp
      _ = _ := by simp only [Finset.sum_add_distrib]
  have hleftTotal :
      (∑ p : Parent, ∑ r : Response,
        if selected p r = .left then budget p r else 0) ≤
      ∑ p : Parent, if p ∈ parents then beta else 0 := by
    apply Finset.sum_le_sum
    intro p _
    by_cases hp : parent p ∈ qset
    · have hmem : p ∈ parents := by simp [parents, hp]
      simp only [hmem, ↓reduceIte]
      calc
        _ ≤ ∑ r : Response, budget p r := by
          apply Finset.sum_le_sum
          intro r _
          by_cases h : selected p r = .left
          · simp [h]
          · simpa [h] using hnonneg p r
        _ ≤ beta := hsumBudget p
    · have hnot : ∀ r, selected p r ≠ .left := by
        intro r h
        exact hp (hleft p r h)
      have hmem : p ∉ parents := by simp [parents, hp]
      simp [hmem, hnot]
  have hrightTotal :
      (∑ p : Parent, ∑ r : Response,
        if selected p r = .right then budget p r else 0) ≤
      ∑ i : Parent × Response,
        if i ∈ children then beta else 0 := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_le_sum
    intro p _
    apply Finset.sum_le_sum
    intro r _
    by_cases h : selected p r = .right
    · have hmem : (p, r) ∈ children := by
        simp [children, hright p r h]
      simp [h, hmem, hsingle p r]
    · simp only [h, ↓reduceIte]
      split_ifs
      · exact hbeta
      · exact le_refl _
  have hparentCard :
      (parents.image parent).card = parents.card :=
    Finset.card_image_of_injOn
      (fun p _ p' _ heq => hparent heq)
  have hchildCard :
      (children.image (fun i => child i.1 i.2)).card =
        children.card :=
    Finset.card_image_of_injOn
      (fun i _ j _ heq => hchild heq)
  have himagesDisjoint :
      Disjoint (parents.image parent)
        (children.image (fun i => child i.1 i.2)) := by
    apply Finset.disjoint_left.mpr
    intro x hx hy
    rcases Finset.mem_image.mp hx with ⟨p, _, hpx⟩
    rcases Finset.mem_image.mp hy with ⟨i, _, hix⟩
    exact hdisjoint p i.1 i.2 (hpx.trans hix.symm)
  have himageSubset :
      parents.image parent ∪
        children.image (fun i => child i.1 i.2) ⊆ qset := by
    intro x hx
    rcases Finset.mem_union.mp hx with hp | hc
    · rcases Finset.mem_image.mp hp with ⟨p, hpm, hpx⟩
      subst x
      exact (Finset.mem_filter.mp hpm).2
    · rcases Finset.mem_image.mp hc with ⟨i, him, hix⟩
      subst x
      exact (Finset.mem_filter.mp him).2
  have hcard : parents.card + children.card ≤ qset.card := by
    calc
      _ = (parents.image parent).card +
            (children.image (fun i => child i.1 i.2)).card := by
              rw [hparentCard, hchildCard]
      _ = (parents.image parent ∪
            children.image (fun i => child i.1 i.2)).card :=
              (Finset.card_union_of_disjoint himagesDisjoint).symm
      _ ≤ qset.card := Finset.card_le_card himageSubset
  calc
    _ = (∑ p : Parent, ∑ r : Response,
          if selected p r = .left then budget p r else 0) +
        (∑ p : Parent, ∑ r : Response,
          if selected p r = .right then budget p r else 0) := hsplit
    _ ≤ (∑ p : Parent, if p ∈ parents then beta else 0) +
        (∑ i : Parent × Response,
          if i ∈ children then beta else 0) :=
            add_le_add hleftTotal hrightTotal
    _ = (parents.card + children.card : ℚ) * beta := by
      simp [← Finset.sum_filter, Finset.sum_const, parents, children,
        add_mul]
    _ ≤ (qset.card : ℚ) * beta :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hbeta
    _ ≤ queryCost domain tree H * beta :=
      mul_le_mul_of_nonneg_right (queried_domain_card_le domain tree H) hbeta

theorem tree_child_indexed_weight_domain_le
    {Q C Out I : Type}
    [Fintype Q] [DecidableEq Q] [Fintype C] [Nonempty C]
    [Fintype I] {N : ℕ}
    (tree : Tree Q C Out N) (domain : Finset Q)
    (child : I → Q) (hchild : Function.Injective child)
    (hcDomain : ∀ i, child i ∈ domain)
    (weight : I → (Q → C) → C → ℚ)
    (hoff : ∀ i H H', AgreeOff (child i) H H' →
      ∀ c, weight i H c = weight i H' c)
    (beta : ℚ) (hbeta : 0 ≤ beta)
    (hlocal : ∀ i H, ∑ c : C, weight i H c ≤ beta) :
    (∑ H : Q → C, ∑ i : I,
      if child i ∈ queried tree H then
        weight i H (H (child i)) else 0) /
        (Fintype.card C : ℚ) ^ Fintype.card Q ≤
      average (queryCost domain tree) * beta / Fintype.card C := by
  classical
  let q : ℚ := Fintype.card C
  have hq : 0 < q := by
    dsimp [q]
    exact_mod_cast Fintype.card_pos
  let W (i : I) (H : Q → C) (c : C) : ℚ :=
    if child i ∈ queried tree H then weight i H c else 0
  have hWoff (i : I) (H H' : Q → C)
      (h : AgreeOff (child i) H H') (c : C) :
      W i H c = W i H' c := by
    have hmem := mem_queried_iff tree (child i) h
    by_cases hi : child i ∈ queried tree H
    · have hi' := hmem.mp hi
      simp [W, hi, hi', hoff i H H' h c]
    · have hi' := mt hmem.mpr hi
      simp [W, hi, hi']
  have hcoord (i : I) :
      (∑ H : Q → C, W i H (H (child i))) * q =
        ∑ H : Q → C, ∑ c : C, W i H c :=
    sum_coord_mul_rat (child i) (W i) (hWoff i)
  have hcount (H : Q → C) :
      ((univ.filter fun i : I => child i ∈ queried tree H).card : ℚ) ≤ queryCost domain tree H := by
    let s := (univ : Finset I).filter
      (fun i => child i ∈ queried tree H)
    have hinj : (s.image child).card = s.card :=
      Finset.card_image_of_injOn
        (fun i _ j _ hij => hchild hij)
    have hsub : s.image child ⊆ (queried tree H).toFinset.filter (fun q => q ∈ domain) := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨i, hi, hix⟩
      subst x
      exact mem_filter.mpr ⟨List.mem_toFinset.mpr (Finset.mem_filter.mp hi).2, hcDomain i⟩
    have hc : s.card ≤ ((queried tree H).toFinset.filter (fun q => q ∈ domain)).card := by
      calc
        _ = (s.image child).card := hinj.symm
        _ ≤ ((queried tree H).toFinset.filter (fun q => q ∈ domain)).card := Finset.card_le_card hsub
    exact (show (s.card : ℚ) ≤ _ by exact_mod_cast hc).trans (queried_domain_card_le domain tree H)
  have hsum :
      q * (∑ H : Q → C, ∑ i : I, W i H (H (child i))) ≤
      (∑ H : Q → C, queryCost domain tree H * beta) := by
    calc
      _ = (∑ i : I, ∑ H : Q → C, W i H (H (child i))) * q := by
        rw [Finset.sum_comm]
        ring
      _ = ∑ i : I, (∑ H : Q → C, W i H (H (child i))) * q := by
        rw [Finset.sum_mul]
      _ = ∑ i : I, ∑ H : Q → C, ∑ c : C, W i H c := by
        apply Finset.sum_congr rfl
        intro i _
        exact hcoord i
      _ = ∑ H : Q → C, ∑ i : I, ∑ c : C, W i H c :=
        Finset.sum_comm
      _ ≤ ∑ H : Q → C, queryCost domain tree H * beta := by
        apply Finset.sum_le_sum
        intro H _
        calc
          (∑ i : I, ∑ c : C, W i H c) ≤
              ∑ i : I, if child i ∈ queried tree H then beta else 0 := by
            apply Finset.sum_le_sum
            intro i _
            by_cases hi : child i ∈ queried tree H
            · simpa only [W, hi, ↓reduceIte] using hlocal i H
            · simp [W, hi]
          _ = ((univ.filter fun i : I =>
              child i ∈ queried tree H).card : ℚ) * beta := by
            rw [← Finset.sum_filter]
            simp [Finset.sum_const, mul_comm]
          _ ≤ queryCost domain tree H * beta :=
            mul_le_mul_of_nonneg_right (hcount H) hbeta
  have hden : 0 < q ^ Fintype.card Q := pow_pos hq _
  change (∑ H : Q → C, ∑ i : I,
      if child i ∈ queried tree H then
        weight i H (H (child i)) else 0) /
      q ^ Fintype.card Q ≤ average (queryCost domain tree) * beta / q
  rw [div_le_div_iff₀ hden hq]
  have he : average (queryCost domain tree) * beta * q ^ Fintype.card Q =
      ∑ H : Q → C, queryCost domain tree H * beta := by
    simp only [average, Fintype.card_fun, Nat.cast_pow, ← sum_mul]
    dsimp only [q] at *
    field_simp
  rw [he]
  simpa only [W, mul_comm] using hsum

theorem tree_both_orders_local_context_domain_le
    {Q C Out Parent Response State : Type}
    [Fintype Q] [DecidableEq Q] [Fintype C] [Nonempty C]
    [Fintype Parent] [Fintype Response] {N : ℕ}
    (tree : Tree Q C Out N) (domain : Finset Q)
    (parent : Parent → Q) (child : Parent → Response → Q)
    (hparent : Function.Injective parent)
    (hchild : Function.Injective
      (fun i : Parent × Response => child i.1 i.2))
    (hdisjoint : ∀ p p' r, parent p ≠ child p' r)
    (hpDomain : ∀ p, parent p ∈ domain)
    (hcDomain : ∀ p r, child p r ∈ domain)
    (state : Parent → (Q → C) → State)
    (hstateOff : ∀ p r (H H' : Q → C),
      (∀ z, z ≠ parent p → z ≠ child p r → H z = H' z) →
      state p H = state p H')
    (weight : State → Parent → Response → C → C → ℚ)
    (budget : State → Parent → Response → ℚ)
    (hnonneg : ∀ s p r, 0 ≤ budget s p r)
    (beta : ℚ) (hbeta : 0 ≤ beta)
    (hlocal : ∀ s p r,
      ∑ a : C, ∑ b : C, weight s p r a b ≤ budget s p r)
    (hsumBudget : ∀ s p, ∑ r : Response, budget s p r ≤ beta) :
    (∑ H : Q → C, ∑ p : Parent, ∑ r : Response,
      if firstOfTwoOffResult tree (parent p) (child p r)
          (hdisjoint p p r) (fun z => H z.1) ≠ .neither then
        weight (state p H) p r (H (parent p)) (H (child p r)) else 0) /
        (Fintype.card C : ℚ) ^ Fintype.card Q ≤
      average (queryCost domain tree) * beta / (Fintype.card C : ℚ) ^ 2 := by
  classical
  let stateOff (p : Parent) (r : Response)
      (off : AwayFromTwo (parent p) (child p r) → C) : State :=
    state p ((splitTwo (C := C) (parent p) (child p r)
      (hdisjoint p p r)).symm
      (off, (Classical.choice inferInstance, Classical.choice inferInstance)))
  have hstateEq (p : Parent) (r : Response) (H : Q → C) :
      stateOff p r (fun z => H z.1) = state p H := by
    apply hstateOff p r
    intro z hx hy
    simp [splitTwo, hx, hy]
  have hpath (H : Q → C) :
      (∑ p : Parent, ∑ r : Response,
        if firstOfTwoOffResult tree (parent p) (child p r)
            (hdisjoint p p r) (fun z => H z.1) ≠ .neither then
          budget (state p H) p r else 0) ≤ queryCost domain tree H * beta :=
    tree_first_pair_grouped_domain_le tree domain parent child hparent hchild
      hdisjoint hpDomain hcDomain (fun p r => budget (state p H) p r) (fun p r => hnonneg (state p H) p r) beta hbeta
      (fun p => hsumBudget (state p H) p) H
  have h := charged_two_fresh_weight_expected_le
    (I := Parent × Response)
    (fun i => parent i.1) (fun i => child i.1 i.2)
    (fun i => hdisjoint i.1 i.1 i.2)
    (fun i off => firstOfTwoOffResult tree (parent i.1) (child i.1 i.2)
      (hdisjoint i.1 i.1 i.2) off ≠ .neither)
    (fun i off a b => weight (stateOff i.1 i.2 off) i.1 i.2 a b)
    (fun i off => budget (stateOff i.1 i.2 off) i.1 i.2)
    (fun H => queryCost domain tree H * beta)
    (fun i off => hlocal (stateOff i.1 i.2 off) i.1 i.2)
    (fun H => by
      simp only [Fintype.sum_prod_type]
      simp_rw [hstateEq]
      exact hpath H)
  simpa only [Fintype.sum_prod_type, hstateEq, average, ← sum_mul, div_mul_eq_mul_div] using h

theorem tree_two_scale_local_context_domain_le
    {Q C Out Parent Response State : Type}
    [Fintype Q] [DecidableEq Q] [Fintype C] [Nonempty C]
    [Fintype Parent] [Fintype Response] {N : ℕ}
    (tree : Tree Q C Out N) (domain : Finset Q)
    (parent : Parent → Q) (child : Parent → Response → Q)
    (hparent : Function.Injective parent)
    (hchild : Function.Injective
      (fun i : Parent × Response => child i.1 i.2))
    (hdisjoint : ∀ p p' r, parent p ≠ child p' r)
    (hpDomain : ∀ p, parent p ∈ domain)
    (hcDomain : ∀ p r, child p r ∈ domain)
    (state : Parent → (Q → C) → State)
    (hstateOff : ∀ p r (H H' : Q → C),
      (∀ z, z ≠ parent p → z ≠ child p r → H z = H' z) →
      state p H = state p H')
    (low high : State → Parent → Response → C → C → Prop)
    (betaLow betaHigh : ℚ)
    (hbetaLow : 0 ≤ betaLow) (hbetaHigh : 0 ≤ betaHigh)
    (hlow : ∀ s p r a,
      ∑ b : C, (if low s p r a b then (1 : ℚ) else 0) ≤
        Fintype.card C * betaLow)
    (hhigh : ∀ s p,
      ∑ r : Response, ∑ a : C, ∑ b : C,
        (if high s p r a b then (1 : ℚ) else 0) ≤
        (Fintype.card C : ℚ) ^ 2 * betaHigh) :
    (∑ H : Q → C, ∑ p : Parent, ∑ r : Response,
      ((if child p r ∈ queried tree H ∧
          low (state p H) p r (H (parent p)) (H (child p r)) then (1 : ℚ) else 0) +
      (if firstOfTwoOffResult tree (parent p) (child p r)
          (hdisjoint p p r) (fun z => H z.1) ≠ .neither ∧
          high (state p H) p r (H (parent p)) (H (child p r)) then (1 : ℚ) else 0))) /
        (Fintype.card C : ℚ) ^ Fintype.card Q ≤
      average (queryCost domain tree) * (betaLow + betaHigh) := by
  classical
  let q : ℚ := Fintype.card C
  have hq : 0 < q := by
    dsimp [q]
    exact_mod_cast Fintype.card_pos
  let lowWeight (i : Parent × Response) (H : Q → C) (b : C) : ℚ :=
    if low (state i.1 H) i.1 i.2 (H (parent i.1)) b then 1 else 0
  have hlowOff (i : Parent × Response) (H H' : Q → C)
      (h : AgreeOff (child i.1 i.2) H H') (b : C) :
      lowWeight i H b = lowWeight i H' b := by
    have hs : state i.1 H = state i.1 H' :=
      hstateOff i.1 i.2 H H' (fun z _ hz => h z hz)
    have hp : H (parent i.1) = H' (parent i.1) :=
      h (parent i.1) (hdisjoint i.1 i.1 i.2)
    simp [lowWeight, hs, hp]
  have hlowLocal (i : Parent × Response) (H : Q → C) :
      ∑ b : C, lowWeight i H b ≤ q * betaLow :=
    hlow (state i.1 H) i.1 i.2 (H (parent i.1))
  have hlowBound := tree_child_indexed_weight_domain_le tree domain
    (fun i : Parent × Response => child i.1 i.2)
    hchild (fun i => hcDomain i.1 i.2) lowWeight hlowOff (q * betaLow)
    (mul_nonneg hq.le hbetaLow) hlowLocal
  let highWeight (s : State) (p : Parent) (r : Response)
      (a b : C) : ℚ := if high s p r a b then 1 else 0
  let highBudget (s : State) (p : Parent) (r : Response) : ℚ :=
    ∑ a : C, ∑ b : C, highWeight s p r a b
  have hhighNonneg (s : State) (p : Parent) (r : Response) :
      0 ≤ highBudget s p r := by
    dsimp [highBudget, highWeight]
    apply Finset.sum_nonneg
    intro a _
    exact Finset.sum_nonneg fun b _ => by split_ifs <;> norm_num
  have hhighLocal (s : State) (p : Parent) (r : Response) :
      ∑ a : C, ∑ b : C, highWeight s p r a b ≤ highBudget s p r := le_refl _
  have hhighBudget (s : State) (p : Parent) :
      ∑ r : Response, highBudget s p r ≤ q ^ 2 * betaHigh := by
    simpa only [highBudget, highWeight, q] using hhigh s p
  have hhighBound := tree_both_orders_local_context_domain_le tree domain
    parent child hparent hchild hdisjoint hpDomain hcDomain state hstateOff
    highWeight highBudget hhighNonneg (q ^ 2 * betaHigh)
    (mul_nonneg (sq_nonneg q) hbetaHigh)
    hhighLocal hhighBudget
  have hlowBound' :
      (∑ H : Q → C, ∑ p : Parent, ∑ r : Response,
        if child p r ∈ queried tree H ∧
            low (state p H) p r (H (parent p)) (H (child p r)) then
          (1 : ℚ) else 0) / q ^ Fintype.card Q ≤ average (queryCost domain tree) * betaLow := by
    have h :
        (∑ H : Q → C, ∑ p : Parent, ∑ r : Response,
          if child p r ∈ queried tree H ∧
              low (state p H) p r (H (parent p)) (H (child p r)) then
            (1 : ℚ) else 0) / q ^ Fintype.card Q ≤
          average (queryCost domain tree) * (q * betaLow) / q := by
      simpa only [ite_and, Fintype.sum_prod_type, lowWeight, q]
        using hlowBound
    calc
      _ ≤ average (queryCost domain tree) * (q * betaLow) / q := h
      _ = average (queryCost domain tree) * betaLow := by field_simp [hq.ne']
  have hhighBound' :
      (∑ H : Q → C, ∑ p : Parent, ∑ r : Response,
        if firstOfTwoOffResult tree (parent p) (child p r)
            (hdisjoint p p r) (fun z => H z.1) ≠ .neither ∧
            high (state p H) p r (H (parent p)) (H (child p r)) then
          (1 : ℚ) else 0) / q ^ Fintype.card Q ≤ average (queryCost domain tree) * betaHigh := by
    have h :
        (∑ H : Q → C, ∑ p : Parent, ∑ r : Response,
          if firstOfTwoOffResult tree (parent p) (child p r)
              (hdisjoint p p r) (fun z => H z.1) ≠ .neither ∧
              high (state p H) p r (H (parent p)) (H (child p r)) then
            (1 : ℚ) else 0) / q ^ Fintype.card Q ≤
          average (queryCost domain tree) * (q ^ 2 * betaHigh) / q ^ 2 := by
      simpa only [ite_and, highWeight, q] using hhighBound
    calc
      _ ≤ average (queryCost domain tree) * (q ^ 2 * betaHigh) / q ^ 2 := h
      _ = average (queryCost domain tree) * betaHigh := by field_simp [hq.ne']
  calc
    _ = (∑ H : Q → C, ∑ p : Parent, ∑ r : Response,
          if child p r ∈ queried tree H ∧
              low (state p H) p r (H (parent p)) (H (child p r)) then
            (1 : ℚ) else 0) / q ^ Fintype.card Q +
        (∑ H : Q → C, ∑ p : Parent, ∑ r : Response,
          if firstOfTwoOffResult tree (parent p) (child p r)
              (hdisjoint p p r) (fun z => H z.1) ≠ .neither ∧
              high (state p H) p r (H (parent p)) (H (child p r)) then
            (1 : ℚ) else 0) / q ^ Fintype.card Q := by
          simp only [Finset.sum_add_distrib, add_div, q]
    _ ≤ average (queryCost domain tree) * betaLow + average (queryCost domain tree) * betaHigh :=
      add_le_add hlowBound' hhighBound'
    _ = average (queryCost domain tree) * (betaLow + betaHigh) := by ring

theorem tree_two_scale_local_context_final_domain_le
    {Q C Out Parent Response State : Type}
    [Fintype Q] [DecidableEq Q] [Fintype C] [Nonempty C]
    [Fintype Parent] [Fintype Response] {N : ℕ}
    (tree : Tree Q C Out N) (domain : Finset Q)
    (selected : Out → Parent × Response)
    (parent : Parent → Q) (child : Parent → Response → Q)
    (hparent : Function.Injective parent)
    (hchild : Function.Injective
      (fun i : Parent × Response => child i.1 i.2))
    (hdisjoint : ∀ p p' r, parent p ≠ child p' r)
    (hpDomain : ∀ p, parent p ∈ domain)
    (hcDomain : ∀ p r, child p r ∈ domain)
    (state : Parent → (Q → C) → State)
    (hstateOff : ∀ p r (H H' : Q → C),
      (∀ z, z ≠ parent p → z ≠ child p r → H z = H' z) →
      state p H = state p H')
    (low high : State → Parent → Response → C → C → Prop)
    (betaLow betaHigh : ℚ)
    (hbetaLow : 0 ≤ betaLow) (hbetaHigh : 0 ≤ betaHigh)
    (hlow : ∀ s p r a,
      ∑ b : C, (if low s p r a b then (1 : ℚ) else 0) ≤
        Fintype.card C * betaLow)
    (hhigh : ∀ s p,
      ∑ r : Response, ∑ a : C, ∑ b : C,
        (if high s p r a b then (1 : ℚ) else 0) ≤
        (Fintype.card C : ℚ) ^ 2 * betaHigh) :
    let failure := fun H : Q → C =>
      let i := selected (tree.run H).1
      low (state i.1 H) i.1 i.2 (H (parent i.1)) (H (child i.1 i.2)) ∨
      high (state i.1 H) i.1 i.2 (H (parent i.1)) (H (child i.1 i.2))
    ((univ.filter failure).card : ℚ) /
        (Fintype.card C : ℚ) ^ Fintype.card Q ≤
      (average (queryCost domain tree) + 1) * (betaLow + betaHigh) := by
  classical
  let point : Out → Q := fun out => child (selected out).1 (selected out).2
  let extended := appendFinalQuery tree point
  have hbound := tree_two_scale_local_context_domain_le extended domain
    parent child hparent hchild hdisjoint hpDomain hcDomain state hstateOff
    low high betaLow betaHigh
    hbetaLow hbetaHigh hlow hhigh
  have hpoint (H : Q → C) :
      (if (let i := selected (tree.run H).1;
            low (state i.1 H) i.1 i.2 (H (parent i.1)) (H (child i.1 i.2)) ∨
            high (state i.1 H) i.1 i.2 (H (parent i.1)) (H (child i.1 i.2)))
        then (1 : ℚ) else 0) ≤
      ∑ p : Parent, ∑ r : Response,
        ((if child p r ∈ queried extended H ∧
            low (state p H) p r (H (parent p)) (H (child p r)) then (1 : ℚ) else 0) +
        (if firstOfTwoOffResult extended (parent p) (child p r)
            (hdisjoint p p r) (fun z => H z.1) ≠ .neither ∧
            high (state p H) p r (H (parent p)) (H (child p r)) then (1 : ℚ) else 0)) := by
    let i := selected (tree.run H).1
    have hmem : child i.1 i.2 ∈ queried extended H :=
      appendFinalQuery_mem tree point H
    have hfirst : firstOfTwoOffResult extended (parent i.1) (child i.1 i.2)
        (hdisjoint i.1 i.1 i.2) (fun z => H z.1) ≠ .neither := by
      rw [firstOfTwoOff_eq]
      exact firstOfTwo_ne_neither_of_right_mem _ _ _ _ hmem
    change (if low (state i.1 H) i.1 i.2 (H (parent i.1)) (H (child i.1 i.2)) ∨
        high (state i.1 H) i.1 i.2 (H (parent i.1)) (H (child i.1 i.2)) then
        (1 : ℚ) else 0) ≤ _
    let wt : Parent → Response → ℚ := fun p r =>
      (if child p r ∈ queried extended H ∧
          low (state p H) p r (H (parent p)) (H (child p r)) then (1 : ℚ) else 0) +
      (if firstOfTwoOffResult extended (parent p) (child p r)
          (hdisjoint p p r) (fun z => H z.1) ≠ .neither ∧
          high (state p H) p r (H (parent p)) (H (child p r)) then (1 : ℚ) else 0)
    have hnonneg (p : Parent) (r : Response) :
        (0 : ℚ) ≤
        ((if child p r ∈ queried extended H ∧
            low (state p H) p r (H (parent p)) (H (child p r)) then (1 : ℚ) else 0) +
        (if firstOfTwoOffResult extended (parent p) (child p r)
            (hdisjoint p p r) (fun z => H z.1) ≠ .neither ∧
            high (state p H) p r (H (parent p)) (H (child p r)) then (1 : ℚ) else 0)) := by
      split_ifs <;> norm_num
    have hsingle :
        ((if child i.1 i.2 ∈ queried extended H ∧
            low (state i.1 H) i.1 i.2 (H (parent i.1)) (H (child i.1 i.2)) then (1 : ℚ) else 0) +
        (if firstOfTwoOffResult extended (parent i.1) (child i.1 i.2)
            (hdisjoint i.1 i.1 i.2) (fun z => H z.1) ≠ .neither ∧
            high (state i.1 H) i.1 i.2 (H (parent i.1)) (H (child i.1 i.2)) then (1 : ℚ) else 0)) ≤
        ∑ p : Parent, ∑ r : Response,
          ((if child p r ∈ queried extended H ∧
              low (state p H) p r (H (parent p)) (H (child p r)) then (1 : ℚ) else 0) +
          (if firstOfTwoOffResult extended (parent p) (child p r)
              (hdisjoint p p r) (fun z => H z.1) ≠ .neither ∧
              high (state p H) p r (H (parent p)) (H (child p r)) then (1 : ℚ) else 0)) := by
      change wt i.1 i.2 ≤ ∑ p : Parent, ∑ r : Response, wt p r
      calc
        _ ≤ ∑ r : Response, wt i.1 r :=
          Finset.single_le_sum (fun r _ => hnonneg i.1 r) (mem_univ i.2)
        _ ≤ ∑ p : Parent, ∑ r : Response, wt p r := by
          exact Finset.single_le_sum
            (s := univ) (f := fun p : Parent => ∑ r : Response, wt p r)
            (fun p _ => Finset.sum_nonneg (fun r _ => hnonneg p r))
            (mem_univ i.1)
    by_cases hlo : low (state i.1 H) i.1 i.2 (H (parent i.1)) (H (child i.1 i.2))
    · have hchoice : (1 : ℚ) ≤
        (if low (state i.1 H) i.1 i.2 (H (parent i.1)) (H (child i.1 i.2)) then 1 else 0) +
        (if firstOfTwoOffResult extended (parent i.1) (child i.1 i.2)
            (hdisjoint i.1 i.1 i.2) (fun z => H z.1) ≠ .neither ∧
            high (state i.1 H) i.1 i.2 (H (parent i.1)) (H (child i.1 i.2)) then 1 else 0) := by
          simp only [if_pos hlo]
          split_ifs <;> norm_num
      simpa only [hlo, true_or, ite_true] using hchoice.trans (by
        simpa only [hmem, true_and] using hsingle)
    · by_cases hhi : high (state i.1 H) i.1 i.2 (H (parent i.1)) (H (child i.1 i.2))
      · have hchoice : (1 : ℚ) ≤
          (if child i.1 i.2 ∈ queried extended H ∧
              low (state i.1 H) i.1 i.2 (H (parent i.1)) (H (child i.1 i.2)) then 1 else 0) +
          (if firstOfTwoOffResult extended (parent i.1) (child i.1 i.2)
              (hdisjoint i.1 i.1 i.2) (fun z => H z.1) ≠ .neither ∧
              high (state i.1 H) i.1 i.2 (H (parent i.1)) (H (child i.1 i.2)) then 1 else 0) := by
          simp [hlo, hhi, hfirst]
        simpa only [hlo, hhi, false_or, ite_true] using hchoice.trans hsingle
      · simp [i, hlo, hhi]
        exact Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun r _ => hnonneg p r
  have hq : (0 : ℚ) < (Fintype.card C : ℚ) ^ Fintype.card Q := by positivity
  calc
    ((univ.filter (fun H : Q → C =>
        let i := selected (tree.run H).1;
        low (state i.1 H) i.1 i.2 (H (parent i.1)) (H (child i.1 i.2)) ∨
        high (state i.1 H) i.1 i.2 (H (parent i.1)) (H (child i.1 i.2)))).card : ℚ) /
        (Fintype.card C : ℚ) ^ Fintype.card Q
      = (∑ H : Q → C, if (let i := selected (tree.run H).1;
          low (state i.1 H) i.1 i.2 (H (parent i.1)) (H (child i.1 i.2)) ∨
          high (state i.1 H) i.1 i.2 (H (parent i.1)) (H (child i.1 i.2))) then (1 : ℚ) else 0) /
          (Fintype.card C : ℚ) ^ Fintype.card Q := by
            simp only [Finset.card_filter, Nat.cast_sum, Nat.cast_ite, Nat.cast_one,
              Nat.cast_zero]
    _ ≤ (∑ H : Q → C, ∑ p : Parent, ∑ r : Response,
          ((if child p r ∈ queried extended H ∧
              low (state p H) p r (H (parent p)) (H (child p r)) then (1 : ℚ) else 0) +
          (if firstOfTwoOffResult extended (parent p) (child p r)
              (hdisjoint p p r) (fun z => H z.1) ≠ .neither ∧
              high (state p H) p r (H (parent p)) (H (child p r)) then (1 : ℚ) else 0))) /
          (Fintype.card C : ℚ) ^ Fintype.card Q := by
            exact div_le_div_of_nonneg_right (Finset.sum_le_sum fun H _ => hpoint H) hq.le
    _ ≤ (average (queryCost domain tree) + 1) * (betaLow + betaHigh) := by
      apply hbound.trans
      apply mul_le_mul_of_nonneg_right _ (add_nonneg hbetaLow hbetaHigh)
      have h := average_mono (fun H : Q → C => queryCost_append_le domain tree point H)
      simpa only [average_add, average_const] using h

end Bcs.TotalOracle
