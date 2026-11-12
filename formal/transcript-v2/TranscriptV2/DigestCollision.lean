import TranscriptV2.DigestCharging

/-! Birthday counting on the actual adaptive query set. Repeated queries
reuse their answer and do not create additional collision opportunities.
The projected version also covers grouped digest/challenge answers. A fixed
domain restriction can exclude PRF inputs without hiding any of their answers
from the program. This lets strand and Merkle inputs share one allowance. -/
namespace TranscriptV2.DigestCollision
open Finset Bcs.TotalOracle Merkle.RandomOracle
open scoped Classical

variable {P A D Out : Type} [DecidableEq P]

private theorem not_before_self {fuel : ℕ} (tree : Tree P A Out fuel)
    (H : P → A) (p : P) : p ∉ before tree H p := by
  induction tree with
  | done _ => simp [before]
  | query q next ih =>
      by_cases h : q = p
      · simp [before,h]
      · simp [before,h,Ne.symm h,ih]

private theorem before_asymm {fuel : ℕ} (tree : Tree P A Out fuel)
    (H : P → A) (p q : P) (hp : p ∈ before tree H q) : q ∉ before tree H p := by
  induction tree with
  | done _ => simp [before] at hp
  | query r next ih =>
      by_cases hrp : r = p
      · subst r
        simp [before]
      · by_cases hrq : r = q
        · simp [before,hrq] at hp
        · have ht : p ∈ before (next (H r)) H q := by
            simpa [before,hrq,Ne.symm hrp] using hp
          simpa [before,hrp,Ne.symm hrq] using ih (H r) ht

private noncomputable def pairs (eligible : P → Prop) {fuel : ℕ} (tree : Tree P A Out fuel) (H : P → A) : Finset (P × P) :=
  ((seen tree H).filter eligible).biUnion fun p =>
    ((before tree H p).toFinset.filter eligible).image fun q => (q,p)

private theorem mem_pairs (eligible : P → Prop) {fuel : ℕ} (tree : Tree P A Out fuel) (H : P → A) (p q : P) :
    (p,q) ∈ pairs eligible tree H ↔ q ∈ (seen tree H).filter eligible ∧
      p ∈ (before tree H q).toFinset.filter eligible := by
  simp [pairs]

private theorem pairs_card (eligible : P → Prop) {fuel : ℕ} (tree : Tree P A Out fuel) (H : P → A) :
    (pairs eligible tree H).card = ∑ p ∈ (seen tree H).filter eligible,
      ((before tree H p).toFinset.filter eligible).card := by
  have disjoint : (((seen tree H).filter eligible) : Set P).PairwiseDisjoint
      (fun p => ((before tree H p).toFinset.filter eligible).image fun q => (q,p)) := by
    intro p _ q _ hne
    apply disjoint_left.mpr
    intro x hx hy
    obtain ⟨a,_,ha⟩ := mem_image.mp hx
    obtain ⟨b,_,hb⟩ := mem_image.mp hy
    exact hne (congrArg Prod.snd (ha.trans hb.symm))
  rw [pairs,card_biUnion disjoint]
  apply sum_congr rfl
  intro p _
  exact card_image_of_injective _ (fun _ _ h => congrArg Prod.fst h)

/-- Every unordered pair can occur in only one temporal direction. This
gives the sharp triangular count without imposing an order on the adversary. -/
theorem sum_before_within_card_le [Fintype P] (eligible : P → Prop) {fuel S : ℕ}
    (tree : Tree P A Out fuel) (H : P → A) (budget : ((seen tree H).filter eligible).card ≤ S) :
    (∑ p ∈ (seen tree H).filter eligible,
      ((before tree H p).toFinset.filter eligible).card) ≤ S*(S-1)/2 := by
  let earlier := pairs eligible tree H
  have hdisjoint : Disjoint earlier (earlier.image Prod.swap) := by
    apply disjoint_left.mpr
    intro x hx hy
    obtain ⟨y,hy,heq⟩ := mem_image.mp hy
    have hx' := (mem_pairs eligible tree H x.1 x.2).mp hx
    have hy' := (mem_pairs eligible tree H y.1 y.2).mp hy
    have hs : y = x.swap := by
      have := congrArg Prod.swap heq
      simpa using this
    subst y
    exact before_asymm tree H x.1 x.2
      (List.mem_toFinset.mp (mem_filter.mp hx'.2).1)
      (List.mem_toFinset.mp (mem_filter.mp hy'.2).1)
  have subset : earlier ∪ earlier.image Prod.swap ⊆ ((seen tree H).filter eligible).offDiag := by
    intro x hx
    have one {y : P × P} (hy : y ∈ earlier) : y ∈ ((seen tree H).filter eligible).offDiag := by
      obtain ⟨hq,hp⟩ := (mem_pairs eligible tree H y.1 y.2).mp hy
      obtain ⟨hp,ep⟩ := mem_filter.mp hp
      have hp := List.mem_toFinset.mp hp
      refine mem_offDiag.mpr ⟨?_,hq,?_⟩
      · exact mem_filter.mpr ⟨List.mem_toFinset.mpr (before_subset tree H y.2 hp),ep⟩
      · intro heq
        rw [heq] at hp
        exact not_before_self tree H y.2 hp
    rcases mem_union.mp hx with hx | hx
    · exact one hx
    · obtain ⟨y,hy,rfl⟩ := mem_image.mp hx
      have h := mem_offDiag.mp (one hy)
      exact mem_offDiag.mpr ⟨h.2.1,h.1,Ne.symm h.2.2⟩
  have twice : 2*earlier.card ≤ ((seen tree H).filter eligible).card*
      (((seen tree H).filter eligible).card-1) := by
    have hc := card_le_card subset
    rw [card_union_of_disjoint hdisjoint,card_image_of_injective _ Prod.swap_injective,
      offDiag_card] at hc
    simpa only [two_mul,Nat.mul_sub_left_distrib,Nat.mul_one] using hc
  rw [← pairs_card eligible tree H]
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 2)).mpr
  calc
    (pairs eligible tree H).card*2 = 2*earlier.card := by simp only [earlier,Nat.mul_comm]
    _ ≤ ((seen tree H).filter eligible).card*(((seen tree H).filter eligible).card-1) := twice
    _ ≤ S*(S-1) := Nat.mul_le_mul budget (Nat.sub_le_sub_right budget 1)

/-- Counting all query inputs is the unrestricted case. -/
theorem sum_before_card_le [Fintype P] {fuel S : ℕ} (tree : Tree P A Out fuel)
    (H : P → A) (budget : (seen tree H).card ≤ S) :
    (∑ p ∈ seen tree H, (before tree H p).toFinset.card) ≤ S*(S-1)/2 := by
  simpa using sum_before_within_card_le (fun _ => True) tree H (by simpa using budget)

def Collision (project : A → D) {fuel : ℕ} (tree : Tree P A Out fuel) (H : P → A) : Prop :=
  ∃ p ∈ seen tree H, ∃ q ∈ seen tree H, p ≠ q ∧ project (H p) = project (H q)

def CollisionWithin (eligible : P → Prop) (project : A → D) {fuel : ℕ}
    (tree : Tree P A Out fuel) (H : P → A) : Prop :=
  ∃ p ∈ (seen tree H).filter eligible, ∃ q ∈ (seen tree H).filter eligible,
    p ≠ q ∧ project (H p) = project (H q)

private def bad (eligible : P → Prop) (project : A → D) {fuel : ℕ} (tree : Tree P A Out fuel)
    (p : P) (H : P → A) (answer : A) : Prop :=
  p ∈ (seen tree H).filter eligible ∧
    ∃ q ∈ (before tree H p).toFinset.filter eligible, project answer = project (H q)

/-- Uniform digest fibers suffice even when each oracle answer also exposes
an arbitrary challenge block. The whole grouped answer remains in the trace,
including answers at inputs outside the selected collision domain. -/
theorem projected_within_ratio_le [Fintype P] [Fintype A] [Nonempty A] [Fintype D] [Nonempty D]
    {fuel S : ℕ} (eligible : P → Prop) (project : A → D) (fiber : ℕ)
    (fibers : ∀ d, (univ.filter fun a => project a = d).card = fiber)
    (cardinality : Fintype.card A = Fintype.card D*fiber)
    (tree : Tree P A Out fuel) (budget : ∀ H, ((seen tree H).filter eligible).card ≤ S) :
    ((univ.filter (CollisionWithin eligible project tree)).card : ℚ) /
        (Fintype.card A : ℚ)^Fintype.card P ≤ ((S*(S-1)/2 : ℕ) : ℚ)/Fintype.card D := by
  let weight := fun p H =>
    (if p ∈ (seen tree H).filter eligible then ((before tree H p).toFinset.filter eligible).card else 0)*fiber
  have off p (H H' : P → A) (h : AgreeOff p H H') a :
      bad eligible project tree p H a → bad eligible project tree p H' a := by
    rintro ⟨hp,q,hq,heq⟩
    have hqp : q ≠ p := by
      intro same
      subst q
      exact not_before_self tree H p (List.mem_toFinset.mp (mem_filter.mp hq).1)
    refine ⟨?_,q,?_,heq.trans (congrArg project (h q hqp))⟩
    · exact mem_filter.mpr ⟨List.mem_toFinset.mpr
        ((mem_queried_iff tree p h).mp (List.mem_toFinset.mp (mem_filter.mp hp).1)),(mem_filter.mp hp).2⟩
    · rwa [← before_congr tree p h]
  have localBound p H : (univ.filter (bad eligible project tree p H)).card ≤ weight p H := by
    by_cases hp : p ∈ (seen tree H).filter eligible
    · have pieces : univ.filter (bad eligible project tree p H) =
          ((before tree H p).toFinset.filter eligible).biUnion fun q =>
            univ.filter fun a => project a = project (H q) := by
        ext a
        simp [bad,hp]
      rw [pieces]
      apply card_biUnion_le.trans
      simp only [fibers,sum_const,nsmul_eq_mul,weight,hp,if_pos]
      exact le_rfl
    · simp [bad,weight,hp]
  have total H : ∑ p, weight p H ≤ S*(S-1)/2*fiber := by
    have sumWeight : (∑ p, weight p H) =
        (∑ p ∈ (seen tree H).filter eligible, ((before tree H p).toFinset.filter eligible).card)*fiber := by
      simp only [weight,← sum_mul]
      congr 1
      rw [← sum_filter]
      simp only [filter_mem_eq_inter,univ_inter]
    rw [sumWeight]
    exact Nat.mul_le_mul_right fiber (sum_before_within_card_le eligible tree H (budget H))
  have cover H (hc : CollisionWithin eligible project tree H) : ∃ p, bad eligible project tree p H (H p) := by
    obtain ⟨p,hp,q,hq,hne,heq⟩ := hc
    rcases DigestCharging.before_total tree H p q (mem_filter.mp hp).1 (mem_filter.mp hq).1 hne with hpq | hqp
    · exact ⟨q,hq,p,mem_filter.mpr ⟨List.mem_toFinset.mpr hpq,(mem_filter.mp hp).2⟩,heq.symm⟩
    · exact ⟨p,hp,q,mem_filter.mpr ⟨List.mem_toFinset.mpr hqp,(mem_filter.mp hq).2⟩,heq⟩
  have count := ratio_exists_coord_le (CollisionWithin eligible project tree) (bad eligible project tree) cover off
    weight localBound (S*(S-1)/2*fiber) total
  have fiberPos : 0 < fiber := by
    have positive : 0 < Fintype.card A := Fintype.card_pos
    rw [cardinality] at positive
    apply Nat.pos_of_ne_zero
    intro zero
    simp only [zero,Nat.mul_zero] at positive
    omega
  apply count.trans_eq
  rw [cardinality]
  simp only [Nat.cast_mul]
  exact mul_div_mul_right _ _ (by exact_mod_cast Nat.ne_of_gt fiberPos)

/-- The unrestricted result retains its original interface. -/
theorem projected_ratio_le [Fintype P] [Fintype A] [Nonempty A] [Fintype D] [Nonempty D]
    {fuel S : ℕ} (project : A → D) (fiber : ℕ)
    (fibers : ∀ d, (univ.filter fun a => project a = d).card = fiber)
    (cardinality : Fintype.card A = Fintype.card D*fiber)
    (tree : Tree P A Out fuel) (budget : ∀ H, (seen tree H).card ≤ S) :
    ((univ.filter (Collision project tree)).card : ℚ) /
        (Fintype.card A : ℚ)^Fintype.card P ≤ ((S*(S-1)/2 : ℕ) : ℚ)/Fintype.card D := by
  simpa only [CollisionWithin,Collision,filter_true] using
    projected_within_ratio_le (fun _ => True) project fiber fibers cardinality tree (by simpa using budget)

/-- Only the fixed domain selected by `eligible` contributes collision
pairs. Queries in every other domain remain available to the adaptive
program, including their answers and their effect on later query choices. -/
theorem within_ratio_le [Fintype P] [Fintype D] [Nonempty D] {fuel S : ℕ}
    (eligible : P → Prop) (tree : Tree P D Out fuel)
    (budget : ∀ H, ((seen tree H).filter eligible).card ≤ S) :
    ((univ.filter (CollisionWithin eligible id tree)).card : ℚ) /
        (Fintype.card D : ℚ)^Fintype.card P ≤ ((S*(S-1)/2 : ℕ) : ℚ)/Fintype.card D := by
  apply projected_within_ratio_le eligible id 1 ?_ (by simp) tree budget
  intro d
  apply card_eq_one.mpr
  refine ⟨d,?_⟩
  ext x
  simp

/-- The standard birthday bound for distinct adaptive random-oracle queries. -/
theorem ratio_le [Fintype P] [Fintype D] [Nonempty D] {fuel S : ℕ}
    (tree : Tree P D Out fuel) (budget : ∀ H, (seen tree H).card ≤ S) :
    ((univ.filter (Collision id tree)).card : ℚ) /
        (Fintype.card D : ℚ)^Fintype.card P ≤ ((S*(S-1)/2 : ℕ) : ℚ)/Fintype.card D := by
  simpa only [CollisionWithin,Collision,filter_true] using
    within_ratio_le (fun _ => True) tree (by simpa using budget)

/-- Exposing challenges alongside each digest does not alter its birthday
bound. No conditioning on, or deletion of, those challenge observations is used. -/
theorem first_ratio_le [Fintype P] [Fintype D] [Nonempty D] [Fintype A] [Nonempty A]
    {fuel S : ℕ} (tree : Tree P (D × A) Out fuel) (budget : ∀ H, (seen tree H).card ≤ S) :
    ((univ.filter (Collision Prod.fst tree)).card : ℚ) /
        (Fintype.card (D × A) : ℚ)^Fintype.card P ≤ ((S*(S-1)/2 : ℕ) : ℚ)/Fintype.card D := by
  apply projected_ratio_le Prod.fst (Fintype.card A) ?_ (Fintype.card_prod D A) tree budget
  intro d
  have pieces : (univ.filter fun a : D × A => a.1 = d) = {d} ×ˢ (univ : Finset A) := by
    ext ⟨x,y⟩
    simp [eq_comm]
  rw [pieces,card_product,card_singleton,card_univ,one_mul]

end TranscriptV2.DigestCollision
