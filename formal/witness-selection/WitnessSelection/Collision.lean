import WitnessSelection.Algebra
import Mathlib.Data.Finset.Powerset

/-! Collision counts and unique selection used by the Fiat–Shamir analysis. -/

namespace WitnessSelection
open Finset
open scoped Classical

variable {F ι : Type} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [DecidableEq ι]

def collisionCoins (x y : Candidate F ι) : Finset (Coins F ι) :=
  univ.filter fun a => fingerprint a x = fingerprint a y

/-- Each row fixes one independent coefficient when original witnesses differ.
Dedicated masks add offsets; they do not enter either random coefficient vector. -/
theorem pair_collision_card_mul_le (x y : Candidate F ι) (hne : x ≠ y) :
    (collisionCoins x y).card * Fintype.card F ^ 2 ≤ Fintype.card (Coins F ι) := by
  by_cases hv : x.1 = y.1
  · have hz : collisionCoins x y = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro a ha
      exact hne (same_data_collision a x y hv (mem_filter.mp ha).2)
    simp [hz]
  · obtain ⟨p,hp⟩ : ∃ p, x.1 p ≠ y.1 p := by
      by_contra h
      apply hv
      funext p
      by_contra hp
      exact h ⟨p,hp⟩
    let Free := {i : ι // i ≠ p} → F
    let restrict : {a : Coins F ι // a ∈ collisionCoins x y} → Free × Free :=
      fun a => (fun i => a.1.1 i.1, fun i => a.1.2 i.1)
    have hinj : Function.Injective restrict := by
      intro a b hab
      apply Subtype.ext
      have ha := collision_dot a.1 x y (mem_filter.mp a.2).2
      have hb := collision_dot b.1 x y (mem_filter.mp b.2).2
      apply Prod.ext
      · exact dot_eq_of_restriction (x.1-y.1) _ p (sub_ne_zero.mpr hp)
          ha.1 hb.1 (fun i hi => congrFun (congrArg Prod.fst hab) ⟨i,hi⟩)
      · exact dot_eq_of_restriction (x.1-y.1) _ p (sub_ne_zero.mpr hp)
          ha.2 hb.2 (fun i hi => congrFun (congrArg Prod.snd hab) ⟨i,hi⟩)
    have hc := Fintype.card_le_of_injective restrict hinj
    have hc' : (collisionCoins x y).card ≤ Fintype.card Free ^ 2 := by
      simpa [Fintype.card_subtype, pow_two] using hc
    calc
      (collisionCoins x y).card * Fintype.card F ^ 2
          ≤ Fintype.card Free ^ 2 * Fintype.card F ^ 2 := Nat.mul_le_mul_right _ hc'
      _ = Fintype.card (Coins F ι) := by rw [coins_card_split p]; dsimp [Free]; ring

def pairEvent (s : Finset (Candidate F ι)) (a : Coins F ι) : Prop :=
  ∃ x ∈ s, ∃ y ∈ s, x ≠ y ∧ fingerprint a x = fingerprint a y

noncomputable def badCoins (s : Finset (Candidate F ι)) : Finset (Coins F ι) :=
  univ.filter (pairEvent s)

omit [Fintype F] [DecidableEq ι] in
theorem pair_event_two (x y : Candidate F ι) (hne : x ≠ y) (a : Coins F ι) :
    pairEvent {x,y} a ↔ fingerprint a x = fingerprint a y := by
  simp [pairEvent, hne, hne.symm, eq_comm]

theorem list_collision_card_mul_le (s : Finset (Candidate F ι)) :
    (badCoins s).card * Fintype.card F ^ 2 ≤
      s.card.choose 2 * Fintype.card (Coins F ι) := by
  have hcover : badCoins s ⊆ (s.powersetCard 2).biUnion fun p => univ.filter (pairEvent p) := by
    intro a ha
    obtain ⟨x,hx,y,hy,hne,hxy⟩ := (mem_filter.mp ha).2
    apply mem_biUnion.mpr
    refine ⟨{x,y}, mem_powersetCard.mpr ⟨?_, by simp [hne]⟩, ?_⟩
    · exact insert_subset hx (singleton_subset_iff.mpr hy)
    · exact mem_filter.mpr ⟨mem_univ _, (pair_event_two x y hne a).mpr hxy⟩
  have hlocal (p : Finset (Candidate F ι)) (hp : p ∈ s.powersetCard 2) :
      (univ.filter (pairEvent p)).card * Fintype.card F ^ 2 ≤ Fintype.card (Coins F ι) := by
    obtain ⟨x,y,hne,rfl⟩ := card_eq_two.mp (mem_powersetCard.mp hp).2
    simpa only [pair_event_two x y hne, collisionCoins] using pair_collision_card_mul_le x y hne
  calc
    (badCoins s).card * Fintype.card F ^ 2 ≤
        (∑ p ∈ s.powersetCard 2, (univ.filter (pairEvent p)).card) * Fintype.card F ^ 2 :=
      Nat.mul_le_mul_right _ ((card_le_card hcover).trans card_biUnion_le)
    _ = ∑ p ∈ s.powersetCard 2, (univ.filter (pairEvent p)).card * Fintype.card F ^ 2 := by rw [sum_mul]
    _ ≤ ∑ _p ∈ s.powersetCard 2, Fintype.card (Coins F ι) := sum_le_sum hlocal
    _ = s.card.choose 2 * Fintype.card (Coins F ι) := by simp

/-- Responses may be selected after both coefficient vectors. Outside the
collision event, any response pair matches at most one committed candidate. -/
theorem unique_matching_candidate (s : Finset (Candidate F ι)) (a : Coins F ι)
    (hgood : a ∉ badCoins s) (t : F × F) (x y : Candidate F ι)
    (hx : x ∈ s) (hy : y ∈ s) (hxt : fingerprint a x = t)
    (hyt : fingerprint a y = t) : x = y := by
  by_contra hne
  exact hgood (mem_filter.mpr ⟨mem_univ _, x, hx, y, hy, hne, hxt.trans hyt.symm⟩)

noncomputable def select (s : Finset (Candidate F ι)) (a : Coins F ι) (t : F × F) :
    Option (Candidate F ι) :=
  if h : ∃ w ∈ s, fingerprint a w = t then some h.choose else none

omit [Fintype F] [DecidableEq ι] in
/-- Selection only returns a member satisfying the early responses. This is
an analysis-level selection function, not an executable decoder. -/
theorem select_valid (s : Finset (Candidate F ι)) (a : Coins F ι) (t : F × F)
    (w : Candidate F ι) (h : select s a t = some w) :
    w ∈ s ∧ fingerprint a w = t := by
  unfold select at h
  split_ifs at h with hm
  cases Option.some.inj h
  exact hm.choose_spec

theorem select_of_match (s : Finset (Candidate F ι)) (a : Coins F ι) (t : F × F)
    (hgood : a ∉ badCoins s) (w : Candidate F ι)
    (hw : w ∈ s) (hwt : fingerprint a w = t) : select s a t = some w := by
  have h : ∃ w ∈ s, fingerprint a w = t := ⟨w,hw,hwt⟩
  rw [select, dif_pos h]
  have heq := unique_matching_candidate s a hgood t h.choose w
    h.choose_spec.1 hw h.choose_spec.2 hwt
  rw [heq]

/-- The chosen witness is a function of the commitment-fixed list, the early
coefficients and responses; the later frontend challenge is not an argument. -/
theorem selected_frontend_decomposition (s : Finset (Candidate F ι)) (a : Coins F ι)
    (t : F × F) (Bad : Candidate F ι → Prop)
    (h : ∃ w ∈ s, fingerprint a w = t ∧ Bad w) :
    a ∈ badCoins s ∨ ∃ w, select s a t = some w ∧ Bad w := by
  by_cases hg : a ∈ badCoins s
  · exact Or.inl hg
  · obtain ⟨w,hw,hwt,hbad⟩ := h
    exact Or.inr ⟨w,select_of_match s a t hg w hw hwt,hbad⟩

/-- There is no candidate-list multiplier on a later challenge's local bound
once the early responses identify a unique projected witness. -/
theorem selected_bad_card_le {C : Type} [Fintype C]
    (s : Finset (Candidate F ι)) (a : Coins F ι) (t : F × F)
    (hgood : a ∉ badCoins s) (Bad : Candidate F ι → C → Prop) (β : ℕ)
    (hlocal : ∀ w ∈ s, fingerprint a w = t → (univ.filter (Bad w)).card ≤ β) :
    (univ.filter fun c => ∃ w ∈ s, fingerprint a w = t ∧ Bad w c).card ≤ β := by
  by_cases hm : ∃ w ∈ s, fingerprint a w = t
  · obtain ⟨w,hw,hwt⟩ := hm
    apply (card_le_card (show (univ.filter fun c => ∃ v ∈ s, fingerprint a v = t ∧ Bad v c) ⊆
        univ.filter (Bad w) from ?_)).trans (hlocal w hw hwt)
    intro c hc
    obtain ⟨v,hv,hvt,hbad⟩ := (mem_filter.mp hc).2
    have heq := unique_matching_candidate s a hgood t v w hv hw hvt hwt
    exact mem_filter.mpr ⟨mem_univ _, by simpa [heq] using hbad⟩
  · have hz : (univ.filter fun c => ∃ w ∈ s, fingerprint a w = t ∧ Bad w c) = ∅ := by
      apply eq_empty_iff_forall_notMem.mpr
      intro c hc
      obtain ⟨w,hw,hwt,_⟩ := (mem_filter.mp hc).2
      exact hm ⟨w,hw,hwt⟩
    rw [hz]
    exact Nat.zero_le β

end WitnessSelection
