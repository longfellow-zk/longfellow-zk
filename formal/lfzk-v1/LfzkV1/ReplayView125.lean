import Bcs.TotalOracle

/-!
# The unseen coordinates after replay lookups

Fixing the adversary's run and the answers to lookups determined by its
output leaves the other coordinates of a total random oracle free.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace LfzkV1.ReplayView125

open Bcs.TotalOracle Merkle.RandomOracle

variable {Q C Out : Type} {fuel : ℕ}

def view (tree : Tree Q C Out fuel) (lookups : Out → List Q) (H : Q → C) :
    (Out × List (Q × C)) × List C :=
  let run := tree.run H
  (run, (lookups run.1).map H)

def revealed (tree : Tree Q C Out fuel) (lookups : Out → List Q) (H : Q → C) : List Q :=
  queried tree H ++ lookups (tree.run H).1

theorem view_eq_iff (tree : Tree Q C Out fuel) (lookups : Out → List Q) (H H' : Q → C) :
    view tree lookups H' = view tree lookups H ↔
      ∀ x ∈ revealed tree lookups H, H' x = H x := by
  constructor
  · intro h x hx
    have hrun := congrArg Prod.fst h
    have hlookup := congrArg Prod.snd h
    change tree.run H' = tree.run H at hrun
    change (lookups (tree.run H').1).map H' = (lookups (tree.run H).1).map H at hlookup
    rw [hrun] at hlookup
    rcases List.mem_append.mp hx with hq | hl
    · obtain ⟨entry, hentry, hpoint⟩ := List.mem_map.mp hq
      have he := Tree.trace_sound tree H entry hentry
      rw [← hrun] at hentry
      rw [← hpoint]
      exact (Tree.trace_sound tree H' entry hentry).symm.trans he
    · exact (List.map_inj_left.mp hlookup) x hl
  · intro h
    have hrun : tree.run H' = tree.run H := Tree.run_congr_on_trace tree H H' fun entry hentry => by
      rw [h _ (List.mem_append_left _ (List.mem_map.mpr ⟨entry, hentry, rfl⟩))]
      exact (Tree.trace_sound tree H entry hentry).symm
    unfold view
    rw [hrun]
    exact congrArg (Prod.mk (tree.run H)) (List.map_inj_left.mpr fun x hx =>
      h x (List.mem_append_right (queried tree H) hx))

/-- Every completion of the unseen coordinates occurs exactly once in its
view fiber. The lookups may repeat points or reuse queries of the adversary. -/
noncomputable def viewFiberEquiv (tree : Tree Q C Out fuel) (lookups : Out → List Q)
    (H : Q → C) :
    {H' : Q → C // view tree lookups H' = view tree lookups H} ≃
      ({x : Q // x ∉ revealed tree lookups H} → C) := by
  classical
  refine {
    toFun := fun H' x => H'.val x.val
    invFun := fun rest => ⟨fun x => if h : x ∈ revealed tree lookups H then H x else rest ⟨x, h⟩,
      (view_eq_iff tree lookups H _).mpr fun x hx => dif_pos hx⟩
    left_inv := ?_
    right_inv := ?_ }
  · intro H'
    apply Subtype.ext
    funext x
    by_cases hx : x ∈ revealed tree lookups H
    · exact (dif_pos hx).trans ((view_eq_iff tree lookups H _).mp H'.property x hx).symm
    · exact dif_neg hx
  · intro rest
    funext x
    exact dif_neg x.property

section Counting

open Finset
attribute [local instance 10000] Classical.propDecidable

private theorem sum_view_card {Sample View : Type} [Fintype Sample] [DecidableEq View]
    (observe : Sample → View) (p : Sample → Prop) :
    (∑ v ∈ univ.image observe, ((univ.filter fun s => observe s = v ∧ p s).card : ℚ)) =
      (univ.filter p).card := by
  have hmem : ∀ s ∈ univ.filter p, observe s ∈ univ.image observe :=
    fun s _ => mem_image.mpr ⟨s, mem_univ _, rfl⟩
  rw [card_eq_sum_card_fiberwise hmem, Nat.cast_sum]
  apply sum_congr rfl
  intro v _
  have he : (univ.filter fun s => observe s = v ∧ p s) =
      (univ.filter p).filter fun s => observe s = v := by
    ext s
    simp [and_comm]
  rw [he]

/-- A replay-density bound on the still-uncovered part of nonidentity
views and a survival bound on identity views give one unconditional count. -/
theorem card_le_of_view_split {Sample View : Type} [Fintype Sample] [DecidableEq View]
    (observe : Sample → View) (identityView : View → Prop)
    (event covered : Sample → Prop) (error survival : ℚ)
    (herr : 0 ≤ error) (hsurv : 0 < survival) (hsurv₁ : survival ≤ 1)
    (herror : ∀ v ∈ univ.image observe, ¬ identityView v →
      ((univ.filter fun s => observe s = v ∧ event s ∧ ¬ covered s).card : ℚ) ≤
        error * (univ.filter fun s => observe s = v).card)
    (hcover : ∀ v ∈ univ.image observe, identityView v →
      survival * (univ.filter fun s => observe s = v ∧ event s).card ≤
        ((univ.filter fun s => observe s = v ∧ covered s).card : ℚ)) :
    ((univ.filter event).card : ℚ) ≤ error * Fintype.card Sample +
      ((univ.filter covered).card : ℚ) / survival := by
  have hsize :
      (∑ v ∈ univ.image observe, ((univ.filter fun s => observe s = v).card : ℚ)) =
        Fintype.card Sample := by
    simpa using sum_view_card observe (fun _ => True)
  rw [← sum_view_card observe event, ← sum_view_card observe covered, ← hsize,
    Finset.mul_sum, div_eq_mul_inv, Finset.sum_mul, ← Finset.sum_add_distrib]
  apply sum_le_sum
  intro v hv
  by_cases hi : identityView v
  · have h := (le_div_iff₀ hsurv).mpr (by simpa only [mul_comm] using hcover v hv hi)
    rw [div_eq_mul_inv] at h
    exact h.trans (le_add_of_nonneg_left (mul_nonneg herr (Nat.cast_nonneg _)))
  · let unseen := univ.filter fun s => observe s = v ∧ event s ∧ ¬ covered s
    let seen := univ.filter fun s => observe s = v ∧ covered s
    have hsub : (univ.filter fun s => observe s = v ∧ event s) ⊆ unseen ∪ seen := by
      intro s hs
      obtain ⟨hview, he⟩ := (mem_filter.mp hs).2
      by_cases hc : covered s
      · exact mem_union_right _ (mem_filter.mpr ⟨mem_univ _, hview, hc⟩)
      · exact mem_union_left _ (mem_filter.mpr ⟨mem_univ _, hview, he, hc⟩)
    have hcard : ((univ.filter fun s => observe s = v ∧ event s).card : ℚ) ≤
        (unseen.card : ℚ) + seen.card := by
      exact_mod_cast (card_le_card hsub).trans (card_union_le _ _)
    have hs : (seen.card : ℚ) ≤ (seen.card : ℚ) * survival⁻¹ := by
      rw [← div_eq_mul_inv, le_div_iff₀ hsurv]
      exact mul_le_of_le_one_right (Nat.cast_nonneg _) hsurv₁
    exact hcard.trans (add_le_add (herror v hv hi) hs)

end Counting

section Hidden

open Finset
attribute [local instance 10000] Classical.propDecidable

variable [Fintype Q] [DecidableEq Q] [Fintype C] [Nonempty C]

/-- A union bound over the unseen slots of a fixed transcript view. The
local event may read every other coordinate of the completed table. -/
theorem hidden_events_count_le (tree : Tree Q C Out fuel) (lookups : Out → List Q) (H : Q → C)
    (points : Finset Q) (hhidden : ∀ x ∈ points, x ∉ revealed tree lookups H)
    (bad : Q → (Q → C) → C → Prop) (δ : ℚ)
    (hoff : ∀ x ∈ points, ∀ H₁ H₂, AgreeOff x H₁ H₂ → ∀ c,
      (bad x H₁ c ↔ bad x H₂ c))
    (hlocal : ∀ x ∈ points, ∀ H₁, view tree lookups H₁ = view tree lookups H →
      ((univ.filter fun c : C => bad x H₁ c).card : ℚ) ≤ Fintype.card C * δ) :
    ((univ.filter fun H₁ : Q → C => view tree lookups H₁ = view tree lookups H ∧
      ∃ x ∈ points, bad x H₁ (H₁ x)).card : ℚ) ≤
    points.card * δ *
      (univ.filter fun H₁ : Q → C => view tree lookups H₁ = view tree lookups H).card := by
  let fixed (U : Q → C) := view tree lookups U = view tree lookups H
  let seen := univ.filter fixed
  let occurs (x : Q) := univ.filter fun U : Q → C => fixed U ∧ bad x U (U x)
  have hcount (x : Q) (hx : x ∈ points) : ((occurs x).card : ℚ) ≤ δ * seen.card := by
    let localBad (U : Q → C) (c : C) := fixed U ∧ bad x U c
    have hfixed (U U' : Q → C) (ha : AgreeOff x U U') : fixed U → fixed U' := by
      intro hu
      apply (view_eq_iff tree lookups H U').mpr
      intro y hy
      rw [← ha y (fun he => hhidden x hx (he ▸ hy))]
      exact (view_eq_iff tree lookups H U).mp hu y hy
    have hconst := card_coord_mul x localBad (fun U U' ha c h =>
      ⟨hfixed U U' ha h.1, (hoff x hx U U' ha c).mp h.2⟩)
    have he : (univ.filter fun U : Q → C => localBad U (U x)) = occurs x := by
      ext U
      simp [localBad, occurs]
    rw [he] at hconst
    have hcast : ((occurs x).card : ℚ) * Fintype.card C =
        ∑ U : Q → C, ((univ.filter (localBad U)).card : ℚ) := by
      exact_mod_cast hconst
    have hq : (0 : ℚ) < Fintype.card C := by exact_mod_cast Fintype.card_pos
    apply le_of_mul_le_mul_right ?_ hq
    calc
      _ = ∑ U : Q → C, ((univ.filter (localBad U)).card : ℚ) := hcast
      _ ≤ ∑ U : Q → C, if fixed U then (Fintype.card C : ℚ) * δ else 0 := by
        apply sum_le_sum
        intro U _
        by_cases h : fixed U
        · simpa only [localBad, h, true_and, if_true] using hlocal x hx U h
        · simp [localBad, h]
      _ = δ * (seen.card : ℚ) * Fintype.card C := by
        rw [← sum_filter]
        simp [seen, sum_const, nsmul_eq_mul, mul_assoc, mul_comm, mul_left_comm]
  have hsub : (univ.filter fun U : Q → C => fixed U ∧ ∃ x ∈ points, bad x U (U x)) =
      points.biUnion occurs := by
    ext U
    simp only [mem_filter, mem_univ, true_and, mem_biUnion, occurs]
    exact ⟨fun ⟨hf, x, hx, hb⟩ => ⟨x, hx, hf, hb⟩,
      fun ⟨x, hx, hf, hb⟩ => ⟨hf, x, hx, hb⟩⟩
  change ((univ.filter fun U : Q → C => fixed U ∧ ∃ x ∈ points, bad x U (U x)).card : ℚ) ≤ _
  rw [hsub]
  calc
    _ ≤ ∑ x ∈ points, ((occurs x).card : ℚ) := by
      exact_mod_cast card_biUnion_le
    _ ≤ ∑ _x ∈ points, δ * (seen.card : ℚ) := sum_le_sum hcount
    _ = _ := by simp [seen, fixed, sum_const, nsmul_eq_mul, mul_assoc]

end Hidden

end LfzkV1.ReplayView125
