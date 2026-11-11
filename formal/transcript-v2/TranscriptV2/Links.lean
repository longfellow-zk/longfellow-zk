import TranscriptV2.Queries
import Mathlib.Tactic.FieldSimp

namespace TranscriptV2
open Finset Bcs.TotalOracle Merkle.RandomOracle
open scoped Classical

/-- A child preimage identifies its full parent preimage, not just a digest.
This unique-parent property lets one queried child pay for at most one guess. -/
structure Links (P Link : Type) where
  parent : P → Option P
  claimed : P → Link

variable {P Link C Out : Type} [DecidableEq P]

def earlyChildren {fuel : ℕ} (links : Links P Link) (tree : Tree P (Link × C) Out fuel)
    (H : P → Link × C) (p : P) : Finset P :=
  ((before tree H p).toFinset).filter fun c => links.parent c = some p

def linkBad {fuel : ℕ} (links : Links P Link) (tree : Tree P (Link × C) Out fuel)
    (p : P) (H : P → Link × C) (a : Link × C) : Prop :=
  ∃ c ∈ earlyChildren links tree H p, a.1 = links.claimed c

theorem earlyChildren_subset {fuel : ℕ} (links : Links P Link)
    (tree : Tree P (Link × C) Out fuel) (H : P → Link × C) (p : P) :
    earlyChildren links tree H p ⊆ seen tree H := by
  intro c hc
  exact List.mem_toFinset.mpr (before_subset tree H p (List.mem_toFinset.mp (mem_filter.mp hc).1))

/-- A queried child names one parent, so it is counted at most once across all
stopped prefixes. This avoids a depth or quadratic-query factor. -/
theorem sum_earlyChildren_le [Fintype P] {fuel : ℕ} (links : Links P Link)
    (tree : Tree P (Link × C) Out fuel) (H : P → Link × C) :
    ∑ p, (earlyChildren links tree H p).card ≤ (seen tree H).card := by
  have hd : ∀ p ∈ (univ : Finset P), ∀ q ∈ univ, p ≠ q →
      Disjoint (earlyChildren links tree H p) (earlyChildren links tree H q) := by
    intro p _ q _ hpq
    apply disjoint_left.mpr
    intro c hc hd
    exact hpq (Option.some.inj ((mem_filter.mp hc).2.symm.trans (mem_filter.mp hd).2))
  rw [← card_biUnion hd]
  apply card_le_card
  intro c hc
  obtain ⟨p,_,hp⟩ := mem_biUnion.mp hc
  exact earlyChildren_subset links tree H p hp

theorem linkBad_off {fuel : ℕ} (links : Links P Link) (tree : Tree P (Link × C) Out fuel)
    (p : P) (H H' : P → Link × C) (h : AgreeOff p H H') (a : Link × C) :
    linkBad links tree p H a → linkBad links tree p H' a := by
  have heq : earlyChildren links tree H p = earlyChildren links tree H' p := by
    simp only [earlyChildren, before_congr tree p h]
  intro ⟨c,hc,ha⟩
  exact ⟨c, heq ▸ hc, ha⟩

theorem link_fiber_card [Fintype Link] [Fintype C] (value : Link) :
    (univ.filter fun a : Link × C => a.1 = value).card = Fintype.card C := by
  have heq : (univ.filter fun a : Link × C => a.1 = value) = {value} ×ˢ univ := by
    ext a; simp [Prod.ext_iff, eq_comm]
  rw [heq, card_product]
  simp

theorem linkBad_card_le [Fintype Link] [Fintype C] {fuel : ℕ}
    (links : Links P Link) (tree : Tree P (Link × C) Out fuel) (p : P) (H : P → Link × C) :
    (univ.filter (linkBad links tree p H)).card ≤
      (earlyChildren links tree H p).card * Fintype.card C := by
  have heq : (univ.filter (linkBad links tree p H)) =
      (earlyChildren links tree H p).biUnion fun c => univ.filter fun a : Link × C =>
        a.1 = links.claimed c := by ext a; simp [linkBad]
  rw [heq]
  apply card_biUnion_le.trans_eq
  simp [link_fiber_card]

def LinkGuess {fuel : ℕ} (links : Links P Link) (tree : Tree P (Link × C) Out fuel)
    (H : P → Link × C) : Prop := ∃ p, linkBad links tree p H (H p)

theorem link_guess_ratio_le [Fintype P] [Fintype Link] [Nonempty Link] [DecidableEq Link]
    [Fintype C] [Nonempty C] [DecidableEq C] {fuel Q : ℕ}
    (links : Links P Link) (tree : Tree P (Link × C) Out fuel)
    (hbudget : ∀ H, (seen tree H).card ≤ Q) :
    ((univ.filter (LinkGuess links tree)).card : ℚ) /
      (Fintype.card (Link × C) : ℚ)^Fintype.card P ≤ (Q : ℚ) / Fintype.card Link := by
  let weight := fun p H => (earlyChildren links tree H p).card * Fintype.card C
  have htotal : ∀ H, ∑ p, weight p H ≤ Q * Fintype.card C := by
    intro H
    dsimp [weight]
    rw [← sum_mul]
    exact Nat.mul_le_mul_right _ ((sum_earlyChildren_le links tree H).trans (hbudget H))
  have h := ratio_exists_coord_le (LinkGuess links tree) (linkBad links tree)
    (fun _ h => h) (linkBad_off links tree) weight (linkBad_card_le links tree)
    (Q * Fintype.card C) htotal
  apply h.trans_eq
  simp only [Nat.cast_mul, Fintype.card_prod]
  have hC : (Fintype.card C : ℚ) ≠ 0 := by positivity
  field_simp

end TranscriptV2
