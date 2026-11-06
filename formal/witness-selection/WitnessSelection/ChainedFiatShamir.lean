import WitnessSelection.IOP
import TranscriptV2.Charging

/-! Witness-selection accounting against an arbitrary adaptive total-oracle
search. All vectors of a field remain in one answer with its link. Other fields
can be included in Rest. Lists depend on the fixed preimage and its ancestors,
not on the oracle answer currently being counted. -/
namespace WitnessSelection.Chained
open Finset Bcs.TotalOracle Merkle.RandomOracle
open scoped Classical

variable {F ι P Link Rest Out : Type} [Field F] [Fintype F] [DecidableEq F]
  [Fintype ι] [DecidableEq ι]

abbrev Answer (Link Rest F ι : Type) := Link × (Rest × Coins F ι)

def badAt (pts : PrefixPoints P)
    (lists : (p : P) → (Fin (pts.slot p) → Answer Link Rest F ι) → Finset (Candidate F ι))
    (p : P) (H : P → Answer Link Rest F ι) (a : Answer Link Rest F ι) : Prop :=
  a.2.2 ∈ badCoins (lists p (pts.chal H p))

omit [DecidableEq F] in
theorem badAt_off (pts : PrefixPoints P)
    (lists : (p : P) → (Fin (pts.slot p) → Answer Link Rest F ι) → Finset (Candidate F ι))
    (p : P) (H H' : P → Answer Link Rest F ι) (h : AgreeOff p H H') (a : Answer Link Rest F ι) :
    badAt pts lists p H a → badAt pts lists p H' a := by
  simpa only [badAt, pts.chal_congr h] using id

theorem badAt_card_mul_le [Fintype Link] [Fintype Rest] (pts : PrefixPoints P)
    (lists : (p : P) → (Fin (pts.slot p) → Answer Link Rest F ι) → Finset (Candidate F ι))
    (L : ℕ) (hsize : ∀ p pref, (lists p pref).card ≤ L)
    (p : P) (H : P → Answer Link Rest F ι) :
    (univ.filter (badAt pts lists p H)).card * Fintype.card F^2 ≤
      L.choose 2 * Fintype.card (Answer Link Rest F ι) := by
  let s := lists p (pts.chal H p)
  have heq : (univ.filter (badAt pts lists p H)) =
      (univ : Finset Link) ×ˢ ((univ : Finset Rest) ×ˢ badCoins s) := by
    ext a
    simp [badAt, s]
  have hlocal := (list_collision_card_mul_le s).trans
    (Nat.mul_le_mul_right _ (Nat.choose_le_choose 2 (hsize p (pts.chal H p))))
  rw [heq, card_product, card_univ, card_product, card_univ]
  calc
    Fintype.card Link * (Fintype.card Rest * (badCoins s).card) * Fintype.card F^2 =
        (Fintype.card Link * Fintype.card Rest) * ((badCoins s).card * Fintype.card F^2) := by ring
    _ ≤ (Fintype.card Link * Fintype.card Rest) * (L.choose 2 * Fintype.card (Coins F ι)) :=
      Nat.mul_le_mul_left _ hlocal
    _ = L.choose 2 * Fintype.card (Answer Link Rest F ι) := by
      simp only [Answer, Fintype.card_prod]; ring

/-- The fingerprint charge plus the same single chain exception as other
frontend components. Combining components should charge that exception once. -/
theorem failure_bound [Fintype P] [DecidableEq P]
    [Fintype Link] [Nonempty Link] [DecidableEq Link]
    [Fintype Rest] [Nonempty Rest] [DecidableEq Rest] {R fuel Q : ℕ}
    (M : TranscriptV2.Chain P Link (Rest × Coins F ι) Out R) (pts : PrefixPoints P)
    (lists : (p : P) → (Fin (pts.slot p) → Answer Link Rest F ι) → Finset (Candidate F ι))
    (L : ℕ) (hsize : ∀ p pref, (lists p pref).card ≤ L)
    (Failure : Out → (P → Answer Link Rest F ι) → Prop)
    (reduction : TranscriptV2.Reduction M (badAt pts lists) Failure)
    (tree : Tree P (Answer Link Rest F ι) Out fuel)
    (hbudget : ∀ H, (TranscriptV2.seen tree H).card ≤ Q) :
    ((univ.filter fun H => Failure (tree.run H).1 H).card : ℚ) /
      (Fintype.card (Answer Link Rest F ι) : ℚ)^Fintype.card P ≤
      (Q*L.choose 2 : ℚ) / (Fintype.card F : ℚ)^2 + (Q+1 : ℚ) / Fintype.card Link := by
  simpa only [Nat.cast_pow] using reduction.failure_ratio_le tree hbudget
    (badAt_off pts lists) (by positivity) (badAt_card_mul_le pts lists L hsize)

end WitnessSelection.Chained
