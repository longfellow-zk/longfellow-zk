import LfzkV2.Current.MdocBudgets
import LfzkV2.Current.Messages
import TranscriptV2.SharedReduction

/-! The current prover's original query allowance is sufficient for shared
single-answer and adjacent-pair charging. The link has 256 bits, so the one
chain exception joins the nonzero-sampling correction in the squared-field
remainder. Protocol-specific coverage and counts are separate checked inputs
to this composition lemma. -/
noncomputable section
namespace LfzkV2.Current.ChainedFS
open Finset TranscriptV2 Merkle.RandomOracle Merkle.RandomOracle.TwoOracleTree
open Bcs.TotalOracle
open scoped Classical

theorem digest_card : Fintype.card Digest = Adapter.Mdoc.binaryOrder^2 := by
  norm_num [Digest, Fintype.card_fun, Fintype.card_fin, Adapter.Mdoc.binaryOrder]

variable {Point Out C Enc D : Type} {R tA Q TM : ℕ}
variable [DecidableEq Enc] [Inhabited D]
variable [Fintype Point] [DecidableEq Point]
variable [Fintype C] [Nonempty C] [DecidableEq C]
variable {Parent Response : Type} [Fintype Parent] [Fintype Response]

variable (M : Chain Point Digest C Out R)
variable (body : TwoOracleTree Enc D Point (Digest × C) Out tA Q)
variable (parent : Parent → Point) (child : Parent → Response → Point)

/-- No verifier query is appended to this tree. The complete-proof final
seal is checked by the reduction and its guessing loss is counted once. -/
theorem ratio_le
    (single : Point → (Point → Digest × C) → (Digest × C) → ℚ)
    (pair : Parent → Response → (Point → Digest × C) → (Digest × C) → (Digest × C) → ℚ)
    (Failure : Out → (Point → Digest × C) → Prop)
    (reduction : SharedReduction M parent child single pair Failure)
    (hne : ∀ p r, parent p ≠ child p r)
    (hsingleOff : ∀ p H H', AgreeOff p H H' → ∀ a, single p H a = single p H' a)
    (hsingleNonneg : ∀ p H a, 0 ≤ single p H a)
    (hpairOff : ∀ p r H H',
      (∀ z, z ≠ parent p → z ≠ child p r → H z = H' z) →
      ∀ a b, pair p r H a b = pair p r H' a b)
    (hpairNonneg : ∀ p r H a b, 0 ≤ pair p r H a b)
    (singleBudget : Point → ℚ)
    (pairBudget : Parent → ℚ)
    (hsingle : ∀ p H, ∑ a, single p H a ≤ Fintype.card (Digest × C) * singleBudget p)
    (hpair : ∀ p H, ∑ r, ∑ a, ∑ b, pair p r H a b ≤
      (Fintype.card (Digest × C) : ℚ)^2 * pairBudget p)
    (hpoint : ∀ z, singleBudget z +
      (∑ p, if parent p = z then pairBudget p else 0) ≤
        2/((Adapter.Mdoc.binaryOrder-1 : ℕ) : ℚ))
    (mt : Fin TM → D) :
    ((univ.filter fun H : Point → Digest × C =>
        Failure ((fixLeft mt default body []).run H).1 H).card : ℚ) /
        (Fintype.card (Digest × C) : ℚ)^Fintype.card Point ≤
      2*Q/(Adapter.Mdoc.binaryOrder : ℚ) +
        (4*Q+1 : ℚ)/(Adapter.Mdoc.binaryOrder : ℚ)^2 := by
  have h := reduction.failure_ratio_le (fixLeft mt default body [])
    (fun H => seen_card_le _ H) hne hsingleOff hsingleNonneg hpairOff hpairNonneg
    singleBudget pairBudget (2/((Adapter.Mdoc.binaryOrder-1 : ℕ) : ℚ))
    (by positivity) hsingle hpair hpoint
  rw [digest_card, Nat.cast_pow] at h
  exact h.trans (mdoc_chained_budget Q)

end LfzkV2.Current.ChainedFS
