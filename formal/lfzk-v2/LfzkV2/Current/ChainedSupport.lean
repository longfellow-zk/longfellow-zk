import LfzkV2.Current.ChainedFS

/-! The distinct-input version of the current chained bound. The program
may make arbitrarily many repeated calls within its syntactic fuel. Only
the cardinality of its actual queried-point set enters the leading bound.
The Merkle composition and commitment-cut transport are separate. -/
noncomputable section
namespace LfzkV2.Current.ChainedFS
open Finset TranscriptV2 Merkle.RandomOracle Merkle.RandomOracle.TwoOracleTree
open Bcs.TotalOracle
open scoped Classical

variable {Point Out C Enc D : Type} {R tA calls queries TM : ℕ}
variable [DecidableEq Enc] [Inhabited D]
variable [Fintype Point] [DecidableEq Point]
variable [Fintype C] [Nonempty C] [DecidableEq C]
variable {Parent Response : Type} [Fintype Parent] [Fintype Response]

theorem ratio_le_support
    (M : Chain Point Digest C Out R)
    (body : TwoOracleTree Enc D Point (Digest × C) Out tA calls)
    (parent : Parent → Point) (child : Parent → Response → Point)
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
    (singleBudget : Point → ℚ) (pairBudget : Parent → ℚ)
    (hsingle : ∀ p H, ∑ a, single p H a ≤ Fintype.card (Digest × C) * singleBudget p)
    (hpair : ∀ p H, ∑ r, ∑ a, ∑ b, pair p r H a b ≤
      (Fintype.card (Digest × C) : ℚ)^2 * pairBudget p)
    (hpoint : ∀ z, singleBudget z +
      (∑ p, if parent p = z then pairBudget p else 0) ≤
        2/((Adapter.Mdoc.binaryOrder-1 : ℕ) : ℚ))
    (mt : Fin TM → D)
    (hqueries : ∀ H : Point → Digest × C,
      (seen (fixLeft mt default body []) H).card ≤ queries) :
    ((univ.filter fun H : Point → Digest × C =>
        Failure ((fixLeft mt default body []).run H).1 H).card : ℚ) /
        (Fintype.card (Digest × C) : ℚ)^Fintype.card Point ≤
      2*queries/(Adapter.Mdoc.binaryOrder : ℚ) +
        (4*queries+1 : ℚ)/(Adapter.Mdoc.binaryOrder : ℚ)^2 := by
  have h := reduction.failure_ratio_le (fixLeft mt default body [])
    hqueries hne hsingleOff hsingleNonneg hpairOff hpairNonneg
    singleBudget pairBudget (2/((Adapter.Mdoc.binaryOrder-1 : ℕ) : ℚ))
    (by positivity) hsingle hpair hpoint
  rw [digest_card, Nat.cast_pow] at h
  exact h.trans (mdoc_chained_budget queries)

end LfzkV2.Current.ChainedFS
