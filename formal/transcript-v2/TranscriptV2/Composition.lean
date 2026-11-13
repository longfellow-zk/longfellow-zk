import TranscriptV2.PathCharges
import Bcs.FiniteProbability

/-! Composition separates local algebra from transcript implementation.

Local proofs give single-answer charges and adjacent-pair charges, including
their independence and averaging laws. This module owns those algebraic data
and the query membership/order facts needed along a recovered path.
`Survival.CausalCharges` combines the costs with causal stopping. The current
runtime's soundness composition proves its accepted-failure cover and preserves
the complete observation, including the original extraction cut.
-/
noncomputable section
namespace TranscriptV2.Composition
open Finset Bcs.TotalOracle Bcs.FiniteProbability Merkle.RandomOracle
open scoped Classical

variable {P D C Parent Response : Type}
variable [Fintype D] [Fintype C] [Fintype Response]

/-- The algebraic interface retains the response family at a pair's parent.
Its budgets are local means, not separately allocated whole-protocol bounds. -/
structure LocalCharges (P D C Parent Response : Type)
    [Fintype D] [Fintype C] [Fintype Response] where
  parent : Parent → P
  child : Parent → Response → P
  distinct : ∀ p r, parent p ≠ child p r
  single : P → (P → D × C) → (D × C) → ℚ
  pair : Parent → Response → (P → D × C) → (D × C) → (D × C) → ℚ
  single_nonneg : ∀ p H a, 0 ≤ single p H a
  pair_nonneg : ∀ p r H a b, 0 ≤ pair p r H a b
  single_off : ∀ p H H', AgreeOff p H H' → ∀ a, single p H a = single p H' a
  pair_off : ∀ p r H H',
    (∀ z, z ≠ parent p → z ≠ child p r → H z = H' z) →
    ∀ a b, pair p r H a b = pair p r H' a b
  singleBudget : P → ℚ
  pairBudget : Parent → ℚ
  single_mean : ∀ p H, ∑ a, single p H a ≤ Fintype.card (D × C) * singleBudget p
  pair_mean : ∀ p H, ∑ r, ∑ a, ∑ b, pair p r H a b ≤
    (Fintype.card (D × C) : ℚ)^2 * pairBudget p

namespace LocalCharges
variable [Fintype Parent] [DecidableEq P]
variable (localProof : LocalCharges P D C Parent Response)

/-- All costs using the same query are added before taking the maximum
over query roles. Different rounds do not receive separate query budgets. -/
def budget (point : P) : ℚ := localProof.singleBudget point +
  ∑ parent, if localProof.parent parent = point then localProof.pairBudget parent else 0

def charge {Out : Type} {fuel : ℕ} (tree : Tree P (D × C) Out fuel) (H : P → D × C) : ℚ :=
  PathCharges.charges (parent := localProof.parent) (child := localProof.child)
    (single := localProof.single) (pair := localProof.pair) tree H

theorem charge_nonneg {Out : Type} {fuel : ℕ} (tree : Tree P (D × C) Out fuel) (H : P → D × C) :
    0 ≤ localProof.charge tree H :=
  PathCharges.charges_nonneg tree H localProof.single_nonneg localProof.pair_nonneg

/-- This is the local reduction a protocol composition must establish for
one common selected witness, rather than choosing a new witness per component. -/
def Covers {rounds : ℕ} (path : ℕ → P) (H : P → D × C) : Prop :=
  (∃ i < rounds, 1 ≤ localProof.single (path i) H (H (path i))) ∨
    (∃ i < rounds, ∃ p r, localProof.parent p = path i ∧ localProof.child p r = path (i+1) ∧
      1 ≤ localProof.pair p r H (H (localProof.parent p)) (H (localProof.child p r)))

theorem charge_mean [Fintype P] [Nonempty D] [Nonempty C]
    {Out : Type} {fuel : ℕ} (tree : Tree P (D × C) Out fuel)
    (allowance : P → ℚ) (bounded : ∀ p, localProof.budget p ≤ allowance p) :
    (∑ H, localProof.charge tree H) ≤ ∑ H : P → D × C, ∑ p ∈ seen tree H, allowance p :=
  shared_role_sum_le tree localProof.parent localProof.child localProof.distinct
    localProof.single localProof.single_off localProof.pair localProof.pair_off localProof.pair_nonneg
    localProof.singleBudget localProof.pairBudget allowance localProof.single_mean localProof.pair_mean bounded

end LocalCharges

/-- These facts concern only the accepted logical path. The adversary may
query other inputs in any order, including speculative child or PRF inputs. -/
structure PathQueries [DecidableEq P] {Out : Type} {fuel rounds : ℕ}
    (tree : Tree P (D × C) Out fuel) (H : P → D × C) (path : ℕ → P) : Prop where
  queried : ∀ i ≤ rounds, path i ∈ seen tree H
  ordered : ∀ i < rounds, firstOfTwo tree H (path i) (path (i+1)) = .left

end TranscriptV2.Composition
