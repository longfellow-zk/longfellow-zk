import TranscriptV2.SharedReduction
import Bcs.FiniteProbability

/-! Composition separates local algebra from transcript implementation.

Local proofs give single-answer charges and adjacent-pair charges, including
their independence and averaging laws. The transcript realization preserves
the complete observation and recovers an accepted path, or charges a
speculative query. Its observation must include the actual extraction cut;
preserving only the submitted proof is insufficient for extraction soundness.

This interface is deliberately conditional. Constructing a realization for
SHA strands, including its cut and final-seal laws, is a separate obligation.
The generic theorem below is not a certificate for an uninstantiated runtime.
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
  SharedReduction.charges (parent := localProof.parent) (child := localProof.child)
    (single := localProof.single) (pair := localProof.pair) tree H

theorem charge_nonneg {Out : Type} {fuel : ℕ} (tree : Tree P (D × C) Out fuel) (H : P → D × C) :
    0 ≤ localProof.charge tree H :=
  SharedReduction.charges_nonneg tree H localProof.single_nonneg localProof.pair_nonneg

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

/-- A transcript implementation must preserve the law of the entire
observation: request, proof, verifier decision, and the actual extraction cut.
The path conclusion includes complete-proof finalization. It may fail only
through the explicit exception or a charge paid by speculative search queries.
No algebraic failure predicate or local soundness bound is assumed here. -/
structure SoundnessRealization [Fintype P] [DecidableEq P]
    {Out RawCoin View : Type} [Fintype RawCoin] {fuel rounds : ℕ}
    (tree : Tree P (D × C) Out fuel) (raw : RawCoin → View)
    (observe : Out → (P → D × C) → View) (accepted : View → Prop)
    (path : Out → (P → D × C) → ℕ → P) where
  observation_law : ∀ event : View → Prop,
    density (fun coin => event (raw coin)) = density (fun H => event (observe (tree.run H).1 H))
  exception : (P → D × C) → Prop
  speculation : (P → D × C) → ℚ
  speculation_nonneg : ∀ H, 0 ≤ speculation H
  accepted_path : ∀ H, accepted (observe (tree.run H).1 H) → ¬exception H →
    PathQueries (rounds := rounds) tree H (path (tree.run H).1 H) ∨ 1 ≤ speculation H

namespace SoundnessRealization

/-- The earlier whole-answer transcript instantiates the contract directly.
This checks the interface against an existing complete chain proof; the
strand implementation must provide its own realization and error analysis. -/
def ofChain [Fintype P] [DecidableEq P] {Out View : Type} {fuel rounds : ℕ}
    (model : Chain P D C Out rounds) (tree : Tree P (D × C) Out fuel)
    (observe : Out → (P → D × C) → View) (accepted : View → Prop)
    (sealValid : ∀ out H, accepted (observe out H) →
      (H (model.finalSealPoint out H)).1 = model.finalSeal out) :
    SoundnessRealization (rounds := rounds) tree
      (fun H => observe (tree.run H).1 H) observe accepted model.point where
  observation_law _ := rfl
  exception := ChainException model tree
  speculation _ := 0
  speculation_nonneg _ := le_rfl
  accepted_path H valid good := by
    obtain ⟨queried,ordered⟩ := model.accepted_path_queries tree H good (sealValid _ H valid)
    exact Or.inl ⟨queried,ordered⟩

variable [Fintype P] [DecidableEq P] [Nonempty D] [Nonempty C] [Fintype Parent]
variable {Out RawCoin View : Type} [Fintype RawCoin] {fuel rounds Q : ℕ}
variable {tree : Tree P (D × C) Out fuel} {raw : RawCoin → View}
variable {observe : Out → (P → D × C) → View} {accepted : View → Prop}
variable {path : Out → (P → D × C) → ℕ → P}
variable (realization : SoundnessRealization (rounds := rounds) tree raw observe accepted path)

/-- Compose independent local proofs with one transcript accounting law.
The two query categories spend the same search budget. The implementation
must separately prove the speculative average and the exception probability;
neither verifier replay nor a second subprotocol receives extra search budget.
Only `eligible` coordinates spend that budget. Excluded coordinates, such as
trusted setup queries, must have zero local charge and no speculative allocation.
Algebraic correspondence is needed only outside these already charged cases:
for example a prequeried stream may otherwise differ from a node's unused
challenge sample. -/
theorem failure_ratio_le (localProof : LocalCharges P D C Parent Response)
    (invalid : View → Prop) (eligible auxiliary : P → Prop) (epsilon delta : ℚ)
    (positive : 0 ≤ epsilon) (queries : ∀ H, ((seen tree H).filter eligible).card ≤ Q)
    (roles : ∀ p, localProof.budget p ≤ if eligible p ∧ ¬auxiliary p then epsilon else 0)
    (speculative : (∑ H, realization.speculation H) ≤
      ∑ H : P → D × C, ∑ p ∈ seen tree H, if eligible p ∧ auxiliary p then epsilon else 0)
    (exceptions : density realization.exception ≤ delta)
    (reduction : ∀ out H, accepted (observe out H) → invalid (observe out H) →
      ¬realization.exception H → realization.speculation H < 1 →
      localProof.Covers (rounds := rounds) (path out H) H) :
    density (fun coin => accepted (raw coin) ∧ invalid (raw coin)) ≤ Q*epsilon+delta := by
  rw [realization.observation_law (fun view => accepted view ∧ invalid view)]
  let cost := fun H => localProof.charge tree H + realization.speculation H
  have nonnegative H : 0 ≤ cost H :=
    add_nonneg (localProof.charge_nonneg tree H) (realization.speculation_nonneg H)
  have cover H (failed : accepted (observe (tree.run H).1 H) ∧ invalid (observe (tree.run H).1 H))
      (good : ¬realization.exception H) : 1 ≤ cost H := by
    by_cases charged : 1 ≤ realization.speculation H
    · exact charged.trans (le_add_of_nonneg_left (localProof.charge_nonneg tree H))
    · have queried := (realization.accepted_path H failed.1 good).resolve_right charged
      have algebra := SharedReduction.charges_of_cover tree H (path (tree.run H).1 H)
        queried.queried queried.ordered localProof.single_nonneg localProof.pair_nonneg
        (reduction _ H failed.1 failed.2 good (lt_of_not_ge charged))
      exact algebra.trans (le_add_of_nonneg_right (realization.speculation_nonneg H))
  have average : (∑ H, cost H) ≤ (Q : ℚ)*epsilon*Fintype.card (P → D × C) := by
    have algebra := localProof.charge_mean tree
      (fun p => if eligible p ∧ ¬auxiliary p then epsilon else 0) roles
    have combined := add_le_add algebra speculative
    simp only [← sum_add_distrib] at combined
    apply combined.trans
    have perQuery p : (if eligible p ∧ ¬auxiliary p then epsilon else 0) +
        (if eligible p ∧ auxiliary p then epsilon else 0) = if eligible p then epsilon else 0 := by
      by_cases inside : eligible p <;> by_cases aux : auxiliary p <;> simp [inside,aux]
    simp only [perQuery,← sum_filter,sum_const,nsmul_eq_mul]
    have total := sum_le_sum (fun H (_ : H ∈ (univ : Finset (P → D × C))) =>
      mul_le_mul_of_nonneg_right
        (show (((seen tree H).filter eligible).card : ℚ) ≤ Q by exact_mod_cast queries H) positive)
    simpa only [sum_const,card_univ,nsmul_eq_mul,mul_comm] using total
  exact SharedFailure.failure_ratio_le _ realization.exception cost nonnegative cover average exceptions

end SoundnessRealization
end TranscriptV2.Composition
