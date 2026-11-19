import Survival.HistoryBounds
import Survival.StoppedCharges
import Survival.SharedBudget
import Survival.QueryStep

/-! The chronological monitor reads an explicit state derived
from the strict query prefix. No completed oracle is part of this interface.
The existing original-cut two-answer charges are retained for backend costs.
-/
noncomputable section
namespace Survival
open Finset Merkle.RandomOracle TranscriptV2 Bcs.FiniteProbability Bcs.TotalOracle
open scoped Classical

structure CausalCharges (P A : Type) [Fintype A] (State : P → Type) where
  extract : (p : P) → List (P × A) → State p
  single : (p : P) → State p → A → ℚ
  budget : P → ℚ
  nonneg : ∀ p state answer, 0 ≤ single p state answer
  mean : ∀ p state, ∑ answer, single p state answer ≤ Fintype.card A * budget p

namespace CausalCharges
variable {P A : Type} [Fintype A] {State : P → Type}
variable (L : CausalCharges P A State)

def advance (past : List (P × A)) (p : P) (a : A) : List (P × A) := past ++ [(p,a)]

omit [Fintype A] in
theorem advance_fold (initial past : List (P × A)) :
    past.foldl (fun state qa => advance state qa.1 qa.2) initial = initial ++ past := by
  induction past generalizing initial with
  | nil => simp
  | cons qa past ih =>
      rw [List.foldl_cons, ih]
      simp only [advance, List.append_assoc, List.singleton_append, Prod.mk.eta]

def safe (marked : P → Bool) (s : List (P × A) × P) (answer : A) : Prop :=
  marked s.2 = true ∨ L.single s.2 (L.extract s.2 s.1) answer < 1

def audit {Out : Type} {fuel : ℕ} (marked : P → Bool) (tree : Tree P A Out fuel) :=
  Survival.History.audit (L.safe marked) marked advance [] tree

theorem opaque_safe (marked : P → Bool) (past : List (P × A)) (p : P)
    (markedPoint : marked p = true) (a : A) : L.safe marked (past,p) a := Or.inl markedPoint

theorem hazard [Nonempty A] (marked : P → Bool) (rate : ℚ)
    (bounded : ∀ p, marked p = false → L.budget p ≤ rate)
    (past : List (P × A)) (p : P) (transparent : marked p = false) :
    density (fun a => ¬L.safe marked (past,p) a) ≤ rate := by
  exact Survival.QueryStep.charge_hazard (marked p) (L.single p (L.extract p past)) rate
    (L.nonneg p _) ((L.mean p _).trans
      (mul_le_mul_of_nonneg_left (bounded p transparent) (Nat.cast_nonneg _)))

theorem safe_at_prefix {Out : Type} {fuel : ℕ} (marked : P → Bool)
    (tree : Tree P A Out fuel) (H : P → A)
    (survived : ((L.audit marked tree).run H).1.1 = false)
    (past rest : List (P × A)) (p : P) (a : A)
    (trace : (tree.run H).2 = past ++ (p,a)::rest) : L.safe marked (past,p) a := by
  have tested := Survival.History.safe_at_prefix (L.safe marked) marked advance [] tree H
    survived past rest p a trace
  simpa only [advance_fold, List.nil_append] using tested

/-- A bridge to an existing local test is required only on the recovered
path. Malformed off-path query states still satisfy the unconditional mean.
-/
theorem no_escape_of_causal_single [DecidableEq P] {Out : Type} {fuel : ℕ}
    (marked : P → Bool) (tree : Tree P A Out fuel) (H : P → A)
    (survived : ((L.audit marked tree).run H).1.1 = false)
    (actual : P → (P → A) → A → ℚ) (p : P) (present : p ∈ seen tree H)
    (transparent : marked p = false)
    (correspondence : ∀ past rest a,
      (tree.run H).2 = past ++ (p,a)::rest → past.map Prod.fst = before tree H p →
      L.single p (L.extract p past) a = actual p H a) : actual p H (H p) < 1 := by
  obtain ⟨past,rest,a,trace,first⟩ := trace_split_before tree H p present
  have tested := L.safe_at_prefix marked tree H survived past rest p a trace
  have value := Tree.trace_sound tree H (p,a) (by
    rw [trace]
    exact List.mem_append_right _ List.mem_cons_self)
  change a = H p at value
  simp only [safe, transparent, Bool.false_eq_true, false_or] at tested
  rw [correspondence past rest a trace first, value] at tested
  exact tested

theorem linear_law_le_support [Fintype P] [DecidableEq P] [Nonempty A]
    {Out : Type} {fuel queries : ℕ}
    (marked : P → Bool) (tree : Tree P A Out fuel)
    (rate allowance : ℚ) (positive : 0 ≤ rate) (allowance_le : allowance ≤ rate)
    (bounded : ∀ p, marked p = false → L.budget p ≤ rate)
    (fresh : FreshOracle.FreshFrom (fun _ => False) tree)
    (queriesBound : ∀ H, (seen tree H).card ≤ queries) :
    density (fun H => ((L.audit marked tree).run H).1.1 = true) +
      allowance * ((∑ H : P → A, (((L.audit marked tree).run H).1.2 : ℚ)) /
        Fintype.card (P → A)) ≤ rate * queries := by
  apply Survival.SharedBudget.accounting_le _
    (Survival.StoppedSearch.transparent (L.safe marked) marked advance [] tree) _
    rate allowance queries positive allowance_le
  · exact Survival.StoppedSearch.counts_le_support (L.safe marked) marked advance [] tree fresh queriesBound
  · exact Survival.StoppedSearch.escape_le (L.safe marked) marked advance rate
      (L.opaque_safe marked) (L.hazard marked rate bounded) [] tree fresh

theorem saturated_law_le_support [Fintype P] [DecidableEq P] [Nonempty A]
    {Out : Type} {fuel queries : ℕ}
    (marked : P → Bool) (tree : Tree P A Out fuel)
    (rate opaqueFraction : ℚ) (hr : 0 ≤ rate) (hr1 : rate ≤ 1)
    (hl : 0 ≤ opaqueFraction) (hl1 : opaqueFraction ≤ 1)
    (bounded : ∀ p, marked p = false → L.budget p ≤ rate)
    (budget : rate * queries ≤ 1)
    (fresh : FreshOracle.FreshFrom (fun _ => False) tree)
    (queriesBound : ∀ H, (seen tree H).card ≤ queries) :
    density (fun H => ((L.audit marked tree).run H).1.1 = true) +
      (opaqueFraction*rate) * ((∑ H : P → A, (((L.audit marked tree).run H).1.2 : ℚ)) /
        Fintype.card (P → A)) ≤ Survival.Hybrid.envelope rate opaqueFraction queries := by
  exact Survival.QueryBudget.history_law_le_support (L.safe marked) marked advance
    rate opaqueFraction hr hr1 hl hl1 (L.opaque_safe marked)
    (L.hazard marked rate bounded) [] tree budget fresh queriesBound

/-- The full generic saturated conclusion retains an externally proved
original-cut cost mean. No resampling or re-extraction on the stopped tree
is introduced by the causal monitor. -/
theorem failure_le_support [Fintype P] [DecidableEq P] [Nonempty A]
    {Out : Type} {fuel queries : ℕ}
    (marked : P → Bool) (tree : Tree P A Out fuel)
    (rate opaqueFraction : ℚ) (hr : 0 ≤ rate) (hr1 : rate ≤ 1)
    (hl : 0 ≤ opaqueFraction) (hl1 : opaqueFraction ≤ 1)
    (bounded : ∀ p, marked p = false → L.budget p ≤ rate)
    (budget : rate * queries ≤ 1)
    (fresh : FreshOracle.FreshFrom (fun _ => False) tree)
    (queriesBound : ∀ H, (seen tree H).card ≤ queries)
    (failed hash : (P → A) → Prop) (cost : (P → A) → ℚ)
    (nonnegative : ∀ H, 0 ≤ cost H)
    (cover : ∀ H, failed H → ¬hash H →
      ((L.audit marked tree).run H).1.1 = true ∨ 1 ≤ cost H)
    (cost_mean : (∑ H, cost H) / Fintype.card (P → A) ≤
      (opaqueFraction*rate) * ((∑ H : P → A, (((L.audit marked tree).run H).1.2 : ℚ)) /
        Fintype.card (P → A))) :
    density failed ≤ Survival.Hybrid.envelope rate opaqueFraction queries + density hash := by
  exact Survival.FiniteCover.failure_le failed hash _ _ cost (opaqueFraction*rate) _
    nonnegative cover cost_mean
    (L.saturated_law_le_support marked tree rate opaqueFraction hr hr1 hl hl1 bounded budget fresh queriesBound)

theorem linear_failure_le_support [Fintype P] [DecidableEq P] [Nonempty A]
    {Out : Type} {fuel queries : ℕ}
    (marked : P → Bool) (tree : Tree P A Out fuel)
    (rate allowance : ℚ) (positive : 0 ≤ rate) (allowance_le : allowance ≤ rate)
    (bounded : ∀ p, marked p = false → L.budget p ≤ rate)
    (fresh : FreshOracle.FreshFrom (fun _ => False) tree)
    (queriesBound : ∀ H, (seen tree H).card ≤ queries)
    (failed hash : (P → A) → Prop) (cost : (P → A) → ℚ)
    (nonnegative : ∀ H, 0 ≤ cost H)
    (cover : ∀ H, failed H → ¬hash H →
      ((L.audit marked tree).run H).1.1 = true ∨ 1 ≤ cost H)
    (cost_mean : (∑ H, cost H) / Fintype.card (P → A) ≤
      allowance * ((∑ H : P → A, (((L.audit marked tree).run H).1.2 : ℚ)) /
        Fintype.card (P → A))) : density failed ≤ rate*queries + density hash := by
  exact Survival.FiniteCover.failure_le failed hash _ _ cost allowance _ nonnegative cover cost_mean
    (L.linear_law_le_support marked tree rate allowance positive allowance_le bounded fresh queriesBound)

section RetainedCharges
variable {D C Parent Response : Type} [Fintype D] [Fintype C] [Fintype Response]
variable [DecidableEq P]
variable {S : P → Type} (K : CausalCharges P (D × C) S)
variable (original : Composition.LocalCharges P D C Parent Response)

/-- Only the monitor changes. The pair weights and all opaque costs remain
the original charges, retaining the original unstopped commitment cut. -/
theorem stopped_charge_of_causal_cover [Fintype Parent] {Out : Type} {fuel rounds : ℕ}
    (marked : P → Bool) (tree : Tree P (D × C) Out fuel) (H : P → D × C)
    (path : ℕ → P) (queried : Composition.PathQueries (rounds := rounds) tree H path)
    (cover : original.Covers (rounds := rounds) path H)
    (survived : ((K.audit marked tree).run H).1.1 = false)
    (causal : ∀ i < rounds, ∀ past rest a,
      (tree.run H).2 = past ++ (path i,a)::rest →
      past.map Prod.fst = before tree H (path i) →
      K.single (path i) (K.extract (path i) past) a = original.single (path i) H a) :
    1 ≤ (Survival.StoppedCharges.restrict original marked).charge (K.audit marked tree) H := by
  have same := Survival.History.audit_trace (K.safe marked) marked advance [] tree H survived
  change ((K.audit marked tree).run H).2 = (tree.run H).2 at same
  have queried' i (within : i ≤ rounds) : path i ∈ seen (K.audit marked tree) H := by
    simpa only [seen, Bcs.TotalOracle.queried, same] using queried.queried i within
  have ordered i (within : i < rounds) :
      firstOfTwo (K.audit marked tree) H (path i) (path (i+1)) = .left := by
    change firstOfTwo (Survival.History.audit (K.safe marked) marked advance [] tree) H
      (path i) (path (i+1)) = .left
    rw [Survival.History.order_preserved (K.safe marked) marked advance [] tree H survived]
    exact queried.ordered i within
  apply PathCharges.charges_of_cover (K.audit marked tree) H path queried' ordered
    (Survival.StoppedCharges.restrict original marked).single_nonneg
    (Survival.StoppedCharges.restrict original marked).pair_nonneg
  apply Survival.StoppedCharges.covers_restrict original marked path H cover
  intro i within transparent
  exact K.no_escape_of_causal_single marked tree H survived original.single (path i)
    (queried.queried i within.le) transparent (causal i within)

end RetainedCharges
end CausalCharges
end Survival
