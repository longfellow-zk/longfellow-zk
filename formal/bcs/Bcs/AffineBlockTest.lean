import Bcs.AffineBlock
import Lean.Util.CollectAxioms

namespace Bcs.AffineBlock.Tests

open Finset FiniteProbability TotalOracle.Footprint Merkle.RandomOracle
open scoped Classical

private def halfRate : Rate := ⟨0, 1/2, by norm_num, by norm_num⟩

/-- Two valid bounds in the same total budget do NOT justify taking the
maximum of the slopes. Their allocated spending is two, not one. -/
example :
    (∀ i : Fin 2, Certificate (fun x : Fin 2 => x = i) (fun _ => 1) halfRate) ∧
    ¬ Certificate (fun _ : Fin 2 => True) (fun _ => 1) halfRate := by
  constructor
  · intro i
    refine ⟨fun _ => by norm_num, ?_⟩
    rw [density_eq_average]
    fin_cases i <;> norm_num [average, Fin.sum_univ_succ, halfRate]
  · intro h
    have hb := h.bound
    norm_num [density, halfRate, average_const] at hb

/-- The intercept remains visible when the adversary spends nothing. -/
example : Certificate (fun _ : Unit => True) (fun _ => 0) (Rate.diagonal 1 (by norm_num)) := by
  constructor
  · intro _; norm_num
  · norm_num [density, Rate.diagonal, average_const]

private def adaptive : Tree Bool Bool Unit 2 :=
  .query false (fun answer => if answer then .query true (fun _ => .done ()) else .done ())

/-- Query ownership is pathwise even when the schedule depends on an
answer. Stopping early is charged by actual calls, not unused fuel. -/
example (H : Bool → Bool) :
    queryCost {false} adaptive H + queryCost {true} adaptive H =
      if H false then 2 else 1 := by
  by_cases h : H false <;> norm_num [adaptive, queryCost, h]

example {n : ℕ} (d : Fin (n+1) → Prop) (h0 : d 0) (hn : ¬ d (Fin.last n)) :
    ∃ i : Fin n, d i.castSucc ∧ ¬ d i.succ := exists_escape d h0 hn

end Bcs.AffineBlock.Tests

open Lean Elab Command

run_cmd do
  for name in #[
      ``Bcs.AffineBlock.parallel,
      ``Bcs.AffineBlock.sequential,
      ``Bcs.AffineBlock.sound_parallel,
      ``Bcs.AffineBlock.queryCost_sum_le,
      ``Bcs.AffineBlock.oracle_parallel_max,
      ``Bcs.AffineBlock.oracle_parallel_certificate,
      ``Bcs.AffineBlock.oracle_sequential_certificate,
      ``Bcs.AffineBlock.oracle_sequential,
      ``Bcs.AffineBlock.of_outside,
      ``Bcs.AffineBlock.of_footprints] do
    for ax in ← collectAxioms name do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unexpected axiom {ax} in {name}"
