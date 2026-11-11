import TranscriptV2.Replay
import Merkle.TreeCompose

/-! Verifier replay as an oracle program, used only in the Merkle composition.
The Fiat--Shamir charging theorem continues to use the original adversary's
query budget. These verifier queries contribute only to the digest-sized
Merkle explanation term; they are not extra protocol rounds. -/
namespace TranscriptV2.Chain
open Merkle.RandomOracle

variable {P Link C Out : Type} {R : ℕ}
variable (M : TranscriptV2.Chain P Link C Out R)

def recomputeFrom (out : Out) : (remaining start : ℕ) → M.State →
    Tree P (Link × C) M.State remaining
  | 0, _, state => .done state
  | remaining+1, start, state =>
      if h : start < R then
        .query (M.input state) fun answer =>
          recomputeFrom out remaining (start+1) (M.advance out ⟨start,h⟩ state answer)
      else .done state

theorem recomputeFrom_result (out : Out) (H : P → Link × C) (remaining start : ℕ)
    (h : start+remaining ≤ R) :
    ((M.recomputeFrom out remaining start (M.replay out H start)).run H).1 =
      M.replay out H (start+remaining) := by
  induction remaining generalizing start with
  | zero => rfl
  | succ remaining ih =>
      have hs : start < R := by omega
      simp only [recomputeFrom, dif_pos hs, Tree.run_query]
      have ha : M.advance out ⟨start,hs⟩ (M.replay out H start)
          (H (M.input (M.replay out H start))) = M.replay out H (start+1) := by
        simp only [replay, dif_pos hs]
      rw [ha]
      simpa only [Nat.add_assoc, Nat.add_comm 1 remaining] using ih (start+1) (by omega)

/-- Replay visits exactly the ordinary boundary inputs, in protocol order.
This describes verifier work and assumes nothing about the prover's order. -/
theorem recomputeFrom_trace (out : Out) (H : P → Link × C) (remaining start : ℕ)
    (h : start+remaining ≤ R) :
    ((M.recomputeFrom out remaining start (M.replay out H start)).run H).2 =
      List.ofFn (fun i : Fin remaining => (M.point out H (start+i.val),H (M.point out H (start+i.val)))) := by
  induction remaining generalizing start with
  | zero => rfl
  | succ remaining ih =>
      have hs : start < R := by omega
      simp only [recomputeFrom,dif_pos hs,Tree.run_query,List.ofFn_succ,Fin.val_zero,Nat.add_zero,Fin.val_succ]
      have ha : M.advance out ⟨start,hs⟩ (M.replay out H start)
          (H (M.input (M.replay out H start))) = M.replay out H (start+1) := by
        simp only [replay,dif_pos hs]
      rw [ha,ih (start+1) (by omega)]
      simp only [Nat.add_assoc,Nat.add_comm 1]
      rfl

def recompute (out : Out) : Tree P (Link × C) (Out × M.State) R :=
  (M.recomputeFrom out R 0 (M.initial out)).map fun state => (out,state)

theorem recompute_result (out : Out) (H : P → Link × C) :
    ((M.recompute out).run H).1 = (out,M.replay out H R) := by
  rw [recompute, Tree.run_map]
  apply congrArg (Prod.mk out)
  simpa only [Nat.zero_add, show M.replay out H 0 = M.initial out from rfl] using
    M.recomputeFrom_result out H R 0 (by omega)

theorem recompute_trace (out : Out) (H : P → Link × C) :
    ((M.recompute out).run H).2 =
      List.ofFn (fun i : Fin R => (M.point out H i.val,H (M.point out H i.val))) := by
  rw [recompute,Tree.run_map]
  simpa only [Nat.zero_add,show M.replay out H 0 = M.initial out from rfl] using
    M.recomputeFrom_trace out H R 0 (by omega)

end TranscriptV2.Chain
