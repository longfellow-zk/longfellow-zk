import LfzkV2.Layered.Replay

/-! Entry blocks add challenges but no sumcheck messages or pad rows. The
slot bound uses the global layer dimensions, never a sum of per-circuit
round counts. -/

namespace LfzkV2.Layered.Replay

open LfzkV2.Replay (vectorSlots)

variable {F : Type}

theorem slots_le {out input : ℕ} (circuit : Layered.Circuit F out input) :
    slots circuit ≤ circuit.ordinaryBudget + circuit.layers := by
  induction circuit with
  | input => simp [slots, layerSlots, Circuit.ordinaryBudget, Circuit.layers]
  | entry n e rest ih =>
      have hn : vectorSlots n = min 1 n := by cases n <;> simp [vectorSlots]
      simp only [slots, layerSlots, Circuit.ordinaryBudget, Circuit.layers, hn] at ih ⊢
      omega
  | @layer out mid input n body rest ih =>
      have hn : vectorSlots n = min 1 n := by cases n <;> simp [vectorSlots]
      simp only [slots, layerSlots, Circuit.ordinaryBudget, Circuit.layers, hn] at ih ⊢
      omega

/-- Independent output sampling costs one linear event per nonempty entry
block, regardless of its number of outputs. Each ordinary layer adds at most
one assertion block and one combining event. -/
theorem ordinaryBudget_le {out input : ℕ} (circuit : Layered.Circuit F out input) :
    circuit.ordinaryBudget ≤ circuit.entryBlocks + 2*circuit.rounds + 2*circuit.layers := by
  induction circuit with
  | input => simp [Circuit.ordinaryBudget, Circuit.entryBlocks, Circuit.rounds, Circuit.layers]
  | entry n e rest ih =>
      simp only [Circuit.ordinaryBudget, Circuit.entryBlocks, Circuit.rounds, Circuit.layers]
      omega
  | @layer out mid input n body rest ih =>
      have hn := Nat.min_le_left 1 n
      simp only [Circuit.ordinaryBudget, Circuit.entryBlocks, Circuit.rounds, Circuit.layers]
      omega

theorem mdoc_hash_budget {out input : ℕ} (circuit : Layered.Circuit F out input)
    (he : circuit.entryBlocks ≤ 1) (hr : circuit.rounds ≤ 274) (hl : circuit.layers ≤ 20) :
    circuit.ordinaryBudget ≤ 589 := by
  have h := ordinaryBudget_le circuit
  omega

theorem mdoc_signature_budget {out input : ℕ} (circuit : Layered.Circuit F out input)
    (he : circuit.entryBlocks ≤ 1) (hr : circuit.rounds ≤ 260) (hl : circuit.layers ≤ 21) :
    circuit.ordinaryBudget ≤ 563 := by
  have h := ordinaryBudget_le circuit
  omega

end LfzkV2.Layered.Replay
