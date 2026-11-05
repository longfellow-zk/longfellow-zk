import LfzkV2.Native.Replay
import LfzkV2.RuntimeSecurity

/-! Conservative native frontend budgets from circuit metadata. A nonempty
assertion batch costs one root test, each sumcheck round costs two, and each
layer's final combination costs one. No semantic property of a layer is
needed to bound these counts. -/

namespace LfzkV2.Native.Circuit

variable {F : Type}

def rounds : {out input : ℕ} → Circuit F out input → ℕ
  | _, _, .input => 0
  | _, _, .layer (mid := mid) _ _ rest => mid + rest.rounds

def layers : {out input : ℕ} → Circuit F out input → ℕ
  | _, _, .input => 0
  | _, _, .layer _ _ rest => 1 + rest.layers

theorem sharpLayerBudget_le {out input : ℕ} (circuit : Circuit F out input) :
    circuit.sharpLayerBudget ≤ 2*circuit.rounds + 2*circuit.layers := by
  induction circuit with
  | input => rfl
  | @layer out mid input a body rest ih =>
      change min 1 a + 2*mid + 1 + rest.sharpLayerBudget ≤
        2*(mid + rest.rounds) + 2*(1 + rest.layers)
      have hmin := Nat.min_le_left 1 a
      omega

theorem hash_frontend_budget {out input : ℕ} (circuit : Circuit F out input)
    (hout : out ≤ 5) (hrounds : circuit.rounds ≤ 274) (hlayers : circuit.layers ≤ 20) :
    out + circuit.sharpLayerBudget ≤ 593 := by
  have := circuit.sharpLayerBudget_le
  omega

theorem signature_frontend_budget {out input : ℕ} (circuit : Circuit F out input)
    (hout : out ≤ 3) (hrounds : circuit.rounds ≤ 260) (hlayers : circuit.layers ≤ 21) :
    out + circuit.sharpLayerBudget ≤ 565 := by
  have := circuit.sharpLayerBudget_le
  omega

theorem replay_slots_le_budget {out input : ℕ} (circuit : Circuit F out input) :
    LfzkV2.Replay.slots circuit.shape ≤ out + circuit.sharpLayerBudget := by
  simpa only [shape_sharpLayerBudget] using LfzkV2.Replay.slots_le_budget circuit.shape

end LfzkV2.Native.Circuit
