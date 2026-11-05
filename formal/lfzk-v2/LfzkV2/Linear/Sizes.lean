import LfzkV2.Linear.Replay
import LfzkV2.Packed.FrontendSizes

/-! Counts for the actual linear-terminal transcript. Round messages contain
two field elements, and each layer adds the cross coefficient and two masked
claims. The committed pad plan has two cells per round and four per layer. -/

namespace LfzkV2.Linear.Replay

variable {F : Type}

def proofElements : {out input : ℕ} → Native.Circuit F out input → ℕ
  | _, _, .input => 0
  | _, _, .layer (mid := mid) _ _ rest => 2*mid+3+proofElements rest

def padElements : {out input : ℕ} → Native.Circuit F out input → ℕ
  | _, _, .input => 0
  | _, _, .layer (mid := mid) _ _ rest => 2*mid+4+padElements rest

theorem proofElements_eq {out input : ℕ} (circuit : Native.Circuit F out input) :
    proofElements circuit = 2*circuit.rounds+3*circuit.layers := by
  induction circuit with
  | input => rfl
  | layer a body rest ih =>
      simp only [proofElements, Native.Circuit.rounds, Native.Circuit.layers]
      omega

theorem padElements_eq {out input : ℕ} (circuit : Native.Circuit F out input) :
    padElements circuit = 2*circuit.rounds+4*circuit.layers := by
  induction circuit with
  | input => rfl
  | layer a body rest ih =>
      simp only [padElements, Native.Circuit.rounds, Native.Circuit.layers]
      omega

end LfzkV2.Linear.Replay
