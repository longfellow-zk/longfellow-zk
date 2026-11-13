import LfzkV2.Current.Selection
import LfzkV2.Current.PrimeClaim
import LfzkV2.Current.AdapterParameters
import LfzkV2.Current.Handoff
import LfzkV2.Current.AdapterTree

namespace LfzkV2.Current.Tests
instance : Fact (Nat.Prime 5) := ⟨by decide⟩

-- Unequal committed masks can cancel a false claim at one rescaling. The
-- reduction must charge this event rather than assume mask equality.
example : Prime.RescalingBad (1 : ZMod 5) 4 1 := by
  unfold Prime.RescalingBad
  decide
example : ¬ Prime.RescalingBad (1 : ZMod 5) 4 2 := by
  unfold Prime.RescalingBad
  decide

-- Layer rows enter the prime statement unbatched: a false layer row fails
-- for every rescaling challenge and masked message.
def falseLayer : Prime.Claim Unit Unit (ZMod 5) := ⟨[⟨1, []⟩], fun _ => 0, fun _ => 0, 0⟩
example (eta mu mask : ZMod 5) :
    ¬ LfzkV2.RowsHold (falseLayer.rows eta mu) (Sum.elim (fun _ => 0) (fun _ => mask)) := by
  rw [Prime.Claim.rows_hold_iff]
  simp [falseLayer, LfzkV2.RowsHold, SumcheckV2.PadExpression.eval]
example (eta mu : ZMod 5) : (falseLayer.rows eta mu).length = 2 := rfl

instance : Fact (Nat.Prime 7) := ⟨by decide⟩

-- Sparse occurrences add when forming the dense split claim. The runtime's
-- weights negate the compiled input row, whose constant is the target.
def repeatedRow : LfzkV2.LinearRow (Unit ⊕ Unit) (ZMod 7) :=
  ⟨1, [(.inl (), 2), (.inl (), 3), (.inr (), 4)]⟩
example : (Prime.Claim.split [] repeatedRow).sharedWeights () = 2 := by
  simp [Prime.Claim.split, Prime.coefficients, repeatedRow]
  decide
example : (Prime.Claim.split [] repeatedRow).target = 1 := rfl
example : (Prime.Claim.split [] repeatedRow).residual (fun _ => 1) (fun _ => 2) = 0 := by
  rw [Prime.Claim.split_residual]
  decide

-- Binary mask bits need not encode a canonical prime integer. The handoff
-- compares the residue in the prime field and still counts all 3 input bits.
example : Handoff.binaryMask (p := 5) (fun _ : Fin 3 => true) = 2 := by
  decide
example : Adapter.residual (Handoff.weights (fun _ : Fin 1 => (2 : ZMod 5)) 3)
    (Handoff.values (fun _ : Fin 1 => true) (fun _ : Fin 3 => true)) 3 = 0 := by
  decide

-- Rescaling the shared-input term never rescales the hiding scalar. Even
-- when eta is zero, the reconstructed mask retains coefficient one.
example {p shared maskBits : ℕ} [Fact p.Prime]
    (weights : Fin shared → ZMod p) (bits : Fin shared → Bool) (mask : Fin maskBits → Bool) :
    Adapter.residual (Handoff.weights weights 0) (Handoff.values bits mask) 0 =
      Handoff.binaryMask mask := by
  rw [Handoff.residual_eq]
  simp

-- The modular product check really can accept a false field equation.
-- For p=7, group order 5 and the false claim 1=0, alpha=5 and quotient=0 pass.
example : Adapter.residual (fun _ : Fin 1 => (1 : ZMod 7)) (fun _ => true) 0 ≠ 0 := by
  decide
example : Adapter.Bad (fun _ : Fin 1 => (1 : ZMod 7)) (fun _ => true) 0 5 2
    ⟨5, by decide⟩ := by
  refine ⟨0, by decide, ?_⟩
  decide +kernel

-- The larger prime field does not supply a separate shared-input candidate.
example (bits : WitnessSelection.Candidate (ZMod 2) Unit → Bool → Bool)
    (other : WitnessSelection.Candidate (ZMod 7) Unit → Unit → ZMod 7)
    (w : Selection.Pair (ZMod 2) (ZMod 7) Unit Unit) (i : Bool) :
    Selection.primeInputs bits other w (.inl i) = if bits w.1 i then 1 else 0 := rfl

-- Masked quotient bits decode little-endian.
example : Adapter.Tree.binaryValue [true, false, true] = 5 := by decide

end LfzkV2.Current.Tests
