import LfzkV2.Linear.TerminalSampling
import LfzkV2.Layered.Soundness
import LigeroFamily.Protocol.Finite

/-! The current prime frontend batches every affine layer row and the final
input equation. Its backend omits the shared bit prefix and contains a hiding
scalar. The binary participant contains its own copy of that scalar: equality
is a consequence of the rescaling check, never an extraction premise. -/
namespace LfzkV2.Current.Prime
open Finset SumcheckV2
open scoped Classical

variable {F Slot Shared Other : Type} [Field F]

/-- Algebraic form of `zk-v2/row_batching.rs::batch`, retaining duplicate terms. -/
def batchRows {n : ℕ} (rows : Fin n → LinearRow Slot F) (rho : Fin n → F) : LinearRow Slot F where
  constant := ∑ i, rho i * (rows i).constant
  terms := (List.ofFn fun i => (rows i).terms.map fun term => (term.1, rho i * term.2)).flatten

theorem batchRows_eval {n : ℕ} (rows : Fin n → LinearRow Slot F) (rho : Fin n → F)
    (values : Slot → F) :
    (batchRows rows rho).eval values = ∑ i, rho i * (rows i).eval values := by
  simp only [batchRows, PadExpression.eval, List.map_flatten, List.sum_flatten,
    List.map_ofFn, List.sum_ofFn, List.map_map, Function.comp_def]
  simp only [mul_add, mul_assoc, List.sum_map_mul_left, ← sum_add_distrib]

def BatchBad {n : ℕ} (residuals rho : Fin n → F) : Prop :=
  residuals ≠ 0 ∧ LigeroFamily.finiteDot rho residuals = 0

theorem batch_rows_or_bad {n : ℕ} (rows : Fin n → LinearRow Slot F) (rho : Fin n → F)
    (values : Slot → F) (h : (batchRows rows rho).eval values = 0) :
    (∀ i, (rows i).eval values = 0) ∨ BatchBad (fun i => (rows i).eval values) rho := by
  by_cases hz : (fun i => (rows i).eval values) = 0
  · exact Or.inl (fun i => congrFun hz i)
  · exact Or.inr ⟨hz, by simpa [batchRows_eval, LigeroFamily.finiteDot] using h⟩

/-- Whole-vector counting: this is one query, even with many prime rows. -/
theorem batch_bad_card_mul_le [Fintype F] [DecidableEq F] {n : ℕ} (residuals : Fin n → F) :
    (univ.filter (BatchBad residuals)).card * Fintype.card F ≤ Fintype.card (Fin n → F) := by
  by_cases hz : residuals = 0
  · simp [BatchBad, hz]
  · have hcard : (univ.filter (BatchBad residuals)).card ≤ Fintype.card F ^ (n-1) := by
      simpa [BatchBad, hz, LigeroFamily.affineEquationSolutions] using
        LigeroFamily.card_affineEquationSolutions_le residuals 0 hz
    have hn : 0 < n := by
      by_contra h
      have hn : n = 0 := by omega
      subst n
      exact hz (Subsingleton.elim _ _)
    calc
      _ ≤ Fintype.card F ^ (n-1) * Fintype.card F := Nat.mul_le_mul_right _ hcard
      _ = Fintype.card (Fin n → F) := by
        rw [← pow_succ]
        simp [Nat.sub_add_cancel hn]

/-- Use the actual affine compiler, including the final input row. Witness
slots here are the reconstructed full prime input/pad vector: the backend
authenticates its batch through the shared-prefix handoff below. -/
theorem compiled_batched_reduction {out input nPublic nPrivate : ℕ} {Pad : Type}
    (circuit : Layered.Circuit F out input) (messages : Layered.Circuit.Messages Pad circuit)
    (index : (Fin nPublic ⊕ Fin nPrivate) ↪ Cube input)
    (publicInputs : Fin nPublic → F) (privateCoordinate : Fin nPrivate → Slot)
    (coordinate : Pad → Slot) (witness : Slot → F) (cs : Linear.Constraints Pad F)
    (hbuild : Linear.buildConstraints (Layered.Circuit.proof circuit messages 0) = some cs)
    (rows : List (LinearRow Slot F))
    (hrows : rows = Linear.compile cs coordinate privateCoordinate
      (fun i => Layered.Circuit.inputWeights circuit messages 0 (index (.inl i))) publicInputs
      (fun i => Layered.Circuit.inputWeights circuit messages 0 (index (.inr i))))
    (rho : Fin rows.length → F)
    (hbatch : (batchRows rows.get rho).eval witness = 0)
    (hfalse : ¬ circuit.Satisfies (circuitInputs index publicInputs privateCoordinate witness)) :
    BatchBad (fun i => (rows.get i).eval witness) rho ∨
      Layered.Circuit.Bad circuit messages
        (circuitInputs index publicInputs privateCoordinate witness) 0 (witness ∘ coordinate) 0 := by
  rcases batch_rows_or_bad rows.get rho witness hbatch with hgood | hbad
  · apply Or.inr
    apply Layered.Circuit.compiled_circuit_reduction circuit messages index publicInputs
      privateCoordinate coordinate witness cs hbuild ?_ hfalse
    rw [← hrows]
    intro row hr
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp hr
    exact hgood i
  · exact Or.inl hbad

/-- `Other` contains the remaining prime inputs and all prime pads. The
shared inputs come from binary unpacking; neither vector includes the hiding
scalar or the dedicated fingerprint masks. -/
structure Claim (Shared Other F : Type) where
  sharedWeights : Shared → F
  otherWeights : Other → F
  target : F

variable [Fintype Shared] [Fintype Other]

def Claim.residual (c : Claim Shared Other F) (shared : Shared → F) (other : Other → F) : F :=
  (∑ i, c.sharedWeights i * shared i) + (∑ i, c.otherWeights i * other i) - c.target

/-- Exactly the affine row from the shared prime participant's `finish`. -/
noncomputable def Claim.row (c : Claim Shared Other F) (eta mu : F) : LinearRow (Other ⊕ Unit) F where
  constant := mu - eta * c.target
  terms := (univ.toList.map fun i => (Sum.inl i, eta * c.otherWeights i)) ++ [(Sum.inr (), -1)]

omit [Fintype Shared] in
theorem Claim.row_eval (c : Claim Shared Other F) (eta mu mask : F) (other : Other → F) :
    (c.row eta mu).eval (Sum.elim other (fun _ => mask)) =
      eta * (∑ i, c.otherWeights i * other i) - mask + mu - eta * c.target := by
  simp [Claim.row, PadExpression.eval, mul_assoc, mul_sum]
  ring

def RescalingBad (residual difference eta : F) : Prop :=
  residual ≠ 0 ∧ eta * residual + difference = 0

theorem rescaling_bad_card [Fintype F] [DecidableEq F] (residual difference : F) :
    (univ.filter fun eta : Linear.TerminalSampling.Nonzero F =>
      RescalingBad residual difference eta.val).card ≤ 1 := by
  apply card_le_one.mpr
  intro a ha b hb
  obtain ⟨hr, ha⟩ := (mem_filter.mp ha).2
  have hb := (mem_filter.mp hb).2.2
  exact Subtype.ext (mul_right_cancel₀ hr (add_right_cancel (ha.trans hb.symm)))

/-- Combining the binary opening with the prime row leaves one affine
equation in eta, even if the two extracted masks differ. -/
theorem Claim.handoff (c : Claim Shared Other F) (shared : Shared → F) (other : Other → F)
    (eta mu binaryMask primeMask : F)
    (hadapter : mu = eta * (∑ i, c.sharedWeights i * shared i) + binaryMask)
    (hrow : (c.row eta mu).eval (Sum.elim other (fun _ => primeMask)) = 0) :
    eta * c.residual shared other + (binaryMask - primeMask) = 0 := by
  rw [c.row_eval, hadapter] at hrow
  dsimp [Claim.residual]
  linear_combination hrow

theorem Claim.true_or_rescaling_bad (c : Claim Shared Other F)
    (shared : Shared → F) (other : Other → F) (eta mu binaryMask primeMask : F)
    (hadapter : mu = eta * (∑ i, c.sharedWeights i * shared i) + binaryMask)
    (hrow : (c.row eta mu).eval (Sum.elim other (fun _ => primeMask)) = 0) :
    (c.residual shared other = 0 ∧ binaryMask = primeMask) ∨
      RescalingBad (c.residual shared other) (binaryMask - primeMask) eta := by
  have h := c.handoff shared other eta mu binaryMask primeMask hadapter hrow
  by_cases hz : c.residual shared other = 0
  · exact Or.inl ⟨hz, by simpa [hz, sub_eq_zero] using h⟩
  · exact Or.inr ⟨hz, h⟩

end LfzkV2.Current.Prime
