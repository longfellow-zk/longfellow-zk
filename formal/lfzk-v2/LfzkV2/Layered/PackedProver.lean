import LfzkV2.Layered.Packed
import LfzkV2.Layered.Prover

/-! Honest completeness uses the same final input equation as extraction.
The packer receives that equation directly, then emits its two affine rows.
Its Frobenius mask relation is needed for honest construction only. -/

namespace LfzkV2.Layered.Packed

open Finset Module SumcheckV2 DualPacking DualPacking.ArtinSchreier
open scoped Classical

variable {K F I J Slot Pad : Type} [Field K] [Fintype K] [Field F] [Fintype F]
  [Algebra K F] [Fintype I] [DecidableEq I] [Fintype J]
variable (S : LfzkV2.Packed.Statement K F I J Slot)

theorem honest_rows {input nPublic nPrivate : ℕ}
    (cs : Linear.Constraints Pad F) (weights : Cube input → F)
    (inputIndex : (Fin nPublic ⊕ Fin nPrivate) ↪ Cube input)
    (packedIndex : Fin nPrivate ↪ J × I) (publicInputs : Fin nPublic → F)
    (coordinate : Pad → Slot) (values : Slot → F)
    (hcs : cs.Holds (values ∘ coordinate)
      (dot weights (S.inputs inputIndex packedIndex publicInputs values))) (delta : I → F)
    (hmask : frobenius K F (S.realize values).r = (S.realize values).b) :
    let T := S.withSource packedIndex cs.inputClaim coordinate
      (fun i => weights (inputIndex (.inl i))) publicInputs
      (fun i => weights (inputIndex (.inr i)))
    let P := T.realize values
    (∀ i, traceF K (P.honestU i) = 0) ∧
      RowsHold (Linear.Packed.rows S cs packedIndex coordinate
        (fun i => weights (inputIndex (.inl i))) publicInputs
        (fun i => weights (inputIndex (.inr i))) P.honestU delta (P.honestA delta)) values := by
  intro T P
  have htrue : P.target = P.trueValue := by
    apply (S.source_claim_iff packedIndex cs.inputClaim coordinate _ publicInputs _ values).mpr
    have h := hcs.2
    rw [LfzkV2.Packed.Statement.inputs, input_sum] at h
    exact h
  have htrace : ∀ i, traceF K (P.honestU i) = 0 := by
    intro i
    rw [P.trace_honestU, htrue, sub_self]
  refine ⟨htrace, (Linear.Packed.rows_iff S cs packedIndex coordinate _ publicInputs _
    P.honestU delta (P.honestA delta) values htrace).mpr ⟨hcs.1, ?_⟩⟩
  exact P.native_linear_completeness htrue hmask delta

/-- Honest completeness with per-proof virtual inputs: the final input
equation over `[public | committed | virtual]` gives true substituted rows. -/
theorem honest_virtual_rows {input nPublic nPrivate nVirtual : ℕ}
    (cs : Linear.Constraints Pad F) (weights : Cube input → F)
    (inputIndex : (Fin nPublic ⊕ Fin nPrivate) ↪ Cube input)
    (virtualIndex : Fin nVirtual ↪ Cube input) (packedIndex : Fin nPrivate ↪ J × I)
    (publicInputs : Fin nPublic → F) (entries : Fin nVirtual → VirtualInput (Fin nPrivate) F)
    (coordinate : Pad → Slot) (values : Slot → F)
    (hcs : cs.Holds (values ∘ coordinate)
      (dot weights (S.virtualInputs inputIndex virtualIndex packedIndex publicInputs entries values)))
    (delta : I → F) (hmask : frobenius K F (S.realize values).r = (S.realize values).b) :
    let T := S.withVirtualSource packedIndex cs.inputClaim coordinate weights inputIndex virtualIndex
      publicInputs entries
    let P := T.realize values
    (∀ i, traceF K (P.honestU i) = 0) ∧
      RowsHold (virtualRows S cs weights inputIndex virtualIndex packedIndex coordinate publicInputs
        entries P.honestU delta (P.honestA delta)) values := by
  intro T P
  have htrue : P.target = P.trueValue :=
    (S.virtual_source_claim_iff packedIndex cs.inputClaim coordinate weights inputIndex virtualIndex
      publicInputs entries values).mpr hcs.2
  have htrace : ∀ i, traceF K (P.honestU i) = 0 := by
    intro i
    rw [P.trace_honestU,htrue,sub_self]
  refine ⟨htrace,(Linear.Packed.rows_iff S cs packedIndex coordinate _ _ _
    P.honestU delta (P.honestA delta) values htrace).mpr ⟨hcs.1,?_⟩⟩
  exact P.native_linear_completeness htrue hmask delta

end LfzkV2.Layered.Packed
