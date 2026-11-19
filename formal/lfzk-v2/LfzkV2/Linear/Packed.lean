import LfzkV2.Linear.Backend
import LfzkV2.Packed.Inputs

/-!
# Packed inputs and the linear-terminal frontend

The dual-packing algebra is unchanged. This file connects its two actual
affine rows to the new frontend compiler, without passing through the old
product-checked frontend or assuming a source-input equation.
-/

namespace LfzkV2.Linear.Packed

open Finset Module SumcheckV2 DualPacking DualPacking.ArtinSchreier
open scoped Classical

variable {K F I J Slot Pad : Type} [Field K] [Fintype K] [Field F] [Fintype F]
  [Algebra K F] [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq F]

variable (S : LfzkV2.Packed.Statement K F I J Slot)

noncomputable def rows {nPublic nPrivate : ℕ} (cs : Constraints Pad F)
    (packedIndex : Fin nPrivate ↪ J × I) (coordinate : Pad → Slot)
    (publicWeights publicInputs : Fin nPublic → F) (privateWeights : Fin nPrivate → F)
    (U delta : I → F) (A : F) : List (LinearRow Slot F) :=
  cs.layers.map (fun row => LfzkV2.Backend.remap row coordinate) ++
    (S.withSource packedIndex cs.inputClaim coordinate publicWeights publicInputs privateWeights).rows U delta A

omit [DecidableEq F] in
/-- The compiler emits only renamed terminal rows and the two packing rows. -/
theorem rows_iff {nPublic nPrivate : ℕ} (cs : Constraints Pad F)
    (packedIndex : Fin nPrivate ↪ J × I) (coordinate : Pad → Slot)
    (publicWeights publicInputs : Fin nPublic → F) (privateWeights : Fin nPrivate → F)
    (U delta : I → F) (A : F) (values : Slot → F)
    (htrace : ∀ k, traceF K (U k) = 0) :
    RowsHold (rows S cs packedIndex coordinate publicWeights publicInputs privateWeights U delta A) values ↔
      (∀ row ∈ cs.layers, row.eval (values ∘ coordinate) = 0) ∧
        ((S.withSource packedIndex cs.inputClaim coordinate publicWeights publicInputs
          privateWeights).realize values).nativeLinearVerify U delta A := by
  simp only [RowsHold, rows, List.forall_mem_append, List.forall_mem_map,
    LfzkV2.Backend.eval_remap]
  exact and_congr_right (fun _ =>
    (S.withSource packedIndex cs.inputClaim coordinate publicWeights publicInputs privateWeights).rows_iff_native
      values U delta A htrace)

theorem frontend_or_bad {out input nPublic nPrivate : ℕ}
    (circuit : Native.Circuit F out input) (m : Circuit.Messages Pad circuit) (point : Fin out → F)
    (cs : Constraints Pad F)
    (hbuild : buildConstraints (Circuit.proof circuit m (monomialWeights point)) = some cs)
    (inputIndex : (Fin nPublic ⊕ Fin nPrivate) ↪ Cube input)
    (packedIndex : Fin nPrivate ↪ J × I) (publicInputs : Fin nPublic → F)
    (coordinate : Pad → Slot) (values : Slot → F) (U delta : I → F) (A : F)
    (hlayers : ∀ row ∈ cs.layers, row.eval (values ∘ coordinate) = 0)
    (hpacking : ((S.withSource packedIndex cs.inputClaim coordinate
      (fun i => Circuit.inputWeights circuit m (monomialWeights point) (inputIndex (.inl i))) publicInputs
      (fun i => Circuit.inputWeights circuit m (monomialWeights point) (inputIndex (.inr i)))).realize values).nativeLinearVerify
        U delta A) :
    ClearAccepts (values ∘ coordinate) 0 (Circuit.proof circuit m (monomialWeights point))
      (dot (Circuit.inputWeights circuit m (monomialWeights point))
        (S.inputs inputIndex packedIndex publicInputs values)) ∨
      (S.withSource packedIndex cs.inputClaim coordinate
        (fun i => Circuit.inputWeights circuit m (monomialWeights point) (inputIndex (.inl i))) publicInputs
        (fun i => Circuit.inputWeights circuit m (monomialWeights point) (inputIndex (.inr i)))).Bad values U delta := by
  let T := S.withSource packedIndex cs.inputClaim coordinate
    (fun i => Circuit.inputWeights circuit m (monomialWeights point) (inputIndex (.inl i))) publicInputs
    (fun i => Circuit.inputWeights circuit m (monomialWeights point) (inputIndex (.inr i)))
  rcases T.target_or_bad values U delta A hpacking with htrue | hbad
  · apply Or.inl
    apply (buildConstraints_correct _ _ _).mp
    refine ⟨cs, hbuild, hlayers, ?_⟩
    have hsource := (S.source_claim_iff packedIndex cs.inputClaim coordinate
      (fun i => Circuit.inputWeights circuit m (monomialWeights point) (inputIndex (.inl i))) publicInputs
      (fun i => Circuit.inputWeights circuit m (monomialWeights point) (inputIndex (.inr i))) values).mp htrue
    rw [LfzkV2.Packed.Statement.inputs, input_sum]
    simpa only [Function.comp_id] using hsource
  · exact Or.inr hbad

/-- Actual linear backend rows imply an accepted native frontend or the
already-counted packing escape. No assertion about product cells is needed. -/
theorem rows_frontend_or_bad {out input nPublic nPrivate : ℕ}
    (circuit : Native.Circuit F out input) (m : Circuit.Messages Pad circuit) (point : Fin out → F)
    (cs : Constraints Pad F)
    (hbuild : buildConstraints (Circuit.proof circuit m (monomialWeights point)) = some cs)
    (inputIndex : (Fin nPublic ⊕ Fin nPrivate) ↪ Cube input)
    (packedIndex : Fin nPrivate ↪ J × I) (publicInputs : Fin nPublic → F)
    (coordinate : Pad → Slot) (values : Slot → F) (U delta : I → F) (A : F)
    (htrace : ∀ k, traceF K (U k) = 0)
    (hrows : RowsHold (rows S cs packedIndex coordinate
      (fun i => Circuit.inputWeights circuit m (monomialWeights point) (inputIndex (.inl i))) publicInputs
      (fun i => Circuit.inputWeights circuit m (monomialWeights point) (inputIndex (.inr i))) U delta A) values) :
    ClearAccepts (values ∘ coordinate) 0 (Circuit.proof circuit m (monomialWeights point))
      (dot (Circuit.inputWeights circuit m (monomialWeights point))
        (S.inputs inputIndex packedIndex publicInputs values)) ∨
      (S.withSource packedIndex cs.inputClaim coordinate
        (fun i => Circuit.inputWeights circuit m (monomialWeights point) (inputIndex (.inl i))) publicInputs
        (fun i => Circuit.inputWeights circuit m (monomialWeights point) (inputIndex (.inr i)))).Bad values U delta := by
  obtain ⟨hlayers, hpacking⟩ := (rows_iff S cs packedIndex coordinate _ publicInputs _ U delta A values htrace).mp hrows
  exact frontend_or_bad S circuit m point cs hbuild inputIndex packedIndex publicInputs coordinate
    values U delta A hlayers hpacking

end LfzkV2.Linear.Packed
