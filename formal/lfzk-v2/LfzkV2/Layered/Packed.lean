import LfzkV2.Layered.Soundness
import LfzkV2.Linear.Packed

/-! The shared-input layered reduction uses the existing authenticated packer.
The two packing rows and their bad event are reused unchanged. This bridge
checks their actual source equation against the single final input weight
array; it does not assume the extracted field cells are bits. -/

namespace LfzkV2.Layered.Packed

open Finset Module SumcheckV2 DualPacking DualPacking.ArtinSchreier
open scoped Classical

variable {K F I J Slot Pad : Type} [Field K] [Fintype K] [Field F] [Fintype F]
  [Algebra K F] [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq F]
variable (S : LfzkV2.Packed.Statement K F I J Slot)

theorem frontend_or_bad {out input nPublic nPrivate : ℕ}
    (circuit : Layered.Circuit F out input) (m : Circuit.Messages Pad circuit)
    (cs : Linear.Constraints Pad F)
    (hbuild : Linear.buildConstraints (Circuit.proof circuit m 0) = some cs)
    (inputIndex : (Fin nPublic ⊕ Fin nPrivate) ↪ Cube input)
    (packedIndex : Fin nPrivate ↪ J × I) (publicInputs : Fin nPublic → F)
    (coordinate : Pad → Slot) (values : Slot → F) (U delta : I → F) (A : F)
    (hlayers : ∀ row ∈ cs.layers, row.eval (values ∘ coordinate) = 0)
    (hpacking : ((S.withSource packedIndex cs.inputClaim coordinate
      (fun i => Circuit.inputWeights circuit m 0 (inputIndex (.inl i))) publicInputs
      (fun i => Circuit.inputWeights circuit m 0 (inputIndex (.inr i)))).realize values).nativeLinearVerify
        U delta A) :
    Linear.ClearAccepts (values ∘ coordinate) 0 (Circuit.proof circuit m 0)
      (dot (Circuit.inputWeights circuit m 0)
        (S.inputs inputIndex packedIndex publicInputs values)) ∨
      (S.withSource packedIndex cs.inputClaim coordinate
        (fun i => Circuit.inputWeights circuit m 0 (inputIndex (.inl i))) publicInputs
        (fun i => Circuit.inputWeights circuit m 0 (inputIndex (.inr i)))).Bad values U delta := by
  let T := S.withSource packedIndex cs.inputClaim coordinate
    (fun i => Circuit.inputWeights circuit m 0 (inputIndex (.inl i))) publicInputs
    (fun i => Circuit.inputWeights circuit m 0 (inputIndex (.inr i)))
  rcases T.target_or_bad values U delta A hpacking with htrue | hbad
  · apply Or.inl
    apply (Linear.buildConstraints_correct _ _ _).mp
    refine ⟨cs, hbuild, hlayers, ?_⟩
    have hsource := (S.source_claim_iff packedIndex cs.inputClaim coordinate
      (fun i => Circuit.inputWeights circuit m 0 (inputIndex (.inl i))) publicInputs
      (fun i => Circuit.inputWeights circuit m 0 (inputIndex (.inr i))) values).mp htrue
    rw [LfzkV2.Packed.Statement.inputs, input_sum]
    simpa only [Function.comp_id] using hsource
  · exact Or.inr hbad

/-- Actual linear backend rows imply an accepted layered frontend or the
already-counted packing escape. No assertion about product cells is needed. -/
theorem rows_frontend_or_bad {out input nPublic nPrivate : ℕ}
    (circuit : Layered.Circuit F out input) (m : Circuit.Messages Pad circuit)
    (cs : Linear.Constraints Pad F)
    (hbuild : Linear.buildConstraints (Circuit.proof circuit m 0) = some cs)
    (inputIndex : (Fin nPublic ⊕ Fin nPrivate) ↪ Cube input)
    (packedIndex : Fin nPrivate ↪ J × I) (publicInputs : Fin nPublic → F)
    (coordinate : Pad → Slot) (values : Slot → F) (U delta : I → F) (A : F)
    (htrace : ∀ k, traceF K (U k) = 0)
    (hrows : RowsHold (Linear.Packed.rows S cs packedIndex coordinate
      (fun i => Circuit.inputWeights circuit m 0 (inputIndex (.inl i))) publicInputs
      (fun i => Circuit.inputWeights circuit m 0 (inputIndex (.inr i))) U delta A) values) :
    Linear.ClearAccepts (values ∘ coordinate) 0 (Circuit.proof circuit m 0)
      (dot (Circuit.inputWeights circuit m 0)
        (S.inputs inputIndex packedIndex publicInputs values)) ∨
      (S.withSource packedIndex cs.inputClaim coordinate
        (fun i => Circuit.inputWeights circuit m 0 (inputIndex (.inl i))) publicInputs
        (fun i => Circuit.inputWeights circuit m 0 (inputIndex (.inr i)))).Bad values U delta := by
  obtain ⟨hlayers, hpacking⟩ := (Linear.Packed.rows_iff S cs packedIndex coordinate _ publicInputs _ U delta A values htrace).mp hrows
  exact frontend_or_bad S circuit m cs hbuild inputIndex packedIndex publicInputs coordinate
    values U delta A hlayers hpacking

/-- Authenticated packed rows for a false layered statement imply either a
frontend challenge failure or the separately counted packing escape. -/
theorem rows_soundness {out input nPublic nPrivate : ℕ}
    (circuit : Layered.Circuit F out input) (m : Circuit.Messages Pad circuit)
    (cs : Linear.Constraints Pad F)
    (hbuild : Linear.buildConstraints (Circuit.proof circuit m 0) = some cs)
    (inputIndex : (Fin nPublic ⊕ Fin nPrivate) ↪ Cube input)
    (packedIndex : Fin nPrivate ↪ J × I) (publicInputs : Fin nPublic → F)
    (coordinate : Pad → Slot) (values : Slot → F) (U delta : I → F) (A : F)
    (htrace : ∀ k, traceF K (U k) = 0)
    (hrows : RowsHold (Linear.Packed.rows S cs packedIndex coordinate
      (fun i => Circuit.inputWeights circuit m 0 (inputIndex (.inl i))) publicInputs
      (fun i => Circuit.inputWeights circuit m 0 (inputIndex (.inr i))) U delta A) values)
    (hfalse : ¬ circuit.Satisfies (S.inputs inputIndex packedIndex publicInputs values)) :
    Circuit.Bad circuit m (S.inputs inputIndex packedIndex publicInputs values) 0
      (values ∘ coordinate) 0 ∨
      (S.withSource packedIndex cs.inputClaim coordinate
        (fun i => Circuit.inputWeights circuit m 0 (inputIndex (.inl i))) publicInputs
        (fun i => Circuit.inputWeights circuit m 0 (inputIndex (.inr i)))).Bad values U delta := by
  rcases rows_frontend_or_bad S circuit m cs hbuild inputIndex packedIndex publicInputs
    coordinate values U delta A htrace hrows with hf | hp
  · exact Or.inl (Circuit.soundness_reduction circuit m _ _ hfalse hf)
  · exact Or.inr hp

end LfzkV2.Layered.Packed
