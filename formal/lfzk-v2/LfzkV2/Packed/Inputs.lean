import LfzkV2.Packed.Counting

/-! Canonical coordinates bind the packing source equation to the actual native
circuit input. The injection can omit the unused tail of the last packed word;
those coordinates receive coefficient zero. -/

namespace LfzkV2.Packed

open Finset Module SumcheckV2 DualPacking DualPacking.ArtinSchreier
open scoped Classical

variable {K F I J Slot Private : Type} [Field K] [Fintype K] [Field F] [Fintype F]
  [Algebra K F] [Fintype I] [DecidableEq I] [Fintype J] [Fintype Private]

noncomputable def unpack (basis : Basis I K F) (word : J → Slot)
    (index : Private ↪ J × I) (values : Slot → F) (i : Private) : F :=
  digit basis (values (word (index i).1)) (index i).2

noncomputable def sourceCoefficients (index : Private ↪ J × I)
    (weights : Private → F) (j : J) (i : I) : F :=
  zeroExtend index weights (j, i)

omit [Fintype K] [Fintype F] [DecidableEq I] in
theorem source_value (basis : Basis I K F) (word : J → Slot)
    (index : Private ↪ J × I) (weights : Private → F) (values : Slot → F) :
    value basis (sourceCoefficients index weights) (values ∘ word) =
      dot weights (unpack basis word index values) := by
  let digits : J × I → F := fun p => digit basis (values (word p.1)) p.2
  calc
    _ = dot digits (zeroExtend index weights) := by
      simp [value, sourceCoefficients, dot, Fintype.sum_prod_type, digits, mul_comm]
    _ = dot (digits ∘ index) weights := dot_zeroExtend index digits weights
    _ = _ := by simp [dot, digits, unpack, mul_comm]

namespace Statement

variable (S : Statement K F I J Slot)

/-- Compile the final symbolic input claim. The original pads stay in place;
only the private-input coefficients are transposed into packed coordinates. -/
noncomputable def withSource {Pad : Type} {nPublic nPrivate : ℕ}
    (index : Fin nPrivate ↪ J × I) (claim : PadExpression Pad F)
    (coordinate : Pad → Slot) (publicWeights publicInputs : Fin nPublic → F)
    (privateWeights : Fin nPrivate → F) : Statement K F I J Slot :=
  { S with
    coefficients := sourceCoefficients index privateWeights
    target := ⟨claim.constant - dot publicWeights publicInputs, mapTerms claim.terms coordinate⟩ }

omit [Fintype K] [Fintype F] [Fintype I] [DecidableEq I] [Fintype J] in
theorem source_target {Pad : Type} {nPublic nPrivate : ℕ}
    (index : Fin nPrivate ↪ J × I) (claim : PadExpression Pad F)
    (coordinate : Pad → Slot) (publicWeights publicInputs : Fin nPublic → F)
    (privateWeights : Fin nPrivate → F) (values : Slot → F) :
    ((S.withSource index claim coordinate publicWeights publicInputs privateWeights).realize values).target =
      claim.eval (values ∘ coordinate) - dot publicWeights publicInputs := by
  simp only [withSource, realize, PadExpression.eval, mapTerms, List.map_map, Function.comp_def]
  ring

omit [Fintype K] [Fintype F] [DecidableEq I] in
theorem source_trueValue {Pad : Type} {nPublic nPrivate : ℕ}
    (index : Fin nPrivate ↪ J × I) (claim : PadExpression Pad F)
    (coordinate : Pad → Slot) (publicWeights publicInputs : Fin nPublic → F)
    (privateWeights : Fin nPrivate → F) (values : Slot → F) :
    ((S.withSource index claim coordinate publicWeights publicInputs privateWeights).realize values).trueValue =
      dot privateWeights (unpack S.basis S.word index values) :=
  source_value S.basis S.word index privateWeights values

omit [Fintype K] [Fintype F] [DecidableEq I] in
/-- A true source claim supplies the exact native input equality. -/
theorem source_claim_iff {Pad : Type} {nPublic nPrivate : ℕ}
    (index : Fin nPrivate ↪ J × I) (claim : PadExpression Pad F)
    (coordinate : Pad → Slot) (publicWeights publicInputs : Fin nPublic → F)
    (privateWeights : Fin nPrivate → F) (values : Slot → F) :
    let P := (S.withSource index claim coordinate publicWeights publicInputs privateWeights).realize values
    P.target = P.trueValue ↔ claim.eval (values ∘ coordinate) =
      dot (Sum.elim publicWeights privateWeights)
        (Sum.elim publicInputs (unpack S.basis S.word index values)) := by
  dsimp only
  rw [source_target, source_trueValue]
  simp only [dot, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
  constructor <;> intro h <;> linear_combination h

/-- Packed private inputs are decoded canonically, then put beside the public
prefix and zero-extended to the circuit's input cube. -/
noncomputable def inputs {input nPublic nPrivate : ℕ}
    (inputIndex : (Fin nPublic ⊕ Fin nPrivate) ↪ Cube input)
    (packedIndex : Fin nPrivate ↪ J × I) (publicInputs : Fin nPublic → F)
    (values : Slot → F) : Cube input → F :=
  circuitInputs inputIndex publicInputs id (unpack S.basis S.word packedIndex values)

/-- Actual backend satisfaction can reach the native frontend only by making
the source equality true, or by hitting the counted packing escape. -/
theorem frontend_or_bad {Pad : Type} [DecidableEq F]
    {out input nPublic nPrivate : ℕ} (circuit : Native.Circuit F out input)
    (m : circuit.Messages Pad Slot) (point : Fin out → F)
    (cs : Constraints Pad Slot F)
    (hbuild : Native.buildConstraints (circuit.proof m (monomialWeights point)) = some cs)
    (inputIndex : (Fin nPublic ⊕ Fin nPrivate) ↪ Cube input)
    (packedIndex : Fin nPrivate ↪ J × I) (publicInputs : Fin nPublic → F)
    (coordinate : Pad → Slot) (values : Slot → F) (U delta : I → F) (A : F)
    (hlayers : ∀ c ∈ cs.layers, c.Holds (values ∘ coordinate))
    (hpacking : ((S.withSource packedIndex cs.inputClaim coordinate
      (fun i => circuit.inputWeights m (monomialWeights point) (inputIndex (.inl i))) publicInputs
      (fun i => circuit.inputWeights m (monomialWeights point) (inputIndex (.inr i)))).realize values).nativeLinearVerify
        U delta A) :
    Native.ClearAccepts (values ∘ coordinate) 0 (circuit.proof m (monomialWeights point))
      (dot (circuit.inputWeights m (monomialWeights point))
        (S.inputs inputIndex packedIndex publicInputs values)) ∨
      (S.withSource packedIndex cs.inputClaim coordinate
        (fun i => circuit.inputWeights m (monomialWeights point) (inputIndex (.inl i))) publicInputs
        (fun i => circuit.inputWeights m (monomialWeights point) (inputIndex (.inr i)))).Bad values U delta := by
  let T := S.withSource packedIndex cs.inputClaim coordinate
    (fun i => circuit.inputWeights m (monomialWeights point) (inputIndex (.inl i))) publicInputs
    (fun i => circuit.inputWeights m (monomialWeights point) (inputIndex (.inr i)))
  rcases T.target_or_bad values U delta A hpacking with htrue | hbad
  · apply Or.inl
    apply (Native.buildConstraints_correct _ _ _).mp
    refine ⟨cs, hbuild, hlayers, ?_⟩
    have hsource := (S.source_claim_iff packedIndex cs.inputClaim coordinate
      (fun i => circuit.inputWeights m (monomialWeights point) (inputIndex (.inl i))) publicInputs
      (fun i => circuit.inputWeights m (monomialWeights point) (inputIndex (.inr i))) values).mp htrue
    rw [inputs, input_sum]
    simpa only [Function.comp_id] using hsource
  · exact Or.inr hbad

/-- Packed private inputs beside the public prefix, with each per-proof
virtual input at its own address. Virtual values are affine views of the
decoded committed inputs; they are never committed themselves. -/
noncomputable def virtualInputs {input nPublic nPrivate nVirtual : ℕ}
    (inputIndex : (Fin nPublic ⊕ Fin nPrivate) ↪ Cube input)
    (virtualIndex : Fin nVirtual ↪ Cube input) (packedIndex : Fin nPrivate ↪ J × I)
    (publicInputs : Fin nPublic → F) (entries : Fin nVirtual → VirtualInput (Fin nPrivate) F)
    (values : Slot → F) : Cube input → F :=
  LfzkV2.virtualInputs inputIndex virtualIndex publicInputs
    (unpack S.basis S.word packedIndex values) entries

/-- Compile the final input claim with the virtual definitions substituted,
as `compile_packed` does: constants on the public side, coefficients added
to the weights of their committed sources. -/
noncomputable def withVirtualSource {Pad : Type} {input nPublic nPrivate nVirtual : ℕ}
    (packedIndex : Fin nPrivate ↪ J × I) (claim : PadExpression Pad F)
    (coordinate : Pad → Slot) (weights : Cube input → F)
    (inputIndex : (Fin nPublic ⊕ Fin nPrivate) ↪ Cube input)
    (virtualIndex : Fin nVirtual ↪ Cube input) (publicInputs : Fin nPublic → F)
    (entries : Fin nVirtual → VirtualInput (Fin nPrivate) F) : Statement K F I J Slot :=
  S.withSource packedIndex claim coordinate
    (substitutedPublicWeights (fun i => weights (inputIndex (.inl i))) (fun v => weights (virtualIndex v)))
    (substitutedPublicInputs publicInputs entries)
    (substitutedPrivateWeights (fun i => weights (inputIndex (.inr i)))
      (fun v => weights (virtualIndex v)) entries)

omit [Fintype K] [Fintype F] [DecidableEq I] in
/-- A true substituted source claim is exactly the final input equation over
`[public | committed | virtual]`. -/
theorem virtual_source_claim_iff {Pad : Type} {input nPublic nPrivate nVirtual : ℕ}
    (packedIndex : Fin nPrivate ↪ J × I) (claim : PadExpression Pad F)
    (coordinate : Pad → Slot) (weights : Cube input → F)
    (inputIndex : (Fin nPublic ⊕ Fin nPrivate) ↪ Cube input)
    (virtualIndex : Fin nVirtual ↪ Cube input) (publicInputs : Fin nPublic → F)
    (entries : Fin nVirtual → VirtualInput (Fin nPrivate) F) (values : Slot → F) :
    let P := (S.withVirtualSource packedIndex claim coordinate weights inputIndex virtualIndex
      publicInputs entries).realize values
    P.target = P.trueValue ↔ claim.eval (values ∘ coordinate) =
      dot weights (S.virtualInputs inputIndex virtualIndex packedIndex publicInputs entries values) := by
  dsimp only
  rw [withVirtualSource,virtualInputs,virtual_input_sum]
  exact S.source_claim_iff packedIndex claim coordinate _ _ _ values

/-- Every unpacked binary coordinate is a bit, including adversarial decoded
words. This is the input guarantee used by the native Boolean circuit. -/
theorem unpack_binary_bit {F I J Slot : Type} [Field F] [Algebra (ZMod 2) F]
    [Fintype I] (S : Statement (ZMod 2) F I J Slot) {Private : Type}
    (index : Private ↪ J × I) (values : Slot → F) (i : Private) :
    unpack S.basis S.word index values i = 0 ∨ unpack S.basis S.word index values i = 1 :=
  canonical_bit S.basis _ _

end Statement
end LfzkV2.Packed
