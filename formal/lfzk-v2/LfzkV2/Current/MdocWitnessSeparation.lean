import LfzkV2.Current.MdocWitness
import LfzkV2.Current.HashSeparation

/-! The concrete input suffix and a static sparse-read certificate imply
the ordinary witness predicate is independent of all adapter randomness. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 4096
namespace LfzkV2.Current.MdocWitness
open ConcreteSetup SumcheckV2
open scoped Classical
variable {B : Type} [Field B] [Algebra (ZMod 2) B]

/-- This is exactly the input boundary checked by Rust's test-only
`hash_inputs::validate`; padding beyond the private input array is excluded too. -/
def ReservedInput (binary : BinaryCircuit B) (u : Cube binary.input) : Prop :=
  binary.nPublic+(binary.nPrivate-276) ≤ (cubeIndex binary.input u).val

abbrev ReadDisjoint (binary : BinaryCircuit B) : Prop :=
  HashCircuit.ReadDisjoint binary.description.layout binary.description.output
    binary.description.others binary.description.carry (ReservedInput binary)

theorem noninterference_of_readDisjoint (binary : BinaryCircuit B) (separated : ReadDisjoint binary) :
    HashNoninterference binary := by
  intro publicBits original mask otp powers base masked targets
  apply HashCircuit.checks_iff_of_readDisjoint
    (reserved := ReservedInput { binary with publicBits := publicBits })
    (separated := separated)
  intro u before
  apply congrArg Adapter.Circuit.bitValue
  apply WitnessInputs.bits_prefix
  · intro i hi
    rw [private_prefix _ _ _ _ i hi,private_prefix _ _ _ _ i hi]
  · exact Nat.lt_of_not_ge before

section Extraction
variable [DecidableEq B]

/-- Read the original private Boolean input array from the selected packed
witness. The final mask/OTP suffix is erased by `HashValid`. -/
def extractedPrivate (binary : BinaryCircuit B)
    (candidate : WitnessSelection.Candidate B binary.description.Original) : Fin binary.nPrivate → Bool :=
  fun i => binary.description.bits candidate (binary.description.inputIndex (.inr i))

theorem reference_agrees (binary : BinaryCircuit B)
    (candidate : WitnessSelection.Candidate B binary.description.Original) :
    HashCircuit.AgreeOutside (ReservedInput binary)
      (Adapter.Circuit.bitValue ∘ WitnessInputs.bits binary
        (WitnessInputs.privateValues binary (extractedPrivate binary candidate) (fun _ => false) (fun _ _ => false)))
      (binary.description.inputs (FingerprintRows.realize (CellLayout.selected binary.description.cells) candidate)) := by
  rw [binary.description.inputs_eq_bits]
  intro u before
  apply congrArg Adapter.Circuit.bitValue
  have bound : (cubeIndex binary.input u).val < binary.nPublic+(binary.nPrivate-276) :=
    Nat.lt_of_not_ge before
  by_cases hp : (cubeIndex binary.input u).val < binary.nPublic
  · let i : Fin binary.nPublic := ⟨_,hp⟩
    have address : u = binary.description.inputIndex (.inl i) := by
      apply (cubeIndex binary.input).injective
      apply Fin.ext
      exact (inputIndex_public _ _ _ _ i).symm
    rw [address,WitnessInputs.bits_public]
    unfold ApplicationSetup.BinaryPublic.bits ApplicationSetup.BinaryPublic.inputs
      Packed.Statement.inputs circuitInputs
    rw [zeroExtend_apply]
    change binary.publicBits i = decide (Adapter.Circuit.bitValue (binary.publicBits i) = (1 : B))
    cases binary.publicBits i <;> simp [Adapter.Circuit.bitValue]
  · let i : Fin binary.nPrivate := ⟨(cubeIndex binary.input u).val-binary.nPublic,by omega⟩
    have address : u = binary.description.inputIndex (.inr i) := by
      apply (cubeIndex binary.input).injective
      apply Fin.ext
      rw [show (cubeIndex binary.input (binary.description.inputIndex (.inr i))).val = binary.nPublic+i.val
        from inputIndex_private _ _ _ _ i]
      dsimp [i]
      omega
    rw [address,WitnessInputs.bits_private,private_prefix]
    · rfl
    · dsimp [i]; omega

theorem hashValid_of_satisfies (binary : BinaryCircuit B) (separated : ReadDisjoint binary)
    (candidate : WitnessSelection.Candidate B binary.description.Original)
    (powers : Fin 2 → Fin 1024 → Bˣ) (base : Bˣ)
    (masked : Fin 2 → Fin 10 → Bool) (targets : Fin 2 → Bˣ)
    (satisfied : (binary.description.circuit powers base masked targets).Satisfies
      (binary.description.inputs (FingerprintRows.realize (CellLayout.selected binary.description.cells) candidate))) :
    HashValid binary (extractedPrivate binary candidate) := by
  have hash := (HashCircuit.build_satisfies_iff _ _ _ _ _ _ _ _ powers base masked targets _).mp satisfied
  exact (HashCircuit.checks_iff_of_readDisjoint _ _ _ _ _ _ _ separated _ _
    _ powers _ base _ masked _ targets _ _ (reference_agrees binary candidate)).mpr hash.1

end Extraction
end LfzkV2.Current.MdocWitness
