import LfzkV2.Current.WitnessInputs
import LfzkV2.Current.HashSeparation

/-! Ordinary witness truth of the hash circuit. The hash is archived at its
natural width and its input-boundary fragments are typed by that prefix, so
its checks depend only on `[public | hash private]` (`checks_prefix`). R, the
quotient pads, the virtual leaves and the adapter's wires cannot change them.
`HashValid` is stated at one reference array; every array that agrees with it
on the hash prefix satisfies the same checks. This is a theorem of the circuit
types, not a premise supplied by the circuit's author. -/
noncomputable section
namespace LfzkV2.Current.MdocWitness
open Application ApplicationSetup ConcreteSetup SumcheckV2
open scoped Classical
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false

variable {B : Type} [Field B] [Algebra (ZMod 2) B]

local notation "bd" => BinaryCircuit.description

/-- The non-adapter checks of the joint binary circuit at an input array. -/
def HashChecks (binary : BinaryCircuit B) (w : Cube binary.input → B) : Prop :=
  HashCircuit.Checks (bd binary).layout (bd binary).output (bd binary).shape (bd binary).others
    (bd binary).carry (bd binary).above (bd binary).read w

/-- Ordinary witness truth: the hash checks on the public bits and the
original hash private bits, with every input outside the hash prefix zero. -/
def HashValid (binary : BinaryCircuit B) (original : Fin binary.nPrivate → Bool) : Prop :=
  HashChecks binary (Adapter.Circuit.bitValue ∘ WitnessInputs.bits binary
    (WitnessInputs.privateValues binary original (fun _ => false) (fun _ _ => false)))

/-- The hash checks at an actual array of committed bits, R and pads, and
an arbitrary per-proof virtual suffix. -/
def HashAt (binary : BinaryCircuit B) (original : Fin binary.nPrivate → Bool)
    (mask : Fin 256 → Bool) (otp : Fin 2 → Fin 10 → Bool)
    (entries : Fin (2*(768+256+10)) → VirtualInput (Fin binary.nPrivate) B) : Prop :=
  HashChecks binary (virtualInputs (bd binary).inputIndex (bd binary).virtualIndex
    (Adapter.Circuit.bitValue ∘ (bd binary).publicBits)
    (Adapter.Circuit.bitValue ∘ WitnessInputs.privateValues binary original mask otp) entries)

/-- Structural separation: the hash checks agree on any two input arrays
that agree on the hash's own input prefix. -/
theorem hashChecks_prefix (binary : BinaryCircuit B) (left right : Cube binary.input → B)
    (same : ∀ x, left (binary.hashIndex x) = right (binary.hashIndex x)) :
    HashChecks binary left ↔ HashChecks binary right :=
  HashCircuit.checks_prefix (bd binary).shape (binary.others.withComponent 0) binary.carry
    ((binary.above.withComponent 0).algebraic) (bd binary).read (bd binary).read left right same

/-- Committed positions of the hash prefix, as public or private indices. -/
theorem hashIndex_committed (binary : BinaryCircuit B) (x : Fin binary.hashWidth) :
    ∃ j, (bd binary).inputIndex j = binary.hashIndex x ∧
      ∀ i : Fin binary.nPrivate, j = .inr i → i.val < binary.hashPrivate := by
  by_cases hp : x.val < binary.nPublic
  · refine ⟨.inl ⟨x.val,hp⟩,?_,fun i h => by cases h⟩
    apply (cubeIndex binary.input).injective
    apply Fin.ext
    change (cubeIndex binary.input (BinaryCircuit.committedIndex binary _)).val = _
    simp only [BinaryCircuit.committedIndex,inputIndex_public,BinaryCircuit.hashIndex_val]
  · have hx := x.isLt
    unfold BinaryCircuit.hashWidth at hx
    refine ⟨.inr ⟨x.val-binary.nPublic,show x.val-binary.nPublic < binary.hashPrivate+276 by omega⟩,?_,?_⟩
    · apply (cubeIndex binary.input).injective
      apply Fin.ext
      change (cubeIndex binary.input (BinaryCircuit.committedIndex binary _)).val = _
      simp only [BinaryCircuit.committedIndex,inputIndex_private,BinaryCircuit.hashIndex_val]
      omega
    · intro i h
      cases h
      dsimp only
      omega

/-- The hash prefix of an actual array of committed bits never reads R, the
pads or a virtual entry. -/
theorem hashAt_prefix (binary : BinaryCircuit B) (original : Fin binary.nPrivate → Bool)
    (mask : Fin 256 → Bool) (otp : Fin 2 → Fin 10 → Bool)
    (entries : Fin (2*(768+256+10)) → VirtualInput (Fin binary.nPrivate) B) (x : Fin binary.hashWidth) :
    virtualInputs (bd binary).inputIndex (bd binary).virtualIndex
        (Adapter.Circuit.bitValue ∘ (bd binary).publicBits)
        (Adapter.Circuit.bitValue ∘ WitnessInputs.privateValues binary original mask otp) entries
        (binary.hashIndex x) =
      (Adapter.Circuit.bitValue ∘ WitnessInputs.bits binary
        (WitnessInputs.privateValues binary original (fun _ => false) (fun _ _ => false))) (binary.hashIndex x) := by
  obtain ⟨j,hj,hprivate⟩ := hashIndex_committed binary x
  rw [← hj,virtualInputs_committed _ _ _ _ _ _ (fun v h => (bd binary).virtualDisjoint j v h.symm)]
  simp only [circuitInputs,zeroExtend_apply,Function.comp_apply]
  cases j with
  | inl i =>
      simp only [Sum.elim_inl,Function.comp_apply]
      rw [WitnessInputs.bits_public]
      rfl
  | inr i =>
      simp only [Sum.elim_inr,id_eq,Function.comp_apply]
      rw [WitnessInputs.bits_private]
      have hi := hprivate i rfl
      simp only [WitnessInputs.privateValues,dif_pos hi]

/-- Truth of the hash is independent of R, the pads and every virtual
definition. -/
theorem hashAt_iff_valid (binary : BinaryCircuit B) (original : Fin binary.nPrivate → Bool)
    (mask : Fin 256 → Bool) (otp : Fin 2 → Fin 10 → Bool)
    (entries : Fin (2*(768+256+10)) → VirtualInput (Fin binary.nPrivate) B) :
    HashAt binary original mask otp entries ↔ HashValid binary original :=
  hashChecks_prefix binary _ _ (hashAt_prefix binary original mask otp entries)

/-- The uniform fact consumed by coin-change proofs. -/
def UniformHashValid (binary : BinaryCircuit B) (original : Fin binary.nPrivate → Bool) : Prop :=
  ∀ mask otp entries, HashAt binary original mask otp entries

theorem uniformHashValid_of_valid {binary : BinaryCircuit B} {original : Fin binary.nPrivate → Bool}
    (valid : HashValid binary original) : UniformHashValid binary original :=
  fun mask otp entries => (hashAt_iff_valid binary original mask otp entries).mpr valid

theorem UniformHashValid.reference {binary : BinaryCircuit B}
    {original : Fin binary.nPrivate → Bool} (valid : UniformHashValid binary original) :
    HashValid binary original :=
  (hashAt_iff_valid binary original (fun _ => false) (fun _ _ => false) (fun _ => ⟨⟨0,show 0 < binary.hashPrivate+276 by omega⟩,0,0⟩)).mp
    (valid _ _ _)

section Extraction
variable [Fintype B] [DecidableEq B]

/-- Read the committed private Boolean inputs from the selected packed
witness. Only its hash prefix matters to `HashValid`. -/
def extractedPrivate (binary : BinaryCircuit B)
    (candidate : WitnessSelection.Candidate B (bd binary).Original) : Fin binary.nPrivate → Bool :=
  (bd binary).privateBits candidate

omit [Fintype B] in
theorem extracted_prefix (binary : BinaryCircuit B)
    (candidate : WitnessSelection.Candidate B (bd binary).Original)
    (entries : Fin (2*(768+256+10)) → VirtualInput (Fin binary.nPrivate) B) (x : Fin binary.hashWidth) :
    (bd binary).inputs entries (FingerprintRows.realize (CellLayout.selected (bd binary).cells) candidate)
        (binary.hashIndex x) =
      (Adapter.Circuit.bitValue ∘ WitnessInputs.bits binary
        (WitnessInputs.privateValues binary (extractedPrivate binary candidate) (fun _ => false)
          (fun _ _ => false))) (binary.hashIndex x) := by
  obtain ⟨j,hj,hprivate⟩ := hashIndex_committed binary x
  rw [← hj]
  simp only [BinaryPublic.inputs,Packed.Statement.virtualInputs]
  rw [virtualInputs_committed _ _ _ _ _ _ (fun v h => (bd binary).virtualDisjoint j v h.symm)]
  have hc := congrFun ((bd binary).committed_eq_bits candidate) ((bd binary).inputIndex j)
  simp only [BinaryPublic.committed,Packed.Statement.inputs] at hc
  rw [hc]
  simp only [Function.comp_apply]
  congr 1
  cases j with
  | inl i =>
      rw [WitnessInputs.bits_public]
      have hb := congrFun ((bd binary).committed_eq_bits candidate) ((bd binary).inputIndex (.inl i))
      simp only [BinaryPublic.committed,Packed.Statement.inputs,circuitInputs,zeroExtend_apply,
        Sum.elim_inl,Function.comp_apply] at hb
      change Adapter.Circuit.bitValue (binary.publicBits i) = _ at hb
      revert hb
      cases (bd binary).bits candidate ((bd binary).inputIndex (.inl i)) <;>
        cases binary.publicBits i <;> simp [Adapter.Circuit.bitValue]
  | inr i =>
      rw [WitnessInputs.bits_private]
      have hi := hprivate i rfl
      simp only [WitnessInputs.privateValues,dif_pos hi,extractedPrivate,BinaryPublic.privateBits]

omit [Fintype B] in
/-- Satisfaction of the actual joint circuit, with any virtual suffix, gives
ordinary hash truth for the extracted private bits. No read-separation
certificate is supplied: separation is a consequence of the circuit types. -/
theorem hashValid_of_satisfies (binary : BinaryCircuit B)
    (candidate : WitnessSelection.Candidate B (bd binary).Original)
    (entries : Fin (2*(768+256+10)) → VirtualInput (Fin binary.nPrivate) B)
    (satisfied : (bd binary).circuit.Satisfies
      ((bd binary).inputs entries (FingerprintRows.realize (CellLayout.selected (bd binary).cells) candidate))) :
    HashValid binary (extractedPrivate binary candidate) := by
  have hash := (HashCircuit.build_satisfies_iff _ _ _ _ _ _ _ _).mp satisfied
  exact (hashChecks_prefix binary _ _ (extracted_prefix binary candidate entries)).mp hash.1

end Extraction
end LfzkV2.Current.MdocWitness

namespace LfzkV2.Current.MdocWitness
open ApplicationSetup ConcreteSetup SumcheckV2
variable {B : Type} [Field B] [Algebra (ZMod 2) B]
local notation "bd" => BinaryCircuit.description

/-- Satisfaction of the joint circuit from its two parts: the hash checks,
and a unit product of the virtual leaves in each tree. -/
theorem satisfies_of [CharP B 2] (binary : BinaryCircuit B) (bits : Fin binary.nPrivate → Bool)
    (entries : Fin (2*(768+256+10)) → VirtualInput (Fin binary.nPrivate) B)
    (hash : HashChecks binary (virtualInputs (bd binary).inputIndex (bd binary).virtualIndex
      (Adapter.Circuit.bitValue ∘ (bd binary).publicBits) (Adapter.Circuit.bitValue ∘ bits) entries))
    (leaves : ∀ tree, ∏ i, (entries (Adapter.ProductTree.wireIndex _ (tree,i))).value
      (Adapter.Circuit.bitValue ∘ bits) = 1) :
    (bd binary).circuit.Satisfies (virtualInputs (bd binary).inputIndex (bd binary).virtualIndex
      (Adapter.Circuit.bitValue ∘ (bd binary).publicBits) (Adapter.Circuit.bitValue ∘ bits) entries) := by
  apply (HashCircuit.build_satisfies_iff _ _ _ _ _ _ _ _).mpr
  refine ⟨hash,(Adapter.ProductTree.satisfies_iff _ _).mpr fun tree => ?_⟩
  have h := leaves tree
  simp only [Function.comp_apply,BinaryPublic.read]
  simp only [virtualInputs_virtual _ _ (bd binary).virtualDisjoint]
  exact h

end LfzkV2.Current.MdocWitness
