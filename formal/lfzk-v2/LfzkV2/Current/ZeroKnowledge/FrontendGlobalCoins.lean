import LfzkV2.Current.ZeroKnowledge.FrontendCompleteHonest
import LfzkV2.Current.ZeroKnowledge.FrontendSelection

/-! The whole frontend's independent coins, with the dedicated fingerprint
masks separated from all cells they select. A single triangular inverse
first recovers every later pad and then recovers both pairs of selector masks.
No independence between the early responses and later cells is assumed.

The inner stage equivalence is instantiated by the concrete frontend
coupling. This module supplies only the finite product bookkeeping and the
exact fingerprint identities needed by that composition. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.Frontend.GlobalCoins

open SumcheckV2 ApplicationSetup ConcreteSetup
open scoped Classical

variable {B : Type} [Field B] [Fintype B] [DecidableEq B] [Algebra (ZMod 2) B]
local notation "P" => Adapter.Mdoc.P
variable (binary : BinaryCircuit B) (prime : PrimePublic P 768)

abbrev BinaryTail := CircuitTape binary.description.template × Packing.Tape (F := B) (0 : Fin 128)
abbrev Source := CircuitTape prime.circuit × ((P × Fin (2^24)) × BinaryTail binary)
abbrev Public := CircuitTape prime.circuit × (((P × MdocAdvice.Value) × Fin 16) × BinaryTail binary)

def tapeEquiv : CompleteHonest.Tape binary prime ≃ Source binary prime where
  toFun coins := (coins.prime,(coins.mask,coins.otp),(coins.binary,coins.packing))
  invFun coins := {
    prime := coins.1
    mask := coins.2.1.1
    otp := coins.2.1.2
    binary := coins.2.2.1
    packing := coins.2.2.2 }
  left_inv _ := rfl
  right_inv _ := rfl

def coinsEquiv : (CompleteHonest.Masks (B := B) × Public binary prime) ≃
    CompleteSimulation.Coins binary prime where
  toFun coins := {
    fingerprints := coins.1
    prime := coins.2.1
    mu := coins.2.2.1.1.1
    advice := coins.2.2.1.1.2
    otpUnused := coins.2.2.1.2
    binary := coins.2.2.2.1
    packing := coins.2.2.2.2 }
  invFun coins := (coins.fingerprints,coins.prime,((coins.mu,coins.advice),coins.otpUnused),
    (coins.binary,coins.packing))
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype (CompleteHonest.Tape binary prime) :=
  Fintype.ofEquiv (Source binary prime) (tapeEquiv binary prime).symm

instance : Fintype (CompleteSimulation.Coins binary prime) :=
  Fintype.ofEquiv (CompleteHonest.Masks (B := B) × Public binary prime) (coinsEquiv binary prime)

/-- Each later fiber sees only the already selected public outputs. In
particular the packing change follows the binary payload, and the binary
change follows both conversion responses. -/
def stages
    (native : CircuitTape prime.circuit ≃ CircuitTape prime.circuit)
    (adapter : CircuitTape prime.circuit → (P × Fin (2^24)) ≃ ((P × MdocAdvice.Value) × Fin 16))
    (binaryStage : CircuitTape prime.circuit → ((P × MdocAdvice.Value) × Fin 16) →
      CircuitTape binary.description.template ≃ CircuitTape binary.description.template)
    (packingStage : CircuitTape prime.circuit → ((P × MdocAdvice.Value) × Fin 16) →
      CircuitTape binary.description.template →
        Packing.Tape (F := B) (0 : Fin 128) ≃ Packing.Tape (F := B) (0 : Fin 128)) :
    CompleteHonest.Tape binary prime ≃ Public binary prime :=
  (tapeEquiv binary prime).trans
    ((Equiv.prodCongr native (Equiv.refl _)).trans
      (Equiv.prodCongrRight fun primeCoin =>
        (Equiv.prodCongr (adapter primeCoin) (Equiv.refl _)).trans
          (Equiv.prodCongrRight fun converted =>
            (Equiv.prodCongr (binaryStage primeCoin converted) (Equiv.refl _)).trans
              (Equiv.prodCongrRight fun binaryCoin => packingStage primeCoin converted binaryCoin))))

omit [Fintype B] [DecidableEq B] in
theorem stages_apply
    (native : CircuitTape prime.circuit ≃ CircuitTape prime.circuit)
    (adapter : CircuitTape prime.circuit → (P × Fin (2^24)) ≃ ((P × MdocAdvice.Value) × Fin 16))
    (binaryStage : CircuitTape prime.circuit → ((P × MdocAdvice.Value) × Fin 16) →
      CircuitTape binary.description.template ≃ CircuitTape binary.description.template)
    (packingStage : CircuitTape prime.circuit → ((P × MdocAdvice.Value) × Fin 16) →
      CircuitTape binary.description.template →
        Packing.Tape (F := B) (0 : Fin 128) ≃ Packing.Tape (F := B) (0 : Fin 128))
    (coins : CompleteHonest.Tape binary prime) :
    let primeCoin := native coins.prime
    let converted := adapter primeCoin (coins.mask,coins.otp)
    let binaryCoin := binaryStage primeCoin converted coins.binary
    stages binary prime native adapter binaryStage packingStage coins =
      (primeCoin,converted,binaryCoin,packingStage primeCoin converted binaryCoin coins.packing) := rfl

variable (coefficients : WitnessSelection.Coins B binary.description.Original ×
  WitnessSelection.Coins P prime.Original)
variable (original : Fin binary.nPrivate → Bool) (remaining : Fin prime.remaining → P)

/-- Dedicated selector cells have coefficient one in their own equation;
the selected data functions contain every other original frontend cell. -/
def selectedEquiv
    (inner : CompleteHonest.Masks (B := B) → CompleteHonest.Tape binary prime ≃ Public binary prime) :
    (CompleteHonest.Tape binary prime × CompleteHonest.Masks (B := B)) ≃
      CompleteSimulation.Coins binary prime :=
  (jointSelectionPayloadEquiv coefficients.1 coefficients.2
    (fun tape => (CompleteHonest.binaryCandidate binary prime original tape (0,0)).1)
    (fun tape => (CompleteHonest.primeCandidate binary prime remaining tape (0,0)).1) inner).trans
      (coinsEquiv binary prime)

omit [DecidableEq B] in
theorem selected_fingerprints
    (inner : CompleteHonest.Masks (B := B) → CompleteHonest.Tape binary prime ≃ Public binary prime)
    (tape : CompleteHonest.Tape binary prime) (masks : CompleteHonest.Masks (B := B)) :
    (selectedEquiv binary prime coefficients original remaining inner (tape,masks)).fingerprints =
      CompleteHonest.responses binary prime coefficients original remaining tape masks := rfl

omit [DecidableEq B] in
theorem recovered_fingerprints
    (inner : CompleteHonest.Masks (B := B) → CompleteHonest.Tape binary prime ≃ Public binary prime)
    (coins : CompleteSimulation.Coins binary prime) :
    let recovered := (selectedEquiv binary prime coefficients original remaining inner).symm coins
    CompleteHonest.responses binary prime coefficients original remaining recovered.1 recovered.2 =
      coins.fingerprints := by
  dsimp only
  rw [← selected_fingerprints binary prime coefficients original remaining inner]
  exact congrArg CompleteSimulation.Coins.fingerprints
    ((selectedEquiv binary prime coefficients original remaining inner).apply_symm_apply coins)

end LfzkV2.Current.ZeroKnowledge.Frontend.GlobalCoins
