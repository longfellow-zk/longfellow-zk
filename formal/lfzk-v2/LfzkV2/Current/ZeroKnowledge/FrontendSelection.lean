import LfzkV2.Current.ZeroKnowledge.FrontendReplay

/-! Coin changes for the selection responses and the later frontend.

The fingerprints cover the complete committed frontend vector, including
every later pad. Thus their responses and those pads cannot be treated as
independent after replay. The triangular coin change instead first exposes
the masked responses, then changes the remaining secret coins in the fiber
they select. Coefficient vectors are fixed before either response; only the
later public reader is allowed to depend on them. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.Frontend
open SumcheckV2
open scoped Classical
variable {F State Index : Type} [Field F] [Fintype Index]

/-- A triangular change of coins: first expose the masked response, then
change the remaining secret coins in the fiber selected by that response.
This also handles simultaneous fingerprints in several committed fields. -/
def responsePayloadEquiv {Secret Masks Responses Payload : Type}
    (selection : Secret → Masks ≃ Responses) (payload : Responses → Secret ≃ Payload) :
    (Secret × Masks) ≃ (Responses × Payload) :=
  ((Equiv.prodCongrRight selection).trans (Equiv.prodComm _ _)).trans
    (Equiv.prodCongrRight payload)

section Joint
variable {B N BinaryIndex PrimeIndex : Type} [Field B] [Field N]
  [Fintype BinaryIndex] [Fintype PrimeIndex]

/-- The response is a pair in each field, sampled in the same pre-frontend
phase. The shared secret may contain the pads and packing randomness of
both participants; neither coefficient vector depends on any response. -/
def jointSelectionPayloadEquiv {Secret Payload : Type}
    (binaryCoefficients : WitnessSelection.Coins B BinaryIndex)
    (primeCoefficients : WitnessSelection.Coins N PrimeIndex)
    (binaryCells : Secret → BinaryIndex → B) (primeCells : Secret → PrimeIndex → N)
    (payload : ((B × B) × (N × N)) → Secret ≃ Payload) :
    (Secret × ((B × B) × (N × N))) ≃ (((B × B) × (N × N)) × Payload) :=
  responsePayloadEquiv (fun secret => Equiv.prodCongr
    (WitnessSelection.maskTranslation binaryCoefficients (binaryCells secret))
    (WitnessSelection.maskTranslation primeCoefficients (primeCells secret))) payload

end Joint

end LfzkV2.Current.ZeroKnowledge.Frontend
