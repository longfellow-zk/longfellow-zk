import LfzkV2.Current.IdealProjections
import LfzkV2.Current.FrontendCounting
import WitnessSelection.Algebra
import Mathlib.Tactic.DeriveFintype

/-! One finite symbolic challenge alphabet for all runtime roles. Shared
field-coordinate accessors use one vector per field; jointly sampled
fingerprints, conversion scalars and backend responses each remain grouped.
Unused factors are analysis randomness, never extra hash calls or bytes. -/
noncomputable section
namespace LfzkV2.Current.IdealSamples
open scoped Classical

inductive Component where
  | binary | binaryNonzero | prime | primeNonzero | fingerprints | batching | opening
  deriving DecidableEq, Fintype

variable (B N IB IN RawBinary RawPrime Openings : Type)
variable [Field B] [Field N] [Fintype IB] [Fintype IN]
variable [DecidableEq IB] [DecidableEq IN]
variable (binaryCapacity primeCapacity : ℕ)

def Data : Component → Type
  | .binary => Fin binaryCapacity → B
  | .binaryNonzero => Linear.TerminalSampling.Nonzero B
  | .prime => Fin primeCapacity → N
  | .primeNonzero => Linear.TerminalSampling.Nonzero N × Linear.TerminalSampling.Nonzero N
  | .fingerprints => WitnessSelection.Coins B IB × WitnessSelection.Coins N IN
  | .batching => RawBinary × RawPrime
  | .opening => Openings

abbrev Answer := (component : Component) →
  Data B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity component

variable [Fintype B] [Fintype N] [DecidableEq B] [DecidableEq N]
variable [Fintype RawBinary] [Fintype RawPrime] [Fintype Openings]

instance dataFintype (component : Component) :
    Fintype (Data B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity component) := by
  cases component <;> dsimp only [Data] <;> infer_instance

/-- Every role component is an exact product factor of the common answer.
No independence is asserted for counterfactual parsers of physical bytes. -/
def factor (component : Component) :
    Answer B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity ≃
      Data B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity component ×
        ((other : {other : Component // other ≠ component}) →
          Data B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity other.val) :=
  Equiv.piSplitAt component _

def decoder (component : Component) :
    BalancedDecoder (Answer B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity)
      (Data B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity component) :=
  IdealProjections.decoder
    (factor B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity component)

theorem decoder_apply (component : Component)
    (answer : Answer B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity) :
    (decoder B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity component).decode answer =
      answer component := rfl

section Frontend
variable {F C : Type} [Field F] [Fintype F] [DecidableEq F] [Fintype C]
variable {capacity : ℕ}

def vectorRead (whole : BalancedDecoder C (Fin capacity → F)) (answer : C) (index : ℕ) : F :=
  if hi : index < capacity then whole.decode answer ⟨index,hi⟩ else 0

def vectorBlock (whole : BalancedDecoder C (Fin capacity → F))
    (offset dimension : ℕ) (fits : offset+dimension ≤ capacity) :
    BalancedDecoder C (Fin dimension → F) :=
  IdealProjections.compose whole
    (IdealProjections.decoder (IdealProjections.boundedSlice capacity offset dimension fits))

omit [DecidableEq F] in
theorem vectorBlock_decode (whole : BalancedDecoder C (Fin capacity → F))
    (offset dimension : ℕ) (fits : offset+dimension ≤ capacity) :
    (vectorBlock whole offset dimension fits).decode =
      fun answer i => vectorRead whole answer (offset+i.val) := by
  funext answer i
  have hi : offset+i.val < capacity := by have := i.isLt; omega
  exact (IdealProjections.boundedSlice_apply capacity offset dimension fits (whole.decode answer) i).trans
    (by simp only [vectorRead,dif_pos hi])

/-- All frontend sampling laws follow from product projections on one
shared coordinate vector and its separate nonzero factor. -/
def frontend (whole : BalancedDecoder C (Fin capacity → F))
    (nonzero : BalancedDecoder C (Linear.TerminalSampling.Nonzero F)) (positive : 0 < capacity) :
    FrontendReplay.Decoder capacity (vectorRead whole) nonzero.decode where
  fieldFiber := (vectorBlock whole 0 1 (by omega)).fiber
  field_balanced := by
    simpa only [Fintype.card_fun,Fintype.card_fin,pow_one] using
      (vectorBlock whole 0 1 (by omega)).balanced
  blocks offset dimension fits := by
    let block := vectorBlock whole offset dimension fits
    exact ⟨{
      decode := block.decode
      fiber := block.fiber
      fiber_bound sample := by
        convert! block.fiber_bound sample using 1
        congr 1
        ext answer
        simp only [Finset.mem_filter]
      balanced := by simpa only [ChallengeBlocks.Kind.dimension,Fintype.card_fun,Fintype.card_fin]
        using block.balanced },vectorBlock_decode whole offset dimension fits⟩
  terminal := {
    decode := nonzero.decode
    fiber := nonzero.fiber
    fiber_bound sample := by
      convert! nonzero.fiber_bound sample using 1
      congr 1
      ext answer
      simp only [Finset.mem_filter]
    balanced := nonzero.balanced }
  terminal_decode := rfl

end Frontend

def primeNonzeroDecoder :
    BalancedDecoder (Answer B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity)
      (Linear.TerminalSampling.Nonzero N) :=
  IdealProjections.compose
    (decoder B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity .primeNonzero)
    (IdealProjections.decoder (Equiv.refl _))

def binaryFrontend (positive : 0 < binaryCapacity) :
    FrontendReplay.Decoder binaryCapacity
      (vectorRead (decoder B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity .binary))
      (decoder B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity .binaryNonzero).decode :=
  frontend (decoder B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity .binary)
    (decoder B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity .binaryNonzero) positive

def primeFrontend (positive : 0 < primeCapacity) :
    FrontendReplay.Decoder primeCapacity
      (vectorRead (decoder B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity .prime))
      (primeNonzeroDecoder B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity).decode :=
  frontend (decoder B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity .prime)
    (primeNonzeroDecoder B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity) positive

def fingerprintBinaryDecoder :
    BalancedDecoder (Answer B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity)
      (WitnessSelection.Coins B IB) :=
  IdealProjections.compose
    (decoder B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity .fingerprints)
    (IdealProjections.decoder (Equiv.refl _))

def fingerprintPrimeDecoder :
    BalancedDecoder (Answer B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity)
      (WitnessSelection.Coins N IN) :=
  IdealProjections.compose
    (decoder B N IB IN RawBinary RawPrime Openings binaryCapacity primeCapacity .fingerprints)
    (IdealProjections.decoder (Equiv.prodComm _ _))

end LfzkV2.Current.IdealSamples
