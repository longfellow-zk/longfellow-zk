import LfzkV2.Current.Selection
import LfzkV2.Current.Prefix

/-! The selected pair at a later query is reconstructed from the first
boundary's answer and the fingerprint responses already present in that
query's prefix. Changing the query's own answer cannot change the candidate
lists, the selection challenges, or the selected pad and input cells. -/
noncomputable section
namespace LfzkV2.Current.Selection
open WitnessSelection

variable {roles : List Role} {Key Block Link Body C Oracle B N IB IN : Type}
variable [Field B] [Field N] [DecidableEq B] [DecidableEq N] [Fintype IB] [Fintype IN]

local notation "Point" => Input roles Key Block Link Body

def atPoint
    (lists : Key → Oracle → Finset (WitnessSelection.Candidate B IB) ×
      Finset (WitnessSelection.Candidate N IN))
    (decode : C → Coins B IB × Coins N IN)
    (response : Point → (B × B) × (N × N))
    (oracle : (Point → Link × C) → Key → Oracle)
    (point : Point) (H : Point → Link × C) : Option (Pair B N IB IN) :=
  if h : 0 < point.rank then
    let candidates := lists point.context (oracle H point.context)
    let coins := decode (point.priorAnswers H ⟨0,h⟩)
    let targets := response point
    (Context.mk candidates.1 candidates.2 coins.1 coins.2 targets.1 targets.2).extract
  else none

/-- The cut-trace property is needed only at this point, not as an assertion
that the recovered commitment is independent of the entire oracle. The
response decoder reads the fixed query preimage and has no oracle argument. -/
theorem atPoint_off
    (lists : Key → Oracle → Finset (WitnessSelection.Candidate B IB) ×
      Finset (WitnessSelection.Candidate N IN))
    (decode : C → Coins B IB × Coins N IN)
    (response : Point → (B × B) × (N × N))
    (oracle : (Point → Link × C) → Key → Oracle)
    (hoff : ∀ point H H', Bcs.TotalOracle.AgreeOff point H H' →
      oracle H point.context = oracle H' point.context)
    (point : Point) (H H' : Point → Link × C)
    (h : Bcs.TotalOracle.AgreeOff point H H') :
    atPoint lists decode response oracle point H = atPoint lists decode response oracle point H' := by
  unfold atPoint
  rw [point.priorAnswers_off h, hoff point H H' h]

end LfzkV2.Current.Selection
