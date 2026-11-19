import LfzkV2.Current.Frontend
import LfzkV2.Current.Handoff

/-! Algebraic composition of the packed binary frontend, prime frontend and
product adapter. The backend supplies the binary compiled rows and the prime
statement: the unbatched layer rows and the native row. The adapter
circuit's semantic identity is stated explicitly: its satisfaction gives the
two product equations on the selected shared bits. No equality between the
two committed hiding masks is assumed. -/
noncomputable section
namespace LfzkV2.Current.Composition
open SumcheckV2 DualPacking.ArtinSchreier

variable {B I J SlotB PadB Other PadN G : Type} [Field B] [Fintype B] [DecidableEq B]
  [Algebra (ZMod 2) B] [Fintype I] [DecidableEq I] [Fintype J]
  [Fintype Other] [CommGroup G]
variable {p shared maskBits M K : ℕ} [Fact p.Prime]

/-- The prime frontend's split claim (`split.rs::split_claim`), with every
pad read at its native cell. -/
def splitClaim {F : Type} [Field F] (n : Frontend.Prime F (Fin shared ⊕ Other) PadN)
    (padCell : PadN → Other) : Prime.Claim (Fin shared) Other F :=
  Prime.Claim.ofConstraints n.constraints padCell n.privateCoordinate
    (fun i => n.circuit.inputWeights n.messages 0 (n.inputIndex (.inl i))) n.publicInputs
    (fun i => n.circuit.inputWeights n.messages 0 (n.inputIndex (.inr i)))

/-- With native pads, the complete compiled prime row vector holds exactly
when the split claim's layer rows hold and its input equation does. -/
theorem splitClaim_rows {F : Type} [Field F] (n : Frontend.Prime F (Fin shared ⊕ Other) PadN)
    (padCell : PadN → Other) (hpad : ∀ i, n.coordinate i = .inr (padCell i))
    (shared : Fin shared → F) (other : Other → F) :
    RowsHold n.rows (Sum.elim shared other) ↔
      RowsHold (splitClaim n padCell).layers other ∧ (splitClaim n padCell).residual shared other = 0 := by
  have hcoordinate : n.coordinate = fun i => .inr (padCell i) := funext hpad
  unfold Frontend.Prime.rows splitClaim
  rw [hcoordinate]
  exact Prime.Claim.ofConstraints_iff _ _ _ _ _ _ shared other

/-- This reduction includes both actual affine compilers, the packing check,
the unbatched prime statement and both conversion challenges. Its conclusion
separates the four algebraic failure sources for later charging at their own
boundaries. Circuit/layout correctness is the explicit `hproducts` premise; no
protocol soundness or event-coverage assumption is hidden in that premise. -/
theorem rows_reduction
    (b : Frontend.Packed B I J SlotB PadB)
    (n : Frontend.Prime (ZMod p) (Fin shared ⊕ Other) PadN)
    (padCell : PadN → Other) (hpad : ∀ i, n.coordinate i = .inr (padCell i))
    (readB : SlotB → B) (other : Other → ZMod p)
    (sharedValues : Fin shared → Bool) (mask : Fin maskBits → Bool)
    (eta mu primeMask : ZMod p)
    (alpha : Fin 2 → Linear.TerminalSampling.Nonzero (ZMod p))
    (generator : G) (horder : orderOf generator = M)
    (quotient : Fin 2 → ℕ) (hquotient : ∀ j, quotient j < K)
    (htrace : ∀ k, traceF (ZMod 2) (b.U k) = 0)
    (hrowsB : RowsHold b.rows readB) :
    let claim := splitClaim n padCell
    let readN := Sum.elim (fun i => if sharedValues i then 1 else 0) other
    (b.circuit.Satisfies (b.inputs readB) →
      ∀ j, Adapter.ProductCheck generator (Handoff.weights claim.sharedWeights eta)
        (Handoff.values sharedValues mask) mu (alpha j).val (quotient j)) →
    RowsHold (claim.rows eta mu) (Sum.elim other (fun _ => primeMask)) →
    (b.circuit.Satisfies (b.inputs readB) ∧ n.circuit.Satisfies (n.inputs readN)) ∨
      b.Bad readB ∨ n.Bad readN ∨
      Prime.RescalingBad (claim.residual (fun i => if sharedValues i then 1 else 0) other)
        (Handoff.binaryMask mask - primeMask) eta ∨
      Handoff.ConversionBad claim.sharedWeights eta mu sharedValues mask M K alpha := by
  intro claim readN hproducts hrowsN
  rcases b.rows_satisfy_or_bad readB htrace hrowsB with hb | hb
  · rcases Handoff.split_handoff claim generator horder sharedValues mask other
      eta mu primeMask alpha quotient hquotient (hproducts hb) hrowsN with hn | hs | hc
    · have hrows : RowsHold n.rows readN :=
        (splitClaim_rows n padCell hpad _ other).mpr hn
      rcases n.rows_satisfy_or_bad readN hrows with hn | hn
      · exact Or.inl ⟨hb,hn⟩
      · exact Or.inr (Or.inr (Or.inl hn))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hs)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr hc)))
  · exact Or.inr (Or.inl hb)

end LfzkV2.Current.Composition
