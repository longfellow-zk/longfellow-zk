import LfzkV2.Current.Frontend
import LfzkV2.Current.Handoff

/-! Algebraic composition of the packed binary frontend, prime frontend and
product adapter. The backend supplies the binary compiled rows and the prime
handoff row. The adapter circuit's semantic identity is stated explicitly:
its satisfaction gives the two product equations on the selected shared bits.
No equality between the two committed hiding masks is assumed. -/
namespace LfzkV2.Current.Composition
open SumcheckV2 DualPacking.ArtinSchreier

variable {B I J SlotB PadB Other PadN G : Type} [Field B] [Fintype B] [DecidableEq B]
  [Algebra (ZMod 2) B] [Fintype I] [DecidableEq I] [Fintype J]
  [Fintype Other] [CommGroup G]
variable {p shared maskBits M K : ℕ} [Fact p.Prime]

/-- This reduction includes both actual affine compilers, the packing check,
the prime row batch and both conversion challenges. Its conclusion separates
the five algebraic failure sources for later charging at their own boundaries.
Circuit/layout correctness is the explicit `hproducts` premise; no protocol
soundness or event-coverage assumption is hidden in that premise. -/
theorem rows_reduction
    (b : Frontend.Packed B I J SlotB PadB)
    (n : Frontend.Prime (ZMod p) (Fin shared ⊕ Other) PadN)
    (readB : SlotB → B) (other : Other → ZMod p)
    (sharedValues : Fin shared → Bool) (mask : Fin maskBits → Bool)
    (rho : Fin n.rows.length → ZMod p) (eta mu primeMask : ZMod p)
    (alpha : Fin 2 → Linear.TerminalSampling.Nonzero (ZMod p))
    (generator : G) (horder : orderOf generator = M)
    (quotient : Fin 2 → ℕ) (hquotient : ∀ j, quotient j < K)
    (htrace : ∀ k, traceF (ZMod 2) (b.U k) = 0)
    (hrowsB : RowsHold b.rows readB) :
    let claim := Prime.Claim.fromRow (Prime.batchRows n.rows.get rho)
    let readN := Sum.elim (fun i => if sharedValues i then 1 else 0) other
    (b.circuit.Satisfies (b.inputs readB) →
      ∀ j, Adapter.ProductCheck generator (Handoff.weights claim.sharedWeights eta)
        (Handoff.values sharedValues mask) mu (alpha j).val (quotient j)) →
    (claim.row eta mu).eval (Sum.elim other (fun _ => primeMask)) = 0 →
    (b.circuit.Satisfies (b.inputs readB) ∧ n.circuit.Satisfies (n.inputs readN)) ∨
      b.Bad readB ∨ n.Bad readN ∨
      Prime.BatchBad (fun i => (n.rows.get i).eval readN) rho ∨
      Prime.RescalingBad (claim.residual (fun i => if sharedValues i then 1 else 0) other)
        (Handoff.binaryMask mask - primeMask) eta ∨
      Handoff.ConversionBad claim.sharedWeights eta mu sharedValues mask M K alpha := by
  intro claim readN hproducts hrowN
  rcases b.rows_satisfy_or_bad readB htrace hrowsB with hb | hb
  · rcases Handoff.batched_handoff n.rows.get rho generator horder sharedValues mask other
      eta mu primeMask alpha quotient hquotient (hproducts hb) hrowN with hn | hbch | hs | hc
    · have hrowsN : RowsHold n.rows readN := by
        intro row hr
        obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hr
        exact hn i
      rcases n.rows_satisfy_or_bad readN hrowsN with hn | hn
      · exact Or.inl ⟨hb,hn⟩
      · exact Or.inr (Or.inr (Or.inl hn))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hbch)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hs))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hc))))
  · exact Or.inr (Or.inl hb)

end LfzkV2.Current.Composition
