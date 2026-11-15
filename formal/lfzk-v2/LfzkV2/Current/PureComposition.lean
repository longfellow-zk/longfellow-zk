import LfzkV2.Current.Frontend
import LfzkV2.Current.PureHandoff

/-! Algebraic composition of the packed binary frontend, a pure-foreign prime
frontend and the product adapter, the pure-foreign counterpart of
`Composition.rows_reduction`. Every prime slot, private input or pad, is a
bit group of the binary commitment. The backend authenticates only the
binary rows; the prime rows reach the adapter batched with the row weights.
The adapter circuit's semantic identity is the explicit `hproducts` premise,
as in the mixed composition. -/
noncomputable section
namespace LfzkV2.Current.PureComposition
open SumcheckV2 DualPacking.ArtinSchreier

variable {B I J SlotB PadB Value PadN G : Type} [Field B] [Fintype B] [DecidableEq B]
  [Algebra (ZMod 2) B] [Fintype I] [DecidableEq I] [Fintype J] [Fintype Value] [CommGroup G]
variable {p bits M K : ℕ} [Fact p.Prime]

/-- `zk::split::pure_claim`: the prime frontend's compiled rows, the layer
rows then the input equation, batched with the row weights. -/
def claim (n : Frontend.Prime (ZMod p) Value PadN) (rho : Fin n.rows.length → ZMod p) :
    RowBatching.Claim Value (ZMod p) :=
  RowBatching.batch n.rows.get rho

/-- The reduction covers the binary compiled rows, the packing check, the
batched prime rows and both conversion challenges. Its conclusion separates
the four algebraic failure sources for charging at their own answers. -/
theorem rows_reduction
    (b : Frontend.Packed B I J SlotB PadB)
    (n : Frontend.Prime (ZMod p) Value PadN) (groups : PureHandoff.Groups Value bits)
    (readB : SlotB → B) (values : Fin bits → Bool)
    (rho : Fin n.rows.length → ZMod p) (alpha : PureHandoff.Conversion p)
    (generator : G) (horder : orderOf generator = M)
    (quotient : Fin 2 → ℕ) (hquotient : ∀ j, quotient j < K)
    (htrace : ∀ k, traceF (ZMod 2) (b.U k) = 0)
    (hrowsB : RowsHold b.rows readB) :
    (b.circuit.Satisfies (b.inputs readB) →
      ∀ j, Adapter.ProductCheck generator (groups.weights (claim n rho).weights) values
        (claim n rho).target (alpha j).val (quotient j)) →
    (b.circuit.Satisfies (b.inputs readB) ∧
        n.circuit.Satisfies (n.inputs (groups.value values))) ∨
      b.Bad readB ∨ n.Bad (groups.value values) ∨
      RowBatching.Bad n.rows.get (groups.value values) rho ∨
      PureHandoff.ConversionBad groups (claim n rho) values M K alpha := by
  intro hproducts
  rcases b.rows_satisfy_or_bad readB htrace hrowsB with hb | hb
  · rcases PureHandoff.pure_handoff generator horder n.rows.get groups values rho alpha
      quotient hquotient (hproducts hb) with hn | hr | hc
    · rcases n.rows_satisfy_or_bad (groups.value values)
        ((RowBatching.holds_get_iff n.rows _).mp hn) with hn | hn
      · exact Or.inl ⟨hb, hn⟩
      · exact Or.inr (Or.inr (Or.inl hn))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hr)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr hc)))
  · exact Or.inr (Or.inl hb)

end LfzkV2.Current.PureComposition
