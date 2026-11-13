import LfzkV2.Current.ApplicationOracle
import LfzkV2.Current.SelectedFrontendOracle

/-! Local count-to-charge bounds, frontend read data and application role
budgets. `RuntimeAdaptiveCharges` builds the actual charge from the decoded
query prefix; backend and final-seal positions have zero application budget. -/
noncomputable section
namespace LfzkV2.Current.ApplicationCharging
open ApplicationOracle Application RecursivePolygero Counting SumcheckV2 Finset
open scoped Classical

variable {roles : List Role} {Key Block Link Body C Oracle B N IB IN : Type}
variable [Field B] [Field N] [Fintype B] [Fintype N] [DecidableEq B] [DecidableEq N]
  [Fintype IB] [Fintype IN] [Fintype C]
local notation "Point" => Input roles Key Block Link Body

theorem indicator_sum_le {Raw : Type} [Fintype Raw] (bad : Raw → Prop)
    (numerator denominator : ℕ) (hden : 0 < denominator)
    (hcount : (univ.filter bad).card * denominator ≤ numerator * Fintype.card Raw) :
    (∑ raw, indicator (bad raw)) ≤ Fintype.card Raw * ((numerator : ℚ)/denominator) := by
  have hsum : (∑ raw, indicator (bad raw)) = ((univ.filter bad).card : ℚ) := by
    simp [indicator]
  rw [hsum, ← mul_div_assoc]
  apply (le_div_iff₀ (show (0 : ℚ) < denominator by exact_mod_cast hden)).mpr
  have h : ((univ.filter bad).card : ℚ) * denominator ≤
      (numerator : ℚ) * Fintype.card Raw := by exact_mod_cast hcount
  simpa only [mul_comm] using h

theorem indicator_link_sum_le [Fintype Link] (bad : C → Prop)
    (numerator denominator : ℕ) (hden : 0 < denominator)
    (hcount : (univ.filter bad).card * denominator ≤ numerator * Fintype.card C) :
    (∑ answer : Link × C, indicator (bad answer.2)) ≤
      Fintype.card (Link × C) * ((numerator : ℚ)/denominator) := by
  rw [Fintype.sum_prod_type]
  simp only [sum_const, card_univ, nsmul_eq_mul]
  have h := mul_le_mul_of_nonneg_left (indicator_sum_le bad numerator denominator hden hcount)
    (show (0 : ℚ) ≤ Fintype.card Link by positivity)
  simpa only [Fintype.card_prod, Nat.cast_mul, mul_assoc] using h

/-- A charge-relevant frontend view omits the full proof's future messages
and answer tape. Equality of these views is a concrete codec/layout
correspondence and remains meaningful before the other frontend is built. -/
structure FrontendData (F Pad Witness PointType C : Type) [Field F] where
  out : ℕ
  input : ℕ
  circuit : Layered.Circuit F out input
  plan : Layered.Replay.PadPlan (Pad := Pad) circuit
  payload : PointType → Layered.Replay.Payload circuit
  inputs : Witness → Cube input → F
  pads : Witness → Pad → F
  decode : C → ℕ → F
  nonzero : C → Linear.TerminalSampling.Nonzero F
  start : ℕ
  fallback : C

def FrontendData.bad {F Pad : Type} [Field F]
    (d : FrontendData F Pad (Selection.Pair B N IB IN) Point C)
    (S : SelectionSource roles Key Block Link Body C Oracle B N IB IN)
    (point : Point) (H : Point → Link × C) (answer : C) : Prop :=
  d.start ≤ point.rank ∧ SelectedFrontendOracle.bad S.lists S.coins S.responses S.oracle
    d.circuit d.plan d.payload d.inputs d.pads d.decode d.nonzero d.start d.fallback point H answer

def roundBudget (B : Type) [Fintype B] (p M K LB LN : ℕ) : Role → ℚ
  | .fingerprint => (LB.choose 2 : ℚ)/(Fintype.card B : ℚ)^2 +
      (LN.choose 2 : ℚ)/(p : ℚ)^2
  | .inputAssertions .binary .. | .assertions .binary .. | .sumcheck .binary .. |
      .terminal .binary .. | .combine .binary .. => 2/((Fintype.card B-1 : ℕ) : ℚ)
  | .inputAssertions .prime .. | .assertions .prime .. | .sumcheck .prime .. |
      .terminal .prime .. | .combine .prime .. => 2/((p-1 : ℕ) : ℚ)
  | .rowBatching => 1/(p : ℚ)
  | .rescaling => 1/((p-1 : ℕ) : ℚ)
  | .conversion => ((2*(K*p/M)+1 : ℕ) : ℚ)^2/((p-1 : ℕ) : ℚ)^2
  | .packing => 1/(Fintype.card B : ℚ)
  | .batching | .opening => 0

variable {p M K LB LN : ℕ}

def budget (point : Point) : ℚ :=
  match point with
  | .round i .. => roundBudget B p M K LB LN (roles.get i)
  | .finalSeal .. => 0

end LfzkV2.Current.ApplicationCharging
