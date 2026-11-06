import LfzkV2.Current.ApplicationOracle
import LfzkV2.Current.SelectedFrontendOracle
import LfzkV2.Current.SelectionPath
import LfzkV2.Current.AdapterParameters

/-! One role-disjoint single-answer charge for the current application.
Frontend and auxiliary protocols share the adaptive query budget.  Backend
batching/opening and final-seal inputs have zero application charge. -/
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

/-- The public plan and samplers are fixed. Only the payload is decoded from
the current preimage; it contains exactly the messages already bound there. -/
structure FrontendLocal {F Pad : Type} [Field F] [Fintype F] [DecidableEq F]
    {out input : ℕ} {circuit : Layered.Circuit F out input}
    {messages : Layered.Circuit.Messages Pad circuit}
    (r : Application.Replay circuit messages C) (Witness PointType : Type)
    (inputs : Witness → Cube input → F) (pads : Witness → Pad → F) where
  capacity : ℕ
  payload : PointType → Layered.Replay.Payload circuit
  start : ℕ
  fallback : C
  decoder : FrontendReplay.Decoder capacity r.decode r.nonzero
  coalesced : FrontendReplay.Coalesced circuit
  fits : FrontendReplay.Fits capacity circuit 0

namespace FrontendLocal
variable {F Pad : Type} [Field F] [Fintype F] [DecidableEq F]
  {out input : ℕ} {circuit : Layered.Circuit F out input}
  {messages : Layered.Circuit.Messages Pad circuit}
  {r : Application.Replay circuit messages C}
  {inputs : Selection.Pair B N IB IN → Cube input → F}
  {pads : Selection.Pair B N IB IN → Pad → F}
variable (f : FrontendLocal r (Selection.Pair B N IB IN)
    (Input roles Key Block Link Body) inputs pads)
  (S : SelectionSource roles Key Block Link Body C Oracle B N IB IN)

def data : FrontendData F Pad (Selection.Pair B N IB IN) Point C where
  out := out
  input := input
  circuit := circuit
  plan := r.plan
  payload := f.payload
  inputs := inputs
  pads := pads
  decode := r.decode
  nonzero := r.nonzero
  start := f.start
  fallback := f.fallback

def bad (point : Point) (H : Point → Link × C) (answer : C) : Prop :=
  f.start ≤ point.rank ∧ SelectedFrontendOracle.bad S.lists S.coins S.responses S.oracle
    circuit r.plan f.payload inputs pads r.decode r.nonzero f.start f.fallback point H answer

omit [Fintype B] [Fintype N] in
theorem bad_data (point : Point) (H : Point → Link × C) (answer : C) :
    f.bad S point H answer ↔ f.data.bad S point H answer := Iff.rfl

omit [Fintype B] [Fintype N] in
theorem bad_off (point : Point) (H H' : Point → Link × C)
    (h : Bcs.TotalOracle.AgreeOff point H H') (answer : C) :
    f.bad S point H answer ↔ f.bad S point H' answer := by
  unfold bad
  rw [SelectedFrontendOracle.bad_off S.lists S.coins S.responses S.oracle S.oracle_off
    circuit r.plan f.payload inputs pads r.decode r.nonzero f.start f.fallback point H H' h answer]

omit [Fintype B] [Fintype N] in
theorem bad_card_mul_le (point : Point) (H : Point → Link × C) :
    (univ.filter (f.bad S point H)).card * (Fintype.card F-1) ≤ 2*Fintype.card C := by
  by_cases hs : f.start ≤ point.rank
  · simpa only [bad, hs, true_and] using SelectedFrontendOracle.bad_card_mul_le
      S.lists S.coins S.responses S.oracle circuit r.plan f.payload inputs pads r.decode r.nonzero
      f.decoder f.start f.fallback point H hs f.coalesced f.fits
  · simp [bad, hs]

end FrontendLocal

variable {I J SlotB PadB Other PadN : Type}
  [Algebra (ZMod 2) B] [Fintype I] [DecidableEq I] [Fintype J] [Fintype Other]
  [DecidableEq IB] [DecidableEq IN]
variable {p shared maskBits M K LB LN : ℕ} [Fact p.Prime]

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

structure Configuration
    (A : System B I J SlotB PadB Other PadN IB IN C C p shared maskBits M K)
    (S : SelectionSource roles Key Block Link Body C Oracle B (ZMod p) IB IN)
    (LB LN : ℕ) where
  binary : FrontendLocal A.binaryReplay (Selection.Pair B (ZMod p) IB IN)
    (Input roles Key Block Link Body)
    (fun w => A.binary.inputs (A.binaryRead w)) (fun w => A.binaryRead w ∘ A.binary.coordinate)
  prime : FrontendLocal A.primeReplay (Selection.Pair B (ZMod p) IB IN)
    (Input roles Key Block Link Body)
    (fun w => A.prime.inputs (A.fullPrimeRead w)) (fun w => A.fullPrimeRead w ∘ A.prime.coordinate)
  batchRead : (point : Input roles Key Block Link Body) → (Fin point.rank → C) →
    BatchPacket (ZMod p) (Fin shared ⊕ Other) A.Pair C
  rescaleRead : (point : Input roles Key Block Link Body) → (Fin point.rank → C) →
    RescaleData (ZMod p) (Fin shared) Other A.Pair
  rescaleDecoder : BalancedDecoder C (Linear.TerminalSampling.Nonzero (ZMod p))
  conversionRead : (point : Input roles Key Block Link Body) → (Fin point.rank → C) →
    ConversionData p (shared+maskBits) A.Pair
  conversionDecoder : BalancedDecoder C (Linear.TerminalSampling.Nonzero (ZMod p) ×
    Linear.TerminalSampling.Nonzero (ZMod p))
  packingRead : (point : Input roles Key Block Link Body) → (Fin point.rank → C) →
    PackingData (ZMod 2) B I J SlotB A.Pair
  packingDecoder : BalancedDecoder C (I → B)
  binarySelectionDecoder : BalancedDecoder C (WitnessSelection.Coins B IB)
  primeSelectionDecoder : BalancedDecoder C (WitnessSelection.Coins (ZMod p) IN)
  binarySelection_agrees : ∀ c, binarySelectionDecoder.decode c = (S.coins c).1
  primeSelection_agrees : ∀ c, primeSelectionDecoder.decode c = (S.coins c).2
  binaryList_bound : ∀ (point : Input roles Key Block Link Body) H,
    (S.lists point.context (S.oracle H point.context)).1.card ≤ LB
  primeList_bound : ∀ (point : Input roles Key Block Link Body) H,
    (S.lists point.context (S.oracle H point.context)).2.card ≤ LN
  order_pos : 0 < M
  bits_le : shared+maskBits ≤ K

namespace Configuration
variable {A : System B I J SlotB PadB Other PadN IB IN C C p shared maskBits M K}
  {S : SelectionSource roles Key Block Link Body C Oracle B (ZMod p) IB IN}
variable (c : Configuration A S LB LN)

def roleCharge (role : Role) (point : Point) (H : Point → Link × C) (answer : Link × C) : ℚ :=
  match role with
  | .fingerprint => indicator (S.binarySelection point H answer.2) +
      indicator (S.primeSelection point H answer.2)
  | .inputAssertions .binary .. | .assertions .binary .. | .sumcheck .binary .. |
      .terminal .binary .. | .combine .binary .. => indicator (c.binary.bad S point H answer.2)
  | .inputAssertions .prime .. | .assertions .prime .. | .sumcheck .prime .. |
      .terminal .prime .. | .combine .prime .. => indicator (c.prime.bad S point H answer.2)
  | .rowBatching => indicator (S.rowBatching c.batchRead point H answer.2)
  | .rescaling => indicator (S.rescale c.rescaleRead c.rescaleDecoder point H answer.2)
  | .conversion => indicator (S.conversion c.conversionRead c.conversionDecoder M K point H answer.2)
  | .packing => indicator (S.packing c.packingRead c.packingDecoder point H answer.2)
  | .batching | .opening => 0

def roleBudget (_c : Configuration A S LB LN) : Role → ℚ := roundBudget B p M K LB LN

def single (point : Point) (H : Point → Link × C) (answer : Link × C) : ℚ :=
  match point with
  | .round i .. => c.roleCharge (roles.get i) point H answer
  | .finalSeal .. => 0

def budget (point : Point) : ℚ :=
  match point with
  | .round i .. => c.roleBudget (roles.get i)
  | .finalSeal .. => 0

theorem roleCharge_nonneg (role : Role) (point : Point) (H : Point → Link × C) (answer : Link × C) :
    0 ≤ c.roleCharge role point H answer := by
  have hi (P : Prop) : 0 ≤ indicator P := by unfold indicator; split_ifs <;> norm_num
  cases role with
  | fingerprint => exact add_nonneg (hi _) (hi _)
  | inputAssertions side entries => cases side <;> exact hi _
  | assertions side stage entries fragments => cases side <;> exact hi _
  | sumcheck side stage index => cases side <;> exact hi _
  | terminal side stage => cases side <;> exact hi _
  | combine side stage entries => cases side <;> exact hi _
  | rowBatching | rescaling | conversion | packing => exact hi _
  | batching | opening => exact le_rfl

theorem single_nonneg (point : Point) (H : Point → Link × C) (answer : Link × C) :
    0 ≤ c.single point H answer := by
  cases point with
  | round i history block => exact c.roleCharge_nonneg _ _ _ _
  | finalSeal history body => exact le_rfl

theorem roleCharge_off (role : Role) (point : Point) (H H' : Point → Link × C)
    (h : Bcs.TotalOracle.AgreeOff point H H') (answer : Link × C) :
    c.roleCharge role point H answer = c.roleCharge role point H' answer := by
  have hb := propext (S.binarySelection_off point H H' h answer.2)
  have hn := propext (S.primeSelection_off point H H' h answer.2)
  have hbf := propext (c.binary.bad_off S point H H' h answer.2)
  have hnf := propext (c.prime.bad_off S point H H' h answer.2)
  have hbatch := propext (S.rowBatching_off c.batchRead point H H' h answer.2)
  have hs := propext (S.rescale_off c.rescaleRead c.rescaleDecoder point H H' h answer.2)
  have hc := propext (S.conversion_off c.conversionRead c.conversionDecoder point H H' h answer.2
    (M := M) (K := K))
  have hp := propext (S.packing_off c.packingRead c.packingDecoder point H H' h answer.2)
  cases role with
  | fingerprint => simp only [roleCharge, hb, hn]
  | inputAssertions side entries => cases side <;> simp only [roleCharge, hbf, hnf]
  | assertions side stage entries fragments => cases side <;> simp only [roleCharge, hbf, hnf]
  | sumcheck side stage index => cases side <;> simp only [roleCharge, hbf, hnf]
  | terminal side stage => cases side <;> simp only [roleCharge, hbf, hnf]
  | combine side stage entries => cases side <;> simp only [roleCharge, hbf, hnf]
  | rowBatching => simp only [roleCharge, hbatch]
  | rescaling => simp only [roleCharge, hs]
  | conversion => simp only [roleCharge, hc]
  | packing => simp only [roleCharge, hp]
  | batching | opening => rfl

theorem single_off (point : Point) (H H' : Point → Link × C)
    (h : Bcs.TotalOracle.AgreeOff point H H') (answer : Link × C) :
    c.single point H answer = c.single point H' answer := by
  cases point with
  | round i history block => exact c.roleCharge_off _ _ _ _ h _
  | finalSeal history body => rfl

theorem single_eq_roleCharge (point : Point) (i : Fin roles.length)
    (hrank : point.rank = i.val) (H : Point → Link × C) (answer : Link × C) :
    c.single point H answer = c.roleCharge (roles.get i) point H answer := by
  cases point with
  | round j history block =>
      have hji : j = i := Fin.ext hrank
      subst j
      rfl
  | finalSeal history body =>
      have hi := i.isLt
      change roles.length = i.val at hrank
      omega

theorem binary_charged (role : Role) (point : Point) (H : Point → Link × C)
    (answer : Link × C) (hrole : frontendSide role = some .binary)
    (hbad : c.binary.bad S point H answer.2) : 1 ≤ c.roleCharge role point H answer := by
  cases role <;> simp only [frontendSide, Option.some.injEq, reduceCtorEq] at hrole
  all_goals subst_vars; simp [roleCharge, indicator, hbad]

theorem prime_charged (role : Role) (point : Point) (H : Point → Link × C)
    (answer : Link × C) (hrole : frontendSide role = some .prime)
    (hbad : c.prime.bad S point H answer.2) : 1 ≤ c.roleCharge role point H answer := by
  cases role <;> simp only [frontendSide, Option.some.injEq, reduceCtorEq] at hrole
  all_goals subst_vars; simp [roleCharge, indicator, hbad]

theorem roleCharge_sum [Fintype Link] (role : Role) (point : Point) (H : Point → Link × C) :
    (∑ answer, c.roleCharge role point H answer) ≤
      Fintype.card (Link × C) * c.roleBudget role := by
  have hB : 0 < Fintype.card B-1 := Nat.sub_pos_of_lt Fintype.one_lt_card
  have hp : 0 < p-1 := Nat.sub_pos_of_lt (Fact.out : p.Prime).one_lt
  have hbcount := (S.binarySelection_card_mul_le c.binarySelectionDecoder
    c.binarySelection_agrees point H).trans (Nat.mul_le_mul_right (Fintype.card C)
      (Nat.choose_le_choose 2 (c.binaryList_bound point H)))
  have hncount := (S.primeSelection_card_mul_le c.primeSelectionDecoder
    c.primeSelection_agrees point H).trans (Nat.mul_le_mul_right (Fintype.card C)
      (Nat.choose_le_choose 2 (c.primeList_bound point H)))
  have hb := indicator_link_sum_le (Link := Link) (S.binarySelection point H)
    (LB.choose 2) (Fintype.card B^2) (by positivity) hbcount
  have hn := indicator_link_sum_le (Link := Link) (S.primeSelection point H)
    (LN.choose 2) (p^2) (by have := (Fact.out : p.Prime).pos; positivity)
    (by simpa only [ZMod.card] using hncount)
  have hbf := indicator_link_sum_le (Link := Link) (c.binary.bad S point H)
    2 (Fintype.card B-1) hB (c.binary.bad_card_mul_le S point H)
  have hnf := indicator_link_sum_le (Link := Link) (c.prime.bad S point H)
    2 (p-1) hp (by simpa only [ZMod.card] using c.prime.bad_card_mul_le S point H)
  have hbatch := indicator_link_sum_le (Link := Link) (S.rowBatching c.batchRead point H)
    1 p (Fact.out : p.Prime).pos
    (by simpa only [ZMod.card, one_mul] using S.rowBatching_card_mul_le c.batchRead point H)
  have hs := indicator_link_sum_le (Link := Link) (S.rescale c.rescaleRead c.rescaleDecoder point H)
    1 (p-1) hp (by simpa only [ZMod.card, one_mul] using
      S.rescale_card_mul_le c.rescaleRead c.rescaleDecoder point H)
  have hc := indicator_link_sum_le (Link := Link)
    (S.conversion c.conversionRead c.conversionDecoder M K point H)
    ((2*(K*p/M)+1)^2) ((p-1)^2) (by positivity)
    (S.conversion_card_mul_le c.conversionRead c.conversionDecoder c.order_pos c.bits_le point H)
  have hpack := indicator_link_sum_le (Link := Link) (S.packing c.packingRead c.packingDecoder point H)
    1 (Fintype.card B) Fintype.card_pos
    (by simpa only [one_mul] using (S.packing_card_mul_le c.packingRead c.packingDecoder point H))
  cases role with
  | fingerprint =>
      simp only [roleCharge, sum_add_distrib, roleBudget, roundBudget]
      exact (add_le_add hb hn).trans_eq (by push_cast; ring)
  | inputAssertions side entries => cases side with
      | binary => exact hbf
      | prime => exact hnf
  | assertions side stage entries fragments => cases side with
      | binary => exact hbf
      | prime => exact hnf
  | sumcheck side stage index => cases side with
      | binary => exact hbf
      | prime => exact hnf
  | terminal side stage => cases side with
      | binary => exact hbf
      | prime => exact hnf
  | combine side stage entries => cases side with
      | binary => exact hbf
      | prime => exact hnf
  | rowBatching => exact hbatch
  | rescaling => exact hs
  | conversion => simpa only [roleCharge, roleBudget, roundBudget, Nat.cast_pow] using hc
  | packing => exact hpack
  | batching | opening => simp only [roleCharge, roleBudget, roundBudget, sum_const_zero, mul_zero, le_refl]

theorem single_sum [Fintype Link] (point : Point) (H : Point → Link × C) :
    (∑ answer, c.single point H answer) ≤ Fintype.card (Link × C) * c.budget point := by
  cases point with
  | round i history block => exact c.roleCharge_sum _ _ _
  | finalSeal history body => simp only [single, budget, sum_const_zero, mul_zero, le_refl]

end Configuration

/-- The generated circuit and every local parser are constructed from this
query's strict prefix.  In particular the adapter's challenge-dependent
constants are fixed before testing this query's explicit candidate answer. -/
structure PrefixConfiguration
    (S : SelectionSource roles Key Block Link Body C Oracle B (ZMod p) IB IN)
    (LB LN : ℕ) where
  system : System B I J SlotB PadB Other PadN IB IN C C p shared maskBits M K
  configuration : Configuration system S LB LN

namespace PrefixConfiguration
variable {S : SelectionSource roles Key Block Link Body C Oracle B (ZMod p) IB IN}
variable (read : (point : Input roles Key Block Link Body) → (Fin point.rank → C) →
  PrefixConfiguration (I := I) (J := J) (SlotB := SlotB) (PadB := PadB)
    (Other := Other) (PadN := PadN) (p := p) (shared := shared) (maskBits := maskBits) (M := M) (K := K) S LB LN)

def single (point : Point) (H : Point → Link × C) (answer : Link × C) : ℚ :=
  (read point (point.priorAnswers H)).configuration.single point H answer

def budget (point : Point) : ℚ :=
  match point with
  | .round i .. => roundBudget B p M K LB LN (roles.get i)
  | .finalSeal .. => 0

theorem single_off (point : Point) (H H' : Point → Link × C)
    (h : Bcs.TotalOracle.AgreeOff point H H') (answer : Link × C) :
    single read point H answer = single read point H' answer := by
  unfold single
  rw [point.priorAnswers_off h]
  exact (read point (point.priorAnswers H')).configuration.single_off point H H' h answer

theorem single_nonneg (point : Point) (H : Point → Link × C) (answer : Link × C) :
    0 ≤ single read point H answer :=
  (read point (point.priorAnswers H)).configuration.single_nonneg point H answer

theorem single_sum [Fintype Link] (point : Point) (H : Point → Link × C) :
    (∑ answer, single read point H answer) ≤ Fintype.card (Link × C) *
      budget (B := B) (p := p) (M := M) (K := K) (LB := LB) (LN := LN) point := by
  have h := (read point (point.priorAnswers H)).configuration.single_sum point H
  simpa only [single, Configuration.budget, Configuration.roleBudget, budget] using h

theorem single_zero_of_role (point : Point) (H : Point → Link × C) (answer : Link × C)
    (hrole : point.role = some .batching ∨ point.role = some .opening) :
    single read point H answer = 0 := by
  cases point with
  | round i history block =>
      rcases hrole with hb | ho
      · have he := Option.some.inj hb
        simp only [single, Configuration.single, he, Configuration.roleCharge]
      · have he := Option.some.inj ho
        simp only [single, Configuration.single, he, Configuration.roleCharge]
  | finalSeal history body => rfl

theorem single_finalSeal (history : History Key Block Link roles.length) (body : Body)
    (H : Point → Link × C) (answer : Link × C) :
    single read (.finalSeal history body) H answer = 0 := rfl

end PrefixConfiguration

end LfzkV2.Current.ApplicationCharging
