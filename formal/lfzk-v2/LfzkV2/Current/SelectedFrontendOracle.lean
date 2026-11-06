import LfzkV2.Current.SelectionReplay
import LfzkV2.Current.FrontendCausality
import LfzkV2.Current.FrontendCounting

/-! Local frontend events use the early selected pair. The current answer is
an explicit candidate argument, while selection reads only the commitment's
cut oracle, the earlier fingerprint answer and already bound responses. Thus
the selected inputs and all their pads stay fixed when counting this query. -/
noncomputable section
namespace LfzkV2.Current.SelectedFrontendOracle
open WitnessSelection
open scoped Classical

variable {roles : List Role} {Key Block Link Body C Oracle B N IB IN F Pad : Type}
variable [Field B] [Field N] [DecidableEq B] [DecidableEq N] [Fintype IB] [Fintype IN]
variable [Field F]

local notation "Point" => Input roles Key Block Link Body

def bad
    (lists : Key → Oracle → Finset (WitnessSelection.Candidate B IB) ×
      Finset (WitnessSelection.Candidate N IN))
    (fingerprintCoins : C → Coins B IB × Coins N IN)
    (response : Point → (B × B) × (N × N))
    (oracle : (Point → Link × C) → Key → Oracle)
    {out input : ℕ} (circuit : Layered.Circuit F out input)
    (plan : Layered.Replay.PadPlan (Pad := Pad) circuit)
    (payload : Point → Layered.Replay.Payload circuit)
    (inputs : Selection.Pair B N IB IN → SumcheckV2.Cube input → F)
    (pads : Selection.Pair B N IB IN → Pad → F)
    (decode : C → ℕ → F) (nonzero : C → Linear.TerminalSampling.Nonzero F)
    (start : ℕ) (fallback : C) (point : Point) (H : Point → Link × C) (answer : C) : Prop :=
  ∃ witness, Selection.atPoint lists fingerprintCoins response oracle point H = some witness ∧
    FrontendReplay.BadAt decode nonzero circuit plan (payload point)
      (fun j => point.answersWith H answer fallback (start+j))
      (inputs witness) (pads witness) (point.rank-start)

/-- Restricting the global strict-ancestor tape to this frontend changes only
its indexing. Its current answer remains explicit, and unavailable future
answers retain the same fallback as the global replay. -/
theorem shifted_answersWith (start : ℕ) (point : Point) (H : Point → Link × C)
    (answer fallback : C) (hstart : start ≤ point.rank) :
    (fun j => point.answersWith H answer fallback (start+j)) =
      completeAnswers
        (fun i : Fin (point.rank-start) =>
          point.priorAnswers H ⟨start+i.val, by have := i.isLt; omega⟩)
        answer fallback := by
  funext j
  by_cases hj : j < point.rank-start
  · have hg : start+j < point.rank := by omega
    simp only [Input.answersWith, completeAnswers, hj, hg, ↓reduceDIte]
  · have hg : ¬start+j < point.rank := by omega
    have he : start+j = point.rank ↔ j = point.rank-start := by omega
    simp only [Input.answersWith, completeAnswers, hj, hg, ↓reduceDIte, he]

/-- The early selector chooses one fixed pair or no pair at all. After this
case split, the actual whole-query frontend count applies to that pair's
inputs and pads, including every shared entry/assertion and combine block. -/
theorem bad_card_mul_le [Fintype F] [DecidableEq F] [Fintype C]
    (lists : Key → Oracle → Finset (WitnessSelection.Candidate B IB) ×
      Finset (WitnessSelection.Candidate N IN))
    (fingerprintCoins : C → Coins B IB × Coins N IN)
    (response : Point → (B × B) × (N × N))
    (oracle : (Point → Link × C) → Key → Oracle)
    {out input : ℕ} (circuit : Layered.Circuit F out input)
    (plan : Layered.Replay.PadPlan (Pad := Pad) circuit)
    (payload : Point → Layered.Replay.Payload circuit)
    (inputs : Selection.Pair B N IB IN → SumcheckV2.Cube input → F)
    (pads : Selection.Pair B N IB IN → Pad → F)
    (decode : C → ℕ → F) (nonzero : C → Linear.TerminalSampling.Nonzero F)
    {capacity : ℕ} (decoder : FrontendReplay.Decoder capacity decode nonzero)
    (start : ℕ) (fallback : C) (point : Point) (H : Point → Link × C)
    (hstart : start ≤ point.rank) (hcoalesced : FrontendReplay.Coalesced circuit)
    (hfits : FrontendReplay.Fits capacity circuit 0) :
    (Finset.univ.filter (bad lists fingerprintCoins response oracle circuit plan payload
      inputs pads decode nonzero start fallback point H)).card * (Fintype.card F-1) ≤
        2 * Fintype.card C := by
  classical
  cases hselected : Selection.atPoint lists fingerprintCoins response oracle point H with
  | none => simp [bad, hselected]
  | some witness =>
      have hcount := FrontendReplay.badAt_prefix_card_mul_le decoder circuit plan
        (payload point) (inputs witness) (pads witness) (point.rank-start)
        (fun i : Fin (point.rank-start) =>
          point.priorAnswers H ⟨start+i.val, by have := i.isLt; omega⟩)
        fallback hcoalesced hfits
      have hevent : bad lists fingerprintCoins response oracle circuit plan payload
          inputs pads decode nonzero start fallback point H =
          fun answer => FrontendReplay.BadAt decode nonzero circuit plan (payload point)
            (completeAnswers
              (fun i : Fin (point.rank-start) =>
                point.priorAnswers H ⟨start+i.val, by have := i.isLt; omega⟩)
              answer fallback) (inputs witness) (pads witness) (point.rank-start) := by
        funext answer
        apply propext
        simp only [bad, hselected, Option.some.injEq]
        constructor
        · rintro ⟨w,hw,hbad⟩
          subst w
          simpa only [shifted_answersWith start point H answer fallback hstart] using hbad
        · intro hbad
          refine ⟨witness,rfl,?_⟩
          simpa only [shifted_answersWith start point H answer fallback hstart] using hbad
      rw [hevent]
      exact hcount

/-- Even a malformed query preimage cannot make this local test read its own
oracle answer implicitly. Its answer is supplied only by `answer`. -/
theorem bad_off
    (lists : Key → Oracle → Finset (WitnessSelection.Candidate B IB) ×
      Finset (WitnessSelection.Candidate N IN))
    (fingerprintCoins : C → Coins B IB × Coins N IN)
    (response : Point → (B × B) × (N × N))
    (oracle : (Point → Link × C) → Key → Oracle)
    (hoff : ∀ point H H', Bcs.TotalOracle.AgreeOff point H H' →
      oracle H point.context = oracle H' point.context)
    {out input : ℕ} (circuit : Layered.Circuit F out input)
    (plan : Layered.Replay.PadPlan (Pad := Pad) circuit)
    (payload : Point → Layered.Replay.Payload circuit)
    (inputs : Selection.Pair B N IB IN → SumcheckV2.Cube input → F)
    (pads : Selection.Pair B N IB IN → Pad → F)
    (decode : C → ℕ → F) (nonzero : C → Linear.TerminalSampling.Nonzero F)
    (start : ℕ) (fallback : C) (point : Point) (H H' : Point → Link × C)
    (h : Bcs.TotalOracle.AgreeOff point H H') (answer : C) :
    bad lists fingerprintCoins response oracle circuit plan payload inputs pads decode nonzero
        start fallback point H answer ↔
      bad lists fingerprintCoins response oracle circuit plan payload inputs pads decode nonzero
        start fallback point H' answer := by
  unfold bad
  rw [Selection.atPoint_off lists fingerprintCoins response oracle hoff point H H' h,
    point.answersWith_off H H' h answer fallback]

/-- The clear compiler's failure transfers to its local preimage test once
the parsed prefix and selected cells are identified. Only messages and
answers through this query are needed; later proof data is irrelevant. -/
theorem bad_of_prefix
    (lists : Key → Oracle → Finset (WitnessSelection.Candidate B IB) ×
      Finset (WitnessSelection.Candidate N IN))
    (fingerprintCoins : C → Coins B IB × Coins N IN)
    (response : Point → (B × B) × (N × N))
    (oracle : (Point → Link × C) → Key → Oracle)
    {out input : ℕ} (circuit : Layered.Circuit F out input)
    (plan : Layered.Replay.PadPlan (Pad := Pad) circuit)
    (payload : Point → Layered.Replay.Payload circuit)
    (inputs : Selection.Pair B N IB IN → SumcheckV2.Cube input → F)
    (pads : Selection.Pair B N IB IN → Pad → F)
    (decode : C → ℕ → F) (nonzero : C → Linear.TerminalSampling.Nonzero F)
    (start : ℕ) (fallback : C) (point : Point) (H : Point → Link × C) (answer : C)
    (w : Selection.Pair B N IB IN) (actualPayload : Layered.Replay.Payload circuit)
    (actualAnswers : ℕ → C)
    (hselected : Selection.atPoint lists fingerprintCoins response oracle point H = some w)
    (hanswers : ∀ j, j ≤ point.rank-start → actualAnswers j =
      point.answersWith H answer fallback (start+j))
    (hmessages : ∀ role, FrontendReplay.queryIndex circuit role 0 ≤ point.rank-start →
      Layered.Replay.layerMessage circuit actualPayload role =
        Layered.Replay.layerMessage circuit (payload point) role)
    (hbad : FrontendReplay.BadAt decode nonzero circuit plan actualPayload actualAnswers
      (inputs w) (pads w) (point.rank-start)) :
    bad lists fingerprintCoins response oracle circuit plan payload inputs pads decode nonzero
      start fallback point H answer := by
  refine ⟨w,hselected,?_⟩
  exact (FrontendReplay.badAt_eq_of_inclusive_prefix decode nonzero circuit plan
    actualPayload (payload point) actualAnswers _ (inputs w) (pads w) (point.rank-start)
    hanswers hmessages).mp hbad

end LfzkV2.Current.SelectedFrontendOracle
