import LfzkV2.Current.FrontendCausality
import LfzkV2.Current.EntryChallenges
import LfzkV2.Current.BalancedDecoder

/-! Whole-answer counting for the current frontend.  The retained algebra
names an entry and a layer assertion separately, although the implementation
samples their coefficients in one answer.  The same sharing occurs between
the final combine coefficient and input-level entries.  The tests below keep
those pairs together; no coordinate read is counted as a new oracle query. -/
namespace LfzkV2.Current.FrontendReplay
open SumcheckV2 Linear.Challenges Finset
open Layered.Replay (LayerRole)
open scoped Classical

variable {F Pad C : Type} [Field F]

/-- The normalized frontend aggregates all entering outputs at a stage.
Thus there is at most one entry before a layer or before the final inputs.
This is a public circuit-layout condition, with no witness or oracle premise. -/
def Coalesced : {out input : ℕ} → Layered.Circuit F out input → Prop
  | _, _, .input => True
  | _, _, .layer _ _ rest => Coalesced rest
  | _, _, .entry _ _ rest =>
      (match rest with | .entry .. => False | _ => True) ∧ Coalesced rest

/-- Every coordinate consumed by the parser is within the ideal decoder's
public capacity. Input entries start after the final combine coefficient. -/
def Fits (capacity : ℕ) : {out input : ℕ} → Layered.Circuit F out input → ℕ → Prop
  | _, _, .input, _ => True
  | _, _, .entry n _ rest, offset =>
      offset+n ≤ capacity ∧ Fits capacity rest (offset+n)
  | _, _, .layer a _ rest, offset =>
      offset+a ≤ capacity ∧ 1 ≤ capacity ∧
        Fits capacity rest (if hasLayers rest then 0 else 1)

/-- A grouped failure is either two fixed affine hyperplanes, an ordinary
quadratic root, or a nonzero terminal root. The two affine hyperplanes are a
conservative cover of the retained compiler's sequential algebraic events. -/
inductive QueryTest (F : Type) [Field F] where
  | empty
  | affine (offset dimension : ℕ) (incoming claim : F)
      (left right : Fin dimension → F)
  | round (data : RoundData F)
  | combine (data : CombineData F)
  | terminal (data : LinearTerminal.Data F)

def QueryTest.Valid (capacity : ℕ) : QueryTest F → Prop
  | .empty => True
  | .affine offset dimension _ _ _ _ => offset+dimension ≤ capacity
  | .round data => 1 ≤ capacity ∧ data.truth.natDegree ≤ 2
  | .combine _ => 1 ≤ capacity
  | .terminal _ => True

def QueryTest.Bad (decode : C → ℕ → F)
    (nonzero : C → Linear.TerminalSampling.Nonzero F) : QueryTest F → C → Prop
  | .empty, _ => False
  | .affine offset _ incoming claim left right, answer =>
      AssertionBad incoming claim (fun i => decode answer (offset+i.val)) left ∨
        AssertionBad incoming claim (fun i => decode answer (offset+i.val)) right
  | .round data, answer => BadRoundEvent data.truth data.message data.claim (decode answer 0)
  | .combine data, answer =>
      BadCombineEvent data.trueA data.trueB data.claimA data.claimB (decode answer 0)
  | .terminal data, answer => data.Bad (nonzero answer).val

/-- The ideal finite answer supplies uniform consecutive field coordinates
and a uniform rejected-zero coordinate. These are distribution laws, not
assumptions about bad-event probabilities. All coordinates of one block are
decoded from the same answer. -/
structure Decoder [Fintype F] [DecidableEq F] [Fintype C]
    (capacity : ℕ) (decode : C → ℕ → F)
    (nonzero : C → Linear.TerminalSampling.Nonzero F) where
  fieldFiber : ℕ
  field_balanced : fieldFiber * Fintype.card F = Fintype.card C
  blocks : ∀ offset dimension, offset+dimension ≤ capacity →
    ∃ sampler : ChallengeBlocks.Sampler F C (.assertions dimension),
      sampler.decode = fun answer i => decode answer (offset+i.val)
  terminal : Linear.TerminalSampling.Sampler F C
  terminal_decode : terminal.decode = nonzero

theorem QueryTest.bad_card_mul_le [Fintype F] [DecidableEq F] [Fintype C]
    {capacity : ℕ} {decode : C → ℕ → F}
    {nonzero : C → Linear.TerminalSampling.Nonzero F}
    (decoder : Decoder capacity decode nonzero) (test : QueryTest F)
    (hvalid : test.Valid capacity) :
    (univ.filter (test.Bad decode nonzero)).card * (Fintype.card F-1) ≤
      2 * Fintype.card C := by
  cases test with
  | empty => simp [QueryTest.Bad]
  | affine offset dimension incoming claim left right =>
      obtain ⟨sampler,hsampler⟩ := decoder.blocks offset dimension hvalid
      let balanced : BalancedDecoder C (Fin dimension → F) := {
        decode := sampler.decode
        fiber := sampler.fiber
        fiber_bound := by
          intro z
          convert! sampler.fiber_bound z using 1
          congr 1
          ext raw
          simp only [mem_filter]
        balanced := by simpa only [Fintype.card_fun, Fintype.card_fin] using sampler.balanced }
      have hlocal : (univ.filter fun beta : Fin dimension → F =>
          AssertionBad incoming claim beta left ∨ AssertionBad incoming claim beta right).card *
            Fintype.card F ≤ 2 * Fintype.card (Fin dimension → F) := by
        convert! EntryChallenges.two_events_card_mul_le incoming claim left right using 1
      have hraw := balanced.bad_card_mul_le
        (fun beta => AssertionBad incoming claim beta left ∨
          AssertionBad incoming claim beta right) 2 (Fintype.card F)
        (by
          convert! hlocal using 1
          congr 2
          ext beta
          simp only [mem_filter])
      have hcount : (univ.filter (QueryTest.Bad decode nonzero
          (.affine offset dimension incoming claim left right))).card * Fintype.card F ≤
          2 * Fintype.card C := by
        simpa only [QueryTest.Bad, balanced, hsampler] using hraw
      exact (Nat.mul_le_mul_left _ (Nat.sub_le _ _)).trans hcount
  | round data =>
      obtain ⟨sampler,hsampler⟩ := decoder.blocks 0 1 (by simpa using hvalid.1)
      let scalar : ChallengeBlocks.Sampler F C .round :=
        ⟨sampler.decode, sampler.fiber, sampler.fiber_bound, sampler.balanced⟩
      have hraw := scalar.raw_bad_card decoder.fieldFiber decoder.field_balanced
        (data := (data : ChallengeBlocks.Data F .round)) hvalid.2
      have hdecode : sampler.decode = fun answer (_ : Fin 1) => decode answer 0 := by
        rw [hsampler]
        funext answer i
        simp only [Nat.zero_add, Fin.eq_zero i, Fin.val_zero]
      have hcount : (univ.filter fun answer =>
          BadRoundEvent data.truth data.message data.claim (decode answer 0)).card ≤
          decoder.fieldFiber * 2 := by
        simpa only [ChallengeBlocks.Data.Bad, ChallengeBlocks.Kind.dimension,
          ChallengeBlocks.Kind.budget, scalar, hdecode] using hraw
      calc
        _ ≤ (decoder.fieldFiber * 2) * (Fintype.card F-1) := Nat.mul_le_mul_right _ hcount
        _ ≤ (decoder.fieldFiber * 2) * Fintype.card F :=
          Nat.mul_le_mul_left _ (Nat.sub_le _ _)
        _ = 2 * Fintype.card C := by rw [← decoder.field_balanced]; ring
  | terminal data =>
      have hraw := decoder.terminal.bad_card_le (fun _ : Unit => data)
      have hcount : (univ.filter fun answer => data.Bad (nonzero answer).val).card ≤
          decoder.terminal.fiber * 2 := by
        simpa only [decoder.terminal_decode, Fintype.card_unit, mul_one, exists_const] using hraw
      calc
        _ ≤ (decoder.terminal.fiber * 2) * (Fintype.card F-1) := Nat.mul_le_mul_right _ hcount
        _ = 2 * Fintype.card C := by
          rw [← Linear.TerminalSampling.nonzero_card, ← decoder.terminal.balanced]
          ring
  | combine data =>
      obtain ⟨sampler,hsampler⟩ := decoder.blocks 0 1 (by simpa only [QueryTest.Valid, Nat.zero_add] using hvalid)
      let scalar : ChallengeBlocks.Sampler F C .combine :=
        ⟨sampler.decode, sampler.fiber, sampler.fiber_bound, sampler.balanced⟩
      have hraw := scalar.raw_bad_card decoder.fieldFiber decoder.field_balanced data trivial
      have hdecode : sampler.decode = fun answer (_ : Fin 1) => decode answer 0 := by
        rw [hsampler]
        funext answer i
        simp only [Nat.zero_add, Fin.eq_zero i, Fin.val_zero]
      have hcount : (univ.filter fun answer =>
          BadCombineEvent data.trueA data.trueB data.claimA data.claimB (decode answer 0)).card ≤
          decoder.fieldFiber := by
        simpa only [ChallengeBlocks.Data.Bad, ChallengeBlocks.Kind.dimension,
          ChallengeBlocks.Kind.budget, scalar, hdecode, mul_one] using hraw
      calc
        _ ≤ decoder.fieldFiber * (Fintype.card F-1) := Nat.mul_le_mul_right _ hcount
        _ ≤ decoder.fieldFiber * Fintype.card F :=
          Nat.mul_le_mul_left _ (Nat.sub_le _ _)
        _ = Fintype.card C := decoder.field_balanced
        _ ≤ 2 * Fintype.card C := by omega

/-- The generalized form lets the structural proof descend through the actual
parser while retaining the carried weights and claim of the preceding layer. -/
noncomputable def BadFrom (decode : C → ℕ → F)
    (nonzero : C → Linear.TerminalSampling.Nonzero F)
    {out input : ℕ} (circuit : Layered.Circuit F out input)
    (plan : Layered.Replay.PadPlan (Pad := Pad) circuit) (payload : Layered.Replay.Payload circuit)
    (answers : ℕ → C) (start offset : ℕ) (w : Cube input → F)
    (weights : Cube out → F) (pads : Pad → F) (claim : F) (query : ℕ) : Prop :=
  ∃ role : LayerRole circuit, queryIndex circuit role start = query ∧
    Data.Bad (dataAtRole decode nonzero circuit plan payload answers start offset
      w weights pads claim role) (sampleAtRole decode nonzero circuit role answers start offset)

theorem badFrom_ge (decode : C → ℕ → F)
    (nonzero : C → Linear.TerminalSampling.Nonzero F)
    {out input : ℕ} (circuit : Layered.Circuit F out input)
    (plan : Layered.Replay.PadPlan (Pad := Pad) circuit) (payload : Layered.Replay.Payload circuit)
    (answers : ℕ → C) (start offset : ℕ) (w : Cube input → F)
    (weights : Cube out → F) (pads : Pad → F) (claim : F) (query : ℕ)
    (h : BadFrom decode nonzero circuit plan payload answers start offset w weights pads claim query) :
    start ≤ query := by
  obtain ⟨role,hindex,_⟩ := h
  simpa only [hindex] using queryIndex_ge circuit role start

omit [Field F] in
theorem append_decode (decode : C → ℕ → F) (answer : C) (offset n m : ℕ) :
    (fun i : Fin (n+m) => decode answer (offset+i.val)) =
      Fin.append (fun i : Fin n => decode answer (offset+i.val))
        (fun i : Fin m => decode answer (offset+n+i.val)) := by
  funext i
  refine Fin.addCases ?_ ?_ i
  · intro j
    simp
  · intro j
    simp [Nat.add_assoc]

/-- At a shared entry/assertion boundary, the two retained failure positions
are contained in two fixed hyperplanes in the complete coefficient block. -/
theorem entry_layer_at_start (decode : C → ℕ → F)
    (nonzero : C → Linear.TerminalSampling.Nonzero F)
    {out next mid input n a : ℕ}
    (e : Layered.Entry (Cube out) (Cube next) n)
    (body : LfzkV2.Native.CircuitLayer (Cube next) (Cube mid) (Fin a) F)
    (rest : Layered.Circuit F mid input)
    (plan : Layered.Replay.PadPlan (Pad := Pad) (.layer a body rest))
    (payload : Layered.Replay.Payload (.layer a body rest))
    (answers : ℕ → C) (start offset : ℕ) (w : Cube input → F)
    (weights : Cube out → F) (pads : Pad → F) (claim : F)
    (h : BadFrom decode nonzero (.entry n e (.layer a body rest)) plan payload
      answers start offset w weights pads claim start) :
    (QueryTest.affine offset (n+a)
      (dot weights (e.previous (body.outputs (rest.eval w)))) claim
      (Fin.append (e.residuals (body.outputs (rest.eval w))) 0)
      (Fin.append (e.residuals (body.outputs (rest.eval w))) (body.residuals (rest.eval w)))).Bad
        decode nonzero (answers start) := by
  obtain ⟨role,hindex,hbad⟩ := h
  have hseq :
      AssertionBad (dot weights (e.previous (body.outputs (rest.eval w)))) claim
        (fun i : Fin n => decode (answers start) (offset+i.val))
        (e.residuals (body.outputs (rest.eval w))) ∨
      AssertionBad (dot weights (e.previous (body.outputs (rest.eval w))) +
          dot (fun i : Fin n => decode (answers start) (offset+i.val))
            (e.residuals (body.outputs (rest.eval w)))) claim
        (fun i : Fin a => decode (answers start) (offset+n+i.val))
        (body.residuals (rest.eval w)) := by
    rcases role with i | i | i | i | i | role
    · exact Or.inl hbad
    · apply Or.inr
      simpa only [dataAtRole, sampleAtRole, LayerRole.kind, Data.Bad,
        ChallengeBlocks.Data.Bad, Layered.Circuit.eval, e.dot_weights] using hbad
    · simp only [queryIndex] at hindex
      omega
    · simp only [queryIndex] at hindex
      omega
    · simp only [queryIndex] at hindex
      omega
    · have hge := queryIndex_ge rest role
          (if hasLayers rest then start+mid+3 else start+mid+2)
      simp only [queryIndex] at hindex
      split_ifs at hindex hge <;> omega
  have hcover := EntryChallenges.sequential_entry_cover _ _ _ _ _ _ hseq
  simpa only [QueryTest.Bad, append_decode] using hcover

theorem layer_round_data_update (decode : C → ℕ → F)
    (nonzero : C → Linear.TerminalSampling.Nonzero F)
    {out mid input a : ℕ} (body : LfzkV2.Native.CircuitLayer (Cube out) (Cube mid) (Fin a) F)
    (rest : Layered.Circuit F mid input)
    (plan : Layered.Replay.PadPlan (Pad := Pad) (.layer a body rest))
    (payload : Layered.Replay.Payload (.layer a body rest))
    (answers : ℕ → C) (start offset : ℕ) (w : Cube input → F)
    (weights : Cube out → F) (pads : Pad → F) (claim : F) (i : Fin mid) (answer : C) :
    dataAtRole decode nonzero (.layer a body rest) plan payload
      (Function.update answers (start+1+i.val) answer) start offset w weights pads claim (.inr (.inl i)) =
    dataAtRole decode nonzero (.layer a body rest) plan payload
      answers start offset w weights pads claim (.inr (.inl i)) := by
  have hb : Function.update answers (start+1+i.val) answer start = answers start :=
    Function.update_of_ne (by omega) _ _
  have hp : SumcheckV1.extract_prefix
      (fun j : Fin mid => decode (Function.update answers (start+1+i.val) answer (start+1+j.val)) 0) i =
      SumcheckV1.extract_prefix (fun j : Fin mid => decode (answers (start+1+j.val)) 0) i := by
    funext j
    change decode (Function.update answers (start+1+i.val) answer (start+1+j.val)) 0 =
      decode (answers (start+1+j.val)) 0
    rw [Function.update_of_ne (by have := j.isLt; omega)]
  dsimp only [dataAtRole, LayerRole.kind, readFrom]
  rw [hb, hp]

theorem layer_terminal_data_update (decode : C → ℕ → F)
    (nonzero : C → Linear.TerminalSampling.Nonzero F)
    {out mid input a : ℕ} (body : LfzkV2.Native.CircuitLayer (Cube out) (Cube mid) (Fin a) F)
    (rest : Layered.Circuit F mid input)
    (plan : Layered.Replay.PadPlan (Pad := Pad) (.layer a body rest))
    (payload : Layered.Replay.Payload (.layer a body rest))
    (answers : ℕ → C) (start offset : ℕ) (w : Cube input → F)
    (weights : Cube out → F) (pads : Pad → F) (claim : F) (i : Fin 1) (answer : C) :
    dataAtRole decode nonzero (.layer a body rest) plan payload
      (Function.update answers (start+1+mid) answer) start offset w weights pads claim
        (.inr (.inr (.inl i))) =
    dataAtRole decode nonzero (.layer a body rest) plan payload
      answers start offset w weights pads claim (.inr (.inr (.inl i))) := by
  have hb : Function.update answers (start+1+mid) answer start = answers start :=
    Function.update_of_ne (by omega) _ _
  have hp : (fun j : Fin mid => decode (Function.update answers (start+1+mid) answer
      (start+1+j.val)) 0) = (fun j : Fin mid => decode (answers (start+1+j.val)) 0) := by
    funext j
    rw [Function.update_of_ne (by have := j.isLt; omega)]
  dsimp only [dataAtRole, LayerRole.kind, readFrom, Linear.LayerMessages.transcript,
    Linear.LayerTranscript.finalClaim, Linear.LayerTranscript.clearRounds,
    Linear.LayerTranscript.terminalPads]
  rw [hb, hp]

theorem layer_combine_data_update (decode : C → ℕ → F)
    (nonzero : C → Linear.TerminalSampling.Nonzero F)
    {out mid input a : ℕ} (body : LfzkV2.Native.CircuitLayer (Cube out) (Cube mid) (Fin a) F)
    (rest : Layered.Circuit F mid input)
    (plan : Layered.Replay.PadPlan (Pad := Pad) (.layer a body rest))
    (payload : Layered.Replay.Payload (.layer a body rest))
    (answers : ℕ → C) (start offset : ℕ) (w : Cube input → F)
    (weights : Cube out → F) (pads : Pad → F) (claim : F) (i : Fin 1) (answer : C) :
    dataAtRole decode nonzero (.layer a body rest) plan payload
      (Function.update answers (start+mid+2) answer) start offset w weights pads claim
        (.inr (.inr (.inr (.inl i)))) =
    dataAtRole decode nonzero (.layer a body rest) plan payload
      answers start offset w weights pads claim (.inr (.inr (.inr (.inl i)))) := by
  have hb : Function.update answers (start+mid+2) answer start = answers start :=
    Function.update_of_ne (by omega) _ _
  have hp : (fun j : Fin mid => decode (Function.update answers (start+mid+2) answer
      (start+1+j.val)) 0) = (fun j : Fin mid => decode (answers (start+1+j.val)) 0) := by
    funext j
    rw [Function.update_of_ne (by have := j.isLt; omega)]
  have hs : Function.update answers (start+mid+2) answer (start+1+mid) =
      answers (start+1+mid) := Function.update_of_ne (by omega) _ _
  dsimp only [dataAtRole, LayerRole.kind, readFrom, Linear.LayerMessages.transcript,
    Linear.LayerTranscript.clearA, Linear.LayerTranscript.clearB,
    Linear.LayerTranscript.terminalPads]
  rw [hb, hp, hs]

theorem layer_final_entry_at_combine (decode : C → ℕ → F)
    (nonzero : C → Linear.TerminalSampling.Nonzero F)
    {out mid input a n : ℕ}
    (body : LfzkV2.Native.CircuitLayer (Cube out) (Cube mid) (Fin a) F)
    (e : Layered.Entry (Cube mid) (Cube input) n)
    (plan : Layered.Replay.PadPlan (Pad := Pad) (.layer a body (.entry n e .input)))
    (payload : Layered.Replay.Payload (.layer a body (.entry n e .input)))
    (answers : ℕ → C) (start offset : ℕ) (w : Cube input → F)
    (weights : Cube out → F) (pads : Pad → F) (claim : F)
    (h : BadFrom decode nonzero (.layer a body (.entry n e .input)) plan payload
      answers start offset w weights pads claim (start+mid+2)) :
    let d := dataAtRole decode nonzero (.layer a body (.entry n e .input)) plan payload
      answers start offset w weights pads claim (.inr (.inr (.inr (.inl 0))))
    (QueryTest.affine 0 (n+1) (d.claimA-d.trueA) 0
      (Fin.cons (d.claimB-d.trueB) 0)
      (Fin.cons (d.claimB-d.trueB) (fun i => -(e.residuals w) i))).Bad
        decode nonzero (answers (start+mid+2)) := by
  let ml := (readFrom decode nonzero (.layer a body (.entry n e .input))
    plan payload answers start offset).1
  let wires := e.previous w
  let Q := body.effectiveQuadratic weights ml.beta
  let L := body.effectiveLinear weights ml.beta
  let q := bindRightAffine Q L wires
  let t := ml.transcript body weights
  have hseq : BadCombineEvent (evaluate wires ml.point) (evaluate q ml.point)
        (t.clearA pads) (t.clearB pads) ml.alpha ∨
      AssertionBad (evaluate wires ml.point + ml.alpha*(evaluate q ml.point-evaluate L ml.point))
        (t.clearA pads + ml.alpha*(t.clearB pads-evaluate L ml.point))
        (fun i : Fin n => decode (answers (start+mid+2)) (1+i.val)) (e.residuals w) := by
    obtain ⟨role,hindex,hbad⟩ := h
    rcases role with i | i | i | i | i | role
    · simp only [queryIndex] at hindex
      omega
    · simp only [queryIndex] at hindex
      have := i.isLt
      omega
    · simp only [queryIndex] at hindex
      omega
    · exact Or.inl hbad
    · apply Or.inr
      have hdot := affine_nextWeights_correct Q L (monomialWeights ml.point) wires ml.alpha
      dsimp only [dataAtRole, sampleAtRole, LayerRole.kind, Data.Bad,
        ChallengeBlocks.Data.Bad, readFrom, hasLayers] at hbad
      change AssertionBad (dot (nextWeights Q (monomialWeights ml.point) ml.alpha) wires)
        (t.nextValue pads) (fun i : Fin n => decode (answers (start+mid+2)) (1+i.val))
        (e.residuals w) at hbad
      rw [hdot] at hbad
      have htalpha : t.alpha = ml.alpha := rfl
      have htlinear : t.linear = evaluate L ml.point := rfl
      simpa only [← evaluate_eq_dot, Linear.LayerTranscript.nextValue, htalpha, htlinear, q] using hbad
    · exact Fin.elim0 role
  have hcover := EntryChallenges.sequential_combine_cover (t.clearA pads) (t.clearB pads)
    (evaluate wires ml.point) (evaluate q ml.point) (evaluate L ml.point) ml.alpha
    (fun i : Fin n => decode (answers (start+mid+2)) (1+i.val)) (e.residuals w) hseq
  have hcons : (fun i : Fin (n+1) => decode (answers (start+mid+2)) i.val) =
      Fin.cons ml.alpha (fun i : Fin n => decode (answers (start+mid+2)) (1+i.val)) := by
    funext i
    refine Fin.cases ?_ ?_ i
    · rfl
    · intro j
      simp [Nat.add_comm]
  change (QueryTest.affine 0 (n+1) (t.clearA pads-evaluate wires ml.point) 0
    (Fin.cons (t.clearB pads-evaluate q ml.point) 0)
    (Fin.cons (t.clearB pads-evaluate q ml.point) (fun i => -(e.residuals w) i))).Bad
      decode nonzero (answers (start+mid+2))
  simp only [QueryTest.Bad, Nat.zero_add, hcons]
  exact hcover

theorem layer_head_update_after (decode : C → ℕ → F)
    (nonzero : C → Linear.TerminalSampling.Nonzero F)
    {out mid input a : ℕ} (body : LfzkV2.Native.CircuitLayer (Cube out) (Cube mid) (Fin a) F)
    (rest : Layered.Circuit F mid input)
    (plan : Layered.Replay.PadPlan (Pad := Pad) (.layer a body rest))
    (payload : Layered.Replay.Payload (.layer a body rest))
    (answers : ℕ → C) (start offset query : ℕ) (answer : C)
    (hquery : start+mid+2 < query) :
    (readFrom decode nonzero (.layer a body rest) plan payload
      (Function.update answers query answer) start offset).1 =
    (readFrom decode nonzero (.layer a body rest) plan payload answers start offset).1 := by
  have hb : Function.update answers query answer start = answers start :=
    Function.update_of_ne (by omega) _ _
  have hp : (fun j : Fin mid => decode (Function.update answers query answer
      (start+1+j.val)) 0) = (fun j : Fin mid => decode (answers (start+1+j.val)) 0) := by
    funext j
    rw [Function.update_of_ne (by have := j.isLt; omega)]
  have hs : Function.update answers query answer (start+1+mid) =
      answers (start+1+mid) := Function.update_of_ne (by omega) _ _
  have ha : Function.update answers query answer (start+mid+2) =
      answers (start+mid+2) := Function.update_of_ne (by omega) _ _
  dsimp only [readFrom]
  rw [hb, hp, hs, ha]

/-- Construct the local test from the actual parser and retained circuit
reduction. The test itself is fixed while the current answer is varied. -/
theorem local_test_cover (decode : C → ℕ → F)
    (nonzero : C → Linear.TerminalSampling.Nonzero F)
    {out input : ℕ} (circuit : Layered.Circuit F out input)
    (plan : Layered.Replay.PadPlan (Pad := Pad) circuit) (payload : Layered.Replay.Payload circuit)
    (answers : ℕ → C) (start offset : ℕ) (w : Cube input → F)
    (weights : Cube out → F) (pads : Pad → F) (claim : F) (query capacity : ℕ)
    (hcoalesced : Coalesced circuit) (hfits : Fits capacity circuit offset) :
    ∃ test : QueryTest F, test.Valid capacity ∧ ∀ answer,
      BadFrom decode nonzero circuit plan payload (Function.update answers query answer)
        start offset w weights pads claim query → test.Bad decode nonzero answer := by
  induction circuit generalizing start offset claim query with
  | input =>
      refine ⟨.empty, trivial, ?_⟩
      rintro answer ⟨role,_,_⟩
      exact Fin.elim0 role
  | @entry out next input n e rest ih =>
      by_cases hquery : query = start
      · subst query
        cases rest with
        | input =>
            refine ⟨.affine offset n (dot weights (e.previous w)) claim
              (e.residuals w) (e.residuals w), hfits.1, ?_⟩
            rintro answer ⟨role,hindex,hbad⟩
            cases role with
            | inl i =>
                apply Or.inl
                simpa only [dataAtRole, sampleAtRole, LayerRole.kind, Data.Bad,
                  ChallengeBlocks.Data.Bad, Layered.Circuit.eval, Function.update_self] using hbad
            | inr role => exact Fin.elim0 role
        | entry m e' rest => exact hcoalesced.1.elim
        | layer a body rest =>
            refine ⟨.affine offset (n+a)
              (dot weights (e.previous (body.outputs (rest.eval w)))) claim
              (Fin.append (e.residuals (body.outputs (rest.eval w))) 0)
              (Fin.append (e.residuals (body.outputs (rest.eval w))) (body.residuals (rest.eval w))),
              ?_, ?_⟩
            · have hf := hfits.2.1
              dsimp only [QueryTest.Valid]
              omega
            · intro answer hbad
              have hcover := entry_layer_at_start decode nonzero e body rest plan payload
                (Function.update answers start answer) start offset w weights pads claim hbad
              simpa only [Function.update_self] using hcover
      · let nextWeights := e.weights weights (fun i => decode (answers start) (offset+i.val))
        obtain ⟨test,htest,hcover⟩ := ih plan payload start (offset+n) w nextWeights claim query
          hcoalesced.2 hfits.2
        refine ⟨test,htest,?_⟩
        rintro answer ⟨role,hindex,hbad⟩
        cases role with
        | inl i => exact (hquery hindex.symm).elim
        | inr role =>
            apply hcover answer
            refine ⟨role,hindex,?_⟩
            simpa only [dataAtRole, LayerRole.kind, sampleAtRole,
              Function.update_of_ne (Ne.symm hquery), nextWeights] using hbad
  | @layer out mid input a body rest ih =>
      by_cases hbefore : query < start
      · refine ⟨.empty,trivial,?_⟩
        intro answer hbad
        exact (Nat.not_le_of_gt hbefore (badFrom_ge _ _ _ _ _ _ _ _ _ _ _ _ _ hbad)).elim
      · have hge : start ≤ query := Nat.le_of_not_gt hbefore
        by_cases hstart : query = start
        · subst query
          refine ⟨.affine offset a (dot weights (body.outputs (rest.eval w))) claim
            (body.residuals (rest.eval w)) (body.residuals (rest.eval w)), hfits.1, ?_⟩
          rintro answer ⟨role,hindex,hbad⟩
          rcases role with i | i | i | i | role
          · apply Or.inl
            simpa only [dataAtRole, sampleAtRole, LayerRole.kind, Data.Bad,
              ChallengeBlocks.Data.Bad, Function.update_self] using hbad
          · simp only [queryIndex] at hindex
            omega
          · simp only [queryIndex] at hindex
            omega
          · simp only [queryIndex] at hindex
            omega
          · have hi := queryIndex_ge rest role
              (if hasLayers rest then start+mid+3 else start+mid+2)
            simp only [queryIndex] at hindex
            split_ifs at hindex hi <;> omega
        · by_cases hround : query < start+1+mid
          · let i : Fin mid := ⟨query-start-1, by omega⟩
            have hi : query = start+1+i.val := by dsimp [i]; omega
            let data := dataAtRole decode nonzero (.layer a body rest) plan payload
              answers start offset w weights pads claim (.inr (.inl i))
            refine ⟨.round data, ⟨hfits.2.1, ?_⟩, ?_⟩
            · exact RoundReplay.dataAt_valid _ _ _ _ _ _
            · rintro answer ⟨role,hindex,hbad⟩
              rcases role with j | j | j | j | role
              · simp only [queryIndex] at hindex
                exact (hstart hindex.symm).elim
              · have hji : j = i := by
                  apply Fin.ext
                  simp only [queryIndex] at hindex
                  omega
                subst j
                rw [hi] at hbad
                rw [layer_round_data_update] at hbad
                simpa only [sampleAtRole, LayerRole.kind, Data.Bad, ChallengeBlocks.Data.Bad,
                  Function.update_self, QueryTest.Bad, data] using hbad
              · simp only [queryIndex] at hindex
                omega
              · simp only [queryIndex] at hindex
                omega
              · have hj := queryIndex_ge rest role
                  (if hasLayers rest then start+mid+3 else start+mid+2)
                simp only [queryIndex] at hindex
                split_ifs at hindex hj <;> omega
          · by_cases hterminal : query = start+1+mid
            · subst query
              let data := dataAtRole decode nonzero (.layer a body rest) plan payload
                answers start offset w weights pads claim (.inr (.inr (.inl 0)))
              refine ⟨.terminal data,trivial,?_⟩
              rintro answer ⟨role,hindex,hbad⟩
              rcases role with j | j | j | j | role
              · simp only [queryIndex] at hindex
                omega
              · simp only [queryIndex] at hindex
                have := j.isLt
                omega
              · have hj : j = 0 := Subsingleton.elim _ _
                subst j
                rw [layer_terminal_data_update] at hbad
                simpa only [sampleAtRole, LayerRole.kind, Data.Bad, Function.update_self,
                  QueryTest.Bad, data] using hbad
              · simp only [queryIndex] at hindex
                omega
              · have hj := queryIndex_ge rest role
                  (if hasLayers rest then start+mid+3 else start+mid+2)
                simp only [queryIndex] at hindex
                split_ifs at hindex hj <;> omega
            · by_cases hcombine : query = start+mid+2
              · subst query
                by_cases hrest : hasLayers rest = true
                · let data := dataAtRole decode nonzero (.layer a body rest) plan payload
                    answers start offset w weights pads claim (.inr (.inr (.inr (.inl 0))))
                  refine ⟨.combine data,hfits.2.1,?_⟩
                  rintro answer ⟨role,hindex,hbad⟩
                  rcases role with j | j | j | j | role
                  · simp only [queryIndex] at hindex
                    omega
                  · simp only [queryIndex] at hindex
                    have := j.isLt
                    omega
                  · simp only [queryIndex] at hindex
                    omega
                  · have hj : j = 0 := Subsingleton.elim _ _
                    subst j
                    rw [layer_combine_data_update] at hbad
                    simpa only [sampleAtRole, LayerRole.kind, Data.Bad, ChallengeBlocks.Data.Bad,
                      Function.update_self, QueryTest.Bad, data] using hbad
                  · have hj := queryIndex_ge rest role (start+mid+3)
                    simp only [queryIndex, hrest, ↓reduceIte] at hindex
                    omega
                · have hrfalse : hasLayers rest = false := Bool.eq_false_iff.mpr hrest
                  cases rest with
                  | input =>
                      let data := dataAtRole decode nonzero (.layer a body .input) plan payload
                        answers start offset w weights pads claim (.inr (.inr (.inr (.inl 0))))
                      refine ⟨.combine data,hfits.2.1,?_⟩
                      rintro answer ⟨role,hindex,hbad⟩
                      rcases role with j | j | j | j | role
                      · simp only [queryIndex] at hindex
                        omega
                      · simp only [queryIndex] at hindex
                        have := j.isLt
                        omega
                      · simp only [queryIndex] at hindex
                        omega
                      · have hj : j = 0 := Subsingleton.elim _ _
                        subst j
                        rw [layer_combine_data_update] at hbad
                        simpa only [sampleAtRole, LayerRole.kind, Data.Bad, ChallengeBlocks.Data.Bad,
                          Function.update_self, QueryTest.Bad, data] using hbad
                      · exact Fin.elim0 role
                  | layer => simp [hasLayers] at hrfalse
                  | entry n e tail =>
                      cases tail with
                      | entry => exact hcoalesced.1.elim
                      | layer => simp [hasLayers] at hrfalse
                      | input =>
                          let data := dataAtRole decode nonzero (.layer a body (.entry n e .input))
                            plan payload answers start offset w weights pads claim
                              (.inr (.inr (.inr (.inl 0))))
                          refine ⟨.affine 0 (n+1) (data.claimA-data.trueA) 0
                            (Fin.cons (data.claimB-data.trueB) 0)
                            (Fin.cons (data.claimB-data.trueB) (fun i => -(e.residuals w) i)), ?_, ?_⟩
                          · have hf := hfits.2.2.1
                            simp only [hasLayers, Bool.false_eq_true, ↓reduceIte] at hf
                            dsimp only [QueryTest.Valid]
                            omega
                          · intro answer hbad
                            have hc := layer_final_entry_at_combine decode nonzero body e plan payload
                              (Function.update answers (start+mid+2) answer) start offset w weights pads claim hbad
                            dsimp only at hc
                            rw [layer_combine_data_update] at hc
                            simpa only [Function.update_self, data] using hc
              · have hafter : start+mid+2 < query := by omega
                by_cases hrest : hasLayers rest = true
                · let ml := (readFrom decode nonzero (.layer a body rest) plan payload answers start offset).1
                  let nextWeights := SumcheckV2.nextWeights (body.effectiveQuadratic weights ml.beta)
                    (monomialWeights ml.point) ml.alpha
                  let nextClaim := (ml.transcript body weights).nextValue pads
                  obtain ⟨test,htest,hcover⟩ := ih plan.2 payload.2 (start+mid+3) 0 w nextWeights
                    nextClaim query hcoalesced (by simpa only [hrest, ↓reduceIte] using hfits.2.2)
                  refine ⟨test,htest,?_⟩
                  rintro answer ⟨role,hindex,hbad⟩
                  rcases role with j | j | j | j | role
                  · simp only [queryIndex] at hindex
                    omega
                  · simp only [queryIndex] at hindex
                    have := j.isLt
                    omega
                  · simp only [queryIndex] at hindex
                    omega
                  · simp only [queryIndex] at hindex
                    omega
                  · apply hcover answer
                    refine ⟨role,?_,?_⟩
                    · simpa only [queryIndex, hrest, ↓reduceIte] using hindex
                    · dsimp only [dataAtRole, LayerRole.kind, sampleAtRole] at hbad
                      rw [layer_head_update_after decode nonzero body rest plan payload answers
                        start offset query answer hafter] at hbad
                      simpa only [hrest, ↓reduceIte, ml, nextWeights, nextClaim] using hbad
                · refine ⟨.empty,trivial,?_⟩
                  intro answer hbad
                  obtain ⟨role,hindex,_⟩ := hbad
                  have hi := queryIndex_lt (.layer a body rest) role start
                  have hf : hasLayers rest = false := Bool.eq_false_iff.mpr hrest
                  simp only [slots, hf, Bool.false_eq_true, ↓reduceIte] at hi
                  omega

theorem badFrom_card_mul_le [Fintype F] [DecidableEq F] [Fintype C]
    {capacity : ℕ} {decode : C → ℕ → F}
    {nonzero : C → Linear.TerminalSampling.Nonzero F}
    (decoder : Decoder capacity decode nonzero)
    {out input : ℕ} (circuit : Layered.Circuit F out input)
    (plan : Layered.Replay.PadPlan (Pad := Pad) circuit) (payload : Layered.Replay.Payload circuit)
    (answers : ℕ → C) (start offset : ℕ) (w : Cube input → F)
    (weights : Cube out → F) (pads : Pad → F) (claim : F) (query : ℕ)
    (hcoalesced : Coalesced circuit) (hfits : Fits capacity circuit offset) :
    (univ.filter fun answer => BadFrom decode nonzero circuit plan payload
      (Function.update answers query answer) start offset w weights pads claim query).card *
        (Fintype.card F-1) ≤ 2 * Fintype.card C := by
  obtain ⟨test,hvalid,hcover⟩ := local_test_cover decode nonzero circuit plan payload answers
    start offset w weights pads claim query capacity hcoalesced hfits
  have hsub : (univ.filter fun answer => BadFrom decode nonzero circuit plan payload
      (Function.update answers query answer) start offset w weights pads claim query) ⊆
      univ.filter (test.Bad decode nonzero) := by
    intro answer hanswer
    exact mem_filter.mpr ⟨mem_univ _, hcover answer (mem_filter.mp hanswer).2⟩
  exact (Nat.mul_le_mul_right _ (card_le_card hsub)).trans
    (test.bad_card_mul_le decoder hvalid)

/-- This is the actual whole-query local bound used by the oracle charging
step. It is derived from circuit structure, not a caller-supplied error budget. -/
theorem badAt_card_mul_le [Fintype F] [DecidableEq F] [Fintype C]
    {capacity : ℕ} {decode : C → ℕ → F}
    {nonzero : C → Linear.TerminalSampling.Nonzero F}
    (decoder : Decoder capacity decode nonzero)
    {out input : ℕ} (circuit : Layered.Circuit F out input)
    (plan : Layered.Replay.PadPlan (Pad := Pad) circuit) (payload : Layered.Replay.Payload circuit)
    (answers : ℕ → C) (w : Cube input → F) (pads : Pad → F) (query : ℕ)
    (hcoalesced : Coalesced circuit) (hfits : Fits capacity circuit 0) :
    (univ.filter fun answer => BadAt decode nonzero circuit plan payload
      (Function.update answers query answer) w pads query).card * (Fintype.card F-1) ≤
        2 * Fintype.card C := by
  exact badFrom_card_mul_le decoder circuit plan payload answers 0 0 w 0 pads 0 query
    hcoalesced hfits

omit [Field F] in
theorem completeAnswers_update {query : ℕ} (past : Fin query → C) (answer fallback : C) :
    completeAnswers past answer fallback =
      Function.update (completeAnswers past fallback fallback) query answer := by
  funext j
  by_cases hj : j = query
  · subst j
    simp [completeAnswers]
  · rw [Function.update_of_ne hj]
    simp only [completeAnswers]
    by_cases hlt : j < query <;> simp only [hlt, hj, ↓reduceDIte, ↓reduceIte]

theorem badAt_prefix_card_mul_le [Fintype F] [DecidableEq F] [Fintype C]
    {capacity : ℕ} {decode : C → ℕ → F}
    {nonzero : C → Linear.TerminalSampling.Nonzero F}
    (decoder : Decoder capacity decode nonzero)
    {out input : ℕ} (circuit : Layered.Circuit F out input)
    (plan : Layered.Replay.PadPlan (Pad := Pad) circuit) (payload : Layered.Replay.Payload circuit)
    (w : Cube input → F) (pads : Pad → F) (query : ℕ) (past : Fin query → C) (fallback : C)
    (hcoalesced : Coalesced circuit) (hfits : Fits capacity circuit 0) :
    (univ.filter fun answer => BadAt decode nonzero circuit plan payload
      (completeAnswers past answer fallback) w pads query).card * (Fintype.card F-1) ≤
        2 * Fintype.card C := by
  simpa only [← completeAnswers_update] using
    badAt_card_mul_le decoder circuit plan payload (completeAnswers past fallback fallback)
      w pads query hcoalesced hfits

end LfzkV2.Current.FrontendReplay
