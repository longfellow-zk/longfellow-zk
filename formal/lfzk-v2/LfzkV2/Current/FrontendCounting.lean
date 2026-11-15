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
public capacity. A layer's tail starts after its combine coefficient. -/
def Fits (capacity : ℕ) : {out input : ℕ} → Layered.Circuit F out input → ℕ → Prop
  | _, _, .input, _ => True
  | _, _, .entry n _ rest, offset =>
      offset+n ≤ capacity ∧ Fits capacity rest (offset+n)
  | _, _, .layer a _ rest, offset =>
      offset+a ≤ capacity ∧ 1 ≤ capacity ∧ Fits capacity rest 1

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

/-- One affine hyperplane, or no test at all: at most one value in `|F|`. -/
def QueryTest.Single : QueryTest F → Prop
  | .empty => True
  | .affine _ _ _ _ left right => left = right
  | _ => False

theorem QueryTest.bad_card_mul_le_single [Fintype F] [DecidableEq F] [Fintype C]
    {capacity : ℕ} {decode : C → ℕ → F}
    {nonzero : C → Linear.TerminalSampling.Nonzero F}
    (decoder : Decoder capacity decode nonzero) (test : QueryTest F)
    (hvalid : test.Valid capacity) (hsingle : test.Single) :
    (univ.filter (test.Bad decode nonzero)).card * Fintype.card F ≤ Fintype.card C := by
  cases test with
  | empty => simp [QueryTest.Bad]
  | affine offset dimension incoming claim left right =>
      change left = right at hsingle
      subst hsingle
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
      have hraw := balanced.bad_card_mul_le
        (fun beta => AssertionBad incoming claim beta left) 1 (Fintype.card F)
        (by simpa only [one_mul] using EntryChallenges.block_bad_card_mul_le incoming claim left)
      simpa only [QueryTest.Bad, or_self, balanced, hsampler, one_mul] using hraw
  | round => exact hsingle.elim
  | combine => exact hsingle.elim
  | terminal => exact hsingle.elim

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

omit [Field F] in
theorem fin_zero_fun_eq (f g : Fin 0 → F) : f = g := funext fun i => Fin.elim0 i

theorem assertionBad_zero {n : ℕ} (incoming claim : F) (beta : Fin n → F) :
    ¬ AssertionBad incoming claim beta 0 := by
  rintro ⟨i, _, hi, _⟩
  exact hi rfl

/-- An entry and the layer it enters are one affine test of their common
coefficient block. The entry is reported alone only when the layer passes. -/
theorem entry_head_cover {n m : ℕ} (incoming claim : F)
    (rho entries : Fin n → F) (beta assertions : Fin m → F)
    (h : AssertionBad incoming claim rho (if ∀ i, assertions i = 0 then entries else 0) ∨
      AssertionBad (incoming + dot rho entries) claim beta assertions) :
    AssertionBad incoming claim (Fin.append rho beta) (Fin.append entries assertions) := by
  rcases h with he | ha
  · by_cases hz : ∀ i, assertions i = 0
    · simp only [hz, implies_true, ↓reduceIte] at he
      have hzero : assertions = 0 := funext hz
      subst hzero
      have heq := ChallengeBlocks.assertion_bad_equation _ _ _ _ he
      obtain ⟨i, _, hi, _⟩ := he
      apply assertion_reduction
      · exact ⟨i.castAdd m, by simpa using hi⟩
      · rw [EntryChallenges.dot_append]
        simp only [dot, Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
        simp only [dot] at heq
        linear_combination -heq
    · simp only [hz, ↓reduceIte] at he
      exact (assertionBad_zero _ _ _ he).elim
  · have heq := ChallengeBlocks.assertion_bad_equation _ _ _ _ ha
    obtain ⟨i, _, hi, _⟩ := ha
    apply assertion_reduction
    · exact ⟨i.natAdd n, by simpa using hi⟩
    · rw [EntryChallenges.dot_append]
      linear_combination -heq

/-- Every test located at a circuit's opening answer is one affine test of
that answer's whole coefficient block: the entry and the assertions of the
layer it enters. -/
theorem head_cover (decode : C → ℕ → F)
    (nonzero : C → Linear.TerminalSampling.Nonzero F)
    {out input : ℕ} (circuit : Layered.Circuit F out input)
    (plan : Layered.Replay.PadPlan (Pad := Pad) circuit) (payload : Layered.Replay.Payload circuit)
    (answers : ℕ → C) (start offset : ℕ) (w : Cube input → F)
    (weights : Cube out → F) (pads : Pad → F) (claim : F) (hcoalesced : Coalesced circuit)
    (h : BadFrom decode nonzero circuit plan payload answers start offset w weights pads claim start) :
    AssertionBad (dot weights (circuit.eval w)) claim
      (fun i : Fin circuit.headWidth => decode (answers start) (offset+i.val))
      (circuit.headResiduals w) := by
  obtain ⟨role,hindex,hbad⟩ := h
  cases circuit with
  | input => exact Fin.elim0 role
  | entry n e rest =>
      cases rest with
      | input =>
          cases role with
          | inl i =>
              have he : AssertionBad (dot weights (e.previous w)) claim
                  (fun i : Fin n => decode (answers start) (offset+i.val)) (e.residuals w) := by
                simpa only [dataAtRole, sampleAtRole, LayerRole.kind, Data.Bad,
                  ChallengeBlocks.Data.Bad, ChallengeBlocks.Kind.dimension, Layered.Circuit.eval,
                  Layered.Circuit.entryResiduals, Layered.Circuit.layerWidth,
                  Layered.Circuit.layerResiduals, IsEmpty.forall_iff, implies_true,
                  ↓reduceIte] using hbad
              have hc := entry_head_cover (m := 0) _ _ _ _ (fun i : Fin 0 => decode (answers start) (offset+n+i.val))
                (Layered.Circuit.layerResiduals (.input (F := F) (n := input)) w)
                (Or.inl (by simpa only [IsEmpty.forall_iff, implies_true, ↓reduceIte] using he))
              simpa only [Layered.Circuit.eval, Layered.Circuit.headResiduals, Layered.Circuit.headWidth,
                Layered.Circuit.layerWidth, append_decode] using hc
          | inr role => exact Fin.elim0 role
      | entry => exact hcoalesced.1.elim
      | @layer _ mid _ a body rest =>
          have hc : AssertionBad (dot weights (e.previous (body.outputs (rest.eval w)))) claim
              (Fin.append (fun i : Fin n => decode (answers start) (offset+i.val))
                (fun i : Fin a => decode (answers start) (offset+n+i.val)))
              (Fin.append (e.residuals (body.outputs (rest.eval w))) (body.residuals (rest.eval w))) := by
            apply entry_head_cover
            rcases role with i | i | i | i | i | role
            · apply Or.inl
              simpa only [dataAtRole, sampleAtRole, LayerRole.kind, Data.Bad,
                ChallengeBlocks.Data.Bad, ChallengeBlocks.Kind.dimension, Layered.Circuit.eval,
                Layered.Circuit.entryResiduals, Layered.Circuit.layerWidth,
                Layered.Circuit.layerResiduals] using hbad
            · apply Or.inr
              simpa only [dataAtRole, sampleAtRole, LayerRole.kind, Data.Bad,
                ChallengeBlocks.Data.Bad, ChallengeBlocks.Kind.dimension, Layered.Circuit.eval,
                e.dot_weights] using hbad
            · simp only [queryIndex] at hindex; omega
            · simp only [queryIndex] at hindex; omega
            · simp only [queryIndex] at hindex; omega
            · have hge := queryIndex_ge rest role (start+mid+2)
              simp only [queryIndex] at hindex
              omega
          simpa only [Layered.Circuit.eval, Layered.Circuit.headResiduals, Layered.Circuit.headWidth,
            Layered.Circuit.layerWidth, Layered.Circuit.layerResiduals, append_decode] using hc
  | @layer _ mid _ a body rest =>
      rcases role with i | i | i | i | role
      · simpa only [dataAtRole, sampleAtRole, LayerRole.kind, Data.Bad, ChallengeBlocks.Kind.dimension,
          ChallengeBlocks.Data.Bad, Layered.Circuit.eval, Layered.Circuit.headWidth,
          Layered.Circuit.headResiduals] using hbad
      · simp only [queryIndex] at hindex; omega
      · simp only [queryIndex] at hindex; omega
      · simp only [queryIndex] at hindex; omega
      · have hge := queryIndex_ge rest role (start+mid+2)
        simp only [queryIndex] at hindex
        omega

/-- The combine answer's test: alpha, then the next weights. The reduction
reports the combine failure only when every check that follows it in this
answer passes, so both are one affine cancellation. -/
noncomputable def combineTest {out mid input a : ℕ}
    (body : LfzkV2.Native.CircuitLayer (Cube out) (Cube mid) (Fin a) F)
    (rest : Layered.Circuit F mid input) (ml : Linear.LayerMessages Pad F mid a)
    (w : Cube input → F) (weights : Cube out → F) (pads : Pad → F) : QueryTest F :=
  let t := ml.transcript body weights
  let wires := rest.eval w
  let q := bindRightAffine (body.effectiveQuadratic weights ml.beta)
    (body.effectiveLinear weights ml.beta) wires
  let v : Fin (rest.headWidth+1) → F :=
    Fin.cons (t.clearB pads - evaluate q ml.point) (fun i => -(rest.headResiduals w i))
  .affine 0 (rest.headWidth+1) (t.clearA pads - evaluate wires ml.point) 0 v v

theorem layer_combine_cover (decode : C → ℕ → F)
    (nonzero : C → Linear.TerminalSampling.Nonzero F)
    {out mid input a : ℕ}
    (body : LfzkV2.Native.CircuitLayer (Cube out) (Cube mid) (Fin a) F)
    (rest : Layered.Circuit F mid input)
    (plan : Layered.Replay.PadPlan (Pad := Pad) (.layer a body rest))
    (payload : Layered.Replay.Payload (.layer a body rest))
    (answers : ℕ → C) (start offset : ℕ) (w : Cube input → F)
    (weights : Cube out → F) (pads : Pad → F) (claim : F) (hcoalesced : Coalesced rest)
    (h : BadFrom decode nonzero (.layer a body rest) plan payload
      answers start offset w weights pads claim (start+mid+2)) :
    (combineTest body rest (readFrom decode nonzero (.layer a body rest) plan payload
      answers start offset).1 w weights pads).Bad decode nonzero (answers (start+mid+2)) := by
  let ml := (readFrom decode nonzero (.layer a body rest) plan payload answers start offset).1
  let wires := rest.eval w
  let Q := body.effectiveQuadratic weights ml.beta
  let L := body.effectiveLinear weights ml.beta
  let q := bindRightAffine Q L wires
  let t := ml.transcript body weights
  let coefficients := fun i : Fin rest.headWidth => decode (answers (start+mid+2)) (1+i.val)
  have hcover : AssertionBad (t.clearA pads - evaluate wires ml.point) 0
      (Fin.cons ml.alpha coefficients)
      (Fin.cons (t.clearB pads - evaluate q ml.point) (fun i => -rest.headResiduals w i)) := by
    obtain ⟨role,hindex,hbad⟩ := h
    rcases role with i | i | i | i | role
    · simp only [queryIndex] at hindex; omega
    · simp only [queryIndex] at hindex; have := i.isLt; omega
    · simp only [queryIndex] at hindex; omega
    · have hc : (∀ i, rest.headResiduals w i = 0) ∧
          BadCombineEvent (evaluate wires ml.point) (evaluate q ml.point)
            (t.clearA pads) (t.clearB pads) ml.alpha := by
        simp only [dataAtRole, sampleAtRole, LayerRole.kind, Data.Bad, ChallengeBlocks.Data.Bad,
          Layered.Replay.gatedCombine_bad] at hbad
        exact hbad
      have hz : rest.headResiduals w = 0 := funext hc.1
      have hf : t.clearA pads ≠ evaluate wires ml.point ∨ t.clearB pads ≠ evaluate q ml.point ∨
          ∃ i, rest.headResiduals w i ≠ 0 := by
        rcases hc.2.1 with hA | hB
        · exact Or.inl hA
        · exact Or.inr (Or.inl hB)
      apply EntryChallenges.combine_entry_reduction _ _ _ _ (evaluate L ml.point) _ _ _ hf
      rw [hz]
      simp only [dot, Pi.zero_apply, mul_zero, Finset.sum_const_zero, add_zero]
      linear_combination hc.2.2
    · have hr : BadFrom decode nonzero rest plan.2 payload.2 answers (start+mid+2) 1 w
          (nextWeights Q (monomialWeights ml.point) ml.alpha) pads (t.nextValue pads) (start+mid+2) :=
        ⟨role, by simpa only [queryIndex] using hindex, by
          simpa only [dataAtRole, sampleAtRole, LayerRole.kind] using hbad⟩
      have hhead := head_cover decode nonzero rest plan.2 payload.2 answers (start+mid+2) 1 w
        _ pads _ hcoalesced hr
      have hdot := affine_nextWeights_correct Q L (monomialWeights ml.point) wires ml.alpha
      rw [hdot] at hhead
      have heq := ChallengeBlocks.assertion_bad_equation _ _ _ _ hhead
      obtain ⟨i, _, hi, _⟩ := hhead
      apply EntryChallenges.combine_entry_reduction _ _ _ _ (evaluate L ml.point) _ _ _
        (Or.inr (Or.inr ⟨i,hi⟩))
      have htalpha : t.alpha = ml.alpha := rfl
      have htlinear : t.linear = evaluate L ml.point := rfl
      simp only [← evaluate_eq_dot, Linear.LayerTranscript.nextValue, htalpha, htlinear] at heq
      linear_combination -heq
  have hcons : (fun i : Fin (rest.headWidth+1) => decode (answers (start+mid+2)) i.val) =
      Fin.cons ml.alpha coefficients := by
    funext i
    refine Fin.cases ?_ ?_ i
    · rfl
    · intro j
      simp [coefficients, Nat.add_comm]
  change (QueryTest.affine 0 (rest.headWidth+1) (t.clearA pads - evaluate wires ml.point) 0
    (Fin.cons (t.clearB pads - evaluate q ml.point) (fun i => -(rest.headResiduals w i)))
    (Fin.cons (t.clearB pads - evaluate q ml.point) (fun i => -(rest.headResiduals w i)))).Bad
      decode nonzero (answers (start+mid+2))
  simp only [QueryTest.Bad, Nat.zero_add, hcons, or_self]
  exact hcover

theorem layer_messages_update_combine (decode : C → ℕ → F)
    (nonzero : C → Linear.TerminalSampling.Nonzero F)
    {out mid input a : ℕ} (body : LfzkV2.Native.CircuitLayer (Cube out) (Cube mid) (Fin a) F)
    (rest : Layered.Circuit F mid input)
    (plan : Layered.Replay.PadPlan (Pad := Pad) (.layer a body rest))
    (payload : Layered.Replay.Payload (.layer a body rest))
    (answers : ℕ → C) (start offset : ℕ) (answer : C) :
    (readFrom decode nonzero (.layer a body rest) plan payload
      (Function.update answers (start+mid+2) answer) start offset).1 =
    { (readFrom decode nonzero (.layer a body rest) plan payload answers start offset).1 with
      alpha := decode answer 0 } := by
  have hb : Function.update answers (start+mid+2) answer start = answers start :=
    Function.update_of_ne (by omega) _ _
  have hp : (fun j : Fin mid => decode (Function.update answers (start+mid+2) answer
      (start+1+j.val)) 0) = (fun j : Fin mid => decode (answers (start+1+j.val)) 0) := by
    funext j
    rw [Function.update_of_ne (by have := j.isLt; omega)]
  have hs : Function.update answers (start+mid+2) answer (start+1+mid) =
      answers (start+1+mid) := Function.update_of_ne (by omega) _ _
  dsimp only [readFrom]
  rw [hb, hp, hs, Function.update_self]

omit [Field F] in
theorem fits_head (capacity : ℕ) {out input : ℕ} (circuit : Layered.Circuit F out input)
    (offset : ℕ) (hcoalesced : Coalesced circuit) (hfits : Fits capacity circuit offset)
    (hoffset : offset ≤ capacity) : offset + circuit.headWidth ≤ capacity := by
  cases circuit with
  | input => simpa [Layered.Circuit.headWidth] using hoffset
  | entry n e rest =>
      cases rest with
      | input => simpa [Layered.Circuit.headWidth, Layered.Circuit.layerWidth] using hfits.1
      | entry => exact hcoalesced.1.elim
      | layer a body rest =>
          have h := hfits.2.1
          simp only [Layered.Circuit.headWidth, Layered.Circuit.layerWidth]
          omega
  | layer a body rest => exact hfits.1

/-- Construct the local test from the actual parser and retained circuit
reduction. The test itself is fixed while the current answer is varied. -/
theorem local_test_cover (decode : C → ℕ → F)
    (nonzero : C → Linear.TerminalSampling.Nonzero F)
    {out input : ℕ} (circuit : Layered.Circuit F out input)
    (plan : Layered.Replay.PadPlan (Pad := Pad) circuit) (payload : Layered.Replay.Payload circuit)
    (answers : ℕ → C) (start offset : ℕ) (w : Cube input → F)
    (weights : Cube out → F) (pads : Pad → F) (claim : F) (query capacity : ℕ)
    (hcoalesced : Coalesced circuit) (hfits : Fits capacity circuit offset)
    (hoffset : offset ≤ capacity) :
    ∃ test : QueryTest F, test.Valid capacity ∧
      (query+1 = start+slots circuit → test.Single) ∧ ∀ answer,
      BadFrom decode nonzero circuit plan payload (Function.update answers query answer)
        start offset w weights pads claim query → test.Bad decode nonzero answer := by
  induction circuit generalizing start offset claim query with
  | input =>
      refine ⟨.empty, trivial, fun _ => trivial, ?_⟩
      rintro answer ⟨role,_,_⟩
      exact Fin.elim0 role
  | @entry out next input n e rest ih =>
      by_cases hquery : query = start
      · subst query
        refine ⟨.affine offset (Layered.Circuit.headWidth (.entry n e rest))
          (dot weights (Layered.Circuit.eval (.entry n e rest) w)) claim
          ((Layered.Circuit.entry n e rest).headResiduals w)
          ((Layered.Circuit.entry n e rest).headResiduals w),
          fits_head capacity _ offset hcoalesced hfits hoffset, fun _ => rfl, ?_⟩
        intro answer hbad
        have hc := head_cover decode nonzero (.entry n e rest) plan payload
          (Function.update answers start answer) start offset w weights pads claim hcoalesced hbad
        simpa only [QueryTest.Bad, Function.update_self, or_self] using hc
      · let nextWeights := e.weights weights (fun i => decode (answers start) (offset+i.val))
        obtain ⟨test,htest,hsingle,hcover⟩ := ih plan payload start (offset+n) w nextWeights claim query
          hcoalesced.2 hfits.2 hfits.1
        refine ⟨test,htest,fun hlast => hsingle (by simpa only [slots] using hlast),?_⟩
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
      · refine ⟨.empty,trivial,fun _ => trivial,?_⟩
        intro answer hbad
        exact (Nat.not_le_of_gt hbefore (badFrom_ge _ _ _ _ _ _ _ _ _ _ _ _ _ hbad)).elim
      · have hge : start ≤ query := Nat.le_of_not_gt hbefore
        by_cases hstart : query = start
        · subst query
          refine ⟨.affine offset a (dot weights (body.outputs (rest.eval w))) claim
            (body.residuals (rest.eval w)) (body.residuals (rest.eval w)), hfits.1, fun _ => rfl, ?_⟩
          intro answer hbad
          have hc := head_cover decode nonzero (.layer a body rest) plan payload
            (Function.update answers start answer) start offset w weights pads claim hcoalesced hbad
          simpa only [QueryTest.Bad, Function.update_self, or_self, Layered.Circuit.eval,
            Layered.Circuit.headWidth, Layered.Circuit.headResiduals] using hc
        · by_cases hround : query < start+1+mid
          · let i : Fin mid := ⟨query-start-1, by omega⟩
            have hi : query = start+1+i.val := by dsimp [i]; omega
            let data := dataAtRole decode nonzero (.layer a body rest) plan payload
              answers start offset w weights pads claim (.inr (.inl i))
            refine ⟨.round data, ⟨hfits.2.1, ?_⟩, fun hlast => ?_, ?_⟩
            · exact RoundReplay.dataAt_valid _ _ _ _ _ _
            · have := slots_positive rest
              simp only [slots] at hlast
              omega
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
              · have hj := queryIndex_ge rest role (start+mid+2)
                simp only [queryIndex] at hindex
                omega
          · by_cases hterminal : query = start+1+mid
            · subst query
              let data := dataAtRole decode nonzero (.layer a body rest) plan payload
                answers start offset w weights pads claim (.inr (.inr (.inl 0)))
              refine ⟨.terminal data,trivial,fun hlast => ?_,?_⟩
              · have := slots_positive rest
                simp only [slots] at hlast
                omega
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
              · have hj := queryIndex_ge rest role (start+mid+2)
                simp only [queryIndex] at hindex
                omega
            · by_cases hcombine : query = start+mid+2
              · subst query
                let ml := (readFrom decode nonzero (.layer a body rest) plan payload answers start offset).1
                refine ⟨combineTest body rest ml w weights pads, ?_, fun _ => rfl, ?_⟩
                · have hh := fits_head capacity rest 1 hcoalesced hfits.2.2 hfits.2.1
                  dsimp only [combineTest, QueryTest.Valid]
                  omega
                · intro answer hbad
                  have hc := layer_combine_cover decode nonzero body rest plan payload
                    (Function.update answers (start+mid+2) answer) start offset w weights pads claim
                    hcoalesced hbad
                  rw [layer_messages_update_combine, Function.update_self] at hc
                  exact hc
              · have hafter : start+mid+2 < query := by omega
                let ml := (readFrom decode nonzero (.layer a body rest) plan payload answers start offset).1
                let nextWeights := SumcheckV2.nextWeights (body.effectiveQuadratic weights ml.beta)
                  (monomialWeights ml.point) ml.alpha
                let nextClaim := (ml.transcript body weights).nextValue pads
                obtain ⟨test,htest,hsingle,hcover⟩ := ih plan.2 payload.2 (start+mid+2) 1 w nextWeights
                  nextClaim query hcoalesced hfits.2.2 hfits.2.1
                refine ⟨test,htest,fun hlast => hsingle (by simp only [slots] at hlast; omega),?_⟩
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
                  · simpa only [queryIndex] using hindex
                  · dsimp only [dataAtRole, LayerRole.kind, sampleAtRole] at hbad
                    rw [layer_head_update_after decode nonzero body rest plan payload answers
                      start offset query answer hafter] at hbad
                    simpa only [ml, nextWeights, nextClaim] using hbad

theorem badFrom_card_mul_le [Fintype F] [DecidableEq F] [Fintype C]
    {capacity : ℕ} {decode : C → ℕ → F}
    {nonzero : C → Linear.TerminalSampling.Nonzero F}
    (decoder : Decoder capacity decode nonzero)
    {out input : ℕ} (circuit : Layered.Circuit F out input)
    (plan : Layered.Replay.PadPlan (Pad := Pad) circuit) (payload : Layered.Replay.Payload circuit)
    (answers : ℕ → C) (start offset : ℕ) (w : Cube input → F)
    (weights : Cube out → F) (pads : Pad → F) (claim : F) (query : ℕ)
    (hcoalesced : Coalesced circuit) (hfits : Fits capacity circuit offset)
    (hoffset : offset ≤ capacity) :
    (univ.filter fun answer => BadFrom decode nonzero circuit plan payload
      (Function.update answers query answer) start offset w weights pads claim query).card *
        (Fintype.card F-1) ≤ 2 * Fintype.card C ∧
    (query+1 = start+slots circuit →
      (univ.filter fun answer => BadFrom decode nonzero circuit plan payload
        (Function.update answers query answer) start offset w weights pads claim query).card *
          Fintype.card F ≤ Fintype.card C) := by
  obtain ⟨test,hvalid,hsingle,hcover⟩ := local_test_cover decode nonzero circuit plan payload answers
    start offset w weights pads claim query capacity hcoalesced hfits hoffset
  have hsub : (univ.filter fun answer => BadFrom decode nonzero circuit plan payload
      (Function.update answers query answer) start offset w weights pads claim query) ⊆
      univ.filter (test.Bad decode nonzero) := by
    intro answer hanswer
    exact mem_filter.mpr ⟨mem_univ _, hcover answer (mem_filter.mp hanswer).2⟩
  exact ⟨(Nat.mul_le_mul_right _ (card_le_card hsub)).trans (test.bad_card_mul_le decoder hvalid),
    fun hlast => (Nat.mul_le_mul_right _ (card_le_card hsub)).trans
      (test.bad_card_mul_le_single decoder hvalid (hsingle hlast))⟩

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
        2 * Fintype.card C :=
  (badFrom_card_mul_le decoder circuit plan payload answers 0 0 w 0 pads 0 query
    hcoalesced hfits (Nat.zero_le _)).1

/-- The frontend's last answer, its combine answer (or its opening answer
with no layers), is one affine test: at most one value in `|F|`. -/
theorem badAt_last_card_mul_le [Fintype F] [DecidableEq F] [Fintype C]
    {capacity : ℕ} {decode : C → ℕ → F}
    {nonzero : C → Linear.TerminalSampling.Nonzero F}
    (decoder : Decoder capacity decode nonzero)
    {out input : ℕ} (circuit : Layered.Circuit F out input)
    (plan : Layered.Replay.PadPlan (Pad := Pad) circuit) (payload : Layered.Replay.Payload circuit)
    (answers : ℕ → C) (w : Cube input → F) (pads : Pad → F) (query : ℕ)
    (hcoalesced : Coalesced circuit) (hfits : Fits capacity circuit 0)
    (hlast : query+1 = slots circuit) :
    (univ.filter fun answer => BadAt decode nonzero circuit plan payload
      (Function.update answers query answer) w pads query).card * Fintype.card F ≤
        Fintype.card C :=
  (badFrom_card_mul_le decoder circuit plan payload answers 0 0 w 0 pads 0 query
    hcoalesced hfits (Nat.zero_le _)).2 (by simpa using hlast)
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

theorem badAt_prefix_last_card_mul_le [Fintype F] [DecidableEq F] [Fintype C]
    {capacity : ℕ} {decode : C → ℕ → F}
    {nonzero : C → Linear.TerminalSampling.Nonzero F}
    (decoder : Decoder capacity decode nonzero)
    {out input : ℕ} (circuit : Layered.Circuit F out input)
    (plan : Layered.Replay.PadPlan (Pad := Pad) circuit) (payload : Layered.Replay.Payload circuit)
    (w : Cube input → F) (pads : Pad → F) (query : ℕ) (past : Fin query → C) (fallback : C)
    (hcoalesced : Coalesced circuit) (hfits : Fits capacity circuit 0)
    (hlast : query+1 = slots circuit) :
    (univ.filter fun answer => BadAt decode nonzero circuit plan payload
      (completeAnswers past answer fallback) w pads query).card * Fintype.card F ≤
        Fintype.card C := by
  simpa only [← completeAnswers_update] using
    badAt_last_card_mul_le decoder circuit plan payload (completeAnswers past fallback fallback)
      w pads query hcoalesced hfits hlast

end LfzkV2.Current.FrontendReplay
