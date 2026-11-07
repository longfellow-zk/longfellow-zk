import LfzkV2.Current.ZeroKnowledge.HonestTranscriptQueries

/-! Honest masked round and terminal messages as one causal oracle program.
The arithmetic is the existing numerical prover arithmetic. Query-tree
construction computes each message before reading its challenge, and its
output is identified with the existing stateful honest prover/replay. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.HonestTranscript
open Merkle.RandomOracle SumcheckV2
open scoped Classical

variable {F State Query Answer : Type} [Field F]
variable (queries : Queries F State Query Answer)

structure Rounds (F State : Type) (n : ℕ) where
  messages : Fin n → RoundPoly F
  point : Fin n → F
  state : State

def rounds : {n : ℕ} → (Cube n → F) → (Cube n → F) → State →
    (Fin n → RoundPoly F) → Tree Query Answer (Rounds F State n) n
  | 0,_,_,state,_ => .done ⟨Fin.elim0,Fin.elim0,state⟩
  | n+1,q,w,state,pads =>
      let message := mask (honestMessage q w) (pads 0)
      (queries.round state message).bind fun answer =>
        (rounds (fold q answer.1) (fold w answer.1) answer.2 (fun i : Fin n => pads i.succ)).map
          fun tail => ⟨Fin.cons message tail.messages,Fin.cons answer.1 tail.point,tail.state⟩

theorem rounds_output {n : ℕ} (q w : Cube n → F) (state : State)
    (pads : Fin n → RoundPoly F) (H : Query → Answer) :
    ((rounds queries q w state pads).run H).1 =
      let reader := (queries.reader H).toReader
      let messages := Frontend.realRounds reader q w state pads
      let replay := Frontend.readRounds reader state messages
      (⟨messages,replay.1,replay.2⟩ : Rounds F State n) := by
  induction n generalizing state with
  | zero => rfl
  | succ n ih =>
      simp only [rounds,Tree.run_bind,Tree.run_map]
      rw [ih]
      rfl

structure Layer (F State : Type) [Field F] (n : ℕ) where
  payload : Frontend.LayerPayload F n
  read : Frontend.LayerRead F State n

def layer {n : ℕ} (q w : Cube n → F) (state : State) (pads : Frontend.LayerTape F n) :
    Tree Query Answer (Layer F State n) (2+n) :=
  (rounds queries q w state pads.1).bind fun round =>
    let A := evaluate w round.point
    let B := evaluate q round.point
    let cross := A*pads.2.2.1+B*pads.2.1-pads.2.2.2
    (queries.terminal round.state cross).bind fun terminal =>
      let factors := (A+terminal.1.val*pads.2.1,B+terminal.1.val*pads.2.2.1)
      (queries.combine terminal.2 factors).map fun combine =>
        ⟨⟨round.messages,cross,factors.1,factors.2⟩,
          ⟨round.point,terminal.1,combine.1,combine.2⟩⟩

/-- This normal form exposes the same cross message before its scale and
both masked factors before alpha. It introduces no extra prover messages. -/
theorem realLayer_eq {n : ℕ} (reader : Frontend.Reader F State)
    (q w : Cube n → F) (state : State) (pads : Frontend.LayerTape F n) :
    Frontend.realLayer reader q w state pads =
      let messages := Frontend.realRounds reader q w state pads.1
      let round := Frontend.readRounds reader state messages
      let A := evaluate w round.1
      let B := evaluate q round.1
      let cross := A*pads.2.2.1+B*pads.2.1-pads.2.2.2
      let scale := (reader.terminal round.2 cross).1
      ⟨messages,cross,A+scale.val*pads.2.1,B+scale.val*pads.2.2.1⟩ := rfl

/-- The tree emits the actual complete honest layer payload and reaches
the very state obtained by replaying that payload at the same oracle. -/
theorem layer_output {n : ℕ} (q w : Cube n → F) (state : State)
    (pads : Frontend.LayerTape F n) (H : Query → Answer) :
    ((layer queries q w state pads).run H).1 =
      let reader := (queries.reader H).toReader
      let payload := Frontend.realLayer reader q w state pads
      (⟨payload,Frontend.readLayer reader state payload⟩ : Layer F State n) := by
  simp only [layer,Tree.run_bind,Tree.run_map,rounds_output]
  rw [realLayer_eq]
  rfl

end LfzkV2.Current.ZeroKnowledge.HonestTranscript
