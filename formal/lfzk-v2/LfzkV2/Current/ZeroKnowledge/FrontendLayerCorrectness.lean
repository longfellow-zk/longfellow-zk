import LfzkV2.Linear.Prover
import LfzkV2.Current.ZeroKnowledge.FrontendLayer

/-! Identification of the stateful simulator coupling with the numerical
honest prover and the existing affine constraint compiler. -/
noncomputable section
namespace LfzkV2.Current.ZeroKnowledge.Frontend
open SumcheckV2
open scoped Classical
variable {F State Pad : Type} [Field F] {n a out : ℕ}

def linearPlan (ids : Layered.Replay.LayerPads Pad n) : Linear.Replay.LayerPads Pad n :=
  ⟨ids.round,ids.a,ids.b,ids.ab,ids.d⟩

def readMessages (reader : Reader F State) (state : State) (payload : LayerPayload F n)
    (beta : Fin a → F) (ids : Layered.Replay.LayerPads Pad n) : Linear.LayerMessages Pad F n a :=
  let replay := readLayer reader state payload
  { roundMessages := payload.rounds
    roundPads := ids.round
    point := replay.point
    beta := beta
    cross := payload.cross
    scale := replay.scale.val
    messageA := payload.claimA
    messageB := payload.claimB
    padA := ids.a, padB := ids.b, padAB := ids.ab, padD := ids.d
    alpha := replay.alpha }

theorem realRounds_eq_masked (reader : Reader F State) (q w : Cube n → F) (state : State)
    (pads : Fin n → RoundPoly F) (i : Fin n) :
    realRounds reader q w state pads i =
      mask ((honestMessages q w (readRounds reader state (realRounds reader q w state pads)).1).get
        (i.cast (honestMessages_length _ _ _).symm)) (pads i) := by
  have h := rounds_clear reader q w state pads
  have hc := congrArg (fun values : List (RoundPoly F) => values[i.val]?) h
  simp only [List.getElem?_ofFn, dif_pos i.isLt] at hc
  have hi : i.val < (honestMessages q w
      (readRounds reader state (realRounds reader q w state pads)).1).length := by
    rw [honestMessages_length]
    exact i.isLt
  rw [List.getElem?_eq_getElem hi] at hc
  have heq := Option.some.inj hc
  simp only [List.get_eq_getElem,Fin.val_cast]
  rw [← heq]
  cases hp : pads i with
  | mk p0 p1 =>
    cases hm : realRounds reader q w state pads i with
    | mk m0 m1 =>
      simp [mask,unmask]

theorem realLayer_messages_eq_honest
    (reader : Reader F State) (state : State)
    (body : Native.CircuitLayer (Cube out) (Cube n) (Fin a) F)
    (weights : Cube out → F) (wires : Cube n → F) (beta : Fin a → F)
    (pads : LayerTape F n) :
    let q := bindRightAffine (body.effectiveQuadratic weights beta) (body.effectiveLinear weights beta) wires
    let payload := realLayer reader q wires state pads
    let replay := readLayer reader state payload
    readMessages reader state payload beta (layerPlan n) =
      Linear.honestLayer body weights wires replay.point replay.scale.val replay.alpha beta
        (linearPlan (layerPlan n)) (padValues pads) := by
  dsimp only
  let q := bindRightAffine (body.effectiveQuadratic weights beta) (body.effectiveLinear weights beta) wires
  have hr : (realLayer reader q wires state pads).rounds =
      fun i => mask ((honestMessages q wires (readRounds reader state
        (realRounds reader q wires state pads.1)).1).get
          (i.cast (honestMessages_length _ _ _).symm)) (pads.1 i) := by
    funext i
    exact realRounds_eq_masked reader q wires state pads.1 i
  dsimp only [readMessages,Linear.honestLayer,linearPlan]
  congr 1

end LfzkV2.Current.ZeroKnowledge.Frontend
