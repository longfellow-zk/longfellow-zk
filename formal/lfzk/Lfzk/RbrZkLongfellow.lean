import Lfzk.ZkSim
import Lfzk.ZkMultilinear
import Lfzk.RbrLayerStepS
import Lfzk.RbrLongfellow

/-!
# The zero-knowledge LayerStep: pad-free state, transitions, per-step budgets

`Lfzk.RbrLongfellow` is the LayerStep of a verifier that checks the sumcheck rounds **in the clear**
(`check_round_c`) and reads a Ligero statement fixed by the commitment.  The deployed verifier
(`zk_common.h:L46-L135`, `symbolic_sumcheck_verifier.rs`) does neither.  Its round polynomials are
padded, and `ConstraintBuilder::next` substitutes `p(1) := claim − p(0)` (`zk_common.h:L336`), so
there is no round check at all.  Each layer's `finalize` emits one linear row and one quadratic
triple (`zk_common.h:L113`).  After the last layer one input row ties the last pair to the
committed columns at a fresh `alpha_in` (`zk_common.h:L129-L133`).  The only verdict is Ligero's, on
the system built from the transcript.  This file is that verifier as a round-by-round state machine
over the schedule of `Lfzk.Rounds`, with its escape counts.

## The state (`ZkState`)

`running zs` carries what the verifier knows: the layer, its `beta`, the layer's incoming public state
(`st`: its points, and the masked claims), the fold coefficient `alpha`, the challenges bound so far,
the **symbolic claim** `e : Expression M F` (`ConstraintBuilder`'s `expr_`), and the **rows emitted
so far** (`LayerRowData`, one per closed layer).  After the input binding the state is `built sys`,
the whole Ligero system (`buildSystemMulti`); after Ligero's challenge, `challenged sys x`.

## The transitions

| slot | transition | what it does |
|---|---|---|
| layer 0's pair | `zkInit` | draws `(G, beta₀, alpha₀)` — `begin_circuit`'s output point and `begin_layer`'s pair, one oracle answer since no message separates them; `e := 0` |
| a sumcheck round | `zkRound` | `e := builder_next e ⟨tr0, tr2, pp0, pp2, r⟩`; never rejects |
| layer `ly + 1`'s pair | `zkCombine` | appends layer `ly`'s `finalize` row, moves to the next state, draws `(beta, alpha)` (`begin_layer`), `e := builder_first alpha wc0 wc1 dwL dwR` |
| the input binding | `zkInputBind` | appends the last row and builds the system with the input row at `alpha_in` |
| Ligero's challenge, query | `zkLigChallenge`, `zkLigQuery` | `.challenged sys x`; accept iff the query passes the test at `(sys, x)` |

Three **shape guards** reject, and nothing else does: a layer closes only after its `w ly` rounds,
the input binding happens after the last layer, and the system must fit the Ligero statement's
fixed tableau (`Fits`).  The deployed verifier's loops have exactly this shape, so the guards never
fire on a proof the deployed verifier parses.

## Doom, per candidate (`ZkWrong`)

Candidates are `Option Lift`.  A real candidate `some ℓ` carries the committed columns and the pad
`asg ℓ` (in the V1 instantiation, the decoded messages of a lift-list member).

* `start` — `ℓ`'s witness does not satisfy the circuit;
* `running zs` at layer `ly` with bound prefix `bnd` — **three branches, and the rows**:
  - (rows) some emitted row is violated by `ℓ`'s pad;
  - (a) `e` de-padded by `ℓ`'s pad is not `ℓ`'s honest claim at the drawn `beta_ly`
    (`H.sum ℓ ly st beta alpha bnd`).  The de-padding is what replaces the clear check:
    `RoundData.unpad` at `ℓ`'s pad passes `check_round_c` by construction (`unpad_sum`), and
    `builder_next_eval` says `e` tracks its claim;
  - (c) `H.Pend ℓ ly bnd` — layer `ly + 1`'s assertion vector, with the coordinates bound so far in
    layer `ly`'s sumcheck, is not identically zero (*pending*: it will be caught at layer `ly + 1`'s
    pair slot);
  - (b) `H.Pend ℓ j []` for some `j > ly` — a deeper layer `j + 1 ≥ ly + 2` has a non-zero
    assertion vector (*deep*);
* `built sys` — `sys` fits and `ℓ`'s assignment does not satisfy it;
* `challenged sys x` — `LigDoomed sys x`, the Ligero classifier's doom, for every candidate;
* `accepted` — never; `failed` — always.

### Why three branches: assertions never reach the output

The compiler keeps assert-zero gates at intermediate layers, and their outputs are dead ends
(`QuadCircuit.DeadEnd`): nothing above reads them.  So an unsatisfied witness need not change the
output layer at all, and "unsatisfied ⇒ the output is not identically zero" is false.  A violated
assertion at layer `ly + 1` is visible only through `beta_{ly+1}`, which multiplies it
(`toLayered_V_decomp`: the layer's values are `V⁰ + beta · S` with `S` the assertion MLE), and only
at layer `ly + 1`'s pair slot, where `beta_{ly+1}` is drawn *after* the claims `(wc0, wc1)` are
fixed.  Branch (c) carries the violation from the moment the layer above starts until that slot;
branch (b) carries it, for free, down to layer `ly`.  The honest values of branch (a) read the next
layer at `beta_{ly+1} = 0` (its assertion-free values `V⁰`); the honest run at a satisfied witness
has `S = 0` everywhere, so that convention is the honest value.

### The budgets per branch

* layer 0's slot: from `start`, if some `H.Pend ℓ j []` holds the new state is wrong for free
  ((b) or (c)); otherwise every intermediate assertion holds, so an unsatisfied candidate has a
  non-zero output-or-layer-0 assertion vector, and `(G, beta₀, alpha₀)` costs `(logv + 2)/|F|`
  (`ZkMultilinear.init_bad_card`, the hypothesis `hinit`);
* a round: (rows), (b) survive; (c) survives except at one challenge (`pend_round`, which is
  `mlin_bind_card`); (a) survives except at two (`sumcheck_step_reduction`) — at most two;
* layer `ly + 1`'s pair: (rows) survives; (b) becomes (b) or (c) at `ly + 1` with nothing bound;
  (c) at the full bound says `W_{ly+1}` is not constant in `beta` (`pend_close`), so whatever pair
  was claimed, `(beta, alpha)` escapes on at most `2|F|` of the `|F|²` pairs
  (`bilinear_zero_card`, which is `toLayered_pair_card`); (a) plus a satisfied row makes the claimed
  pair wrong at `beta = 0` (`final`, `layer_checks_imply_sumcheck`), and the same count applies;
* the input binding: (c) and (b) cannot hold at the last layer (`pend_last`); (a) and (rows) are
  as in the clear chain, `1/|F|`.

The **phantom** candidate `none` is wrong at every field state and at `built sys` exactly when `sys`
fits, and follows `LigDoomed` at `challenged`.  It exists so that the candidate type is non-empty —
`right_of_accepts` needs an undoomed candidate at `.accepted` even when the lift list is empty — and
it is **free**: it never escapes a field slot, so its weight (`wt none = 0`) adds nothing to the list
factor (`doomPres_of_weighted`).

## The per-step budgets (all per real candidate, `k` the decoder's balance)

* `zkInit_budget` — `kinit · binit`, `binit` the layer-0 count above
  (`(logv + 2)·|F|^(logv+1)` from `RbrZkSplit.hinit_of_output`);
* `zkRound_budget` — `k · 2`;
* `zkCombine_budget` — `kpair · 2|F|`;
* `zkInputBind_budget` — `k · 1`;
* `zkLigChallenge_budget`, `zkLigQuery_budget` — **doomed-prefix**, no list factor: from a doomed
  `built sys` (no candidate satisfies `sys`), every escaping challenge is in `escaping sys`; from a
  doomed `challenged sys x`, every escaping query is in the test.

## What is a hypothesis here

The analysis data the budgets are stated against, all about honest values and none about the
prover.  `ZkHonest` (`sum_eq`, `next_eq`, `deg_le`: the honest partial sums at the layer's own
`beta`, the next layer read at `beta = 0`) and the pending predicate `Pend`.  `ZkBoundary`: `rel`
(`LayeredCircuit.layer_rel`, `layer_claim_at_schedule`), `final` (`honest_final` at
`beta_{ly+1} = 0`), `W_affine` (`toLayered_V_decomp`), `pend_round` (`mlin_bind_card`),
`pend_close` (the assertion MLE is `W 1 − W 0`), `pend_last` (the input layer has no assertions),
`hin` (`toLayered_hin`).  And `hinit` (`RbrZkSplit.hinit_of_output` from `init_bad_card`).  The
`Lfzk.Arith` lemmas named are the ones in `ConcreteCircuitBridge`; `Lfzk.ZkArithBoundary`
assembles them, under `QuadCircuit.DeadEnd` and `Isolated`, into a `ZkHonest`, a `ZkBoundary` and a
whole `RbrZkSplit.ZkFieldData` at `Sat := Satisfied` (`ZkArithInit.zkFieldDataOf`), for a code that
agrees with the construction.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Lfzk.RbrZkLongfellow

open Finset Sumcheck RbrLongfellow Lfzk.RbrLayerStepS
open scoped Classical

/-! ## 1. Messages and the verifier's public computation -/

/-- A sumcheck round's transmitted data: `tr[0]`, `tr[2]` and the pad indices of their blinders.
`tr[1]` is not sent: `p(1)` is substituted (`zk_common.h:L336`). -/
structure ZkRoundMsg (M : ℕ) (F : Type) where
  tr0 : F
  tr2 : F
  pp0 : Fin M
  pp2 : Fin M

/-- A layer close's transmitted data: the masked `wc[0]`, `wc[1]` and the layer's claim-pad
indices `CLAIM_PAD[layer]` (`zk_common.h:L246`). -/
structure ZkCloseMsg (M : ℕ) (F : Type) where
  wc0 : F
  wc1 : F
  dwL : Fin M
  dwR : Fin M
  dwLR : Fin M

/--
**The zero-knowledge verifier's code.**  Everything the verifier computes, none of it an honest
value: the state `begin_circuit` produces from the output point, the next layer's state from the
bound challenges and the masked claims, the recomputed `EQQ` (`zk_common.h:L107-L111`), the input
row's coefficients and public binding (`input_constraint`, `zk_common.h:L406-L418`), the size of the
Ligero tableau, how a message carries its round or close data, and the coin decoders.
-/
structure ZkCode (C F X Q Msg Gpt : Type) (M ninp logw logc : ℕ) where
  /-- `begin_circuit`'s state at an output point: claims of zero, both points `G`. -/
  st0 : Gpt → LayerState logw logc F
  /-- The next layer's state from the bound challenges and the masked `wc`s. -/
  stNext : List F → F → F → LayerState logw logc F
  /-- The verifier's `EQQ` at a layer's close, at its state, its `beta`, `alpha` and bound. -/
  eqqOf : ℕ → LayerState logw logc F → F → F → List F → F
  /-- The number of public input wires. -/
  npub : ℕ
  /-- The input row's coefficients `b_i = eq0_i + alpha_in · eq1_i` at the last layer's bound. -/
  inCoeffs : List F → F → Fin ninp → F
  /-- The input row's public binding, folded from the verifier's own public input. -/
  pubBinding : List F → F → F
  /-- The Ligero statement's linear rows. -/
  nlin : ℕ
  /-- The Ligero statement's quadratic triples. -/
  nt : ℕ
  /-- A sumcheck round's message data. -/
  roundOf : Msg → ZkRoundMsg M F
  /-- A layer close's message data. -/
  closeOf : Msg → ZkCloseMsg M F
  /-- Layer 0's pair slot's decoder: `(G, beta₀, alpha₀)`. -/
  decodeInit : C → Gpt × F × F
  /-- A later layer's pair decoder: `(beta, alpha)` (`begin_layer`). -/
  decodePair : C → F × F
  /-- The field-element decoder (sumcheck rounds, later `alpha`s, `alpha_in`). -/
  decodeF : C → F
  /-- Ligero's linear-combination decoder. -/
  decodeChal : C → X
  /-- Ligero's query decoder. -/
  decodeQuery : C → Q

/-- **The honest values, and the pending predicate.**  `RbrLongfellow.Honest` with the layer's own
`beta` as an argument: `sum ℓ ly st b a bnd` is candidate `ℓ`'s honest partial sum of layer `ly`'s
polynomial at the layer's `beta = b`, fold coefficient `a` and bound prefix `bnd`, with the next
layer read at `beta_{ly+1} = 0`.  `Pend ℓ ly bnd` says layer `ly + 1`'s assertion vector, with the
coordinates `bnd` bound, is not identically zero (see the module docstring). -/
structure ZkHonest (F Lift : Type) [Field F] (logw logc : ℕ) where
  /-- The honest partial sum. -/
  sum : Lift → ℕ → LayerState logw logc F → F → F → List F → F
  /-- The honest round polynomial. -/
  poly : Lift → ℕ → LayerState logw logc F → F → F → List F → Polynomial F
  deg_le : ∀ ℓ ly st b a bnd, (poly ℓ ly st b a bnd).natDegree ≤ 2
  sum_eq : ∀ ℓ ly st b a bnd,
    (poly ℓ ly st b a bnd).eval 0 + (poly ℓ ly st b a bnd).eval 1 = sum ℓ ly st b a bnd
  next_eq : ∀ ℓ ly st b a bnd r, (poly ℓ ly st b a bnd).eval r = sum ℓ ly st b a (bnd ++ [r])
  /-- Layer `ly + 1`'s assertion vector, with `bnd` bound in layer `ly`'s sumcheck, is not
  identically zero. -/
  Pend : Lift → ℕ → List F → Prop

/-! ## 2. The state -/

/-- The zero-knowledge verifier's state inside LayerStep. -/
structure ZkRunning (M logw logc : ℕ) (F : Type) [Field F] where
  /-- Which layer. -/
  layer : ℕ
  /-- The layer's `beta`, drawn at its pair slot. -/
  beta : F
  /-- The layer's incoming points, and the masked claims. -/
  st : LayerState logw logc F
  /-- The coefficient combining the layer's two inherited claims. -/
  alpha : F
  /-- The challenges bound so far in this layer's sumcheck. -/
  bound : List F
  /-- The symbolic claim (`ConstraintBuilder::expr_`). -/
  e : Expression M F
  /-- The `finalize` rows emitted so far, one per closed layer. -/
  rows : List (LayerRowData M F)

/-- **The zero-knowledge LayerStep's state.** -/
inductive ZkState (M ninp logw logc : ℕ) (F X : Type) [Field F] where
  | start
  | running (zs : ZkRunning M logw logc F)
  /-- After the input binding: the Ligero system the transcript determines. -/
  | built (sys : LigeroSystem ninp M F)
  /-- After Ligero's linear-combination challenge. -/
  | challenged (sys : LigeroSystem ninp M F) (x : X)
  | accepted
  | failed

/-! ## 3. The transitions -/

section Transitions

variable {C F X Q Msg Gpt : Type} [Field F] [SumcheckInterp F] {M ninp logw logc : ℕ}

/-- The system fits the Ligero statement's tableau. -/
def Fits (V : ZkCode C F X Q Msg Gpt M ninp logw logc) (sys : LigeroSystem ninp M F) : Prop :=
  sys.linear.length ≤ V.nlin ∧ sys.quad.length ≤ V.nt

/-- Layer 0's pair slot: `begin_circuit`'s point and `begin_layer`'s pair from one answer; the claim
expression starts at zero (`zkExpr none`). -/
def zkInit (V : ZkCode C F X Q Msg Gpt M ninp logw logc) (c : C) :
    ZkState M ninp logw logc F X → ZkState M ninp logw logc F X
  | .start =>
      .running { layer := 0
                 beta := (V.decodeInit c).2.1
                 st := V.st0 (V.decodeInit c).1
                 alpha := (V.decodeInit c).2.2
                 bound := []
                 e := Expression.zero M F
                 rows := [] }
  | .running _ => .failed
  | .built _ => .failed
  | .challenged _ _ => .failed
  | .accepted => .failed
  | .failed => .failed

/-- The `finalize` row of the layer `zs` is in, at a close message. -/
def closeRow (V : ZkCode C F X Q Msg Gpt M ninp logw logc) (zs : ZkRunning M logw logc F)
    (cm : ZkCloseMsg M F) : LayerRowData M F :=
  { e := zs.e
    eqq := V.eqqOf zs.layer zs.st zs.beta zs.alpha zs.bound
    wc0 := cm.wc0
    wc1 := cm.wc1
    var_dwL := cm.dwL
    var_dwR := cm.dwR
    var_dwLR := cm.dwLR }

/-- **Close a layer and start the next**: emit the closed layer's row, move to the next state, draw
its `(beta, alpha)`, and combine its masked claims at `alpha` (`ConstraintBuilder::first`).  The
guard `zs.layer + 1 < nl` holds on every run (the pair slot of layer `ly + 1 < nl` follows layer
`ly`'s rounds); it keeps the model from closing a layer below the circuit. -/
noncomputable def zkCombine (nl : ℕ) (w : ℕ → ℕ) (V : ZkCode C F X Q Msg Gpt M ninp logw logc)
    (cm : ZkCloseMsg M F) (c : C) :
    ZkState M ninp logw logc F X → ZkState M ninp logw logc F X
  | .running zs =>
      if zs.bound.length = w zs.layer ∧ zs.layer + 1 < nl then
        .running { layer := zs.layer + 1
                   beta := (V.decodePair c).1
                   st := V.stNext zs.bound cm.wc0 cm.wc1
                   alpha := (V.decodePair c).2
                   bound := []
                   e := builder_first (V.decodePair c).2 cm.wc0 cm.wc1 cm.dwL cm.dwR
                   rows := zs.rows ++ [closeRow V zs cm] }
      else .failed
  | .start => .failed
  | .built _ => .failed
  | .challenged _ _ => .failed
  | .accepted => .failed
  | .failed => .failed

/-- The round data `ConstraintBuilder::next` consumes, at a round message and a challenge. -/
def roundData (rm : ZkRoundMsg M F) (r : F) : RoundData M F :=
  ⟨rm.tr0, rm.tr2, rm.pp0, rm.pp2, r⟩

/-- **A sumcheck round**: `ConstraintBuilder::next`, and nothing is checked. -/
noncomputable def zkRound (V : ZkCode C F X Q Msg Gpt M ninp logw logc) (rm : ZkRoundMsg M F)
    (c : C) : ZkState M ninp logw logc F X → ZkState M ninp logw logc F X
  | .running zs =>
      .running { zs with
        bound := zs.bound ++ [V.decodeF c]
        e := builder_next zs.e (roundData rm (V.decodeF c)) }
  | .start => .failed
  | .built _ => .failed
  | .challenged _ _ => .failed
  | .accepted => .failed
  | .failed => .failed

/-- **The system the transcript determines**: every layer's row and triple, and the input row at
`alpha_in` with `got = wc0 + alpha_in · wc1` and the last layer's claim pads. -/
noncomputable def inputSystem (V : ZkCode C F X Q Msg Gpt M ninp logw logc)
    (zs : ZkRunning M logw logc F) (cm : ZkCloseMsg M F) (a : F) : LigeroSystem ninp M F :=
  buildSystemMulti V.npub (zs.rows ++ [closeRow V zs cm]) (V.inCoeffs zs.bound a)
    (V.pubBinding zs.bound a) (cm.wc0 + a * cm.wc1) a cm.dwL cm.dwR

/-- **The input binding**: close the last layer and build the system at the drawn `alpha_in`. -/
noncomputable def zkInputBind (nl : ℕ) (w : ℕ → ℕ) (V : ZkCode C F X Q Msg Gpt M ninp logw logc)
    (cm : ZkCloseMsg M F) (c : C) :
    ZkState M ninp logw logc F X → ZkState M ninp logw logc F X
  | .running zs =>
      if zs.bound.length = w zs.layer ∧ zs.layer + 1 = nl ∧
          Fits V (inputSystem V zs cm (V.decodeF c)) then
        .built (inputSystem V zs cm (V.decodeF c))
      else .failed
  | .start => .failed
  | .built _ => .failed
  | .challenged _ _ => .failed
  | .accepted => .failed
  | .failed => .failed

/-- **Ligero's challenge.** -/
def zkLigChallenge (V : ZkCode C F X Q Msg Gpt M ninp logw logc) (c : C) :
    ZkState M ninp logw logc F X → ZkState M ninp logw logc F X
  | .built sys => .challenged sys (V.decodeChal c)
  | .start => .failed
  | .running _ => .failed
  | .challenged _ _ => .failed
  | .accepted => .failed
  | .failed => .failed

/-- **Ligero's query**: accept iff the query passes the test at the built system and the
challenge. -/
noncomputable def zkLigQuery (V : ZkCode C F X Q Msg Gpt M ninp logw logc)
    (acc : LigeroSystem ninp M F → X → Finset Q) (c : C) :
    ZkState M ninp logw logc F X → ZkState M ninp logw logc F X
  | .challenged sys x => if V.decodeQuery c ∈ acc sys x then .accepted else .failed
  | .start => .failed
  | .running _ => .failed
  | .built _ => .failed
  | .accepted => .failed
  | .failed => .failed

/--
**The zero-knowledge verifier's transitions**, on the proof's messages `ms` (slot `m` reads message
`m`) with query test `acc` (which may read the query slot's message: the Ligero response).
-/
noncomputable def zkSteps (nl : ℕ) (w : ℕ → ℕ) (V : ZkCode C F X Q Msg Gpt M ninp logw logc)
    (ms : ℕ → Msg) (acc : ∀ m : ℕ, (Fin m → C) → LigeroSystem ninp M F → X → Finset Q) :
    StepsS C (ZkState M ninp logw logc F X) nl w where
  pair ly m _ c s := if ly.val = 0 then zkInit V c s else zkCombine nl w V (V.closeOf (ms m)) c s
  round _ _ m _ c s := zkRound V (V.roundOf (ms m)) c s
  inputBind m _ c s := zkInputBind nl w V (V.closeOf (ms m)) c s
  ligeroChallenge _ _ c s := zkLigChallenge V c s
  ligeroQuery m pref c s := zkLigQuery V (acc m pref) c s

end Transitions

/-! ## 4. Doom -/

section Doom

variable {C F X Q Msg Gpt Lift : Type} [Field F] {M ninp logw logc : ℕ}

/-- Some emitted row is violated by a pad. -/
def RowsBad (pad : Pad M F) (rows : List (LayerRowData M F)) : Prop :=
  ∃ L ∈ rows, ¬ ligero_layer_checks L.e pad L.eqq L.wc0 L.wc1 L.var_dwL L.var_dwR L.var_dwLR

/-- **Doom, per candidate.**  See the module docstring. -/
def ZkWrong (V : ZkCode C F X Q Msg Gpt M ninp logw logc) (H : ZkHonest F Lift logw logc)
    (asg : Lift → LigeroAssignment ninp M F) (Sat : Lift → Prop)
    (LigDoomed : LigeroSystem ninp M F → X → Prop) :
    Option Lift → ZkState M ninp logw logc F X → Prop
  | some ℓ, .start => ¬ Sat ℓ
  | some ℓ, .running zs => RowsBad (asg ℓ).2 zs.rows ∨
      evaluates_to zs.e (asg ℓ).2 ≠ H.sum ℓ zs.layer zs.st zs.beta zs.alpha zs.bound ∨
      H.Pend ℓ zs.layer zs.bound ∨ ∃ j, zs.layer < j ∧ H.Pend ℓ j []
  | some ℓ, .built sys => Fits V sys ∧ ¬ sys.Sat (asg ℓ).1 (asg ℓ).2
  | none, .start => True
  | none, .running _ => True
  | none, .built sys => Fits V sys
  | _, .challenged sys x => LigDoomed sys x
  | _, .accepted => False
  | _, .failed => True

/-- The weight of a candidate in the list factor: `1` for a real one, `0` for the phantom. -/
def wt : Option Lift → ℕ
  | none => 0
  | some _ => 1

theorem sum_wt [Fintype Lift] : ∑ cand : Option Lift, wt cand = Fintype.card Lift := by
  rw [Fintype.sum_option]
  simp [wt]

/-- No candidate's assignment satisfies the system. -/
def NoSat (asg : Lift → LigeroAssignment ninp M F) (sys : LigeroSystem ninp M F) : Prop :=
  ∀ ℓ : Lift, ¬ sys.Sat (asg ℓ).1 (asg ℓ).2

omit [Field F] in
/-- **Doom at `built sys` is `Fits ∧ NoSat`**: the phantom asks the first, the real candidates the
second. -/
theorem doomed_built_iff [Field F] (V : ZkCode C F X Q Msg Gpt M ninp logw logc)
    (H : ZkHonest F Lift logw logc) (asg : Lift → LigeroAssignment ninp M F) (Sat : Lift → Prop)
    (LigDoomed : LigeroSystem ninp M F → X → Prop) (sys : LigeroSystem ninp M F) :
    (∀ cand : Option Lift, ZkWrong V H asg Sat LigDoomed cand (.built sys)) ↔
      Fits V sys ∧ NoSat asg sys := by
  constructor
  · intro h
    exact ⟨h none, fun ℓ => (h (some ℓ)).2⟩
  · rintro ⟨hf, hn⟩ cand
    cases cand with
    | none => exact hf
    | some ℓ => exact ⟨hf, hn ℓ⟩

end Doom

/-! ## 5. The weighted union bound -/

section Weighted

variable {C S Cand : Type} [Fintype C] {T : ℕ}

/--
**The list factor, weighted.**  If from a wrong state at most `wt cand · b` answers make the state
right for `cand`, then at most `(∑ wt) · b` answers undo doom.  A candidate of weight `0` must
never escape; the phantom is such a candidate.
-/
theorem doomPres_of_weighted [Fintype Cand] (ch : Bcs.ClaimChain C T S Cand) (wt : Cand → ℕ)
    (b : ℕ) (i : Fin T) (pref : Fin i.val → C)
    (hb : ∀ cand : Cand, ch.Wrong cand (ch.state i.val pref) →
      (univ.filter fun c : C =>
        ¬ ch.Wrong cand (ch.step i pref c (ch.state i.val pref))).card ≤ wt cand * b)
    (hdoom : ch.doomed i.val pref) :
    (univ.filter fun c : C => ¬ ch.doomed (i.val + 1) (Bcs.extend pref c)).card
      ≤ (∑ cand, wt cand) * b := by
  classical
  refine le_trans (Finset.card_le_card (t := univ.biUnion fun cand : Cand =>
      univ.filter fun c : C =>
        ¬ ch.Wrong cand (ch.step i pref c (ch.state i.val pref))) ?_) ?_
  · intro c hc
    simp only [mem_filter, mem_univ, true_and, Bcs.ClaimChain.doomed, not_forall] at hc
    obtain ⟨cand, hcand⟩ := hc
    rw [Bcs.ClaimChain.state_extend] at hcand
    exact Finset.mem_biUnion.mpr ⟨cand, mem_univ _, mem_filter.mpr ⟨mem_univ _, hcand⟩⟩
  · calc (univ.biUnion fun cand : Cand => univ.filter fun c : C =>
            ¬ ch.Wrong cand (ch.step i pref c (ch.state i.val pref))).card
        ≤ ∑ cand : Cand, (univ.filter fun c : C =>
            ¬ ch.Wrong cand (ch.step i pref c (ch.state i.val pref))).card :=
          Finset.card_biUnion_le
      _ ≤ ∑ cand : Cand, wt cand * b := Finset.sum_le_sum (fun cand _ => hb cand (hdoom cand))
      _ = (∑ cand, wt cand) * b := by rw [Finset.sum_mul]

variable {nl : ℕ} {w : ℕ → ℕ}

/--
**LayerStep as a `Bcs.Rbr`, at weighted field budgets and doomed-prefix Ligero budgets.**  The
per-slot budget is `mixedBudget (∑ wt) …`.
-/
noncomputable def layerStepRbrW [Fintype Cand] (steps : StepsS C S nl w)
    (Wrong : Cand → S → Prop) (init : S) (wt : Cand → ℕ) (bpair bround bin blig bquery : ℕ)
    {Accepts : (Fin (Rounds.Role.length nl w) → C) → Prop} {Fails : Prop}
    (wrong_init : Fails → ∀ cand : Cand, Wrong cand init)
    (budget_pair : ∀ (ly : Fin nl) (m : ℕ) (pref : Fin m → C) (cand : Cand) (s : S),
      Wrong cand s → (univ.filter fun c : C => ¬ Wrong cand (steps.pair ly m pref c s)).card
        ≤ wt cand * bpair)
    (budget_round : ∀ (ly : Fin nl) (j : Fin (w ly.val)) (m : ℕ) (pref : Fin m → C) (cand : Cand)
      (s : S), Wrong cand s →
      (univ.filter fun c : C => ¬ Wrong cand (steps.round ly j m pref c s)).card
        ≤ wt cand * bround)
    (budget_in : ∀ (m : ℕ) (pref : Fin m → C) (cand : Cand) (s : S), Wrong cand s →
      (univ.filter fun c : C => ¬ Wrong cand (steps.inputBind m pref c s)).card ≤ wt cand * bin)
    (budget_lig : ∀ (m : ℕ) (pref : Fin m → C) (s : S), (∀ cand : Cand, Wrong cand s) →
      (univ.filter fun c : C =>
        ¬ ∀ cand : Cand, Wrong cand (steps.ligeroChallenge m pref c s)).card ≤ blig)
    (budget_query : ∀ (m : ℕ) (pref : Fin m → C) (s : S), (∀ cand : Cand, Wrong cand s) →
      (univ.filter fun c : C =>
        ¬ ∀ cand : Cand, Wrong cand (steps.ligeroQuery m pref c s)).card ≤ bquery)
    (right_of_accepts : ∀ tape : Fin (Rounds.Role.length nl w) → C, Accepts tape →
      ∃ cand : Cand, ¬ (layerStepChainS steps Wrong init).Wrong cand
        ((layerStepChainS steps Wrong init).state (Rounds.Role.length nl w)
          (Bcs.trunc tape (Rounds.Role.length nl w) le_rfl))) :
    Bcs.Rbr C (Rounds.Role.length nl w) Accepts Fails :=
  chainRbr (layerStepChainS steps Wrong init)
    (fun i => mixedBudget (nl := nl) (w := w) (∑ cand, wt cand) bpair bround bin blig bquery
      (Rounds.Role.indexEquiv.symm i))
    wrong_init
    (by
      intro i pref hdoom
      cases hrole : Rounds.Role.indexEquiv.symm i with
      | layerPair ly =>
          simp only [mixedBudget, RbrLayerStep.classBudget]
          refine doomPres_of_weighted _ wt bpair i pref (fun cand hw => ?_) hdoom
          simp only [layerStepChainS, stepAtS, hrole]
          exact budget_pair ly i.val pref cand _ hw
      | sumcheck ly j =>
          simp only [mixedBudget, RbrLayerStep.classBudget]
          refine doomPres_of_weighted _ wt bround i pref (fun cand hw => ?_) hdoom
          simp only [layerStepChainS, stepAtS, hrole]
          exact budget_round ly j i.val pref cand _ hw
      | inputBind =>
          simp only [mixedBudget, RbrLayerStep.classBudget]
          refine doomPres_of_weighted _ wt bin i pref (fun cand hw => ?_) hdoom
          simp only [layerStepChainS, stepAtS, hrole]
          exact budget_in i.val pref cand _ hw
      | ligeroChallenge =>
          simp only [mixedBudget, RbrLayerStep.classBudget]
          refine doomPres_of_doomed _ blig i pref (fun hw => ?_) hdoom
          simp only [layerStepChainS, stepAtS, hrole]
          exact budget_lig i.val pref _ hw
      | ligeroQuery =>
          simp only [mixedBudget, RbrLayerStep.classBudget]
          refine doomPres_of_doomed _ bquery i pref (fun hw => ?_) hdoom
          simp only [layerStepChainS, stepAtS, hrole]
          exact budget_query i.val pref _ hw)
    right_of_accepts

end Weighted

/-! ## 6. The per-step budgets -/

section Budgets

variable {C F X Q Msg Gpt Lift : Type} [Fintype C] [Field F] [Fintype F] [DecidableEq F]
  [SumcheckInterp F]
variable {M ninp logw logc : ℕ}
variable (V : ZkCode C F X Q Msg Gpt M ninp logw logc) (H : ZkHonest F Lift logw logc)
  (asg : Lift → LigeroAssignment ninp M F) (Sat : Lift → Prop)
  (LigDoomed : LigeroSystem ninp M F → X → Prop)

omit [Fintype C] [Fintype F] [DecidableEq F] [SumcheckInterp F] in
/-- A transition that lands in `running`, `failed` or a fitting `built` never undoes the phantom's
doom. -/
theorem phantom_stays (s' : ZkState M ninp logw logc F X)
    (hs : (∃ zs, s' = .running zs) ∨ s' = .failed ∨ ∃ sys, s' = .built sys ∧ Fits V sys) :
    ZkWrong V H asg Sat LigDoomed none s' := by
  rcases hs with ⟨zs, rfl⟩ | rfl | ⟨sys, rfl, hf⟩
  · exact trivial
  · exact trivial
  · exact hf

omit [Fintype F] [DecidableEq F] [SumcheckInterp F] in
/-- The empty-count helper: if no answer escapes, the count is `0 ≤ anything`. -/
theorem card_filter_le_of_none {P : C → Prop} [DecidablePred P] (b : ℕ) (h : ∀ c, ¬ P c) :
    (univ.filter P).card ≤ b := by
  refine le_trans (Finset.card_le_card (t := (∅ : Finset C)) ?_) (by simp)
  intro c hc
  simp only [mem_filter, mem_univ, true_and] at hc
  exact absurd hc (h c)

omit [SumcheckInterp F] in
/--
**Layer 0's pair slot: `kinit · binit`.**  From an unsatisfied candidate: if some layer's assertion
vector below the output is non-zero (`H.Pend ℓ j []` for some `j`), the new state is wrong for free —
branch (c) at `j = 0`, branch (b) at `j > 0`.  Otherwise an answer escapes only by decoding to a
triple `(G, β, α)` at which the candidate's honest layer-0 claim is zero — the claim the verifier
starts from is zero — and `hinit` is that count (`ZkMultilinear.init_bad_card`).
-/
theorem zkInit_budget [Fintype Gpt] [DecidableEq Gpt] (kinit binit : ℕ)
    (hbal : ∀ y : Gpt × F × F, (univ.filter fun c : C => V.decodeInit c = y).card ≤ kinit)
    (hinit : ∀ ℓ : Lift, ¬ Sat ℓ → (∀ j, ¬ H.Pend ℓ j []) →
      (univ.filter fun p : Gpt × F × F =>
        H.sum ℓ 0 (V.st0 p.1) p.2.1 p.2.2 [] = 0).card ≤ binit)
    (cand : Option Lift) (s : ZkState M ninp logw logc F X)
    (hw : ZkWrong V H asg Sat LigDoomed cand s) :
    (univ.filter fun c : C => ¬ ZkWrong V H asg Sat LigDoomed cand (zkInit V c s)).card
      ≤ wt cand * (kinit * binit) := by
  classical
  cases cand with
  | none =>
      refine card_filter_le_of_none _ fun c hc => hc ?_
      cases s <;> exact phantom_stays V H asg Sat LigDoomed _ (by simp [zkInit])
  | some ℓ =>
      rw [show wt (some ℓ) = 1 from rfl, one_mul]
      cases s with
      | start =>
          have hnsat : ¬ Sat ℓ := hw
          by_cases hpend : ∃ j, H.Pend ℓ j []
          · obtain ⟨j, hj⟩ := hpend
            refine card_filter_le_of_none _ fun c hc => hc ?_
            simp only [zkInit, ZkWrong]
            rcases Nat.eq_zero_or_pos j with rfl | hj0
            · exact Or.inr (Or.inr (Or.inl hj))
            · exact Or.inr (Or.inr (Or.inr ⟨j, hj0, hj⟩))
          · have hnp : ∀ j, ¬ H.Pend ℓ j [] := fun j hj => hpend ⟨j, hj⟩
            refine le_trans (Finset.card_le_card ?_) (Bcs.card_decode_le V.decodeInit kinit hbal
                (fun p => H.sum ℓ 0 (V.st0 p.1) p.2.1 p.2.2 [] = 0) binit
                (by convert hinit ℓ hnsat hnp))
            intro c hc
            simp only [mem_filter, mem_univ, true_and] at hc ⊢
            simp only [zkInit, ZkWrong, not_or, ne_eq, not_not] at hc
            obtain ⟨-, hcl, -, -⟩ := hc
            rw [← hcl]
            simp
      | running _ => exact card_filter_le_of_none _ fun c hc => hc trivial
      | built _ => exact card_filter_le_of_none _ fun c hc => hc trivial
      | challenged _ _ => exact card_filter_le_of_none _ fun c hc => hc trivial
      | accepted => exact card_filter_le_of_none _ fun c hc => hc trivial
      | failed => exact card_filter_le_of_none _ fun c hc => hc trivial

omit [Fintype F] in
/-- The de-padded round polynomial passes the clear round check at its claim, by construction. -/
theorem check_unpad (rd : RoundData M F) (pad : Pad M F) (cl : F) :
    check_round_c cl (rd.unpad pad cl) rd.chal = some (rd.step pad cl) := by
  rw [check_round_c, if_pos (by simp), RoundData.step]

omit [Fintype C] [Fintype F] [DecidableEq F] [SumcheckInterp F] in
/-- A violated row stays violated as rows are appended. -/
theorem rowsBad_append (pad : Pad M F) (rows extra : List (LayerRowData M F))
    (h : RowsBad pad rows) : RowsBad pad (rows ++ extra) := by
  obtain ⟨L, hL, hbad⟩ := h
  exact ⟨L, List.mem_append_left _ hL, hbad⟩

omit [Fintype C] [Fintype F] [DecidableEq F] [SumcheckInterp F] in
/-- **A satisfied close row makes a wrong claim a wrong pair.**  The row forces the de-padded claim
to `eqq · W'₀ · W'₁` (`layer_checks_imply_sumcheck`); the honest claim is `eqq · W₀ · W₁` (`hfinal`);
so the claimed pair is not the honest one. -/
theorem pair_wrong_of_row {e : Expression M F} {pad : Pad M F} {eqq wc0 wc1 : F}
    {dwL dwR dwLR : Fin M} {honest W0 W1 : F}
    (hrow : ligero_layer_checks e pad eqq wc0 wc1 dwL dwR dwLR)
    (hcl : evaluates_to e pad ≠ honest) (hfinal : honest = eqq * W0 * W1) :
    W0 ≠ wc0 + pad dwL ∨ W1 ≠ wc1 + pad dwR := by
  have h := layer_checks_imply_sumcheck e pad eqq wc0 wc1 dwL dwR dwLR hrow
  by_contra hc
  push Not at hc
  exact hcl (by rw [h, hfinal, hc.1, hc.2])

/-- **The boundary facts the round, close and input steps use.**  `W ℓ ly st b` is candidate `ℓ`'s
honest pair at layer `ly`'s points at the layer's `beta = b`; see the module docstring for the
`Lfzk.Arith` lemma behind each field. -/
structure ZkBoundary (nl : ℕ) (w : ℕ → ℕ) where
  /-- The honest pair at a layer's points, at the layer's `beta`. -/
  W : Lift → ℕ → LayerState logw logc F → F → F × F
  /-- **The layer relation**: the honest claim a layer starts from is the `alpha`-combination of
  its honest pair. -/
  rel : ∀ ℓ ly st b a, H.sum ℓ ly st b a [] = (W ℓ ly st b).1 + a * (W ℓ ly st b).2
  /-- **The layer identity at the full bound**: the honest claim is `EQQ` (at the layer's own
  `beta`) times the next layer's honest pair at the points the bound determines, read at
  `beta_{ly+1} = 0`.  Only at the circuit's own layers `ly < nl`: the run never closes a layer
  below the input layer (`zkCombine`'s and `zkInputBind`'s guards). -/
  final : ∀ ℓ ly st b a bnd wc0 wc1, bnd.length = w ly → ly < nl →
    H.sum ℓ ly st b a bnd = V.eqqOf ly st b a bnd
      * (W ℓ (ly + 1) (V.stNext bnd wc0 wc1) 0).1 * (W ℓ (ly + 1) (V.stNext bnd wc0 wc1) 0).2
  /-- **A layer's honest pair is affine in the layer's own `beta`** (`toLayered_V_decomp`: the
  values are `V⁰ + beta · S`). -/
  W_affine : ∀ ℓ ly st (b : F),
    (W ℓ ly st b).1 = (W ℓ ly st 0).1 + b * ((W ℓ ly st 1).1 - (W ℓ ly st 0).1) ∧
      (W ℓ ly st b).2 = (W ℓ ly st 0).2 + b * ((W ℓ ly st 1).2 - (W ℓ ly st 0).2)
  /-- **Binding a coordinate keeps a pending assertion pending, but for one value**
  (`mlin_bind_card`). -/
  pend_round : ∀ ℓ ly bnd, H.Pend ℓ ly bnd →
    (univ.filter fun r : F => ¬ H.Pend ℓ ly (bnd ++ [r])).card ≤ 1
  /-- **A pending assertion at the full bound is the slope of the next layer's pair in its
  `beta`**: the assertion MLE at the bound points is `W 1 − W 0`, and it is non-zero. -/
  pend_close : ∀ ℓ ly bnd wc0 wc1, bnd.length = w ly → H.Pend ℓ ly bnd →
    W ℓ (ly + 1) (V.stNext bnd wc0 wc1) 1 ≠ W ℓ (ly + 1) (V.stNext bnd wc0 wc1) 0
  /-- **The input layer has no assertions**: nothing is pending at or below the last layer. -/
  pend_last : ∀ ℓ j bnd, nl ≤ j + 1 → ¬ H.Pend ℓ j bnd
  /-- **The input layer**: the verifier's public binding plus the input row's private part, at the
  candidate's columns, is the `alpha`-combination of the candidate's honest input-layer pair. -/
  hin : ∀ ℓ ly bnd wc0 wc1 a, bnd.length = w ly → ly + 1 = nl →
    V.pubBinding bnd a + ∑ i ∈ privIdx ninp V.npub, V.inCoeffs bnd a i * (asg ℓ).1 i
      = (W ℓ (ly + 1) (V.stNext bnd wc0 wc1) 0).1
        + a * (W ℓ (ly + 1) (V.stNext bnd wc0 wc1) 0).2

variable {V H asg}

/--
**A sumcheck round: `k · 2`.**  Branches (rows) and (b) do not read the round.  Branch (c) survives
but for one challenge (`pend_round`).  Branch (a): at the candidate's pad, the round's de-padded
polynomial does not depend on the challenge and passes the clear check by construction; the
expression's new value is its evaluation at the challenge (`builder_next_eval`), so escaping is
`sumcheck_step_reduction`'s bad event, at most two roots.
-/
theorem zkRound_budget {nl : ℕ} {w : ℕ → ℕ} (B : ZkBoundary V H asg nl w) (rm : ZkRoundMsg M F)
    (k : ℕ) (hbal : ∀ y : F, (univ.filter fun c : C => V.decodeF c = y).card ≤ k)
    (cand : Option Lift) (s : ZkState M ninp logw logc F X)
    (hw : ZkWrong V H asg Sat LigDoomed cand s) :
    (univ.filter fun c : C => ¬ ZkWrong V H asg Sat LigDoomed cand (zkRound V rm c s)).card
      ≤ wt cand * (k * 2) := by
  classical
  cases cand with
  | none =>
      refine card_filter_le_of_none _ fun c hc => hc ?_
      cases s <;> exact phantom_stays V H asg Sat LigDoomed _ (by simp [zkRound])
  | some ℓ =>
      rw [show wt (some ℓ) = 1 from rfl, one_mul]
      cases s with
      | running zs =>
          by_cases hpend : H.Pend ℓ zs.layer zs.bound
          · have h1 := Bcs.card_decode_le V.decodeF k hbal
              (fun r => ¬ H.Pend ℓ zs.layer (zs.bound ++ [r])) 1
              (by convert B.pend_round ℓ zs.layer zs.bound hpend)
            refine le_trans (le_trans (Finset.card_le_card ?_) h1) (by omega)
            intro c hc
            simp only [mem_filter, mem_univ, true_and] at hc ⊢
            intro hp
            exact hc (by simp only [zkRound, ZkWrong]; exact Or.inr (Or.inr (Or.inl hp)))
          rcases hw with hrows | hcl | hp | hdeep
          · exact card_filter_le_of_none _ fun c hc => hc (Or.inl hrows)
          · set p := (asg ℓ).2
            set cl := evaluates_to zs.e p
            set Ptrue := H.poly ℓ zs.layer zs.st zs.beta zs.alpha zs.bound
            set P := (roundData rm 0).unpad p cl
            have hfalse : cl ≠ Ptrue.eval 0 + Ptrue.eval 1 := by
              rw [H.sum_eq]; exact hcl
            refine le_trans (Finset.card_le_card (t := univ.filter fun c : C =>
              BadRoundEvent Ptrue P (V.decodeF c)) ?_)
              (RbrBudgets.sumcheckRound V.decodeF k hbal Ptrue P 2
                (H.deg_le ℓ zs.layer zs.st zs.beta zs.alpha zs.bound) le_rfl)
            intro c hc
            simp only [mem_filter, mem_univ, true_and] at hc ⊢
            simp only [zkRound, ZkWrong, not_or, ne_eq, not_not] at hc
            have hesc := hc.2.1
            -- the de-padded polynomial at this challenge is `P`
            have hP : (roundData rm (V.decodeF c)).unpad p cl = P := rfl
            have hchk : check_round_c cl P (V.decodeF c)
                = some ((roundData rm (V.decodeF c)).step p cl) := by
              rw [← hP]; exact check_unpad (roundData rm (V.decodeF c)) p cl
            have hnext : evaluates_to (builder_next zs.e (roundData rm (V.decodeF c))) p
                = (roundData rm (V.decodeF c)).step p cl := builder_next_eval _ _ _
            rcases sumcheck_step_reduction Ptrue P cl ((roundData rm (V.decodeF c)).step p cl)
              (V.decodeF c) hchk hfalse with hstill | hbad
            · exact absurd (by rw [← hnext, hesc,
                ← H.next_eq ℓ zs.layer zs.st zs.beta zs.alpha zs.bound (V.decodeF c)]) hstill
            · exact hbad
          · exact absurd hp hpend
          · exact card_filter_le_of_none _ fun c hc => hc (Or.inr (Or.inr (Or.inr hdeep)))
      | start => exact card_filter_le_of_none _ fun c hc => hc trivial
      | built _ => exact card_filter_le_of_none _ fun c hc => hc trivial
      | challenged _ _ => exact card_filter_le_of_none _ fun c hc => hc trivial
      | accepted => exact card_filter_le_of_none _ fun c hc => hc trivial
      | failed => exact card_filter_le_of_none _ fun c hc => hc trivial

omit [Fintype C] [SumcheckInterp F] in
/-- **The pair slot's count.**  If `b ↦ W b` is affine in each coordinate and the claimed pair
`(W'₀, W'₁)` differs from `W b₀`, then `W'₀ + α·W'₁ = (W β).1 + α·(W β).2` at most `2|F|` of the
`|F|²` pairs `(β, α)`. -/
theorem pair_escape_card (W : F → F × F) (W'0 W'1 b0 : F)
    (haff : ∀ b : F, (W b).1 = (W 0).1 + b * ((W 1).1 - (W 0).1) ∧
      (W b).2 = (W 0).2 + b * ((W 1).2 - (W 0).2))
    (hpair : (W b0).1 ≠ W'0 ∨ (W b0).2 ≠ W'1) :
    (univ.filter fun q : F × F => W'0 + q.2 * W'1 = (W q.1).1 + q.2 * (W q.1).2).card
      ≤ 2 * Fintype.card F := by
  classical
  have hS : ∀ b a : F, (W'0 + a * W'1) - ((W b).1 + a * (W b).2)
      = (W'0 - (W 0).1) + a * (W'1 - (W 0).2) + b * (-((W 1).1 - (W 0).1))
        + a * b * (-((W 1).2 - (W 0).2)) := by
    intro b a
    rw [(haff b).1, (haff b).2]
    ring
  have hne : ¬ (W'0 - (W 0).1 = 0 ∧ W'1 - (W 0).2 = 0 ∧ -((W 1).1 - (W 0).1) = 0 ∧
      -((W 1).2 - (W 0).2) = 0) := by
    rintro ⟨e00, e10, e01, e11⟩
    have h1 := (haff b0).1
    have h2 := (haff b0).2
    rcases hpair with hp | hp
    · exact hp (by linear_combination h1 - b0 * e01 - e00)
    · exact hp (by linear_combination h2 - b0 * e11 - e10)
  refine le_trans (Finset.card_le_card ?_) (bilinear_zero_card
    (fun b a => (W'0 + a * W'1) - ((W b).1 + a * (W b).2)) _ _ _ _ hS hne)
  intro q hq
  simp only [mem_filter, mem_univ, true_and] at hq ⊢
  rw [hq]
  ring

omit [Fintype C] [Fintype F] [DecidableEq F] [SumcheckInterp F] in
/-- **A non-constant affine pair differs from any fixed pair at `0` or at `1`.** -/
theorem exists_pair_ne (W : F → F × F) (W' : F × F) (hne : W 1 ≠ W 0) :
    ∃ b0 : F, (W b0).1 ≠ W'.1 ∨ (W b0).2 ≠ W'.2 := by
  by_cases h0 : W 0 = W'
  · refine ⟨1, ?_⟩
    by_contra hc
    push Not at hc
    exact hne (by rw [h0]; exact Prod.ext hc.1 hc.2)
  · refine ⟨0, ?_⟩
    by_contra hc
    push Not at hc
    exact h0 (Prod.ext hc.1 hc.2)

omit [SumcheckInterp F] in
/--
**Close a layer, start the next: `kpair · 2|F|`.**  Branch (rows) survives.  Branch (b) at layer
`ly` is branch (b) or (c) at layer `ly + 1` with nothing bound.  Branch (c) at the full bound makes
the next layer's honest pair non-constant in its `beta` (`pend_close`), so it differs from the
claimed pair at `beta = 0` or `1`.  Branch (a) with a satisfied new row makes the claimed pair wrong
at `beta = 0` (`pair_wrong_of_row`, `final`).  In the last two cases the next layer's claim minus its
honest value is a form in the drawn `(beta, alpha)`, affine in each (`W_affine`,
`builder_first_eval`, `rel`), and not identically zero: at most `2|F|` of the `|F|²` pairs escape
(`bilinear_zero_card`).
-/
theorem zkCombine_budget {nl : ℕ} {w : ℕ → ℕ} (B : ZkBoundary V H asg nl w) (cm : ZkCloseMsg M F)
    (kpair : ℕ) (hbal : ∀ y : F × F, (univ.filter fun c : C => V.decodePair c = y).card ≤ kpair)
    (cand : Option Lift) (s : ZkState M ninp logw logc F X)
    (hw : ZkWrong V H asg Sat LigDoomed cand s) :
    (univ.filter fun c : C => ¬ ZkWrong V H asg Sat LigDoomed cand (zkCombine nl w V cm c s)).card
      ≤ wt cand * (kpair * (2 * Fintype.card F)) := by
  classical
  cases cand with
  | none =>
      refine card_filter_le_of_none _ fun c hc => hc ?_
      cases s with
      | running zs =>
          refine phantom_stays V H asg Sat LigDoomed _ ?_
          simp only [zkCombine]
          split_ifs <;> simp
      | _ => exact phantom_stays V H asg Sat LigDoomed _ (by simp [zkCombine])
  | some ℓ =>
      rw [show wt (some ℓ) = 1 from rfl, one_mul]
      cases s with
      | running zs =>
          by_cases hlen : zs.bound.length = w zs.layer ∧ zs.layer + 1 < nl
          · set p := (asg ℓ).2
            -- the count, from any `beta` at which the claimed pair is not the honest one
            have hcount : ∀ b0 : F,
                ((B.W ℓ (zs.layer + 1) (V.stNext zs.bound cm.wc0 cm.wc1) b0).1
                    ≠ cm.wc0 + p cm.dwL ∨
                  (B.W ℓ (zs.layer + 1) (V.stNext zs.bound cm.wc0 cm.wc1) b0).2
                    ≠ cm.wc1 + p cm.dwR) →
                (univ.filter fun c : C =>
                  ¬ ZkWrong V H asg Sat LigDoomed (some ℓ)
                    (zkCombine nl w V cm c (.running zs))).card
                  ≤ kpair * (2 * Fintype.card F) := by
              intro b0 hpair
              have hcnt := pair_escape_card
                (fun b => B.W ℓ (zs.layer + 1) (V.stNext zs.bound cm.wc0 cm.wc1) b)
                (cm.wc0 + p cm.dwL) (cm.wc1 + p cm.dwR) b0
                (fun b => B.W_affine ℓ (zs.layer + 1) _ b) hpair
              refine le_trans (Finset.card_le_card ?_) (Bcs.card_decode_le V.decodePair kpair hbal
                (fun q => cm.wc0 + p cm.dwL + q.2 * (cm.wc1 + p cm.dwR)
                  = (B.W ℓ (zs.layer + 1) (V.stNext zs.bound cm.wc0 cm.wc1) q.1).1
                    + q.2 * (B.W ℓ (zs.layer + 1) (V.stNext zs.bound cm.wc0 cm.wc1) q.1).2)
                (2 * Fintype.card F) (by convert hcnt))
              intro c hc
              simp only [mem_filter, mem_univ, true_and] at hc ⊢
              simp only [zkCombine, if_pos hlen, ZkWrong, not_or, ne_eq, not_not] at hc
              have hesc := hc.2.1
              rw [builder_first_eval, B.rel] at hesc
              exact hesc
            by_cases hpend : H.Pend ℓ zs.layer zs.bound
            · obtain ⟨b0, hb0⟩ := exists_pair_ne
                (fun b => B.W ℓ (zs.layer + 1) (V.stNext zs.bound cm.wc0 cm.wc1) b)
                (cm.wc0 + p cm.dwL, cm.wc1 + p cm.dwR)
                (B.pend_close ℓ zs.layer zs.bound cm.wc0 cm.wc1 hlen.1 hpend)
              exact hcount b0 hb0
            rcases hw with hrows | hcl | hp | ⟨j, hj, hpj⟩
            · refine card_filter_le_of_none _ fun c hc => hc ?_
              simp only [zkCombine, if_pos hlen, ZkWrong]
              exact Or.inl (rowsBad_append _ _ _ hrows)
            · by_cases hrow : ligero_layer_checks (closeRow V zs cm).e p (closeRow V zs cm).eqq
                  (closeRow V zs cm).wc0 (closeRow V zs cm).wc1 (closeRow V zs cm).var_dwL
                  (closeRow V zs cm).var_dwR (closeRow V zs cm).var_dwLR
              · have hfin := B.final ℓ zs.layer zs.st zs.beta zs.alpha zs.bound cm.wc0 cm.wc1 hlen.1
                  (by have := hlen.2; omega)
                have hpair := pair_wrong_of_row hrow hcl hfin
                exact hcount 0 (by simpa only [closeRow] using hpair)
              · refine card_filter_le_of_none _ fun c hc => hc ?_
                simp only [zkCombine, if_pos hlen, ZkWrong]
                exact Or.inl ⟨closeRow V zs cm, List.mem_append_right _ (by simp), hrow⟩
            · exact absurd hp hpend
            · refine card_filter_le_of_none _ fun c hc => hc ?_
              simp only [zkCombine, if_pos hlen, ZkWrong]
              rcases Nat.lt_or_ge (zs.layer + 1) j with hlt | hge
              · exact Or.inr (Or.inr (Or.inr ⟨j, hlt, hpj⟩))
              · obtain rfl : j = zs.layer + 1 := by omega
                exact Or.inr (Or.inr (Or.inl hpj))
          · refine card_filter_le_of_none _ fun c hc => hc ?_
            simp only [zkCombine, if_neg hlen, ZkWrong]
      | start => exact card_filter_le_of_none _ fun c hc => hc trivial
      | built _ => exact card_filter_le_of_none _ fun c hc => hc trivial
      | challenged _ _ => exact card_filter_le_of_none _ fun c hc => hc trivial
      | accepted => exact card_filter_le_of_none _ fun c hc => hc trivial
      | failed => exact card_filter_le_of_none _ fun c hc => hc trivial

omit [SumcheckInterp F] in
/--
**The input binding: `k · 1`.**  Branches (b) and (c) cannot hold at the last layer (`pend_last`),
and the guard demands the last layer.  For (a) and (rows): an escape is an assignment satisfying the
built system.  Then every emitted row holds, so the claim was wrong and the last row makes the
claimed pair wrong; and the input row says the claimed pair's `alpha_in`-combination is the input
row's linear form, which `hin` says is the honest pair's.  Escaping is `InputBindingBad` at
`alpha_in`.
-/
theorem zkInputBind_budget {nl : ℕ} {w : ℕ → ℕ} (B : ZkBoundary V H asg nl w)
    (cm : ZkCloseMsg M F) (k : ℕ)
    (hbal : ∀ y : F, (univ.filter fun c : C => V.decodeF c = y).card ≤ k)
    (cand : Option Lift) (s : ZkState M ninp logw logc F X)
    (hw : ZkWrong V H asg Sat LigDoomed cand s) :
    (univ.filter fun c : C =>
        ¬ ZkWrong V H asg Sat LigDoomed cand (zkInputBind nl w V cm c s)).card
      ≤ wt cand * (k * 1) := by
  classical
  cases cand with
  | none =>
      refine card_filter_le_of_none _ fun c hc => hc ?_
      cases s with
      | running zs =>
          refine phantom_stays V H asg Sat LigDoomed _ ?_
          simp only [zkInputBind]
          split_ifs with hg
          · exact Or.inr (Or.inr ⟨_, rfl, hg.2.2⟩)
          · simp
      | _ => exact phantom_stays V H asg Sat LigDoomed _ (by simp [zkInputBind])
  | some ℓ =>
      rw [show wt (some ℓ) = 1 from rfl, one_mul]
      cases s with
      | running zs =>
          set p := (asg ℓ).2
          rcases hw with hrows | hcl | hpend | ⟨j, hj, hpj⟩
          · refine card_filter_le_of_none _ fun c hc => hc ?_
            simp only [zkInputBind]
            split_ifs with hg
            · refine ⟨hg.2.2, fun hsat => ?_⟩
              rw [inputSystem, buildSystemMulti_Sat] at hsat
              obtain ⟨L, hL, hbad⟩ := hrows
              exact hbad (hsat.1 L (List.mem_append_left _ hL))
            · trivial
          · set Wn := B.W ℓ (zs.layer + 1) (V.stNext zs.bound cm.wc0 cm.wc1) 0
            refine le_trans (Finset.card_le_card (t := univ.filter fun c : C =>
              InputBindingBad Wn.1 Wn.2 (cm.wc0 + p cm.dwL) (cm.wc1 + p cm.dwR) (V.decodeF c))
              ?_) (RbrBudgets.inputBind V.decodeF k hbal _ _ _ _)
            intro c hc
            simp only [mem_filter, mem_univ, true_and] at hc ⊢
            by_cases hg : zs.bound.length = w zs.layer ∧ zs.layer + 1 = nl ∧
                Fits V (inputSystem V zs cm (V.decodeF c))
            · simp only [zkInputBind, if_pos hg, ZkWrong, not_and, not_not] at hc
              have hsat := hc hg.2.2
              rw [inputSystem, buildSystemMulti_Sat] at hsat
              obtain ⟨hlay, hinp⟩ := hsat
              have hrow := hlay (closeRow V zs cm) (List.mem_append_right _ (by simp))
              have hfin := B.final ℓ zs.layer zs.st zs.beta zs.alpha zs.bound cm.wc0 cm.wc1 hg.1
                (by have := hg.2.1; omega)
              have hpair := pair_wrong_of_row hrow hcl hfin
              refine ⟨hpair, ?_⟩
              have hhin := B.hin ℓ zs.layer zs.bound cm.wc0 cm.wc1 (V.decodeF c) hg.1 hg.2.1
              simp only [ligero_input_row] at hinp
              linear_combination hhin.symm + hinp
            · simp only [zkInputBind, if_neg hg, ZkWrong, not_true_eq_false] at hc
          · refine card_filter_le_of_none _ fun c hc => hc ?_
            simp only [zkInputBind]
            split_ifs with hg
            · have hlast := hg.2.1
              exact absurd hpend (B.pend_last ℓ zs.layer zs.bound (by omega))
            · trivial
          · refine card_filter_le_of_none _ fun c hc => hc ?_
            simp only [zkInputBind]
            split_ifs with hg
            · have hlast := hg.2.1
              exact absurd hpj (B.pend_last ℓ j [] (by omega))
            · trivial
      | start => exact card_filter_le_of_none _ fun c hc => hc trivial
      | built _ => exact card_filter_le_of_none _ fun c hc => hc trivial
      | challenged _ _ => exact card_filter_le_of_none _ fun c hc => hc trivial
      | accepted => exact card_filter_le_of_none _ fun c hc => hc trivial
      | failed => exact card_filter_le_of_none _ fun c hc => hc trivial

variable (V H asg)

omit [Fintype F] [DecidableEq F] [SumcheckInterp F] in
/--
**Ligero's challenge from a doomed prefix: `kchal · |escaping sys|`, no list factor.**  A doomed
prefix is `built sys` with `sys` fitting and no candidate satisfying it; the state after is
`challenged sys x`, doomed iff `LigDoomed sys x`.
-/
theorem zkLigChallenge_budget [Fintype Lift] [DecidableEq X] (escaping : LigeroSystem ninp M F → Finset X)
    (hesc : ∀ sys, Fits V sys → NoSat asg sys → ∀ x, ¬ LigDoomed sys x → x ∈ escaping sys)
    (kchal blig : ℕ)
    (hbal : ∀ y : X, (univ.filter fun c : C => V.decodeChal c = y).card ≤ kchal)
    (hblig : ∀ sys, Fits V sys → NoSat asg sys → kchal * (escaping sys).card ≤ blig)
    (s : ZkState M ninp logw logc F X)
    (hw : ∀ cand : Option Lift, ZkWrong V H asg Sat LigDoomed cand s) :
    (univ.filter fun c : C =>
        ¬ ∀ cand : Option Lift, ZkWrong V H asg Sat LigDoomed cand (zkLigChallenge V c s)).card
      ≤ blig := by
  classical
  cases s with
  | built sys =>
      obtain ⟨hf, hn⟩ := (doomed_built_iff V H asg Sat LigDoomed sys).mp hw
      refine le_trans (Finset.card_le_card (t := univ.filter fun c : C =>
        V.decodeChal c ∈ escaping sys) ?_)
        (le_trans (Bcs.card_preimage_le_of_balanced V.decodeChal kchal hbal (escaping sys))
          (hblig sys hf hn))
      intro c hc
      simp only [mem_filter, mem_univ, true_and, not_forall] at hc ⊢
      obtain ⟨cand, hcand⟩ := hc
      cases cand <;> exact hesc sys hf hn _ hcand
  | start => exact card_filter_le_of_none _ fun c hc => hc fun cand => by cases cand <;> trivial
  | running _ => exact card_filter_le_of_none _ fun c hc => hc fun cand => by cases cand <;> trivial
  | challenged _ _ =>
      exact card_filter_le_of_none _ fun c hc => hc fun cand => by cases cand <;> trivial
  | accepted => exact card_filter_le_of_none _ fun c hc => hc fun cand => by cases cand <;> trivial
  | failed => exact card_filter_le_of_none _ fun c hc => hc fun cand => by cases cand <;> trivial

omit [Fintype F] [DecidableEq F] [SumcheckInterp F] in
/-- **Ligero's query from a doomed prefix: `kq · bq`, no list factor.**  A doomed prefix is
`challenged sys x` with `LigDoomed sys x` (the phantom says so); the run accepts only at a query in
the test. -/
theorem zkLigQuery_budget [Fintype Lift] [Fintype Q] [DecidableEq Q] (acc : LigeroSystem ninp M F → X → Finset Q)
    (kq bq : ℕ) (hbal : ∀ y : Q, (univ.filter fun c : C => V.decodeQuery c = y).card ≤ kq)
    (hbq : ∀ sys x, LigDoomed sys x → (acc sys x).card ≤ bq)
    (s : ZkState M ninp logw logc F X)
    (hw : ∀ cand : Option Lift, ZkWrong V H asg Sat LigDoomed cand s) :
    (univ.filter fun c : C =>
        ¬ ∀ cand : Option Lift, ZkWrong V H asg Sat LigDoomed cand (zkLigQuery V acc c s)).card
      ≤ kq * bq := by
  classical
  cases s with
  | challenged sys x =>
      have hx : LigDoomed sys x := hw none
      refine le_trans (Finset.card_le_card (t := univ.filter fun c : C =>
        V.decodeQuery c ∈ acc sys x) ?_)
        (le_trans (Bcs.card_preimage_le_of_balanced V.decodeQuery kq hbal (acc sys x))
          (Nat.mul_le_mul_left kq (hbq sys x hx)))
      intro c hc
      simp only [mem_filter, mem_univ, true_and, not_forall] at hc ⊢
      by_contra hnot
      obtain ⟨cand, hcand⟩ := hc
      simp only [zkLigQuery, if_neg hnot] at hcand
      cases cand <;> exact hcand trivial
  | start => exact card_filter_le_of_none _ fun c hc => hc fun cand => by cases cand <;> trivial
  | running _ => exact card_filter_le_of_none _ fun c hc => hc fun cand => by cases cand <;> trivial
  | built _ => exact card_filter_le_of_none _ fun c hc => hc fun cand => by cases cand <;> trivial
  | accepted => exact absurd (hw none) (by simp [ZkWrong])
  | failed => exact card_filter_le_of_none _ fun c hc => hc fun cand => by cases cand <;> trivial

end Budgets

end Lfzk.RbrZkLongfellow
